export const meta = {
  name: 'reduce',
  description: 'Split a stuck step into 2-4 children with a kernel-checked implication; red team screens the children first',
  whenToUse: 'A step is big or builders report missing_lemma. args: {step, hints?: [{statement_en, statement_lean}]}',
  phases: [
    { title: 'Propose', detail: 'design children + R-file, iterate with gate check-reduction --dry' },
    { title: 'Screen', detail: 'red team checks every child for small counterexamples' },
    { title: 'Submit', detail: 'gate check-reduction records the reduction and freezes the children' },
  ],
}

const step = args && args.step
if (!step) throw new Error('reduce: args.step is required')
const hints = args.hints || []

const PROPOSAL = {
  type: 'object',
  properties: {
    ok: { type: 'boolean', description: 'true only if gate check-reduction --dry printed PRECHECK PASSED' },
    bundle_path: { type: 'string' },
    children: { type: 'array', items: { type: 'object', properties: { id: { type: 'string' }, statement_en: { type: 'string' }, statement_lean: { type: 'string' } }, required: ['id', 'statement_en', 'statement_lean'] } },
    rationale: { type: 'string', description: 'why the children are each easier than the parent' },
    gate_output: { type: 'string' },
  },
  required: ['ok', 'bundle_path', 'children', 'rationale', 'gate_output'],
}

phase('Propose')
const prop = await agent(
  `Reduce step ${step} into 2-4 strictly easier child statements whose conjunction implies it. ` +
  (hints.length ? `Builders reported these missing lemmas; use them if they fit: ${JSON.stringify(hints)}. ` : '') +
  `1) \`python3 tools/desk.py status ${step}\` and read its statement file. ` +
  `2) \`python3 tools/gate.py next-reduction ${step}\` gives the reduction theorem name and imports. ` +
  `Name each child with a slug: a short snake_case name for what it claims, starting with a letter ` +
  `(e.g. edge_count, never a number); its step id is ${step}__<slug>. ` +
  `3) Write the proof file lean/Recon/Scratch/${step}/reduction.lean proving ` +
  `\`theorem Recon.Checked.R_${step}_r<k> : Recon.Statements.S_${step}__<slug 1> → ... → Recon.Statements.S_${step} :=\` ` +
  `(imports: Mathlib, the parent statement and each child statement module, nothing else). ` +
  `4) Write notes/sketches/${step}/reduction.json: {"parent": "${step}", "by": "reducer", "proof_file": "lean/Recon/Scratch/${step}/reduction.lean", ` +
  `"children": [{"slug": ..., "title": ..., "statement_en": ..., "statement_lean": <Lean Prop using Recon.* defs>}, ...]}. ` +
  `5) Iterate with \`python3 tools/gate.py check-reduction notes/sketches/${step}/reduction.json --dry\` until PRECHECK PASSED. ` +
  `Do NOT run it without --dry. A child must not restate the parent; a useless split (P → P) earns nothing.`,
  { label: `reducer:${step}`, phase: 'Propose', agentType: 'builder', schema: PROPOSAL })
if (!prop || !prop.ok) return { step, reduced: false, prop }

phase('Screen')
const SCREEN = {
  type: 'object',
  properties: {
    any_false: { type: 'boolean' },
    findings: { type: 'array', items: { type: 'object', properties: { child: { type: 'string' }, witness: { type: 'string' }, encoding_fidelity: { type: 'string' } }, required: ['child', 'witness', 'encoding_fidelity'] } },
  },
  required: ['any_false', 'findings'],
}
const screen = await agent(
  `Screen these proposed child statements of step ${step} for falsity before they enter the ledger: ` +
  `${JSON.stringify(prop.children)}. For each child, encode it in notes/sketches/${step}/screen_<child>.py and run ` +
  `\`python3 tools/search/small_graphs.py counterexample --claim <file> --n-max 7\`. Report any witness.`,
  { label: `screen:${step}`, phase: 'Screen', agentType: 'red-team', schema: SCREEN })
if (screen && screen.any_false) {
  log(`${step}: a child looks false on small graphs; reduction not submitted`)
  return { step, reduced: false, prop, screen }
}

phase('Submit')
const SUBMIT = { type: 'object', properties: { accepted: { type: 'boolean' }, output: { type: 'string' } }, required: ['accepted', 'output'] }
const sub = await agent(
  `Run exactly: \`python3 tools/gate.py check-reduction ${prop.bundle_path} --actor reducer\` from the repository root. ` +
  `accepted = the last line is ACCEPTED. Return the last 30 lines of output. Change nothing.`,
  { label: `submit:${step}`, phase: 'Submit', effort: 'low', schema: SUBMIT })
return { step, reduced: !!(sub && sub.accepted), children: prop.children.map(c => c.id), prop, screen, submit: sub }
