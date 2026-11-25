export const meta = {
  name: 'redteam',
  description: 'Hunt for a counterexample to one step on small graphs; if a witness turns up, a builder proves the negated twin',
  whenToUse: 'A step is suspected false (believe_false sketch, statement_seems_false releases). args: {step}',
  phases: [
    { title: 'Hunt', detail: 'encode the statement as a Python claim and search n <= 7 plus random samples' },
    { title: 'Refute', detail: 'turn the witness into a Lean proof of <step>_neg' },
  ],
}

const step = args && args.step
if (!step) throw new Error('redteam: args.step is required')

const HUNT = {
  type: 'object',
  properties: {
    witness_found: { type: 'boolean' },
    claim_file: { type: 'string' },
    encoding_fidelity: { type: 'string', description: 'how exactly the Python claim matches the Lean statement; known gaps' },
    witness: { type: 'string', description: 'graph6 and Lean term(s) from the tool output' },
    search_scope: { type: 'string' },
  },
  required: ['witness_found', 'claim_file', 'encoding_fidelity', 'witness', 'search_scope'],
}

phase('Hunt')
const hunt = await agent(
  `Hunt for a counterexample to step ${step}. Read \`python3 tools/desk.py status ${step}\`. Encode the Lean ` +
  `statement as claim(G) and/or claim_pair(G, H) in notes/sketches/${step}/redteam_hunt.py. Run ` +
  `\`python3 tools/search/small_graphs.py counterexample --claim notes/sketches/${step}/redteam_hunt.py --n-max 7 --random 2000 --random-n 8 9\`. ` +
  `Fix and re-run if the encoding is wrong. Report what the tool printed.`,
  { label: `redteam:${step}:hunt`, phase: 'Hunt', agentType: 'red-team', schema: HUNT })

if (!hunt || !hunt.witness_found) return { step, refuted: false, hunt }

phase('Refute')
// Inline builder (not workflow('build')): workflow nesting is one level and campaign calls us.
const target = `${step}_neg`
const label = 'twin'
const RESULT = {
  type: 'object',
  properties: {
    verdict: { type: 'string', enum: ['ACCEPTED', 'REJECTED', 'GAVE_UP'] },
    file: { type: 'string' },
    gate_output: { type: 'string' },
    notes: { type: 'string' },
  },
  required: ['verdict', 'file', 'gate_output', 'notes'],
}
const build = await agent(
  `Refute step ${step}: prove its negated twin ${target} (Recon.Statements.S_${target} := ¬ S_${step}). ` +
  `The red team found this witness on small graphs: ${hunt.witness}. Encoding notes: ${hunt.encoding_fidelity}. ` +
  `Write lean/Recon/Scratch/${step}/${label}.lean. Exhibit the witness graph(s) explicitly; for small Fin n ` +
  `goals \`decide\` (never native_decide) or explicit case analysis usually works. If the witness does not ` +
  `actually violate the Lean statement (encoding gap), stop and report GAVE_UP explaining the gap. ` +
  `Iterate with \`cd lean && lake env lean Recon/Scratch/${step}/${label}.lean\` and ` +
  `\`python3 tools/gate.py precheck ${target} lean/Recon/Scratch/${step}/${label}.lean\`, then submit once with ` +
  `\`python3 tools/gate.py check ${target} lean/Recon/Scratch/${step}/${label}.lean --actor redteam-${label}\`.`,
  { label: `builder:${target}`, phase: 'Refute', agentType: 'builder', schema: RESULT })
return { step, refuted: !!(build && build.verdict === 'ACCEPTED'), hunt, build }
