export const meta = {
  name: 'think',
  description: 'Paper first: thinkers sketch routes for one step, a red-team agent attacks each sketch',
  whenToUse: 'A frozen step has no surviving sketch yet. args: {step, angles?: string[]}',
  phases: [
    { title: 'Sketch', detail: 'one thinker per angle writes notes/sketches/<step>/t<i>.md' },
    { title: 'Refute', detail: 'one red-team agent per sketch hunts for a concrete flaw' },
  ],
}

const step = args && args.step
if (!step) throw new Error('think: args.step is required')

const ANGLES = (args.angles && args.angles.length) ? args.angles : [
  'DIRECT: unfold the definitions in lean/Recon/Basic.lean and find the shortest route that Mathlib already supports; favour explicit equivalences and finite counting that Lean can follow.',
  'STRUCTURAL: look for the classical argument in the literature (Kelly counting, induction on vertices or edges, decomposition into components or blocks) and an intermediate lemma that would make the step easy.',
]

const SKETCH = {
  type: 'object',
  properties: {
    verdict: { type: 'string', enum: ['route', 'believe_false', 'stuck'] },
    sketch_path: { type: 'string' },
    summary: { type: 'string' },
    lemmas_needed: { type: 'array', items: { type: 'string' } },
    mathlib_api: { type: 'array', items: { type: 'string' } },
    formalization_risk: { type: 'string', enum: ['low', 'medium', 'high'] },
  },
  required: ['verdict', 'sketch_path', 'summary', 'lemmas_needed', 'formalization_risk'],
}

const VERDICT = {
  type: 'object',
  properties: {
    refuted: { type: 'boolean' },
    flaw: { type: 'string', description: 'exact step that fails and why; empty if none' },
    counterexample: { type: 'string', description: 'graph6 or description, if any' },
    repairable: { type: 'boolean' },
  },
  required: ['refuted', 'flaw', 'repairable'],
}

const results = await pipeline(
  ANGLES,
  (angle, _a, i) => agent(
    `Step ${step}. Write a paper sketch for it from this angle:\n${angle}\n\n` +
    `Write the sketch to notes/sketches/${step}/t${i + 1}.md. Start with ` +
    `\`python3 tools/desk.py status ${step}\` and respect its dead_ends. ` +
    `Return the structured summary.`,
    { label: `thinker:${step}:t${i + 1}`, phase: 'Sketch', agentType: 'thinker', schema: SKETCH }),
  (sk, _a, i) => {
    if (!sk || sk.verdict === 'stuck') return { sketch: sk, verdict: null }
    return agent(
      `Attack the sketch at ${sk.sketch_path} for step ${step} ` +
      `(the statement is in the file named by \`python3 tools/desk.py status ${step}\`). ` +
      (sk.verdict === 'believe_false'
        ? 'The thinker believes the statement is FALSE. Try to confirm with a small-graph witness. Report refuted=true if the falsity argument is wrong. '
        : 'Find the first step that fails. ') +
      'Mark it refuted only with a concrete flaw.',
      { label: `refuter:${step}:t${i + 1}`, phase: 'Refute', agentType: 'red-team', schema: VERDICT })
      .then(v => ({ sketch: sk, verdict: v }))
  },
)

const all = results.filter(Boolean)
const surviving = all.filter(r => r.sketch && r.sketch.verdict === 'route' && r.verdict && !r.verdict.refuted)
const believeFalse = all.filter(r => r.sketch && r.sketch.verdict === 'believe_false' && r.verdict && !r.verdict.refuted)
log(`${step}: ${surviving.length} surviving sketch(es), ${believeFalse.length} falsity claim(s) standing`)

return {
  step,
  surviving: surviving.map(r => ({ path: r.sketch.sketch_path, summary: r.sketch.summary, lemmas: r.sketch.lemmas_needed, risk: r.sketch.formalization_risk, flaw_notes: r.verdict.flaw })),
  believe_false: believeFalse.map(r => ({ path: r.sketch.sketch_path, evidence: r.verdict.counterexample || r.sketch.summary })),
  killed: all.filter(r => r.verdict && r.verdict.refuted).map(r => ({ path: r.sketch.sketch_path, flaw: r.verdict.flaw })),
  note: 'Record surviving sketches with: python3 tools/desk.py sketch <step> --path <p> --by <label> --survived',
}
