export const meta = {
  name: 'think-structural',
  description: 'Paper first: thinkers sketch routes for one step, a red-team agent attacks each sketch',
  whenToUse: 'A frozen step has no surviving sketch yet. args: {step, angles?: string[]}',
  phases: [
    { title: 'Sketch', detail: 'one thinker per angle writes notes/sketches/<step>/t<i>.md' },
    { title: 'Refute', detail: 'one red-team agent per sketch hunts for a concrete flaw' },
  ],
}

const step = args && args.step
if (!step) throw new Error('think: args.step is required')

// Lease heartbeat: long phases outlive a 120-minute lease. When the caller holds the lease
// (campaign passes args.holder), every long-running worker renews it while it works.
const holder = args && args.holder
const OFF = (args && args.offset) | 0  // sketch numbering offset, so earlier t<i>.md files are kept
const HB = holder
  ? ` Lease heartbeat: holder ${holder} leases step ${step}. Run \`python3 tools/desk.py beat ${step} --holder ${holder} --minutes 120 --note "<what you are doing>"\` ` +
    `when you start, and again whenever about 30 minutes have passed since your last beat (check \`date\`; beat between ` +
    `compile iterations, test runs or sketch sections). If a beat fails because another holder has the lease, stop at once ` +
    `and report that the lease was lost, with what you finished.`
  : ''

const NOCOUNT = ' HARD RULE (overrides any instruction in your role file to test on small graphs): do NOT enumerate or sample graphs, do NOT run tools/search/small_graphs.py or any script that counts, classifies or checks graphs for some range of n, and do NOT report class sizes, membership tables or no-witness counts. The conjecture is known for n <= 13, so small-n statistics carry no weight here. Work by paper argument for all n. At most, ONE explicit hand-constructed graph or family may be described as a counterexample to a lemma, with its verification written out on paper.'
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
    `Write the sketch to notes/sketches/${step}/t${i + 1 + OFF}.md. Start with ` +
    `\`python3 tools/desk.py status ${step}\` and respect its dead_ends. ` +
    `Return the structured summary.` + NOCOUNT + HB,
    { label: `thinker:${step}:t${i + 1 + OFF}`, phase: 'Sketch', agentType: 'thinker', schema: SKETCH }),
  (sk, _a, i) => {
    if (!sk || sk.verdict === 'stuck') return { sketch: sk, verdict: null }
    return agent(
      `Attack the sketch at ${sk.sketch_path} for step ${step} ` +
      `(the statement is in the file named by \`python3 tools/desk.py status ${step}\`). ` +
      (sk.verdict === 'believe_false'
        ? 'The thinker believes the statement is FALSE. Try to confirm with a small-graph witness. Report refuted=true if the falsity argument is wrong. '
        : 'Find the first step that fails. ') +
      'Mark it refuted only with a concrete flaw in the paper argument (or one explicit hand-verified counterexample to a lemma).' + NOCOUNT + HB,
      { label: `refuter:${step}:t${i + 1 + OFF}`, phase: 'Refute', agentType: 'red-team', schema: VERDICT })
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
