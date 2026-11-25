export const meta = {
  name: 'fidelity',
  description: 'Two independent reviewers check that a proposed root statement says what its English says',
  whenToUse: 'A step is proposed and needs fidelity passes before the human approves it. args: {step}',
  phases: [{ title: 'Review', detail: 'back-translation lens and testing lens, in parallel' }],
}

const step = args && args.step
if (!step) throw new Error('fidelity: args.step is required')

const REVIEW = {
  type: 'object',
  properties: {
    verdict: { type: 'string', enum: ['pass', 'fail'] },
    mismatch: { type: 'string', description: 'the concrete mismatch for a fail; empty for pass' },
    recorded: { type: 'boolean', description: 'desk.py fidelity printed "recorded"' },
    notes_path: { type: 'string' },
  },
  required: ['verdict', 'mismatch', 'recorded', 'notes_path'],
}

const LENSES = [
  ['fid-backtranslate', 'BACK-TRANSLATION: before reading statement_en, write your own precise English reading of the Lean statement (expanding every Recon.* definition from lean/Recon/Basic.lean). Then compare it with statement_en clause by clause.'],
  ['fid-testing', 'TESTING: encode the Lean reading and the English reading as two Python predicates over networkx graphs and run both over all graphs with n <= 6 using tools/search/small_graphs.py as a library (python3 with sys.path including tools/search). Any graph where they differ is a fail. Also check vacuity: does the hypothesis ever hold?'],
]

phase('Review')
const reviews = await parallel(LENSES.map(([label, lens]) => () => agent(
  `Fidelity review of proposed step ${step}. Lens: ${lens}\n` +
  `Write notes to notes/sketches/${step}/fidelity_${label}.md, then record exactly once: ` +
  `\`python3 tools/desk.py fidelity ${step} --reviewer ${label} --verdict pass|fail --notes-file notes/sketches/${step}/fidelity_${label}.md\`.`,
  { label: `${label}:${step}`, phase: 'Review', agentType: 'fidelity-reviewer', schema: REVIEW })))

const ok = reviews.filter(Boolean)
const passes = ok.filter(r => r.verdict === 'pass' && r.recorded).length
if (passes === 2) log(`${step}: 2/2 fidelity passes. Human next: ! python3 tools/desk.py approve ${step} && python3 tools/desk.py freeze ${step}`)
else log(`${step}: ${passes}/2 passes; restate the statement (desk.py propose --replace) before approval`)
return { step, passes, reviews: ok }
