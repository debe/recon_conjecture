export const meta = {
  name: 'build',
  description: 'Lean second: one builder formalizes a step, escalating to two more on failure; the gate decides',
  whenToUse: 'A frozen step has a surviving sketch. args: {step, target?, sketches?: string[], escalate?: boolean}',
  phases: [
    { title: 'Build', detail: 'builder b1 iterates against lake and gate precheck, then gate check' },
    { title: 'Escalate', detail: 'if b1 fails: b2 and b3 try different decompositions in parallel' },
  ],
}

const step = args && args.step
if (!step) throw new Error('build: args.step is required')
const target = args.target || step              // `${step}_neg` to refute the step
const sketches = args.sketches || []
const escalate = args.escalate !== false

// Lease heartbeat: long phases outlive a 120-minute lease. When the caller holds the lease
// (campaign passes args.holder), every long-running worker renews it while it works.
const holder = args && args.holder
const HB = holder
  ? ` Lease heartbeat: holder ${holder} leases step ${step}. Run \`python3 tools/desk.py beat ${step} --holder ${holder} --minutes 120 --note "<what you are doing>"\` ` +
    `when you start, and again whenever about 30 minutes have passed since your last beat (check \`date\`; beat between ` +
    `compile iterations, test runs or sketch sections). If a beat fails because another holder has the lease, stop at once ` +
    `and report that the lease was lost, with what you finished.`
  : ''

const RESULT = {
  type: 'object',
  properties: {
    verdict: { type: 'string', enum: ['ACCEPTED', 'REJECTED', 'GAVE_UP'] },
    file: { type: 'string' },
    gate_output: { type: 'string', description: 'last lines of the gate output' },
    release_reason: { type: 'string', enum: ['none', 'hypothesis_too_weak', 'missing_lemma', 'statement_seems_false', 'does_not_elaborate', 'out_of_time', 'other'] },
    missing_lemmas: {
      type: 'array',
      items: { type: 'object', properties: { statement_en: { type: 'string' }, statement_lean: { type: 'string' } }, required: ['statement_en', 'statement_lean'] },
    },
    notes: { type: 'string', description: 'what was tried, what failed, the closest partial progress' },
  },
  required: ['verdict', 'file', 'gate_output', 'release_reason', 'missing_lemmas', 'notes'],
}

const brief = (label, extra) =>
  `Target ${target} (step ${step}). Write your proof at lean/Recon/Scratch/${step}/${label}.lean. ` +
  (sketches.length ? `Sketches to follow: ${sketches.join(', ')}. ` : 'No sketch: find your own route. ') +
  `Iterate with \`cd lean && lake env lean Recon/Scratch/${step}/${label}.lean\`, then ` +
  `\`python3 tools/gate.py precheck ${target} lean/Recon/Scratch/${step}/${label}.lean\`; when it passes, ` +
  `submit once with \`python3 tools/gate.py check ${target} lean/Recon/Scratch/${step}/${label}.lean --actor ${label}\`. ` +
  `Verdict ACCEPTED only if the gate printed ACCEPTED. ${extra || ''} ` +
  `Stop after about 25 compile iterations without progress and report GAVE_UP with an honest release_reason.` + HB

phase('Build')
const first = await agent(brief('b1'), { label: `builder:${target}:b1`, phase: 'Build', agentType: 'builder', schema: RESULT })
if (first && first.verdict === 'ACCEPTED') return { step, target, accepted: true, by: 'b1', results: [first] }

const stop = !escalate || !first || first.release_reason === 'statement_seems_false' || first.release_reason === 'hypothesis_too_weak'
if (stop) return { step, target, accepted: false, results: [first].filter(Boolean) }

phase('Escalate')
const prior = `A first builder failed. Its notes: ${first.notes}. Its file ${first.file} may be a useful start; copy, do not edit it.`
const STRATS = [
  'Decompose aggressively: prove three to six small helper lemmas first, each compiled on its own.',
  'Change representation: work with explicit equivalences or Finset counting instead of the route b1 took; search Mathlib (grep under lean/.lake/packages/mathlib) for existing lemmas.',
]
const more = await parallel(STRATS.map((s, i) => () =>
  agent(brief(`b${i + 2}`, `${prior} Strategy: ${s}`), { label: `builder:${target}:b${i + 2}`, phase: 'Escalate', agentType: 'builder', schema: RESULT })))
const results = [first, ...more].filter(Boolean)
const win = results.find(r => r.verdict === 'ACCEPTED')
return { step, target, accepted: !!win, results }
