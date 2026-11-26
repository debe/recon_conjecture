export const meta = {
  name: 'campaign',
  description: 'One fleet round: strategist picks frozen steps, each runs think -> build | redteam | reduce, then a round report',
  whenToUse: 'The default loop once steps are frozen. args: {maxSteps?: 1, steps?: string[], round?: number}',
  phases: [
    { title: 'Select', detail: 'strategist reads the desk, picks and leases steps' },
    { title: 'Work', detail: 'per step: think, then build / redteam / reduce as results dictate' },
    { title: 'Report', detail: 'record sketches, release leases with reasons, write notes/rounds/<n>.md' },
  ],
}

const maxSteps = (args && args.maxSteps) || 1
const forced = (args && args.steps) || []

const PICKS = {
  type: 'object',
  properties: {
    round: { type: 'number' },
    picks: { type: 'array', items: { type: 'object', properties: {
      step: { type: 'string' },
      plan: { type: 'string', enum: ['think', 'build', 'redteam', 'reduce'] },
      sketches: { type: 'array', items: { type: 'string' } },
      why: { type: 'string' },
    }, required: ['step', 'plan', 'sketches', 'why'] } },
  },
  required: ['round', 'picks'],
}

phase('Select')
const sel = await agent(
  `Plan one campaign round. Run \`python3 tools/desk.py summary\`, read the newest notes/rounds/*.md if any. ` +
  (forced.length ? `Work exactly on these steps: ${forced.join(', ')}. ` : `Pick at most ${maxSteps} frozen, unleased step(s). `) +
  `For each choose a plan (think if no surviving sketch; build if a sketch survived (list its paths); redteam if you ` +
  `suspect it is false; reduce after repeated missing_lemma releases). Lease each: ` +
  `\`python3 tools/desk.py lease <id> --holder campaign --minutes 120 --note "<plan>"\` (the workers renew it with desk.py beat while they run). round = 1 + the highest notes/rounds/<n>.md number.`,
  { label: 'strategist:select', phase: 'Select', agentType: 'strategist', schema: PICKS })
if (!sel || !sel.picks.length) return { round: sel && sel.round, picks: [], note: 'nothing to do: freeze steps first (librarian -> fidelity -> human approve)' }
const picks = sel.picks.slice(0, Math.max(maxSteps, forced.length))
log(`round ${sel.round}: ${picks.map(p => `${p.step}:${p.plan}`).join(', ')}`)

// Every sub-workflow gets the lease holder so its workers renew the lease (desk.py beat).
const run = (name, a) => workflow(name, { ...a, holder: 'campaign' }).catch(e => ({ error: String(e) }))

const outcomes = await pipeline(
  picks,
  p => {
    if (p.plan === 'build') return run('build', { step: p.step, sketches: p.sketches }).then(r => ({ kind: 'build', r }))
    if (p.plan === 'redteam') return run('redteam', { step: p.step }).then(r => ({ kind: 'redteam', r }))
    if (p.plan === 'reduce') return run('reduce', { step: p.step }).then(r => ({ kind: 'reduce', r }))
    return run('think', { step: p.step }).then(r => ({ kind: 'think', r }))
  },
  (prev, p) => {
    if (prev.kind !== 'think' || !prev.r || prev.r.error) return [prev]
    if (prev.r.surviving && prev.r.surviving.length)
      return run('build', { step: p.step, sketches: prev.r.surviving.map(s => s.path) }).then(r => [prev, { kind: 'build', r }])
    if (prev.r.believe_false && prev.r.believe_false.length)
      return run('redteam', { step: p.step }).then(r => [prev, { kind: 'redteam', r }])
    return [prev]
  },
  (hist, p) => {
    const last = hist[hist.length - 1]
    if (last.kind !== 'build' || !last.r || last.r.accepted) return hist
    const lemmas = (last.r.results || []).flatMap(x => x.missing_lemmas || [])
    if (!lemmas.length) return hist
    return run('reduce', { step: p.step, hints: lemmas }).then(r => [...hist, { kind: 'reduce', r }])
  },
)

phase('Report')
const report = await agent(
  `Write the report for campaign round ${sel.round} to notes/rounds/${sel.round}.md. Outcomes (JSON): ` +
  `${JSON.stringify(outcomes).slice(0, 60000)}\n` +
  `Also: (1) attach every surviving sketch with \`python3 tools/desk.py sketch <id> --path <p> --by <label> --survived\` ` +
  `and killed ones without --survived; (2) for every picked step that is still frozen, release it: ` +
  `\`python3 tools/desk.py release <id> --holder campaign --reason <reason> --note "<what was tried>"\`; ` +
  `(3) verify claims against \`python3 tools/desk.py summary\` - only the desk decides what is checked; ` +
  `(4) end with 1-3 recommended next actions. Use only the status words checked, refuted, reduced, sketch, proposed, dead.`,
  { label: 'strategist:report', phase: 'Report', agentType: 'strategist' })
return { round: sel.round, picks, outcomes, report }
