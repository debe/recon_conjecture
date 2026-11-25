export const meta = {
  name: 'librarian',
  description: 'Literature sweep and Mathlib API map for one topic, then propose (never freeze) steps with citations',
  whenToUse: 'Opening a program or before attacking a new class. args: {topic, program, maxProposals?}',
  phases: [
    { title: 'Sweep', detail: 'literature scout and Mathlib scout in parallel' },
    { title: 'Propose', detail: 'turn the findings into proposed desk steps' },
  ],
}

const topic = args && args.topic
const program = args && args.program
if (!topic || !program) throw new Error('librarian: args.topic and args.program are required')
const maxProposals = args.maxProposals || 3
const slug = topic.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '')

phase('Sweep')
const [lit, lib] = await parallel([
  () => agent(
    `Literature sweep on "${topic}" for the graph reconstruction conjecture. Write notes/literature/${slug}.md: ` +
    `exact statements, citations (author, year, venue, DOI/arXiv), proof ideas, formalization difficulty. ` +
    `Mark anything not confirmed from a source as UNVERIFIED. Return a short summary of the most formalizable results.`,
    { label: `lit:${slug}`, phase: 'Sweep', agentType: 'librarian' }),
  () => agent(
    `Mathlib API map for "${topic}". Search lean/.lake/packages/mathlib/Mathlib (grep) for the declarations a ` +
    `formalization would need (SimpleGraph.induce, Iso, degree, edgeFinset, Connected, IsTree, counting lemmas, ...). ` +
    `Write notes/mathlib/${slug}.md with exact names, file paths and gaps. Return a short summary.`,
    { label: `mathlib:${slug}`, phase: 'Sweep', agentType: 'librarian' }),
])

phase('Propose')
const PROPS = {
  type: 'object',
  properties: { proposed: { type: 'array', items: { type: 'object', properties: { id: { type: 'string' }, title: { type: 'string' }, source: { type: 'string' } }, required: ['id', 'title', 'source'] } } },
  required: ['proposed'],
}
const props = await agent(
  `Using notes/literature/${slug}.md and notes/mathlib/${slug}.md (summaries: ${lit} /// ${lib}), propose at most ` +
  `${maxProposals} new steps in program ${program}, smallest formalizable results first. Check existing ids with ` +
  `\`python3 tools/desk.py list --program ${program}\` and use the next free <program>_<nnn>. For each: ` +
  `\`python3 tools/desk.py propose <id> --title ... --en ... --lean '<Prop>' --author librarian\` (the Lean body may ` +
  `use only Mathlib and Recon.* from lean/Recon/Basic.lean; no comments, no strings). Fix and retry if desk refuses.`,
  { label: `propose:${slug}`, phase: 'Propose', agentType: 'librarian', schema: PROPS })
return { topic, program, proposed: props ? props.proposed : [], next: 'run the fidelity workflow on each proposed step' }
