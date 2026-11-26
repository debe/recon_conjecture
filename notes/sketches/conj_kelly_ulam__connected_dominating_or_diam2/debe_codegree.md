# debe_codegree: codegree refinement of the pure class — what transfers, what does not, and three larger classes

Thinker `debe_codegree`, 2026-11-26. Targets: the frozen residuals
`conj_kelly_ulam__connected_dominating_or_diam2__{dominating_edge_impure,diam2_impure}`.
**A sketch, not a result.** Nothing here is checked. It does **not** close either residual.

Step record read first: parent `reduced` (r1), `dead_ends` empty, sketches t1–t5. Read: t4 §§2–4,
§9.2, t5 §1, `options_combinatorial.md` O3, `attack_options.md`, the checked
`L_…__pure_degree_class.lean`. Vocabulary: "paper argument" = mine, unchecked, valid for every n
unless said otherwise. "Tested" / "evidence" = small-graph search; it only served to discard wrong
lemmas and to size classes, and it is never the content of an argument.

## 1. Verdict: partial

| Question | Answer |
|---|---|
| Gap 2 (card-tie of codegree) | **The tie is false**, already for G = H = P₅ (§3). It cannot be repaired: the codegree of (σu, f_u y) is \|N′_u ∩ N(y)\|, a function of the unknown N′_u. |
| What is card-tied instead | The *first-vertex* triangle keys t(x) (triangles through x) and t̄(x) (independent triples through x). For a type-F pair, codeg(x, y) = t(x) + t(y) − (t(G) − t(F)) when x ~ y. So the codegree key is "t(x) plus a second-vertex term", and only t(x) survives the map (x, y) ↦ (σx, f_x y). |
| Gap 1 (transfer of refined purity) | **Closed by a full paper argument under a recognizable side condition (R)** (Theorem A, §4): among vertices of equal degree, t(x) = t(x′) ⇔ t̄(x) = t̄(x′). Under (R) the joint count e_a(F, c) asked for in the task is a deck invariant (Corollary A2). **Open without (R)**, and not derivable from the data this method has: the linear system has a kernel (§5). |
| Strictly larger class than Lemma P | Yes, three, each with a full paper argument for all n: **Theorem D** (level-wise half purity, §7; no codegree; contains Lemma P and t1's (★)), **Theorem B** (triangle/codegree escape, §6), **Theorem E** (one card plus the multiset of triangle keys, §8; this is where the codegree \|N′_u ∩ N(y)\| really bites). |
| Do they reach the residual face? | Purity-type classes: **no, by an all-n argument** (Proposition L, §9): on a graph whose degree classes are automorphism orbits every first-vertex key is constant on degree classes, so every refinement collapses to Lemma P. Theorem E does reach every known member (evidence only), but its argument is generic (it holds verbatim for tournaments), so it is a carving tool, not a decisive step. |

Recommended child (best ratio of bite to Lean cost): **Theorem D**. Its Lean body elaborates
(§12), and the checked proof of `pure_degree_class` already contains all but about 250 lines of
it.

## 2. Setting

G on n ≥ 4 vertices (n ≥ 4 is needed for Kelly's lemma on triples; Theorem D needs only n ≥ 3).
A hypomorphism is σ with card isomorphisms f_x : G − x ≅ H − σx. From t4 §2:
T0 (deg_H σx = deg_G x, e(G) = e(H)), T1 (if N′_u := f_u⁻¹(N_H(σu)) equals N(u) for one u, then
G ≅ H), L1 (the map Φ(x, y) = (σx, f_x y) is a bijection of ordered pairs that keeps the type
F = G − x − y), Lemma G and Lemma P (checked as `pure_degree_class`).

**Vertex keys.** t(x) = number of edges inside N(x); t̄(x) = number of non-edges inside
V ∖ N[x]; κ(x) = (deg x, t(x), t̄(x)). Totals t(G), t̄(G) = triangles, independent triples.

**K0 (keys are card-tied).** κ_H(σx) = κ_G(x).
Paper argument: t(G) = t(H) and t̄(G) = t̄(H) by Kelly's lemma with k = 3 < n (checked:
`conj_kelly_ulam__disconnected__kelly_induced_count`, F = K₃ and F = 3K₁). t(x) = t(G) − t(G − x),
and f_x gives t(G − x) = t(H − σx); the same for t̄. Degree is T0.

**Pair laws.** For x ≠ y put F = G − x − y, s = e(G) − e(F), c = t(G) − t(F), c̄ = t̄(G) − t̄(F),
γ = codeg(x, y), γ̄ = number of common non-neighbours outside {x, y}.

| | x ≁ y | x ~ y |
|---|---|---|
| bit law (t4) | deg x + deg y = s | deg x + deg y = s + 1 |
| Law 0 / its dual | t(x) + t(y) = c | t(x) + t(y) = c + γ |
| Law 1 / its dual | t̄(x) + t̄(y) = c̄ + γ̄ | t̄(x) + t̄(y) = c̄ |

Paper argument: inclusion–exclusion on triangles through x or y; a triangle through both needs
the edge xy and a common neighbour. Law 1 is Law 0 in the complement. s, c, c̄ depend only on F
and on deck invariants, so the same constants hold in H.

So **t is exact on non-adjacent pairs and t̄ is exact on adjacent pairs**; each is off by a
codegree on the other side. This is t4 §9.2 ("the correction is [x ~ y]·codeg") turned into a
tool: use two keys, one exact on each side.

Typed counts, for a key k and a type F, over ordered pairs (x, y), x ≠ y, of type F:
π_k(F) = #{κ(x) = k}, ε_k(F) = #{κ(x) = k, x ~ y}, ν_k(F) = π_k − ε_k.
**L1′.** π_k(F; G) = π_k(F; H) (Φ keeps the type and, by K0, the first key).

## 3. Gap 2: the codegree is not card-tied

Take G = H = P₅ = u – p₁ – p₂ – p₃ – p₄, σ = id, f_x = id for x ≠ u, and f_u = the reflection
of the path G − u = p₁p₂p₃p₄. This is a hypomorphism. Φ(u, p₂) = (u, p₃). Both pairs are
non-adjacent, have deg u = 1 and type K₁ + K₂, but codeg(u, p₂) = 1 and codeg(u, p₃) = 0.

So the key (deg x, type, codeg(x, y)) is **not** preserved by Φ, and no argument in the style of
Lemma P can place (σu, f_u y) in the codegree class of (u, y). In general
codeg_H(σu, f_u y) = |N′_u ∩ N_{G−u}(y)|, which depends on the unknown N′_u.

What replaces it: every card-tied *pair* statistic is a function of the rooted card (G − x, y),
and every *count* through y in G − x is already a function of (card type of x, F)
(#Q(G − x) − #Q(F)). So a card-tied refinement of (deg x, F) by subgraph counts is a refinement
by a **first-vertex key** and nothing else. The codegree then enters in two legitimate ways:
as the offset in the laws of §2 (Theorems A, B) and as |N′_u ∩ N(y)| in the key multiset of H
(Theorem E).

## 4. Theorem A: refined purity transfers under (R)

**(R)** For all x, x′ with deg x = deg x′: t(x) = t(x′) ⇔ t̄(x) = t̄(x′).
(R) is a property of the multiset of keys, so by K0 it passes to every hypomorphic H. It
contains t4's observed face condition "Σ_{w~x} deg w is a function of deg x" (two main
eigenvalues), because t̄(x) = Σ_{w~x} deg w − t(x) + g(deg x) with
g(d) = C(n − 1, 2) − e(G) − d(2n − 3 − d)/2 (count the bichromatic corners of the triples
through x; own derivation; the identity was tested on every graph with n ≤ 7).

**Theorem A (refined Lemma G).** If G satisfies (R) and H is hypomorphic to G, then
ε_k(F; G) = ε_k(F; H) for every key k and type F.

Paper argument. Fix F. Let Ω be the set of keys that occur at a vertex; Ω is the same for G and
H. By (R), an element of Ω is determined by its (deg, t) part and also by its (deg, t̄) part.
For k = (a, t, t̄) ∈ Ω define two *partner keys*, both computed from Ω, s, c, c̄ alone:
- k^adj = the unique key of Ω with (deg, t̄) = (s + 1 − a, c̄ − t̄), if there is one;
- k^non = the unique key of Ω with (deg, t) = (s − a, c − t), if there is one.

If k ∉ Ω both sides of the claim are 0. For k ∈ Ω, in G and in H alike:

1. *Adjacent swap.* (x, y) ↦ (y, x) is a bijection from the adjacent type-F pairs with
   κ(x) = k onto the adjacent type-F pairs with deg x = s + 1 − a and t̄(x) = c̄ − t̄.
   (Forward: bit law and Law 1. Backward: the partner y has deg y = a, t̄(y) = t̄, hence
   κ(y) = k by (R), since k ∈ Ω.) So ε_k = ε_{k^adj}, and ε_k = 0 if k^adj does not exist.
2. *Non-adjacent swap.* In the same way, with the bit law and Law 0: ν_k = ν_{k^non}, and
   ν_k = 0 if k^non does not exist.
3. Put k′ = k^adj and k″ = (k′)^non. Then
   ε_k = ε_{k′} = π_{k′} − ν_{k′} = π_{k′} − ν_{k″} = π_{k′} − π_{k″} + ε_{k″},
   with the convention that a term whose key does not exist is 0, and
   deg k″ = s − (s + 1 − a) = a − 1.
4. Induction on a. π is shared by L1′, the keys k′, k″ are the same for G and H, and ε_{k″} is
   shared by the induction hypothesis (for a = 0 there is no k″). ∎

**Corollary A1 (refined Lemma P).** If G satisfies (R) and some vertex u has: for all y ≠ u and
all x′ ≠ y′ with κ(x′) = κ(u) and G − x′ − y′ ≅ G − u − y, (u ~ y ⇔ x′ ~ y′); then G is
reconstructible. Argument: as t4 §4 with ε_k, π_k in place of e_a, π_a. No card-tie of a pair
statistic is used: (σu, f_u y) has first key κ(u) by K0.

**Corollary A2 (the joint count of the task).** Under (R), for a type-F pair with κ(x) = k the
codegree is a function of (k, F, [x ~ y]): γ = t(k) + t(k^adj) − c if adjacent, and
γ = γ̄ − (n − 2) + s with γ̄ = t̄(k) + t̄(k^non) − c̄ if not. Hence
e_a(F, c₀) = Σ {ε_k(F) : deg k = a, γ(k, F, 1) = c₀} is a deck invariant under (R). Under (R)
the codegree key therefore carries no information beyond κ(x).

**Generalization (paper, not tested).** The argument uses only: a card-tied key containing the
degree, one component exact on non-adjacent pairs, one exact on adjacent pairs, and
injectivity of both projections on Ω. Clique counts through x (K_r, r ≥ 3) are exact on
non-adjacent pairs and independent-set counts on adjacent pairs, so (R_r) "equal degree ⇒
(clique vector equal ⇔ coclique vector equal)" works the same way.

Tested: the recursion of step 3 as a single-graph identity for every graph with (R)
(`debe_codegree_claims.py`, part 2): NO WITNESS, exhaustive n = 3..7 plus 150 random graphs each
on n = 8, 9.

## 5. Gap 1 without (R): why this method stops

All that the method knows about H for a fixed F is: the row sums π_k(F), the swap symmetry, and
the laws of §2, which say which key pairs (k, k′) a type-F pair may carry:
adjacent ⇒ deg + deg′ = s + 1, t̄ + t̄′ = c̄, t + t′ ≥ c; non-adjacent ⇒ deg + deg′ = s,
t + t′ = c, t̄ + t̄′ ≥ c̄. An *abstract table* is a symmetric non-negative integer array on
admissible key pairs with these row sums. ε_k is forced iff it is constant over abstract tables.

Without (R) the admissible graph on keys has even cycles on which ε_k alternates. The shortest
shape (paper): with k₁ = (a, t₁, v), k₂ = (a, t₂, v), t₁ ≠ t₂ (this is exactly a failure of (R)),

    k₁ —adj— (s+1−a, t₃, c̄−v) —adj— k₂ —non— (s−a, c−t₂, w) —adj— (a+1, t₅, c̄−w) —adj— (s−a, c−t₁, w) —non— k₁

is admissible when t₁ + t₃ ≥ c, t₂ + t₃ ≥ c, t₅ ≥ t₁, t₅ ≥ t₂, v + w ≥ c̄. Adding ±1 alternately
keeps every row sum and changes ε_{k₁}. For the degree key alone the admissible graph is a path
with at most one loop (that is the telescoping of Lemma G), so nothing of this kind exists.

Evidence that the kernel is real and not an artefact (`debe_codegree_kernel.py`, linear
programming with the obvious multiplicity caps): for n ≤ 7 every ε_k(F) of every graph is forced
(20112 classes at n = 7). In a random sample of 4000 of the 12346 graphs on 8 vertices, 9 of
137170 classes are not forced over the reals, 4 of them refined-pure in G. Two sample graphs
checked over the integers: `GhEMdW` (key (3, 0, 2): ε = 0 = "all non-adjacent", π = 1, abstract
tables allow ε = 1) and `GHVfCw` (key (4, 2, 1): ε = 0, π = 2, abstract tables allow ε ∈ {0, 1, 2}).
Both fail (R); in `GHVfCw` the keys (4, 2, 0), (4, 2, 1), (4, 2, 2) share (deg, t), which is the
cycle above with t and t̄ exchanged. No class of a graph with (R) was ever unforced, as
Theorem A says.

**Consequence.** "Refined pure ⇒ reconstructible" without (R) is not reachable by counting
first-vertex-keyed pair types. A proof would need an input of a different kind (a second card,
as in t4 §6, or the vertex-level system of §8). I have no such argument. The count e_a(F, c) of
the task stays an **unproved guess** outside (R).

## 6. Theorem B: triangle / codegree escape

Here the codegree is used honestly, as the offset between t(y) and the key of a would-be
partner.

**Esc(u, y).** If u ~ y: there are no z ≠ w with G − z − w ≅ G − u − y, deg z = deg y − 1 and
t(z) = t(y) − codeg(u, y). If u ≁ y: there are no z ≠ w with G − z − w ≅ G − u − y,
deg z = deg y + 1 and t̄(z) = t̄(y) − γ̄(u, y).

**Theorem B.** If Esc(u, y) holds, then [σu ~ f_u y] = [u ~ y] for every hypomorphism. Hence a
graph with a vertex u such that Esc(u, y) for all y ≠ u is reconstructible (T1).

Paper argument, case u ~ y (the other is the complement). Put y* = f_u y, F = G − u − y, and
suppose σu ≁ y*. (σu, y*) is a type-F pair of H with κ(σu) = κ(u). Bit law and Law 0 in H:
deg_H y* = s − deg u = deg y − 1 and t_H(y*) = c − t(u) = t(y) − codeg(u, y) (the last equalities
are the laws in G for the adjacent pair (u, y)). Let z = σ⁻¹y* and w = f_z⁻¹(σu). By K0,
(deg z, t(z)) = (deg y − 1, t(y) − codeg(u, y)), and f_z restricts to G − z − w ≅ H − y* − σu ≅ F.
This contradicts Esc. ∎ No (R), no telescoping: one step of the chain of Theorem A, cut off
because a row is empty.

Remark. Esc(u, y) with u ~ y implies that all type-F pairs with first (deg, t) equal to that of
u are adjacent (a non-adjacent one would have its second vertex as z). So Theorem B is
"refined purity plus a transfer that needs no (R)".

Tested in strong single-card form (`debe_codegree_claims.py`, part 3): NO WITNESS.

## 7. Theorem D: level-wise half purity (the recommended child)

No codegree here. It came out of asking what Lemma P really uses, and it is the largest
explicit class of this sketch.

Call y ≠ u **forced** (for u) if every ordered pair x′ ≠ y′ with deg x′ = deg u and
G − x′ − y′ ≅ G − u − y has the adjacency of (u, y). The *card level* of y is
j(y) = deg y − [u ~ y] = deg_{G−u}(y).

**Theorem D.** Let u be a vertex such that for every j: every neighbour y of u with
deg y = j + 1 is forced, **or** every non-neighbour y ≠ u with deg y = j is forced. Then G is
reconstructible.

Paper argument. Let b(y) = [u ~ y] and b′(y) = [σu ~ f_u y].
1. *Per-pair Lemma P.* If y is forced, b′(y) = b(y). This is the argument of t4 §4 for the one
   type F = G − u − y: Lemma G gives e_a(F; H) = e_a(F; G) ∈ {0, π_a(F)} and (σu, f_u y) is a
   type-F pair with first degree a = deg u.
2. *Level balance (t4 T2, t2 lemma B).* deg_H(f_u y) = j(y) + b′(y), y ↦ f_u y is a bijection
   V − u → V(H) − σu, and by T0 the degree multisets of V(H) − σu and V − u agree. So for all
   k: #{y : j(y) + b′(y) = k} = #{y : j(y) + b(y) = k}. With n′_j = #{y : j(y) = j, b′ = 1} and
   n_j likewise, this reads n′_{k−1} − n′_k = n_{k−1} − n_k; induction from k = 0 gives
   n′_j = n_j for every j.
3. Fix j and let L = {y : j(y) = j}. If the neighbours in L are forced, {b = 1} ∩ L ⊆ {b′ = 1} ∩ L
   and both have n_j elements, so they are equal. If the non-neighbours in L are forced,
   {b′ = 1} ∩ L ⊆ {b = 1} ∩ L, and again equality. So b′ = b everywhere, N′_u = N(u), T1. ∎

Contains:
- **the checked pure degree class** (every y is forced; the implication elaborates in the
  Scratch file of §12);
- **per-vertex purity**: all y forced for one u. The checked Lean proof calls its hypothesis
  only as `hpure u y x z …`, never with another first pair, so its body carries over with one
  changed call: `lean/Recon/Scratch/…/debe_per_vertex.lean` elaborates (Scratch only, not a gate
  verdict);
- **t1's (★) / t2's degree separation** (no neighbour y and non-neighbour w with
  deg y = deg w + 1): then every level has no neighbour or no non-neighbour, and the
  corresponding alternative holds vacuously.

It is a statable fragment of t4's Remark T (row sums from T2, cells from purity), which t4
left as a diagnostic because the full transport class is awkward in Lean.

"Forced" may be widened by Theorem B (Esc) and Corollary A1 ((R) and refined purity) without
changing steps 2–3. In tests that adds almost nothing (§10).

Tested in strong single-card form (`debe_codegree_claim_level.py`): for every u as in Theorem D,
every one-vertex extension of G − u with the degree sequence and the pair table of G attaches
to exactly N(u); NO WITNESS, exhaustive n = 3..7 plus 150 random graphs each on n = 8, 9.

## 8. Theorem E: one card plus the multiset of triangle keys

For u and a graph G′ on the same vertices say G′ **agrees with G off u** if G′ − u = G − u.

**Theorem E.** Let n ≥ 4 and let u be a vertex such that every G′ that agrees with G off u and
has the same multiset of keys {κ_{G′}(x)} as G is isomorphic to G. Then G is reconstructible.

Paper argument. Let H be hypomorphic. Let φ = f_u ∪ {u ↦ σu} and G′ = φ⁻¹(H). G′ agrees with G
off u and G′ ≅ H. The key multiset of H equals that of G by K0. So G ≅ G′ ≅ H. ∎

This is the old scheme "one card plus a recognizable parameter" (t2's class one2 uses
neighbour degrees). What is specific here is the parameter, and it answers the task's item
"a statistic recoverable for (σu, f_u y) from the card at u plus recognizable data": writing
S = N′_u, the vertex f_u y has key

    ( j(y) + [y ∈ S],  t_{G−u}(y) + [y ∈ S]·|S ∩ N(y)|,  t̄_{G−u}(y) + [y ∉ S]·|non-neighbours of y outside S ∪ {u, y}| )

and σu has key (|S|, e(G[S]), ē(G − u − S)). The codegree |S ∩ N(y)| of the unknown pair enters
the *multiset equation* "these n keys are the keys of G". Nothing has to be tied pair by pair.
The hypothesis of Theorem E says that this system in the unknown S has only the solutions
α(N(u)), α ∈ Aut(G − u).

Evidence (§10): every graph on n ≤ 8 vertices satisfies the hypothesis, and so do all six face
members of t4 §8 (n = 8, 12, 16) and Paley(13), Clebsch, 4×4 rook, Shrikhande, Paley(17) minus a
vertex. With degree keys alone 3269 of the 12346 graphs on 8 vertices fail, and so do four of
the six face members and all five SRG graphs. I know **no graph outside the class**, and I
have no argument that none exists; for large n I expect members of the complement (a guess).

**Caution: Theorem E is not graph-specific.** The argument is "pull back, compare a
recognizable multiset" and holds verbatim for tournaments with any recognizable key.
Stockmeyer's tournaments simply fail the hypothesis. So Theorem E cannot be the decisive step.
It turns the residual into "at every vertex u there is a non-isomorphic G′ that agrees off u and
has the same triangle keys", which has an "∃ G′" clause (t4 avoided such residuals) and no
known member. Whether that is a better residual than the present one is a strategist decision.

## 9. Proposition L: purity refinements cannot reach the symmetric face

**Proposition L (paper).** Let Aut(G) be transitive on every degree class, and let κ be a
first-vertex key that is a function of the card type and of deck invariants. If a pair (u, y)
is forced in the κ-typed sense (Corollary A1 or Theorem B), it is forced in the degree-typed
sense of §7. So on such a graph the hypotheses of Corollary A1, of Theorem B and of Theorem D
with widened "forced" hold only if those of per-vertex Lemma P, respectively of Theorem D,
already hold.

Argument: x and αx have isomorphic cards, so κ is constant on orbits, i.e. on degree classes;
π_k and ε_k are then the degree-typed counts. For Theorem B: Esc(u, y) implies purity for the
(deg, t) key (remark in §6), which is degree purity here.

Three of t4's six face members are of this kind (computed: `GhEJ]o`, ``K[N_ZpBVe`q{`` and the
n = 16 graph have exactly two vertex orbits, the two degree classes). `KbcrMZwA~c@r` is not
(six orbits of size 2, six distinct keys, (R) fails); it lies outside A, B, D for no structural
reason that I can name. On two-orbit graphs only a statistic of a *pair* can help, and by §3 a
card-tied pair statistic is the rooted card itself. That is t4 §9.2's "per-vertex Lemma G",
which t4 judged close to the conjecture; I agree and have nothing to add. Theorem E reaches
these graphs only because it uses the keys of *all* vertices of H at once.

## 10. Evidence (single-graph statistics; evidence only)

Scripts next to this file. "pure" = checked class; PV = per-vertex purity; D = Theorem D;
D+ = Theorem D with forced widened by Esc and (R)-refined purity; B = Theorem B alone;
A = Corollary A1; E = Theorem E; E_deg = Theorem E with degree keys only.

| n = 8, exhaustive | total | pure (t4 §7) | PV | D | D+ | B | (R) | A | E_deg | E |
|---|---|---|---|---|---|---|---|---|---|---|
| all graphs | 12346 | 11304 | 11983 | 12317 | 12319 | 11844 | 2672 | 2667 | 9077 | 12346 |
| dominating edge (G, Ḡ connected) | 6962 | 6340 | — | 6947 | 6948 | — | — | — | 4681 | 6962 |
| D2 | 218 | 183 | — | 217 | 217 | — | — | — | 152 | 218 |

| Frozen residuals at n = 8 | members | in PV | in B | in D | left after D |
|---|---|---|---|---|---|
| `dominating_edge_impure` | 26 | 13 | 10 | 20 | `GH?gmg`, `GxckIs`, `GKYZ}{`, `Gl]o^[`, `GHvT~o`, `GLvnnw` |
| `diam2_impure` | 5 | 2 | 4 | 4 | `GhEJ]o` |

- n = 7: D holds for 1030 of 1044 graphs; of the 15 residual members (all dominating-edge) 9
  are in D.
- Face members of t4 §8: `GhdYLc`, `GhEKzW` are in D (and in B); `GhEJ]o`, the two n = 12
  graphs and the n = 16 graph are in none of A, B, D (for the three two-orbit ones this is what
  Proposition L says, given that they are not in D) and all six are in E. The four
  SRG-minus-vertex graphs tested for D (n = 12, 15) satisfy (R), are not in D and are in E.
- **The codegree refinements (A, B) add almost nothing on top of D for n ≤ 8**: D+ ∖ D has 2
  graphs at n = 8, none in a residual. (R) is rare for small n (keys collide) and where it
  holds the refined key seldom separates more than the degree does.
- Linear forcing (§5), `debe_codegree_kernel.py`: n ≤ 7 all classes forced; n = 8, sample of
  4000 graphs: 9 of 137170 classes not forced, 4 of them refined-pure, none in a graph with (R).

## 11. What breaks for tournaments, 3-uniform hypergraphs, infinite graphs

| Step | Tournaments | Graph-specific ingredient |
|---|---|---|
| K0 (keys tied) | 3-cycle counts through a vertex are tied by Kelly's lemma; scores are not tied to cards (t1 §8, t4 §10; not re-derived here) | deg x = e(G) − e(G − x) |
| Laws 0 and 1 | fail: every pair carries an arc, so no pair is exempt from the correction term, and there is no complement to dualize in | "a triangle cannot contain a non-edge" and the symmetric bit law |
| Theorems A, B, D | fail with Lemma G (t4 tested the analogue of Lemma G false on Stockmeyer pairs) | bit law |
| Level balance (step 2 of D) | needs tied scores; fails | T0 |
| Theorem E | **holds verbatim** | none; see the caution in §8 |
| Proposition L | holds verbatim | none (it is a negative statement) |

3-uniform hypergraphs: the bit becomes a codegree in [0, n − 2] (t4 §10), so Lemma G and
everything built on it (A, B, D) fail; E again survives formally. Infinite graphs: every
argument here is finite counting.

## 12. Lean

All bodies below elaborate in
`lean/Recon/Scratch/conj_kelly_ulam__connected_dominating_or_diam2/debe_codegree_statements.lean`
(gitignored; `lake env lean`, no errors; **not** a gate verdict). The same file contains two
implications that elaborate there: `pure_of_LD` (the Theorem D statement implies the statement
`S_…__pure_degree_class`, i.e. the new class contains the old one) and `diam2_of`
(Theorem D child + residual-minus-D ⇒ `S_…__diam2_impure`, the shape of a 2-child reduction;
`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).

**Proposed child `level_half_pure` (Theorem D):**
```lean
Recon.ClassReconstructible (fun n G => ∃ u : Fin n, ∀ j : ℕ, (∀ y : Fin n, G.Adj u y → (G.neighborSet y).ncard = j + 1 → ∀ x' y' : Fin n, (G.neighborSet x').ncard = (G.neighborSet u).ncard → x' ≠ y' → Nonempty (G.induce ({u, y}ᶜ : Set (Fin n)) ≃g G.induce ({x', y'}ᶜ : Set (Fin n))) → G.Adj x' y') ∨ (∀ y : Fin n, y ≠ u → ¬ G.Adj u y → (G.neighborSet y).ncard = j → ∀ x' y' : Fin n, (G.neighborSet x').ncard = (G.neighborSet u).ncard → x' ≠ y' → Nonempty (G.induce ({u, y}ᶜ : Set (Fin n)) ≃g G.induce ({x', y'}ᶜ : Set (Fin n))) → ¬ G.Adj x' y'))
```
Builder plan. Import `Recon.Checked.L_conj_kelly_ulam__connected_dominating_or_diam2__pure_degree_class`
and reuse its helpers by name.

| Piece | Content | Source / API | Lines |
|---|---|---|---|
| `forced_adj`, `forced_nonadj` | step 1: the two halves of `key` in the checked main theorem, each for one y with its own hypothesis | copy of the checked proof body (`sym_facts`, `arith`, `pi_eq`, `p_eq_e_add_m`, `hbit`, `bit_law`, `restrictIso`) | 80 |
| `card_deg_iso` | card degree of y equals card degree of f_u y | `SimpleGraph.Iso.mapNeighborSet`, `Nat.card_congr`, `Nat.card_coe_set_eq` | 15 |
| `deg_split` | deg_H(f_u y) = j(y) + b′(y), deg_G y = j(y) + b(y) | checked `deg_in_card` | 20 |
| `level_count` | #{w ≠ σu : deg_H w = k} = #{x ≠ u : deg_G x = k}, and the same set counted through y ↦ f_u y | `Set.ncard_congr` twice (pattern of `pi_eq`) | 60 |
| `level_balance` | n′_j = n_j | `Set.ncard_union_eq` for the split by b, then `Nat.rec` on j with `omega` (pattern of `arith`) | 70 |
| main | step 3: `Set.eq_of_subset_of_ncard_le` per level, then checked `iso_of_nbhd` | | 50 |

Estimate 250–350 new lines, risk low to medium (only `ncard` plumbing; every idea is in the
checked file). Per-vertex purity alone (drop the levels) is the checked proof body with one
changed call (`debe_per_vertex.lean` in the same Scratch directory elaborates); its body is
`∃ u, ∀ y x' y', y ≠ u → deg x' = deg u → x' ≠ y' → G − u − y ≅ G − x' − y' → (u ~ y ↔ x' ~ y')`.

**Optional child `one_card_triangle_keys` (Theorem E):**
```lean
Recon.ClassReconstructible (fun n G => 4 ≤ n ∧ ∃ u : Fin n, ∀ G' : SimpleGraph (Fin n), (∀ a b : Fin n, a ≠ u → b ≠ u → (G'.Adj a b ↔ G.Adj a b)) → (∀ d t s : ℕ, {x : Fin n | (G'.neighborSet x).ncard = d ∧ {p : Fin n × Fin n | G'.Adj x p.1 ∧ G'.Adj x p.2 ∧ G'.Adj p.1 p.2}.ncard = t ∧ {p : Fin n × Fin n | G'ᶜ.Adj x p.1 ∧ G'ᶜ.Adj x p.2 ∧ G'ᶜ.Adj p.1 p.2}.ncard = s}.ncard = {x : Fin n | (G.neighborSet x).ncard = d ∧ {p : Fin n × Fin n | G.Adj x p.1 ∧ G.Adj x p.2 ∧ G.Adj p.1 p.2}.ncard = t ∧ {p : Fin n × Fin n | Gᶜ.Adj x p.1 ∧ Gᶜ.Adj x p.2 ∧ Gᶜ.Adj p.1 p.2}.ncard = s}.ncard) → Nonempty (G ≃g G'))
```
(The pair sets count 2t(x) and 2t̄(x).) Builder plan: K0 from the checked
`L_conj_kelly_ulam__disconnected__kelly_induced_count` at k = 3 with F = ⊤ and F = ⊥ on `Fin 3`
(bridge "S induces K₃ ⇔ S is a 3-clique": `SimpleGraph.cliqueFinset`,
`SimpleGraph.mem_cliqueFinset_iff`, `SimpleGraph.is3Clique_iff`), the split "triangles of G =
triangles through x ⊔ triangles of G − x" (`Finset.filter`, `Finset.map` along
`Function.Embedding.subtype`), invariance of the three counts under an isomorphism
(`Set.ncard_congr`), the permutation φ (the `f`/`g` pair inside the checked `iso_of_nbhd`, as an
`Equiv`), G′ = `SimpleGraph.comap φ H` with `SimpleGraph.Iso.comap`. Estimate 450–700 lines, risk
medium (the triangle split is the new plumbing).

**Not recommended as children now** (bodies `RP` and `ESC` in the Scratch file): Corollary A1
and Theorem B. Each needs K0 and the laws (about 300 lines beyond Theorem E's K0) and buys
almost nothing for n ≤ 8 (§10).

**Reduction shape.** For each frozen residual R: children `level_half_pure` and
"R ∧ ¬(Theorem D predicate)" (¬PURE then follows from ¬D and may be dropped), implication by
`by_cases` (theorem `diam2_of`). The Theorem D child would be stated under both parents; the
proof file is the same up to the name.

## 13. Where this could break

1. **Nothing here closes a residual.** After Theorem D the n = 8 residual still has 7 members,
   and the symmetric face is untouched by every purity-type class (Proposition L).
2. **Theorem A may be nearly empty where it matters.** (R) holds on the two-orbit face, but
   there the refined key equals the degree. I found no residual member that Corollary A1
   removes and Theorem D does not.
3. **Theorem E has unknown strength for large n** and an "∃ G′" residual. Its hypothesis
   quantifies over all graphs agreeing off u; nobody has a structural description of the
   complement class. It must not be read as progress on the conjecture.
4. **K0 needs n ≥ 4** (Kelly with k = 3 < n). The bodies for A, B, E carry `4 ≤ n`; Theorem D
   does not need it.
5. **ℕ subtraction in the laws.** State them additively (t(z) + codeg = t(y)), as in the bodies.
6. **Level balance in Lean** is t2's lemma B in different clothes; t2 estimated 250–450 lines for
   the standalone statement. My estimate is lower because only the count at one vertex is
   needed and `deg_in_card` is already checked.
7. **§5 is an argument about a method, not about graphs.** The LP run says that the linear data
   leave ε_k open for some graphs on 8 vertices; all those graphs are reconstructible
   (McKay, n ≤ 13), so some other input always decides. I did not look for the input.
8. **Strictness of the new classes rests on computed examples** (e.g. `GhdYLc` satisfies the
   Theorem D predicate and has no pure degree). The containment "pure ⊆ D" elaborates in the
   Scratch file; strictness is a single-graph fact a builder could `decide` only with effort.
9. **Attribution.** I found no source for Theorems A, B, D or Proposition L (not searched
   beyond the repo's literature notes). Theorem E is the classical one-card scheme with a new
   parameter.

## 14. Files next to this sketch

| File | What | Result |
|---|---|---|
| `debe_codegree_lib.py` | keys, (R), tables, per-pair forcing labels, class predicates | |
| `debe_codegree_claims.py` | laws of §2; recursion of Theorem A; strong single-card form of per-pair forcing | NO WITNESS, 1549 checks (n = 3..7 exhaustive, 150 random each on n = 8, 9) |
| `debe_codegree_claim_level.py` | Theorem D and level balance, strong single-card form | NO WITNESS, 1549 checks |
| `debe_codegree_stats.py` | per-vertex classes on the residuals (§10) | |
| `debe_codegree_onecard.py` | Theorem E classes (§8, §10) | |
| `debe_codegree_ceiling.py` | one card plus the full pair table (a variant of E; every n = 8 leftover is in it) | |
| `debe_codegree_kernel.py` | linear forcing of ε_k (§5); `g6 <graph6>` gives integer ranges | n ≤ 7: all forced; n = 8 sample: 9 of 137170 not forced |

Run a claim with
`python3 tools/search/small_graphs.py counterexample --claim <file> --n-min 3 --n-max 7 --random 150 --random-n 8 9`.

## 15. Sources

- t1.md–t5.md in this directory (T0, T1, T2, lemma B, (★), Lemma G, Lemma P, Remark T, cut
  identity); `notes/literature/options_combinatorial.md` O3, `attack_options.md`.
- P. J. Kelly, *A congruence theorem for trees*, Pacific J. Math. 7 (1957) 961–968: Kelly's
  lemma; used only through the checked step `conj_kelly_ulam__disconnected__kelly_induced_count`.
- S. K. Gupta, P. Mangal, V. Paliwal, Discrete Math. 272 (2003) 291–296 (pv, pav): secondary via
  arXiv:2601.00620 as recorded in `options_combinatorial.md`; primary UNVERIFIED. **Not used** in
  any argument here; the joint count it suggests is settled only under (R) (Corollary A2).
- J. A. Aravind, S. Monikandan, arXiv:2601.00620 (2026): as summarized in the repo notes; not used.
- P. K. Stockmeyer, J. Graph Theory 1 (1977) 19–25: via t4 §10 and `t4_stockmeyer_check.py`,
  UNVERIFIED against the paper.
- B. D. McKay, arXiv:2102.01942: the conjecture holds for n ≤ 13 (as in CLAUDE.md); this is why
  no test here is a test of reconstructibility.
- Two-main-eigenvalue characterization "Σ_{w~x} deg w is affine in deg x" (Hagos 2002, Linear
  Algebra Appl.): from memory, UNVERIFIED; used only in a remark of §4.
