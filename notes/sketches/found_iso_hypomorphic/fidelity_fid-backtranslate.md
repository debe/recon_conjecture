# Fidelity review: found_001 (lens: back-translation, reviewer fid-backtranslate)

Statement file: lean/Recon/Statements/S_found_001.lean
sha256 49733e140cd4e0f2da10fd9883cad5412ace17d29c1379762617cf0fbfdc2809 (matches ledger statement_sha256
and human_approved_sha256).

## 1. Independent reading of the Lean (written before reading statement_en)

`∀ (n : ℕ) (G H : SimpleGraph (Fin n)), Nonempty (G ≃g H) → Recon.Hypomorphic G H`

Expanding `Recon.Hypomorphic` and `Recon.card` (Basic.lean):

> For every natural number n and every pair of simple graphs G, H on the vertex set
> {0, ..., n-1}: if there is a graph isomorphism from G to H (a bijection f of the vertices with
> G.Adj a b <-> H.Adj (f a) (f b)), then there is a bijection sigma of {0, ..., n-1} such that,
> for every vertex x, the subgraph of G induced on all vertices except x is isomorphic
> to the subgraph of H induced on all vertices except sigma(x).

I confirmed this unfolding mechanically. In a scratch file importing only
`Recon.Statements.S_found_001`, `S_found_001 ↔ ∀ n G H, Nonempty (G ≃g H) → ∃ σ : Fin n ≃ Fin n,
∀ x, Nonempty (G.induce {x}ᶜ ≃g H.induce {σ x}ᶜ)` is closed by `Iff.rfl`, and the scratch file
elaborates under the pinned toolchain.

## 2. Comparison with statement_en, clause by clause

statement_en: "For every n and all graphs G, H on Fin n: if G and H are isomorphic, then G and H
have the same deck (are hypomorphic)."

| English clause | Lean | Match |
|---|---|---|
| for every n | `∀ (n : ℕ)` | yes. No n >= 3 bound, and none is needed: the implication iso => hypo holds for every n, including n = 0, 1, 2. The English likewise has no bound. |
| all graphs G, H on Fin n | `(G H : SimpleGraph (Fin n))` | yes. Both graphs use the same vertex type `Fin n`, as the English says. |
| G and H are isomorphic | `Nonempty (G ≃g H)` | yes. `≃g` is `RelIso G.Adj H.Adj`: a bijection that preserves and reflects adjacency, which is the correct notion of graph isomorphism. `Nonempty` is the right Prop-level "there exists an isomorphism". |
| same deck (hypomorphic) | `Recon.Hypomorphic G H` | yes. There is a bijection sigma with card G x ≅ card H (sigma x) for all x. That is the standard Bondy–Hemminger definition, and it is equivalent to the multisets of card isomorphism classes being equal. Cards are induced subgraphs on {x}ᶜ (vertex deletion, not edge deletion), and card isomorphism is again `≃g`. |

Quantifier order and scope: n, G and H are universally quantified at the front. The hypothesis
scopes over the conclusion only. The existential over sigma sits inside Hypomorphic, after G and H
are fixed, and that is the correct order (sigma may depend on G and H).

## 3. Failure-mode checklist

- Wrong quantifier order or scope: none.
- Missing or extra hypothesis: none. The absence of `3 ≤ n` is correct here and matches the English.
- `Fin n` against arbitrary types: the English says Fin n, and the Lean uses Fin n. (A general-type
  version would be strictly stronger. It is not what is claimed and not needed.)
- ≤ against <, or off-by-one: no numeric comparisons appear.
- Vacuous: no. The hypothesis is satisfiable, for example by G = H with `Iso.refl`.
- Trivially true: no. It is easy, but not definitionally true. A proof needs to transport each card
  along the isomorphism restricted to {x}ᶜ -> {f x}ᶜ, which is a real (small) Lean lemma. That
  makes it an appropriate foundational target.
- Notion of isomorphism, card or deck: all correct (see the table).
- Nonempty against an explicit structure: `Nonempty` is used in both the hypothesis and the card
  condition, and that is appropriate for a Prop.
- Coercions: `({x}ᶜ : Set (Fin n))` is coerced to a subtype, which is the intended vertex set
  of the card. There are no numeric coercions.

Sanity: the statement is true (take sigma = f and restrict f to the complements). So the
negated twin should not be provable, and nothing here suggests otherwise.

## 4. Side observation (not a fidelity issue)

The ledger record already shows `human_approved: true` / `approved_by: debe` while `fidelity` is
empty and the status is `proposed`. The lifecycle in CLAUDE.md asks for 2 fidelity passes before
approval. The human may want to confirm that this ordering was intended before freezing.

## Verdict: PASS

The Lean statement says exactly what statement_en says.
