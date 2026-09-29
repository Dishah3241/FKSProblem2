# FKS Problem 2 in dimension three

A Lean-checked proof of the `d = 3` case of FKS Problem 2: **every simple graph on seven
vertices, or its complement, has a unit-distance representation in ℝ³**.
The question is from Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*,
J. Combin. Theory Ser. A 171 (2020), 105146,
[§5, Problem 2](https://arxiv.org/abs/1802.03092).

> A **unit-distance representation** places vertices at distinct points so that every edge
> has length one. Non-edges are unconstrained and may also have length one. Distances are
> Euclidean, not those of the sup metric.

The research audience is discrete geometers and extremal graph theorists studying unit-distance
representations, graph dimension and distance Ramsey questions.

The full question remains **open**: for every positive integer `d`, must every graph on
`2d + 1` vertices, or its complement, have such a representation in ℝᵈ?
[Alon–Kupavskii (2014), §3](https://arxiv.org/abs/1306.3916) defines `f_D(s)` as the least
dimension that works for every graph on `s` vertices in this disjunction. The proved case
gives `f_D(7) ≤ 3`; combined with FKS Theorem 4's published lower bound, it gives `f_D(7) = 3`.
The formal target is the disjunction itself; the numerical lower bound is not formalized here.
The literature check did not establish priority, so no claim of a new or first proof is made.

| | |
|---|---|
| Proof | `questionAt3` is proved; no `sorry` in the development; only `propext`, `Classical.choice` and `Quot.sound` |
| General problem | `question` is stated and marked open; it is not an admitted theorem |
| Comparator | Accepted by Lean and NanoDa in the local macOS run ([record](docs/comparator-2026-09-28.md)) |
| Library | [GraphDimension at the pinned revision](https://github.com/Dishah3241/GraphDimension/tree/9acc3a712d477b79c3a699c160b20726309eb3c6); the main proof is `SimpleGraph.unitDistEmbeddable_three_or_compl_fin_seven` |
| Statement review | Two statements authored blind and proved equivalent in [Stage1](FKSProblem2/Stage1/Equivalence.lean); the owner signed [Compass rows 1–10](docs/compass.md) on 2026-09-24 |
| Release review | grok (grok-4.7-build), run `20260929-001335-5a12c3af`: "publish after fixes", every fix applied ([record](docs/review-2026-09-29.md)) |
| Blueprint | [Source](blueprint/src/content.tex); publication pending |
| `formal-conjectures` | No inherited statement or proof PR; the statement was authored in this project |
| Mathlib | Reusable proof machinery is in GraphDimension; no Mathlib PR for this release |
| Palomar | Not yet submitted |

**Review.** A release review by grok, which wrote none of P9's own Lean, found the statement faithful and the
target right, and asked for documentation fixes, all applied ([record](docs/review-2026-09-29.md)). grok models
wrote parts of GraphDimension during earlier rungs, so the review is independent of P9's work but not of the whole
library. The managing agent, Claude Code (Claude Opus 5.5), contributed integration and fixes to the development.

## The statement

[InlineFKSProblem2.lean](FKSProblem2/Standalone/Mathlib/InlineFKSProblem2.lean) imports only
Mathlib and states:

```lean
def HasUnitDistanceRepresentation (d : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → EuclideanSpace ℝ (Fin d),
    Function.Injective p ∧ ∀ u v : V, G.Adj u v → dist (p u) (p v) = 1

def questionAt3 : Prop :=
  ∀ G : SimpleGraph (Fin 7),
    HasUnitDistanceRepresentation 3 G ∨ HasUnitDistanceRepresentation 3 Gᶜ
```

`Fin 7` covers every seven-vertex simple graph up to relabelling; the complement uses the same
vertex set. The generated [Challenge.lean](Challenge.lean) advertises precisely this claim,
and [Solution.lean](Solution.lean) proves it as `FKSProblem2.Palomar.target`.
The challenge's deliberate proof hole is excluded from the development's zero-`sorry` count.
The general statement also includes `d = 0`, the trivial one-vertex case. That case and
`d = 1`, along with the fidelity witnesses and separating examples, are proved here.

## The proof

A seven-vertex graph and its complement have 21 edges between them, so one has at most ten.
The library proves that a graph on at most seven vertices with at most ten edges embeds in ℝ³
unless it contains `K₅` or `K₃,₃` as an ordinary subgraph. The proof deletes low-degree
vertices, uses a degree-two reduction, and classifies the remaining small configurations,
with explicit placements in ℝ³. One six-vertex classification is certified by Lean's kernel
using `decide` over all `2^15` labelled graphs.

If the sparse graph contains `K₅`, its complement is a subgraph of `K₁,₁,₅`, which has an
explicit unit-distance representation in ℝ³. If it contains `K₃,₃`, its complement is a
subgraph of the cone over two disjoint triangles, which also has an explicit representation.
Thus one side always embeds. The repository's predicate bridge transfers that library theorem
to the frozen statement and then to the inline Palomar claim.

## Checking it

Lean and Mathlib are pinned to `v4.35.0-rc2`; the exact dependency revisions are in
[lake-manifest.json](lake-manifest.json). In a linked worktree, first run
`scripts/worktree-setup.sh`. Ensure `lake` is on `PATH`, including for the scripts below:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake exe axioms
lake exe fidelity
lake exe module-system
lake exe layering
lake exe proof-links
lake exe standalone-mathlib
lake exe style
lake exe documentation
lake exe palomar-compatibility
scripts/check-palomar-challenge.sh
scripts/lint-env.sh
leanblueprint all
leanblueprint checkdecls
scripts/audit-probes.sh
```

CI runs these gates. The audit probes test the committed `HEAD`, so release verification
must be repeated after the manager commits the release files. Comparator's command and the
macOS isolation caveat are in its [record](docs/comparator-2026-09-28.md).
