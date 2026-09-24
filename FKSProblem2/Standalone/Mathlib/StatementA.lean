/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# FKS Problem 2

The unit-distance Ramsey question of Frankl, Kupavskii and Swanepoel, *Embedding graphs in
Euclidean space*, J. Combin. Theory A 171 (2020), 105146, Problem 2 of §5 (arXiv:1802.03092):
must every simple graph on `2d + 1` vertices, or its complement, admit a unit-distance
representation in `ℝ^d`?

In the notation of N. Alon and A. Kupavskii, *Two notions of unit distance graphs*,
J. Combin. Theory A 125 (2014) (arXiv:1306.3916), this asks whether `f_D(2d + 1) = d`, where
`f_D(s)` is the least `d` such that every graph on `s` vertices, or its complement, has a
unit-distance representation in `ℝ^d`. Theorem 4 of Frankl–Kupavskii–Swanepoel gives
`⌈(s - 1)/2⌉ ≤ f_D(s) ≤ ⌈s/2⌉`, so the question asks whether their lower bound is sharp at
the odd values `s = 2d + 1`.

## Main declarations

* `HasUnitDistanceRepresentation`: `G` has a unit-distance representation in `ℝ^d`: an
  injective placement of the vertices in `ℝ^d` under which every edge has length `1`.
  Non-edges are unconstrained and may also have length `1`; this is the Erdős–Harary–Tutte
  notion.
* `questionAt`: the question, for one fixed `d`.
* `question`: the question, for every `d`.
* `questionAt3`: the `d = 3` instance, the chosen first target.
-/

@[expose] public section

namespace FKSProblem2.StatementA

/-- `G` has a unit-distance representation in `ℝ^d` when there is an injective placement `p` of
the vertices of `G` in the `d`-dimensional Euclidean space `EuclideanSpace ℝ (Fin d)` under
which every edge of `G` has length exactly `1`.

This is the Erdős–Harary–Tutte notion: the vertices sit at distinct points, adjacent vertices
sit at distance `1`, and non-adjacent vertices are unconstrained — they may also sit at
distance `1`, so the placement need not be faithful. (The faithful variant, which also forbids
length-`1` non-edges, is a different quantity; the source tracks it separately as `f_FD`.)
Injectivity constrains only non-adjacent vertices, since adjacent vertices are automatically
`1 > 0` apart. At `d = 0` the space is a single point, so exactly the edgeless graphs on at
most one vertex have a unit-distance representation there. -/
def HasUnitDistanceRepresentation (d : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
    ∃ p : V → EuclideanSpace ℝ (Fin d),
      Function.Injective p ∧ ∀ u v : V, G.Adj u v → dist (p u) (p v) = 1

/-- Separating example for `HasUnitDistanceRepresentation`, against its two nearest wrong
readings. Injectivity does real work: in `ℝ^0` the empty graph on two vertices has a placement
satisfying the edge clause vacuously, yet it has no unit-distance representation, since two
distinct vertices cannot occupy the single point of `ℝ^0`; the reading that drops injectivity
would accept it. Non-edges may have length `1`: the complete bipartite graph `K_{1,3}` has an
injective placement in `ℝ^2` that sends every edge to length `1` and some non-edge to length
`1` as well — the center of the star with three leaves at angles `0°, 60°, 180°` on the unit
circle — which the faithful reading would reject. -/
def HasUnitDistanceRepresentation.separating : Prop :=
    (∃ p : Fin 2 → EuclideanSpace ℝ (Fin 0),
        ∀ u v : Fin 2, (⊥ : SimpleGraph (Fin 2)).Adj u v → dist (p u) (p v) = 1) ∧
      ¬HasUnitDistanceRepresentation 0 (⊥ : SimpleGraph (Fin 2)) ∧
      ∃ p : Fin 1 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 2), Function.Injective p ∧
        (∀ u v : Fin 1 ⊕ Fin 3,
            (completeBipartiteGraph (Fin 1) (Fin 3)).Adj u v →
              dist (p u) (p v) = 1) ∧
        ∃ u v : Fin 1 ⊕ Fin 3,
          ¬(completeBipartiteGraph (Fin 1) (Fin 3)).Adj u v ∧
            dist (p u) (p v) = 1

/-- FKS Problem 2 at a fixed `d`: every simple graph `G` on the vertex set `Fin (2 * d + 1)` —
hence, up to relabeling, every simple graph on exactly `2 * d + 1` vertices — admits a
unit-distance representation in `ℝ^d`, or its complement `Gᶜ` does. The complement is taken on
the same vertex set, with two distinct vertices adjacent exactly when they are non-adjacent in
`G`, so an isolated vertex of `G` is adjacent to every other vertex of `Gᶜ`. Both `d` and `G`
are universally quantified; the placement is existentially quantified inside
`HasUnitDistanceRepresentation`.

This is the source's phrasing "either `G` or its complement on `2d + 1` vertices has dimension
at most `d`": the Erdős–Harary–Tutte dimension of a graph is the least `d` for which it has a
unit-distance representation in `ℝ^d`, and since `ℝ^d'` sits isometrically inside `ℝ^d` for
`d' ≤ d` by padding with zero coordinates, having dimension at most `d` is equivalent to having
a unit-distance representation in `ℝ^d` itself. -/
def questionAt (d : ℕ) : Prop :=
    ∀ G : SimpleGraph (Fin (2 * d + 1)),
      HasUnitDistanceRepresentation d G ∨ HasUnitDistanceRepresentation d Gᶜ

/-- Separating example for `questionAt`, against its nearest wrong reading, the one that drops
the complement. At `d = 1` the question holds: of the four graphs on three vertices up to
isomorphism, the edgeless graph, the single-edge graph and the two-edge path each have a
unit-distance representation in `ℝ^1` (put each edge's endpoints a unit apart and isolated
vertices anywhere), and the triangle has none since three pairwise unit points cannot be
collinear, but the triangle's complement is edgeless. Yet not every graph on three vertices
itself has a unit-distance representation in `ℝ^1`, so the complement is doing real work: the
complement-free misreading is false at `d = 1` while `questionAt 1` is true. -/
def questionAt.separating : Prop :=
    questionAt 1 ∧ ¬∀ G : SimpleGraph (Fin 3), HasUnitDistanceRepresentation 1 G

/-- FKS Problem 2 in full: for every `d`, every simple graph on `2 * d + 1` vertices, or its
complement, has a unit-distance representation in `ℝ^d`. The source asks this for positive `d`;
the instance `d = 0` is one vertex in the one-point space `ℝ^0` and holds trivially, so
quantifying over all of `ℕ` is equivalent to quantifying over the positive integers and adds no
hypothesis. -/
def question : Prop :=
    ∀ d : ℕ, questionAt d

/-- Witness for `question`: the range of the question is inhabited with genuine instances, so
the claim is not vacuous. At `d = 0` the instance is the trivial one-vertex case, and at `d = 1`
it is the settled three-vertex case: every graph on three vertices either has a unit-distance
representation in `ℝ^1` or has an edgeless complement, which embeds any three distinct points. -/
def question.witness : Prop :=
    questionAt 0 ∧ questionAt 1

/-- The `d = 3` instance of FKS Problem 2, the chosen first target: every simple graph on
seven vertices, or its complement, has a unit-distance representation in `ℝ^3`. Since the known
bounds give `3 ≤ f_D(7) ≤ 4`, this instance is equivalent to `f_D(7) = 3`. -/
def questionAt3 : Prop :=
    ∀ G : SimpleGraph (Fin 7),
      HasUnitDistanceRepresentation 3 G ∨ HasUnitDistanceRepresentation 3 Gᶜ

/-- Witness for `questionAt3`: the instance is not satisfied by every graph, so the question is
not trivial — some graphs on seven vertices, such as the complete graph `K₇`, whose seven
pairwise unit points would span six dimensions, have no unit-distance representation in `ℝ^3`
themselves. The content of the question lies in the disjunction with the complement. -/
def questionAt3.witness : Prop :=
    ∃ G : SimpleGraph (Fin 7), ¬HasUnitDistanceRepresentation 3 G

end FKSProblem2.StatementA
