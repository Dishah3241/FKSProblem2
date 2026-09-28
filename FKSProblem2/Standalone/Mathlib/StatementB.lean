/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Frankl–Kupavskii–Swanepoel, Problem 2

Source: *Embedding graphs in Euclidean space*, JCTA 171 (2020), 105146,
arXiv:1802.03092, §5, Problem 2.

A unit-distance representation is an injective map into Euclidean space that sends edges
to pairs at distance exactly one. Non-edges are unconstrained, including permission to have
distance one. This is the source's definition, not the stronger faithful representation.
`EuclideanSpace ℝ (Fin d)` has the Euclidean norm, not the supremum norm on functions.

The vertices are labelled by `Fin (2 * d + 1)`. Every graph of the required order can be
labelled this way. Complementation keeps this entire type: `Gᶜ.Adj u v` means
`u ≠ v ∧ ¬ G.Adj u v`, including edges from an isolated vertex to all other vertices.

The fidelity companions below are propositions specifying examples, not proofs of them.
-/

@[expose] public section

namespace FKSProblem2.StatementB

/-- The question at a fixed natural dimension `d`: for every simple graph on `2 * d + 1`
vertices, there exists an injective placement for which either all edges of the graph or
all edges of its complement have length one. The placement and the alternative may depend
on the graph. There is no restriction on non-edges and no minimum-degree hypothesis.

This definition also includes the boundary `d = 0`, beyond the positive-dimensional question:
there is one vertex and no edges in either graph, so the unique map into `ℝ⁰` suffices. -/
def problem2At (d : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin (2 * d + 1)),
    ∃ f : Fin (2 * d + 1) → EuclideanSpace ℝ (Fin d),
      Function.Injective f ∧
        ((∀ u v, G.Adj u v → dist (f u) (f v) = 1) ∨
          (∀ u v, Gᶜ.Adj u v → dist (f u) (f v) = 1))

/-- Open problem: the whole question, over precisely the positive dimensions `d = n + 1`.
The quantifier order is dimension, graph, then placement and choice of graph or complement;
the elementary content of the latter quantifiers is displayed in `problem2At`. -/
def problem2 : Prop :=
  ∀ n : ℕ, problem2At (n + 1)

/-- The first target: every graph on seven vertices or its complement has an injective
unit-distance representation in three-dimensional Euclidean space. -/
def problem2Three : Prop :=
  problem2At 3

/-- A boundary check together with a nondegenerate instance: the question holds for one
vertex in `ℝ⁰` and for every graph on three vertices in `ℝ¹`. The second conjunct tests a
positive dimension with actual edges, rather than only the vacuous one-vertex case. -/
def problem2At.witness : Prop :=
  problem2At 0 ∧ problem2At 1

/-- Two separations in dimension one. The question for three vertices holds, but the
version requiring the graph itself always to embed fails (the triangle is a counterexample).
Moreover, the graph consisting of the edge `0--1` and the isolated vertex `2` has an injective
unit-distance representation with the non-edge `1--2` also at distance one, for example at
coordinates `0, 1, 2`. Thus edge preservation does not mean faithful representation. -/
def problem2At.separating : Prop :=
  problem2At 1 ∧
    (¬ ∀ G : SimpleGraph (Fin 3),
      ∃ f : Fin 3 → EuclideanSpace ℝ (Fin 1),
        Function.Injective f ∧ ∀ u v, G.Adj u v → dist (f u) (f v) = 1) ∧
    ∃ G : SimpleGraph (Fin 3),
      (∀ u v, G.Adj u v ↔ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∧
      ∃ f : Fin 3 → EuclideanSpace ℝ (Fin 1),
        Function.Injective f ∧
          (∀ u v, G.Adj u v → dist (f u) (f v) = 1) ∧
          ¬ G.Adj 1 2 ∧ dist (f 1) (f 2) = 1

/-- The whole question includes the three-vertex case, and that case holds with the
nontrivial separations above. In particular, testing only empty graphs would miss the need
for the complement alternative already at dimension one. -/
def problem2.witness : Prop :=
  (problem2 → problem2At 1) ∧ problem2At.separating

/-- In the dimension-one specialization of the whole question, requiring both alternatives
would be stronger: the triangle cannot be placed on a line with all edges of length one.
The example also distinguishes unit-distance representations from faithful ones. -/
def problem2.separating : Prop :=
  (problem2 → problem2At 1) ∧ problem2At.separating

/-- A seven-vertex test for the first target: the complete graph cannot be represented
in `ℝ³`, whereas its edgeless complement can. Thus the choice of alternative has geometric
content even though both graphs have the prescribed vertex type. The first conjunct records
that this is the dimension tested by `problem2Three`. -/
def problem2Three.witness : Prop :=
  (problem2Three → problem2At 3) ∧
    (¬ ∃ f : Fin 7 → EuclideanSpace ℝ (Fin 3),
      Function.Injective f ∧ ∀ u v, u ≠ v → dist (f u) (f v) = 1) ∧
    (∃ f : Fin 7 → EuclideanSpace ℝ (Fin 3), Function.Injective f)

/-- A non-faithful representation on seven vertices: take the single edge `0--1` and
five isolated vertices, placed at consecutive integer coordinates on an axis in `ℝ³`.
The non-edge `1--2` has length one. All seven vertices remain distinct. The final implication
relates this same graph to the alternatives quantified by `problem2Three`. -/
def problem2Three.separating : Prop :=
  ∃ G : SimpleGraph (Fin 7),
    (∀ u v, G.Adj u v ↔ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∧
    (∃ f : Fin 7 → EuclideanSpace ℝ (Fin 3),
      Function.Injective f ∧
        (∀ u v, G.Adj u v → dist (f u) (f v) = 1) ∧
        ¬ G.Adj 1 2 ∧ dist (f 1) (f 2) = 1) ∧
    (problem2Three →
      ∃ f : Fin 7 → EuclideanSpace ℝ (Fin 3),
        Function.Injective f ∧
          ((∀ u v, G.Adj u v → dist (f u) (f v) = 1) ∨
            (∀ u v, Gᶜ.Adj u v → dist (f u) (f v) = 1)))

end FKSProblem2.StatementB

/-!
## Formal proof

Proved in `StatementBProof`. The bare `witness` and `separating` lines link every `witness`
and `separating` companion, including `problem2Three`'s.

* `problem2` → open: FKS 2020 Problem 2
* `problem2Three` → `problem2Three.proof`
* `witness` → `witness.proof`
* `separating` → `separating.proof`
-/
