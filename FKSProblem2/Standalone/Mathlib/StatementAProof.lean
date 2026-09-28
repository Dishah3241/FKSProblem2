/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem2.Standalone.Mathlib.StatementA

import FKSProblem2.Standalone.Mathlib.Support.GraphDimensionBridge

import GraphDimension.Extremal.SevenVertices
import GraphDimension.Geometry.Equilateral
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Pairwise
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Proofs of statement A

Every graph on seven vertices, or its complement, has a unit-distance representation in `ℝ³`:
the shared library's seven-vertex disjunction, with the representation predicate rewritten
through the bridge on each side of the disjunction. The `d = 0` and `d = 1` instances of the
question are elementary: an edge, a two-edge path, and an edgeless graph each lie on a line
with their edges at unit length, and the triangle, which does not so lie, has an edgeless
complement.
-/

public section

namespace FKSProblem2.StatementA

/-! ### Points on a coordinate axis

An edge, a two-edge path, and an edgeless graph on three vertices are placed on the real axis
so that their edges join points one unit apart. -/

/-- The point `x` of the real axis, as a point of `EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def linePt (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 x

lemma dist_linePt (x y : ℝ) : dist (linePt x) (linePt y) = |x - y| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]
  simp [linePt, PiLp.single_eq_same]

lemma linePt_ne_linePt {x y : ℝ} (h : x ≠ y) : linePt x ≠ linePt y := by
  intro hxy
  apply h
  simpa [linePt, PiLp.single_eq_same] using
    congrArg (fun p : EuclideanSpace ℝ (Fin 1) => p.ofLp 0) hxy

/-- Every graph on `Fin 3` whose edges join consecutive points among three distinct real
points has a unit-distance representation in `ℝ^1`: an edge, a two-edge path, and an edgeless
graph do, and so does every edgeless complement. -/
lemma hasUnitDistanceRepresentation_fin_three_of (G : SimpleGraph (Fin 3)) (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h01 : G.Adj 0 1 → dist (linePt x) (linePt y) = 1)
    (h02 : G.Adj 0 2 → dist (linePt x) (linePt z) = 1)
    (h12 : G.Adj 1 2 → dist (linePt y) (linePt z) = 1) :
    HasUnitDistanceRepresentation 1 G := by
  refine ⟨fun i => ![linePt x, linePt y, linePt z] i, ?_, ?_⟩
  · intro u v huv
    fin_cases u <;> fin_cases v
    · rfl
    · exact absurd huv (linePt_ne_linePt hxy)
    · exact absurd huv (linePt_ne_linePt hxz)
    · exact absurd huv (linePt_ne_linePt (Ne.symm hxy))
    · rfl
    · exact absurd huv (linePt_ne_linePt hyz)
    · exact absurd huv (linePt_ne_linePt (Ne.symm hxz))
    · exact absurd huv (linePt_ne_linePt (Ne.symm hyz))
    · rfl
  · intro u v huv
    fin_cases u <;> fin_cases v
    · exact absurd (G.ne_of_adj huv rfl) (by decide)
    · exact h01 huv
    · exact h02 huv
    · exact (dist_comm _ _).trans (h01 huv.symm)
    · exact absurd (G.ne_of_adj huv rfl) (by decide)
    · exact h12 huv
    · exact (dist_comm _ _).trans (h02 huv.symm)
    · exact (dist_comm _ _).trans (h12 huv.symm)
    · exact absurd (G.ne_of_adj huv rfl) (by decide)

/-! ### The instances `d = 0` and `d = 1` -/

/-- The `d = 0` instance of the question: the single vertex of `Fin 1` in the one-point space
`ℝ^0`. -/
theorem questionAt_zero : questionAt 0 := by
  intro G
  left
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro u v _
    exact @Subsingleton.elim _ (inferInstanceAs (Subsingleton (Fin 1))) u v
  · intro u v huv
    exact False.elim (G.ne_of_adj huv
      (@Subsingleton.elim _ (inferInstanceAs (Subsingleton (Fin 1))) u v))

/-- The `d = 1` instance of the question: of a graph on three vertices and its complement, one
is an edge, a two-edge path, or edgeless, each of which lies on a line with its edges at unit
length; the triangle, which does not so lie, has an edgeless complement. -/
theorem questionAt_one : questionAt 1 := by
  intro G
  by_cases h01 : G.Adj 0 1 <;> by_cases h02 : G.Adj 0 2 <;> by_cases h12 : G.Adj 1 2
  · -- The triangle: its complement is edgeless.
    right
    have hcompl : Gᶜ = ⊥ := by
      have h10 : G.Adj 1 0 := h01.symm
      have h20 : G.Adj 2 0 := h02.symm
      have h21 : G.Adj 2 1 := h12.symm
      ext u v
      fin_cases u <;> fin_cases v <;>
        simp [SimpleGraph.compl_adj, h01, h02, h12, h10, h20, h21]
    rw [hcompl]
    exact hasUnitDistanceRepresentation_fin_three_of _ 0 1 2 (by norm_num) (by norm_num)
      (by norm_num) (fun h => absurd h (by simp)) (fun h => absurd h (by simp))
      (fun h => absurd h (by simp))
  · -- Edges `0--1` and `0--2`: the two-edge path through `0`.
    left
    exact hasUnitDistanceRepresentation_fin_three_of G 1 0 2 (by norm_num) (by norm_num)
      (by norm_num) (fun h => by norm_num [dist_linePt])
      (fun h => by norm_num [dist_linePt]) (fun h => absurd h h12)
  · -- Edges `0--1` and `1--2`: the two-edge path through `1`.
    left
    exact hasUnitDistanceRepresentation_fin_three_of G 0 1 2 (by norm_num) (by norm_num)
      (by norm_num) (fun h => by norm_num [dist_linePt]) (fun h => absurd h h02)
      (fun h => by norm_num [dist_linePt])
  · -- Edge `0--1` alone.
    left
    exact hasUnitDistanceRepresentation_fin_three_of G 0 1 2 (by norm_num) (by norm_num)
      (by norm_num) (fun h => by norm_num [dist_linePt]) (fun h => absurd h h02)
      (fun h => absurd h h12)
  · -- Edges `0--2` and `1--2`: the two-edge path through `2`.
    left
    exact hasUnitDistanceRepresentation_fin_three_of G 0 2 1 (by norm_num) (by norm_num)
      (by norm_num) (fun h => absurd h h01) (fun h => by norm_num [dist_linePt])
      (fun h => by norm_num [dist_linePt])
  · -- Edge `0--2` alone.
    left
    exact hasUnitDistanceRepresentation_fin_three_of G 1 0 2 (by norm_num) (by norm_num)
      (by norm_num) (fun h => absurd h h01) (fun h => by norm_num [dist_linePt])
      (fun h => absurd h h12)
  · -- Edge `1--2` alone.
    left
    exact hasUnitDistanceRepresentation_fin_three_of G 0 2 1 (by norm_num) (by norm_num)
      (by norm_num) (fun h => absurd h h01) (fun h => absurd h h02)
      (fun h => by norm_num [dist_linePt])
  · -- The edgeless graph.
    left
    exact hasUnitDistanceRepresentation_fin_three_of G 0 1 2 (by norm_num) (by norm_num)
      (by norm_num) (fun h => absurd h h01) (fun h => absurd h h02)
      (fun h => absurd h h12)

/-! ### The `d = 3` instance -/

/-- The `d = 3` instance of the question: the shared library's seven-vertex disjunction, with
the representation predicate rewritten through the bridge on each side of the disjunction. -/
theorem questionAt3.proof : questionAt3 := by
  change ∀ G : SimpleGraph (Fin 7),
    HasUnitDistanceRepresentation 3 G ∨ HasUnitDistanceRepresentation 3 Gᶜ
  intro G
  rcases G.unitDistEmbeddable_three_or_compl_fin_seven with h | h
  · exact Or.inl ((hasUnitDistanceRepresentation_iff_unitDistEmbeddable G 3).mpr h)
  · exact Or.inr ((hasUnitDistanceRepresentation_iff_unitDistEmbeddable Gᶜ 3).mpr h)

/-! ### The fidelity companions -/

/-- `(Real.sqrt 3 / 2) ^ 2` is `3 / 4`. -/
private lemma sq_sqrt_three_div_two : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The three leaves of the star `K_{1,3}`, on the unit circle about the origin at angles
`0°`, `60°`, and `180°`: each leaf is at distance `1` from the origin, and the first two leaves
are at distance `1` from each other. -/
private noncomputable def starLeaf : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![EuclideanSpace.single 0 1,
    EuclideanSpace.single 0 (1 / 2) + EuclideanSpace.single 1 (Real.sqrt 3 / 2),
    EuclideanSpace.single 0 (-1)]

/-- The star `K_{1,3}` with its centre at the origin. -/
private noncomputable def starPoint : Fin 1 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  Sum.elim (fun _ => 0) starLeaf

private lemma dist_starPoint_center (i : Fin 3) :
    dist (starPoint (Sum.inl 0)) (starPoint (Sum.inr i)) = 1 := by
  fin_cases i
  · simp [starPoint, starLeaf, EuclideanSpace.dist_eq]
  · simp [starPoint, starLeaf, EuclideanSpace.dist_eq, sq_sqrt_three_div_two]
    norm_num
  · simp [starPoint, starLeaf, EuclideanSpace.dist_eq]

private lemma starLeaf_injective : Function.Injective starLeaf := by
  intro a b hab
  have h0 : (starLeaf a).ofLp 0 = (starLeaf b).ofLp 0 :=
    congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) hab
  fin_cases a <;> fin_cases b
  all_goals
    first
      | rfl
      | (simp [starLeaf] at h0; try norm_num at h0)

private lemma starPoint_injective : Function.Injective starPoint := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subsingleton.elim a b)
    | inr b =>
      have h : (starPoint (Sum.inl a)).ofLp 0 = (starPoint (Sum.inr b)).ofLp 0 := by
        exact congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) hab
      fin_cases b
      · simp [starPoint, starLeaf] at h
        try norm_num at h
      · simp [starPoint, starLeaf] at h
        try norm_num at h
      · simp [starPoint, starLeaf] at h
        try norm_num at h
  | inr a =>
    cases b with
    | inl b =>
      have h : (starPoint (Sum.inr a)).ofLp 0 = (starPoint (Sum.inl b)).ofLp 0 := by
        exact congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) hab
      fin_cases a
      · simp [starPoint, starLeaf] at h
        try norm_num at h
      · simp [starPoint, starLeaf] at h
        try norm_num at h
      · simp [starPoint, starLeaf] at h
        try norm_num at h
    | inr b => exact congrArg Sum.inr (starLeaf_injective hab)

theorem HasUnitDistanceRepresentation.separating.proof :
    HasUnitDistanceRepresentation.separating := by
  refine ⟨⟨fun _ => 0, fun u v h =>
    False.elim ((SimpleGraph.bot_adj u v).mp h)⟩, ?_,
    starPoint, starPoint_injective, ?_, ?_⟩
  · intro h
    unfold HasUnitDistanceRepresentation at h
    obtain ⟨p, hp, -⟩ := h
    exact (by norm_num : (0 : Fin 2) ≠ 1) (hp (Subsingleton.elim (p 0) (p 1)))
  · intro u v h
    cases u with
    | inl u =>
      cases v with
      | inl v => simp [completeBipartiteGraph_adj] at h
      | inr v => exact dist_starPoint_center v
    | inr u =>
      cases v with
      | inl v => exact (dist_comm _ _).trans (dist_starPoint_center u)
      | inr v => simp [completeBipartiteGraph_adj] at h
  · refine ⟨Sum.inr 0, Sum.inr 1, ?_, ?_⟩
    · simp [completeBipartiteGraph_adj]
    · have hd : dist (starPoint (Sum.inr 0)) (starPoint (Sum.inr 1))
          = dist (starLeaf 0) (starLeaf 1) := rfl
      rw [hd, EuclideanSpace.dist_eq]
      simp only [starLeaf, Matrix.cons_val_zero]
      norm_num [Real.dist_eq, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt 3),
        sq_sqrt_three_div_two]

theorem questionAt.separating.proof : questionAt.separating := by
  refine ⟨questionAt_one, ?_⟩
  intro h
  obtain ⟨f, -, hdist⟩ := h (⊤ : SimpleGraph (Fin 3))
  have hpw : Pairwise fun i j : Fin 3 => dist (f i) (f j) = 1 := fun i j hij =>
    hdist i j ((SimpleGraph.top_adj i j).mpr hij)
  have hcard := EuclideanGeometry.card_le_of_equilateral (p := f) hpw
  simp only [Fintype.card_fin] at hcard
  omega

theorem question.witness.proof : question.witness :=
  ⟨questionAt_zero, questionAt_one⟩

theorem questionAt3.witness.proof : questionAt3.witness := by
  refine ⟨(⊤ : SimpleGraph (Fin 7)), ?_⟩
  intro h
  unfold HasUnitDistanceRepresentation at h
  obtain ⟨f, -, hdist⟩ := h
  have hpw : Pairwise fun i j : Fin 7 => dist (f i) (f j) = 1 := fun i j hij =>
    hdist i j ((SimpleGraph.top_adj i j).mpr hij)
  have hcard := EuclideanGeometry.card_le_of_equilateral (p := f) hpw
  simp only [Fintype.card_fin] at hcard
  omega

end FKSProblem2.StatementA
