/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem2.Standalone.Mathlib.StatementB

import FKSProblem2.Standalone.Mathlib.StatementAProof
import GraphDimension.Geometry.Equilateral

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Pairwise
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Proof of statement B

The placement condition displayed in `problem2At` is statement A's unit-distance
representation, so the instances follow from statement A's: the `d = 0` and `d = 1` cases are
elementary, and `problem2Three` is statement A's seven-vertex disjunction. The complete graph
`K₇`, whose seven pairwise unit points would need six dimensions, is the witness that the
alternative with the complement has geometric content.
-/

public section

namespace FKSProblem2.StatementB

open FKSProblem2.StatementA

/-- The point `x` of the first coordinate axis, as a point of `EuclideanSpace ℝ (Fin 3)`. -/
private noncomputable def axisPt (x : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 x

private lemma axisPt_injective : Function.Injective axisPt := by
  intro x y hxy
  simpa [axisPt, PiLp.single_eq_same] using
    congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) hxy

/-- The graph on `Fin n` with the single edge `a--b`. -/
private noncomputable def singleEdgeGraph {n : ℕ} (a b : Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {s(a, b)}

private lemma singleEdgeGraph_adj {n : ℕ} {a b : Fin n} (hab : a ≠ b) (u v : Fin n) :
    (singleEdgeGraph a b).Adj u v ↔ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  rw [singleEdgeGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨hmem, -⟩
    rcases Sym2.eq_iff.1 hmem with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by simp, hab⟩
    · exact ⟨by simp, Ne.symm hab⟩

/-- The single-edge graph on `Fin 3`, placed on the real axis at coordinates `0, 1, 2`: its
edge has length `1`, all vertices are distinct, and the non-edge `1--2` also has length `1`. -/
private lemma singleEdgeFin3_representation :
    ∃ p : Fin 3 → EuclideanSpace ℝ (Fin 1),
      Function.Injective p ∧
        (∀ u v, (singleEdgeGraph (0 : Fin 3) 1).Adj u v → dist (p u) (p v) = 1) ∧
        ¬(singleEdgeGraph (0 : Fin 3) 1).Adj 1 2 ∧ dist (p 1) (p 2) = 1 := by
  refine ⟨fun i => ![linePt 0, linePt 1, linePt 2] i, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    fin_cases u <;> fin_cases v
    · rfl
    · exact absurd huv (linePt_ne_linePt (by norm_num))
    · exact absurd huv (linePt_ne_linePt (by norm_num))
    · exact absurd huv (linePt_ne_linePt (by norm_num))
    · rfl
    · exact absurd huv (linePt_ne_linePt (by norm_num))
    · exact absurd huv (linePt_ne_linePt (by norm_num))
    · exact absurd huv (linePt_ne_linePt (by norm_num))
    · rfl
  · intro u v
    rw [singleEdgeGraph_adj (by decide) u v]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · change dist (linePt 0) (linePt 1) = 1
      rw [dist_linePt]
      norm_num
    · change dist (linePt 1) (linePt 0) = 1
      rw [dist_linePt]
      norm_num
  · rw [singleEdgeGraph_adj (by decide) 1 2]
    simp
  · change dist (linePt 1) (linePt 2) = 1
    rw [dist_linePt]
    norm_num

/-- The single-edge graph on `Fin 7`, placed on the first coordinate axis of `ℝ^3` at
coordinates `0, 1, …, 6`: its edge has length `1`, all vertices are distinct, and the non-edge
`1--2` also has length `1`. -/
private lemma singleEdgeFin7_representation :
    ∃ p : Fin 7 → EuclideanSpace ℝ (Fin 3),
      Function.Injective p ∧
        (∀ u v, (singleEdgeGraph (0 : Fin 7) 1).Adj u v → dist (p u) (p v) = 1) ∧
        ¬(singleEdgeGraph (0 : Fin 7) 1).Adj 1 2 ∧ dist (p 1) (p 2) = 1 := by
  refine ⟨fun i => axisPt ((i : ℕ) : ℝ), ?_, ?_, ?_, ?_⟩
  · intro u v huv
    exact Fin.val_injective (Nat.cast_injective (axisPt_injective huv))
  · intro u v
    rw [singleEdgeGraph_adj (by decide) u v]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [axisPt]
    · simp [axisPt]
  · rw [singleEdgeGraph_adj (by decide) 1 2]
    simp
  · simp [axisPt]
    norm_num [Real.dist_eq]

/-! ### The instances -/

/-- The `d = 0` instance of statement B: the single vertex of `Fin 1` in the one-point space
`ℝ^0`. -/
theorem problem2At_zero : problem2At 0 := by
  intro G
  refine ⟨fun _ => 0, fun u v _ =>
    @Subsingleton.elim _ (inferInstanceAs (Subsingleton (Fin 1))) u v, Or.inl ?_⟩
  intro u v huv
  exact False.elim (G.ne_of_adj huv
    (@Subsingleton.elim _ (inferInstanceAs (Subsingleton (Fin 1))) u v))

/-- The `d = 1` instance of statement B: statement A's three-vertex disjunction. -/
theorem problem2At_one : problem2At 1 := by
  intro G
  have h := FKSProblem2.StatementA.questionAt_one G
  unfold FKSProblem2.StatementA.HasUnitDistanceRepresentation at h
  rcases h with ⟨f, hf, hG⟩ | ⟨f, hf, hGc⟩
  · exact ⟨f, hf, Or.inl hG⟩
  · exact ⟨f, hf, Or.inr hGc⟩

theorem problem2Three.proof : problem2Three := by
  intro G
  have h := FKSProblem2.StatementA.questionAt3.proof G
  unfold FKSProblem2.StatementA.HasUnitDistanceRepresentation at h
  rcases h with ⟨f, hf, hG⟩ | ⟨f, hf, hGc⟩
  · exact ⟨f, hf, Or.inl hG⟩
  · exact ⟨f, hf, Or.inr hGc⟩

/-! ### The fidelity companions -/

theorem problem2At.witness.proof : problem2At.witness :=
  ⟨problem2At_zero, problem2At_one⟩

/-- The triangle `K₃` has no unit-distance representation in `ℝ^1`: three pairwise unit points
cannot lie on a line. -/
private lemma not_representation_triangle :
    ¬∀ G : SimpleGraph (Fin 3), ∃ f : Fin 3 → EuclideanSpace ℝ (Fin 1),
      Function.Injective f ∧ ∀ u v, G.Adj u v → dist (f u) (f v) = 1 := by
  intro h
  obtain ⟨f, -, hdist⟩ := h (⊤ : SimpleGraph (Fin 3))
  have hpw : Pairwise fun i j : Fin 3 => dist (f i) (f j) = 1 := fun i j hij =>
    hdist i j ((SimpleGraph.top_adj i j).mpr hij)
  have hcard := EuclideanGeometry.card_le_of_equilateral (p := f) hpw
  simp only [Fintype.card_fin] at hcard
  omega

theorem problem2At.separating.proof : problem2At.separating :=
  ⟨problem2At_one, not_representation_triangle, singleEdgeGraph (0 : Fin 3) 1,
    singleEdgeGraph_adj (by decide), singleEdgeFin3_representation⟩

theorem problem2.witness.proof : problem2.witness :=
  ⟨fun h => h 0, problem2At.separating.proof⟩

theorem problem2.separating.proof : problem2.separating :=
  problem2.witness.proof

theorem problem2Three.witness.proof : problem2Three.witness := by
  refine ⟨fun h => h, ?_, ?_⟩
  · rintro ⟨f, -, hdist⟩
    have hpw : Pairwise fun i j : Fin 7 => dist (f i) (f j) = 1 := fun i j hij =>
      hdist i j hij
    have hcard := EuclideanGeometry.card_le_of_equilateral (p := f) hpw
    simp only [Fintype.card_fin] at hcard
    omega
  · exact ⟨fun i => axisPt ((i : ℕ) : ℝ), fun u v huv =>
      Fin.val_injective (Nat.cast_injective (axisPt_injective huv))⟩

theorem problem2Three.separating.proof : problem2Three.separating :=
  ⟨singleEdgeGraph (0 : Fin 7) 1, singleEdgeGraph_adj (by decide),
    singleEdgeFin7_representation, fun h => h _⟩

end FKSProblem2.StatementB
