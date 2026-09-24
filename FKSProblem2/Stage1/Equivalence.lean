/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FKSProblem2.Standalone.Mathlib.StatementA
public import FKSProblem2.Standalone.Mathlib.StatementB

/-! # Equivalence of the two statements of FKS Problem 2 -/

public section

namespace FKSProblem2.Stage1

theorem questionAt_iff (d : ℕ) :
    FKSProblem2.StatementA.questionAt d ↔ FKSProblem2.StatementB.problem2At d := by
  unfold StatementA.questionAt StatementB.problem2At
    StatementA.HasUnitDistanceRepresentation
  constructor
  · intro h G
    rcases h G with ⟨f, hf, hG⟩ | ⟨f, hf, hGc⟩
    · exact ⟨f, hf, Or.inl hG⟩
    · exact ⟨f, hf, Or.inr hGc⟩
  · intro h G
    rcases h G with ⟨f, hf, hG | hGc⟩
    · exact Or.inl ⟨f, hf, hG⟩
    · exact Or.inr ⟨f, hf, hGc⟩

theorem questionAt_zero : FKSProblem2.StatementA.questionAt 0 := by
  change ∀ G : SimpleGraph (Fin 1),
    StatementA.HasUnitDistanceRepresentation 0 G ∨
      StatementA.HasUnitDistanceRepresentation 0 Gᶜ
  intro G
  left
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro u v _
    exact Subsingleton.elim u v
  · intro u v huv
    exact False.elim ((G.ne_of_adj huv) (Subsingleton.elim u v))

theorem question_iff :
    FKSProblem2.StatementA.question ↔ FKSProblem2.StatementB.problem2 := by
  change (∀ d, StatementA.questionAt d) ↔
    (∀ n, StatementB.problem2At (n + 1))
  constructor
  · intro h n
    exact (questionAt_iff (n + 1)).mp (h (n + 1))
  · intro h d
    cases d with
    | zero => exact questionAt_zero
    | succ n => exact (questionAt_iff (n + 1)).mpr (h n)

theorem questionAt3_iff :
    FKSProblem2.StatementA.questionAt3 ↔
      FKSProblem2.StatementB.problem2Three := by
  change StatementA.questionAt 3 ↔ StatementB.problem2At 3
  exact questionAt_iff 3

end FKSProblem2.Stage1
