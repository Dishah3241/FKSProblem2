/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem2.Standalone.Mathlib.InlineFKSProblem2

import FKSProblem2.Standalone.Mathlib.StatementAProof

/-!
# Proof of the inlined statement

The inline statement repeats statement A's declarations with the same bodies, so each proof is
the corresponding proof in `StatementAProof`: the `d = 3` disjunction from the shared library's
seven-vertex result, and the `d = 0` and `d = 1` instances from the elementary line
placements. FKS 2020 Problem 2 itself remains open; only its `d = 3` instance is proved.
-/

public section

namespace FKSProblem2.Standalone.Mathlib.InlineFKSProblem2

theorem HasUnitDistanceRepresentation.separating.proof :
    HasUnitDistanceRepresentation.separating :=
  FKSProblem2.StatementA.HasUnitDistanceRepresentation.separating.proof

theorem questionAt.separating.proof : questionAt.separating :=
  FKSProblem2.StatementA.questionAt.separating.proof

theorem question.witness.proof : question.witness :=
  FKSProblem2.StatementA.question.witness.proof

theorem questionAt3.proof : questionAt3 :=
  FKSProblem2.StatementA.questionAt3.proof

theorem questionAt3.witness.proof : questionAt3.witness :=
  FKSProblem2.StatementA.questionAt3.witness.proof

end FKSProblem2.Standalone.Mathlib.InlineFKSProblem2
