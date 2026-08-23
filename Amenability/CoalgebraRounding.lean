/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CoalgebraRoundingFinite
import Amenability.FundamentalTheoremCoalgebra

/-!
# Global coalgebraic rounding
-/

open Coalgebra Module

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

/-- The global finite-subcoalgebra rounding theorem. -/
theorem exists_finiteSubcoalgebra_ratio_le
    (F : FiniteSubcoalgebra k H)
    (S : SplitDualFiltration k F.Dual)
    (E : Submodule k H)
    [FiniteDimensional k E]
    (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k H,
      C.carrier ≠ ⊥ ∧
        (finrank k (F.carrier * C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (finrank k (F.carrier * E) : ℚ) /
            (finrank k E : ℚ) := by
  obtain ⟨G, hEG⟩ := exists_finiteSubcoalgebra_containing_submodule E
  exact exists_finiteSubcoalgebra_ratio_le_of_le F S E hE G hEG

end

end UnifiedRounding
