/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.RightCoideal

/-!
# Two-sided coideals
-/

open TensorProduct

namespace Coalgebra

noncomputable section

universe u v

variable {k : Type u} {C : Type v}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A right coideal is the existing right-subcomodule predicate for the
regular right comodule. -/
abbrev IsRightCoideal (P : Submodule k C) : Prop :=
  IsRightSubcomodule (C := C) P

/-- A left coideal of a coalgebra. -/
def IsLeftCoideal (P : Submodule k C) : Prop :=
  ∀ c : C, c ∈ P →
    Coalgebra.comul (R := k) (A := C) c ∈
      LinearMap.range (P.subtype.lTensor C)

/-- A subspace which is both a left and a right coideal is a subcoalgebra.
No cocommutativity assumption is needed. -/
theorem isSubcoalgebra_of_twoSidedCoideal
    {P : Submodule k C}
    (hR : ∀ b : C, b ∈ P →
      Coalgebra.comul (R := k) (A := C) b ∈
        LinearMap.range (P.subtype.rTensor C))
    (hL : ∀ b : C, b ∈ P →
      Coalgebra.comul (R := k) (A := C) b ∈
        LinearMap.range (P.subtype.lTensor C)) :
    HopfAmenability.IsSubcoalgebra (k := k) P := by
  intro c hc
  rw [HopfAmenability.range_mapIncl_self_eq_inf P]
  constructor
  · exact hR c hc
  · exact hL c hc

/-- Predicate-packaged version of `isSubcoalgebra_of_twoSidedCoideal`. -/
theorem isSubcoalgebra_of_left_and_right_coideal
    {P : Submodule k C}
    (hR : IsRightCoideal P) (hL : IsLeftCoideal P) :
    HopfAmenability.IsSubcoalgebra (k := k) P :=
  isSubcoalgebra_of_twoSidedCoideal hR hL

/-- The regular-comodule formulation and the right-coideal formulation agree. -/
theorem isRightSubcomodule_iff_isRightCoideal (P : Submodule k C) :
    IsRightSubcomodule (C := C) P ↔ IsRightCoideal P :=
  Iff.rfl

end

end Coalgebra
