/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Comodule
import Amenability.TensorSquareIntersection

/-!
# Right coideals and subcoalgebras
-/

open Coalgebra TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {C : Type v}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A subcoalgebra is a right subcomodule of the regular comodule. -/
theorem IsSubcoalgebra.isRightSubcomodule
    {B : Submodule k C} (hB : IsSubcoalgebra (k := k) B) :
    IsRightSubcomodule (C := C) B := by
  intro x hx
  have hcomul := hB hx
  rw [range_mapIncl_self_eq_inf B] at hcomul
  exact hcomul.1

/-- In a cocommutative coalgebra, every right coideal is a subcoalgebra. -/
theorem isSubcoalgebra_of_isRightSubcomodule
    [Coalgebra.IsCocomm k C]
    {B : Submodule k C}
    (hB : IsRightSubcomodule (C := C) B) :
    IsSubcoalgebra (k := k) B := by
  intro x hx
  have hright := hB x hx
  have hleft : Coalgebra.comul (R := k) (A := C) x ∈
      LinearMap.range (B.subtype.lTensor C) := by
    have hnatural : ∀ q : B ⊗[k] C,
        (B.subtype.lTensor C) (TensorProduct.comm k B C q) =
          TensorProduct.comm k C C ((B.subtype.rTensor C) q) := by
      intro q
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp [hz, hw]
      | tmul b c => rfl
    rcases hright with ⟨z, hz⟩
    refine ⟨TensorProduct.comm k B C z, ?_⟩
    rw [hnatural z, hz]
    exact Coalgebra.comm_comul k x
  rw [range_mapIncl_self_eq_inf B]
  exact ⟨hB x hx, hleft⟩

/-- Right subcomodules of the regular comodule are precisely subcoalgebras
in the cocommutative case. -/
theorem isRightSubcomodule_iff_isSubcoalgebra
    [Coalgebra.IsCocomm k C]
    {B : Submodule k C} :
    IsRightSubcomodule (C := C) B ↔ IsSubcoalgebra (k := k) B :=
  ⟨isSubcoalgebra_of_isRightSubcomodule,
    IsSubcoalgebra.isRightSubcomodule⟩

end

end HopfAmenability
