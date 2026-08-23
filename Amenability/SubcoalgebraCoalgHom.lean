/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubcoalgebraCoalgebra
import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Restricting the codomain of a coalgebra homomorphism to a subcoalgebra
-/

open Coalgebra LinearMap TensorProduct

namespace HopfAmenability

universe u v w

variable {k : Type u} {X : Type v} {H : Type w}
variable [Field k]
variable [AddCommGroup X] [Module k X] [Coalgebra k X]
variable [AddCommGroup H] [Module k H] [Coalgebra k H]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

namespace CoalgHom

/--
If the image of a coalgebra homomorphism lies in a subcoalgebra `C`, then it
corestricts to a coalgebra homomorphism with codomain `C`.
-/
noncomputable def codRestrictSubcoalgebra
    (f : X →ₗc[k] H)
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C)
    (hf : ∀ x : X, f x ∈ C) :
    letI := subcoalgebraCoalgebra C hC
    X →ₗc[k] C := by
  letI := subcoalgebraCoalgebra C hC
  let g : X →ₗ[k] C := f.toLinearMap.codRestrict C hf
  exact
    { g with
      counit_comp := by
        ext x
        change
          Coalgebra.counit (R := k) (A := H) (f x) =
            Coalgebra.counit (R := k) (A := X) x
        exact CoalgHomClass.counit_comp_apply f x
      map_comp_comul := by
        ext x
        apply tensorProduct_mapIncl_injective C C
        change
          TensorProduct.map C.subtype C.subtype
              (TensorProduct.map g g
                (Coalgebra.comul (R := k) (A := X) x)) =
            TensorProduct.map C.subtype C.subtype
              (Coalgebra.comul (R := k) (A := C) (g x))
        calc
          _ = TensorProduct.map f.toLinearMap f.toLinearMap
              (Coalgebra.comul (R := k) (A := X) x) := by
                rw [TensorProduct.map_map]
                rfl
          _ = Coalgebra.comul (R := k) (A := H) (f x) := by
                exact CoalgHomClass.map_comp_comul_apply f x
          _ = Coalgebra.comul (R := k) (A := H) ((g x : C) : H) := by
                rfl
          _ = TensorProduct.map C.subtype C.subtype
              (Coalgebra.comul (R := k) (A := C) (g x)) := by
                have h :=
                  CoalgHomClass.map_comp_comul_apply
                    (subcoalgebraInclusion C hC) (g x)
                change
                  TensorProduct.map C.subtype C.subtype
                      (Coalgebra.comul (R := k) (A := C) (g x)) =
                    Coalgebra.comul (R := k) (A := H) ((g x : C) : H) at h
                exact h.symm }

/--
The underlying ambient value of the corestricted coalgebra map is unchanged.
-/
@[simp]
theorem coe_codRestrictSubcoalgebra
    (f : X →ₗc[k] H)
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C)
    (hf : ∀ x : X, f x ∈ C)
    (x : X) :
    letI := subcoalgebraCoalgebra C hC
    ((codRestrictSubcoalgebra f C hC hf x : C) : H) = f x := by
  let := subcoalgebraCoalgebra C hC
  rfl

end CoalgHom

end HopfAmenability
