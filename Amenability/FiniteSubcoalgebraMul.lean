/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.FiniteSubcoalgebra
import Amenability.FiniteSubcoalgebraProduct
import Amenability.SubcoalgebraCoalgHom
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Multiplication of finite subcoalgebras as a coalgebra quotient

For finite subcoalgebras `F,C` of a bialgebra `H`, the multiplication map
`F ⊗ C → FC` is a surjective coalgebra homomorphism.
-/

open Coalgebra LinearMap TensorProduct

namespace HopfAmenability

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [Bialgebra k H]

namespace FiniteSubcoalgebra

/--
The product of two finite subcoalgebras.
-/
noncomputable def mul
    (F C : FiniteSubcoalgebra k H) :
    FiniteSubcoalgebra k H where
  carrier := F.carrier * C.carrier
  isSubcoalgebra := F.isSubcoalgebra.mul C.isSubcoalgebra
  finiteDimensional := finiteDimensional_mul F.carrier C.carrier

/--
The ambient multiplication map restricted to `F ⊗ C`.
-/
noncomputable def ambientMulCoalgHom
    (F C : FiniteSubcoalgebra k H) :
    F.carrier ⊗[k] C.carrier →ₗc[k] H :=
  (Bialgebra.mulCoalgHom k H).comp
    (CoalgHom.tensorMapStruct
      (subcoalgebraInclusion F.carrier F.isSubcoalgebra)
      (subcoalgebraInclusion C.carrier C.isSubcoalgebra))

@[simp]
theorem ambientMulCoalgHom_tmul
    (F C : FiniteSubcoalgebra k H)
    (f : F.carrier) (c : C.carrier) :
    ambientMulCoalgHom F C (f ⊗ₜ[k] c) = (f : H) * (c : H) :=
  rfl

/--
Every value of the restricted multiplication map lies in `FC`.
-/
theorem ambientMulCoalgHom_mem_mul
    (F C : FiniteSubcoalgebra k H)
    (x : F.carrier ⊗[k] C.carrier) :
    ambientMulCoalgHom F C x ∈ (mul F C).carrier := by
  induction x using TensorProduct.induction_on with
  | zero =>
      exact zero_mem _
  | tmul f c =>
      exact Submodule.mul_mem_mul f.2 c.2
  | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy

/--
Multiplication `F ⊗ C → FC` as a coalgebra homomorphism.
-/
noncomputable def mulCoalgHom
    (F C : FiniteSubcoalgebra k H) :
    F.carrier ⊗[k] C.carrier →ₗc[k] (mul F C).carrier :=
  CoalgHom.codRestrictSubcoalgebra
    (X := F.carrier ⊗[k] C.carrier)
    (H := H)
    (ambientMulCoalgHom F C)
    (mul F C).carrier
    (mul F C).isSubcoalgebra
    (ambientMulCoalgHom_mem_mul F C)

@[simp]
theorem coe_mulCoalgHom_tmul
    (F C : FiniteSubcoalgebra k H)
    (f : F.carrier) (c : C.carrier) :
    (((mulCoalgHom F C (f ⊗ₜ[k] c) :
        (mul F C).carrier) : H)) =
      (f : H) * (c : H) := by
  rfl

/--
The underlying linear map of `mulCoalgHom` is mathlib's canonical
surjection `Submodule.mulMap'`.
-/
theorem mulCoalgHom_toLinearMap
    (F C : FiniteSubcoalgebra k H) :
    (mulCoalgHom F C :
        F.carrier ⊗[k] C.carrier →ₗ[k] (mul F C).carrier) =
      Submodule.mulMap' F.carrier C.carrier := by
  apply TensorProduct.ext'
  intro f c
  apply Subtype.ext
  rfl

/--
The coalgebra multiplication map `F ⊗ C → FC` is surjective.
-/
theorem mulCoalgHom_surjective
    (F C : FiniteSubcoalgebra k H) :
    Function.Surjective (mulCoalgHom F C) := by
  change Function.Surjective
    (mulCoalgHom F C :
      F.carrier ⊗[k] C.carrier →ₗ[k] (mul F C).carrier)
  rw [← LinearMap.range_eq_top]
  rw [mulCoalgHom_toLinearMap]
  exact LinearMap.range_eq_top.mpr
    (Submodule.mulMap'_surjective F.carrier C.carrier)

end FiniteSubcoalgebra

end HopfAmenability
