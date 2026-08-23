/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.FiniteSubcoalgebra
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Dual algebra map of a coalgebra homomorphism

Precomposition by a coalgebra homomorphism gives an algebra homomorphism
between convolution duals. If the coalgebra homomorphism is surjective,
the dual algebra homomorphism is injective.
-/

open Coalgebra WithConv

namespace HopfAmenability

universe u v w

namespace CoalgHom

section Linear

variable {k : Type u} {C : Type v} {D : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [CoalgebraStruct k C]
variable [AddCommGroup D] [Module k D] [CoalgebraStruct k D]

/--
The linear map on convolution duals induced by precomposition with a
coalgebra homomorphism.
-/
noncomputable def dualLinearMap
    (f : C →ₗc[k] D) :
    WithConv (Module.Dual k D) →ₗ[k]
      WithConv (Module.Dual k C) :=
  (WithConv.linearEquiv k (Module.Dual k C)).symm.toLinearMap.comp
    (f.toLinearMap.dualMap.comp
      (WithConv.linearEquiv k (Module.Dual k D)).toLinearMap)

@[simp]
theorem dualLinearMap_apply
    (f : C →ₗc[k] D)
    (φ : WithConv (Module.Dual k D))
    (x : C) :
    dualLinearMap f φ x = φ (f x) :=
  rfl

end Linear

section Algebra

variable {k : Type u} {C : Type v} {D : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup D] [Module k D] [Coalgebra k D]

/--
The algebra homomorphism on convolution duals induced by a coalgebra
homomorphism.
-/
noncomputable def dualAlgHom
    (f : C →ₗc[k] D) :
    WithConv (Module.Dual k D) →ₐ[k]
      WithConv (Module.Dual k C) :=
  AlgHom.ofLinearMap (dualLinearMap f)
    (by
      apply WithConv.ext
      ext x
      simp [dualLinearMap])
    (by
      intro φ ψ
      apply WithConv.ext
      exact LinearMap.convMul_comp_coalgHom_distrib φ ψ f)

@[simp]
theorem dualAlgHom_apply
    (f : C →ₗc[k] D)
    (φ : WithConv (Module.Dual k D))
    (x : C) :
    dualAlgHom f φ x = φ (f x) :=
  rfl

/--
The dual algebra homomorphism of a surjective coalgebra homomorphism is
injective.

The proof is pointwise, avoiding any coercion through `dualMap`.
-/
theorem dualAlgHom_injective_of_surjective
    (f : C →ₗc[k] D)
    (hf : Function.Surjective f) :
    Function.Injective (dualAlgHom f) := by
  intro φ ψ h
  apply WithConv.ext
  ext d
  obtain ⟨c, rfl⟩ := hf d
  have hc := congrArg
    (fun η : WithConv (Module.Dual k C) => η c) h
  simpa only [dualAlgHom_apply] using hc

end Algebra

end CoalgHom

end HopfAmenability
