/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubcoalgebraCoalgebraStruct
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.Flat.Basic

/-!
# Pulling a coalgebra structure back along an injective coalgebra map

Mathlib's `Coalgebra.TensorProduct.map` assumes genuine coalgebras on all
four factors. Its construction only needs the `CoalgebraStruct`s, so we
first provide that weaker version.

We then use it to transport the coalgebra axioms from a genuine coalgebra
`H` back along an injective coalgebra-structure morphism `C → H`.
-/

open Coalgebra LinearMap TensorProduct
open scoped TensorProduct

namespace HopfAmenability

universe u v w x y

namespace CoalgHom

variable {k : Type u}
variable [Field k]
variable {A : Type v} {B : Type w} {C : Type x} {D : Type y}
variable [AddCommGroup A] [Module k A] [CoalgebraStruct k A]
variable [AddCommGroup B] [Module k B] [CoalgebraStruct k B]
variable [AddCommGroup C] [Module k C] [CoalgebraStruct k C]
variable [AddCommGroup D] [Module k D] [CoalgebraStruct k D]

set_option backward.defeqAttrib.useBackward true in
/--
The tensor product of two coalgebra-structure morphisms.

This is the `CoalgebraStruct`-level analogue of
`Coalgebra.TensorProduct.map`.
-/
noncomputable def tensorMapStruct
    (f : A →ₗc[k] B) (g : C →ₗc[k] D) :
    A ⊗[k] C →ₗc[k] B ⊗[k] D where
  toLinearMap := AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by
    ext a c
    simp
  map_comp_comul := by
    ext a c
    dsimp
    simp only [← CoalgHomClass.map_comp_comul_apply]
    hopf_tensor_induction comul (R := k) a with a₁ a₂
    hopf_tensor_induction comul (R := k) c with c₁ c₂
    simp

@[simp]
theorem tensorMapStruct_tmul
    (f : A →ₗc[k] B) (g : C →ₗc[k] D)
    (a : A) (c : C) :
    tensorMapStruct f g (a ⊗ₜ[k] c) = f a ⊗ₜ[k] g c :=
  rfl

@[simp]
theorem tensorMapStruct_toLinearMap
    (f : A →ₗc[k] B) (g : C →ₗc[k] D) :
    (tensorMapStruct f g : A ⊗[k] C →ₗ[k] B ⊗[k] D) =
      TensorProduct.map f.toLinearMap g.toLinearMap := by
  exact TensorProduct.AlgebraTensorModule.map_eq _ _

/--
Tensoring two injective coalgebra-structure morphisms over a field gives
an injective map.
-/
theorem tensorMapStruct_injective
    (f : A →ₗc[k] B) (g : C →ₗc[k] D)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (tensorMapStruct f g) := by
  change Function.Injective
    (TensorProduct.AlgebraTensorModule.map f.toLinearMap g.toLinearMap)
  simpa only [TensorProduct.AlgebraTensorModule.map_eq] using
    TensorProduct.map_injective_of_flat_flat
      f.toLinearMap g.toLinearMap hf hg

/--
Naturality of the ordinary tensor-product associator.
-/
theorem tensorMapStruct_assoc
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module k E] [CoalgebraStruct k E]
    [AddCommGroup F] [Module k F] [CoalgebraStruct k F]
    (f : A →ₗc[k] B) (g : C →ₗc[k] D) (h : E →ₗc[k] F)
    (z : (A ⊗[k] C) ⊗[k] E) :
    tensorMapStruct f (tensorMapStruct g h)
        (TensorProduct.assoc k A C E z) =
      TensorProduct.assoc k B D F
        (tensorMapStruct (tensorMapStruct f g) h z) := by
  change
    TensorProduct.map f.toLinearMap
        (TensorProduct.map g.toLinearMap h.toLinearMap)
        (TensorProduct.assoc k A C E z) =
      TensorProduct.assoc k B D F
        (TensorProduct.map
          (TensorProduct.map f.toLinearMap g.toLinearMap)
          h.toLinearMap z)
  exact TensorProduct.map_map_assoc
    f.toLinearMap g.toLinearMap h.toLinearMap z

end CoalgHom

section InjectivePullback

variable {k : Type u} {C : Type v} {H : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [CoalgebraStruct k C]
variable [AddCommGroup H] [Module k H] [Coalgebra k H]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

omit [CoalgebraStruct k C] [Coalgebra k H] in
/--
The tensor square of an injective linear map is injective.
-/
theorem tensorSquare_injective
    (f : C →ₗ[k] H) (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map f f) := by
  exact TensorProduct.map_injective_of_flat_flat f f hf hf

omit [CoalgebraStruct k C] [Coalgebra k H] in
/--
The right-associated tensor cube of an injective linear map is injective.
-/
theorem tensorCubeRight_injective
    (f : C →ₗ[k] H) (hf : Function.Injective f) :
    Function.Injective
      (TensorProduct.map f (TensorProduct.map f f)) := by
  exact TensorProduct.map_injective_of_flat_flat f
    (TensorProduct.map f f) hf (tensorSquare_injective f hf)

/--
Compatibility of `f ⊗ f` with the comultiplication preserved by `f`.
-/
@[simp]
private theorem tensorMapStruct_comul
    (f : C →ₗc[k] H) (x : C) :
    CoalgHom.tensorMapStruct f f
        (Coalgebra.comul (R := k) (A := C) x) =
      Coalgebra.comul (R := k) (A := H) (f x) := by
  change
    TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) (A := C) x) =
      Coalgebra.comul (R := k) (A := H) (f x)
  exact CoalgHomClass.map_comp_comul_apply f x

/--
Compatibility of `f` with the counit.
-/
@[simp]
private theorem coalgHom_counit
    (f : C →ₗc[k] H) (x : C) :
    Coalgebra.counit (R := k) (A := H) (f x) =
      Coalgebra.counit (R := k) (A := C) x :=
  CoalgHomClass.counit_comp_apply f x

/--
Transport `Δ ⊗ id` through the tensor maps induced by `f`.
-/
private theorem tensorMapStruct_rTensor_comul
    (f : C →ₗc[k] H)
    (z : C ⊗[k] C) :
    CoalgHom.tensorMapStruct
        (CoalgHom.tensorMapStruct f f) f
        ((Coalgebra.comul (R := k) (A := C)).rTensor C z) =
      (Coalgebra.comul (R := k) (A := H)).rTensor H
        (CoalgHom.tensorMapStruct f f z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x y =>
      simp
  | add x y hx hy =>
      simp [hx, hy]

/--
Transport `id ⊗ Δ` through the tensor maps induced by `f`.
-/
private theorem tensorMapStruct_lTensor_comul
    (f : C →ₗc[k] H)
    (z : C ⊗[k] C) :
    CoalgHom.tensorMapStruct f
        (CoalgHom.tensorMapStruct f f)
        ((Coalgebra.comul (R := k) (A := C)).lTensor C z) =
      (Coalgebra.comul (R := k) (A := H)).lTensor H
        (CoalgHom.tensorMapStruct f f z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x y =>
      simp
  | add x y hx hy =>
      simp [hx, hy]

/--
Transport `ε ⊗ id` through `id_k ⊗ f`.
-/
private theorem tensorMapStruct_rTensor_counit
    (f : C →ₗc[k] H)
    (z : C ⊗[k] C) :
    CoalgHom.tensorMapStruct (CoalgHom.id k k) f
        ((Coalgebra.counit (R := k) (A := C)).rTensor C z) =
      (Coalgebra.counit (R := k) (A := H)).rTensor H
        (CoalgHom.tensorMapStruct f f z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x y =>
      simp
  | add x y hx hy =>
      simp [hx, hy]

/--
Transport `id ⊗ ε` through `f ⊗ id_k`.
-/
private theorem tensorMapStruct_lTensor_counit
    (f : C →ₗc[k] H)
    (z : C ⊗[k] C) :
    CoalgHom.tensorMapStruct f (CoalgHom.id k k)
        ((Coalgebra.counit (R := k) (A := C)).lTensor C z) =
      (Coalgebra.counit (R := k) (A := H)).lTensor H
        (CoalgHom.tensorMapStruct f f z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x y =>
      simp
  | add x y hx hy =>
      simp [hx, hy]

/--
An injective coalgebra-structure morphism into a genuine coalgebra forces
the coalgebra axioms on its domain.
-/
@[instance_reducible]
noncomputable def coalgebraOfInjectiveCoalgHom
    (f : C →ₗc[k] H)
    (hf : Function.Injective f) :
    Coalgebra k C := by
  constructor
  · ext x
    apply CoalgHom.tensorMapStruct_injective f
      (CoalgHom.tensorMapStruct f f) hf
      (CoalgHom.tensorMapStruct_injective f f hf hf)
    change
      CoalgHom.tensorMapStruct f (CoalgHom.tensorMapStruct f f)
          ((TensorProduct.assoc k C C C)
            ((Coalgebra.comul (R := k) (A := C)).rTensor C
              (Coalgebra.comul (R := k) (A := C) x))) =
        CoalgHom.tensorMapStruct f (CoalgHom.tensorMapStruct f f)
          ((Coalgebra.comul (R := k) (A := C)).lTensor C
            (Coalgebra.comul (R := k) (A := C) x))
    calc
      _ = TensorProduct.assoc k H H H
          (CoalgHom.tensorMapStruct
            (CoalgHom.tensorMapStruct f f) f
            ((Coalgebra.comul (R := k) (A := C)).rTensor C
              (Coalgebra.comul (R := k) (A := C) x))) := by
            exact CoalgHom.tensorMapStruct_assoc f f f _
      _ = TensorProduct.assoc k H H H
          ((Coalgebra.comul (R := k) (A := H)).rTensor H
            (Coalgebra.comul (R := k) (A := H) (f x))) := by
            rw [tensorMapStruct_rTensor_comul f]
            rw [tensorMapStruct_comul f]
      _ = (Coalgebra.comul (R := k) (A := H)).lTensor H
          (Coalgebra.comul (R := k) (A := H) (f x)) := by
            exact Coalgebra.coassoc_apply (R := k) (A := H) (f x)
      _ = CoalgHom.tensorMapStruct f (CoalgHom.tensorMapStruct f f)
          ((Coalgebra.comul (R := k) (A := C)).lTensor C
            (Coalgebra.comul (R := k) (A := C) x)) := by
            rw [tensorMapStruct_lTensor_comul f]
            rw [tensorMapStruct_comul f]
  · ext x
    apply CoalgHom.tensorMapStruct_injective
      (CoalgHom.id k k) f Function.injective_id hf
    rw [LinearMap.comp_apply]
    rw [tensorMapStruct_rTensor_counit f]
    rw [tensorMapStruct_comul f]
    rw [Coalgebra.rTensor_counit_comul]
    simp
  · ext x
    apply CoalgHom.tensorMapStruct_injective
      f (CoalgHom.id k k) hf Function.injective_id
    rw [LinearMap.comp_apply]
    rw [tensorMapStruct_lTensor_counit f]
    rw [tensorMapStruct_comul f]
    rw [Coalgebra.lTensor_counit_comul]
    simp

end InjectivePullback

end HopfAmenability
