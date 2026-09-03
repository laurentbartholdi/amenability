/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfAlgebraHom
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-! # Cleft exact sequences of Hopf algebras -/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w x

variable {k : Type u}

/-- The right coinvariants of a Hopf morphism `B → C`. -/
noncomputable def rightCoinvariants
    {B : Type v} {C : Type w} [Field k]
    [Ring B] [HopfAlgebra k B] [Ring C] [HopfAlgebra k C]
    (p : HopfAlgebraHom (k := k) (H := B) C) : Submodule k B :=
  LinearMap.ker
    ((TensorProduct.map LinearMap.id p.toAlgHom.toLinearMap).comp
        (Coalgebra.comul (R := k) (A := B)) -
      (TensorProduct.mk k B C).flip 1)

/-- For cocommutative Hopf algebras, a right coinvariant is also a left
coinvariant. -/
theorem leftCoaction_eq_of_mem_rightCoinvariants
    {B : Type v} {C : Type w} [Field k]
    [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Ring C] [HopfAlgebra k C]
    (p : HopfAlgebraHom (k := k) (H := B) C) (b : B)
    (hb : b ∈ rightCoinvariants p) :
    TensorProduct.map p.toAlgHom.toLinearMap LinearMap.id
        (Coalgebra.comul (R := k) b) = 1 ⊗ₜ[k] b := by
  have hright :
      TensorProduct.map LinearMap.id p.toAlgHom.toLinearMap
          (Coalgebra.comul (R := k) b) = b ⊗ₜ[k] 1 := by
    change ((TensorProduct.map LinearMap.id p.toAlgHom.toLinearMap).comp
        (Coalgebra.comul (R := k) (A := B)) -
      (TensorProduct.mk k B C).flip 1) b = 0 at hb
    simpa [LinearMap.sub_apply] using sub_eq_zero.mp hb
  have hnat (z : B ⊗[k] B) :
      TensorProduct.map p.toAlgHom.toLinearMap LinearMap.id
          ((TensorProduct.comm k B B).toLinearMap z) =
        (TensorProduct.comm k B C).toLinearMap
          (TensorProduct.map LinearMap.id p.toAlgHom.toLinearMap z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (fun u v => u + v) hx hy
    | tmul x y => simp
  calc
    _ = TensorProduct.map p.toAlgHom.toLinearMap LinearMap.id
        ((TensorProduct.comm k B B).toLinearMap
          (Coalgebra.comul (R := k) b)) := by
            exact congrArg
              (TensorProduct.map p.toAlgHom.toLinearMap LinearMap.id)
              (Coalgebra.comm_comul k b).symm
    _ = (TensorProduct.comm k B C).toLinearMap
        (TensorProduct.map LinearMap.id p.toAlgHom.toLinearMap
          (Coalgebra.comul (R := k) b)) := hnat _
    _ = (TensorProduct.comm k B C).toLinearMap (b ⊗ₜ[k] 1) := by rw [hright]
    _ = 1 ⊗ₜ[k] b := by simp

/-- Intrinsic data for a cleft exact sequence. -/
structure CleftExactSequence
    (A : Type v) (B : Type w) (C : Type x) [Field k]
    [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C] where
  inclusion : HopfAlgebraHom (k := k) (H := A) B
  projection : HopfAlgebraHom (k := k) (H := B) C
  inclusion_injective : Function.Injective inclusion
  projection_surjective : Function.Surjective projection
  projection_inclusion : ∀ a,
    projection (inclusion a) = algebraMap k C (Coalgebra.counit (R := k) a)
  coalgebraSection : C →ₗc[k] B
  projection_section : projection.toAlgHom.toLinearMap.comp
      coalgebraSection.toLinearMap = LinearMap.id
  section_one : coalgebraSection 1 = 1
  coinvariants : LinearMap.range inclusion.toAlgHom.toLinearMap =
    rightCoinvariants projection

end

end HopfAmenability
