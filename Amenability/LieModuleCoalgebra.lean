/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.LinearAlgebra.TensorProduct.Map
import Amenability.TwoSidedCoideal

/-!
# Coalgebras carrying a compatible Lie-module structure
-/

namespace Coalgebra

universe u v w

/-- A coalgebra which is also a Lie module, with every Lie action operator a
coderivation. Counit compatibility follows from this axiom. -/
class IsLieModuleCoalgebra
    (k : Type u) (L : Type v) (M : Type w)
    [Field k]
    [LieRing L] [LieAlgebra k L]
    [AddCommGroup M] [Module k M]
    [LieRingModule L M] [LieModule k L M]
    [Coalgebra k M] : Prop where
  comul_lie : ∀ x : L,
    Coalgebra.comul (R := k) (A := M) ∘ₗ LieModule.toEnd k L M x =
      ((LieModule.toEnd k L M x).rTensor M +
        (LieModule.toEnd k L M x).lTensor M) ∘ₗ
          Coalgebra.comul (R := k) (A := M)

variable {k : Type u} {L : Type v} {M : Type w}
variable [Field k]
variable [LieRing L] [LieAlgebra k L]
variable [AddCommGroup M] [Module k M]
variable [LieRingModule L M] [LieModule k L M]
variable [Coalgebra k M] [IsLieModuleCoalgebra k L M]

/-- Pointwise form of the coderivation compatibility. -/
theorem comul_lie_apply (x : L) (m : M) :
    Coalgebra.comul (R := k) (A := M) ⁅x, m⁆ =
      (LieModule.toEnd k L M x).rTensor M
          (Coalgebra.comul (R := k) (A := M) m) +
        (LieModule.toEnd k L M x).lTensor M
          (Coalgebra.comul (R := k) (A := M) m) := by
  have h := congrArg (fun f : M →ₗ[k] TensorProduct k M M => f m)
    (IsLieModuleCoalgebra.comul_lie (k := k) (L := L) (M := M) x)
  simpa using h

/-- Pointwise form of the counit compatibility. -/
theorem counit_lie_apply (x : L) (m : M) :
    Coalgebra.counit (R := k) (A := M) ⁅x, m⁆ = 0 := by
  let ε := Coalgebra.counit (R := k) (A := M)
  let εε : TensorProduct k M M →ₗ[k] k :=
    (TensorProduct.lid k k).toLinearMap.comp
      ((ε.lTensor k).comp (ε.rTensor M))
  have hleft (f : M →ₗ[k] k) (y : M) :
      (TensorProduct.lid k k) (_root_.TensorProduct.map ε f
        (Coalgebra.comul (R := k) (A := M) y)) = f y := by
    have hy := congrArg (fun z => (TensorProduct.lid k k) z)
      (LinearMap.congr_fun (CoassocSimps.map_counit_comp_comul_left f) y)
    simpa [εε, ε] using hy
  have hright (f : M →ₗ[k] k) (y : M) :
      (TensorProduct.lid k k) (_root_.TensorProduct.map f ε
        (Coalgebra.comul (R := k) (A := M) y)) = f y := by
    have hy := congrArg (fun z => (TensorProduct.lid k k) z)
      (LinearMap.congr_fun (CoassocSimps.map_counit_comp_comul_right f) y)
    simpa [εε, ε] using hy
  have h := congrArg εε (comul_lie_apply x m)
  have h' :
      (TensorProduct.lid k k)
          (_root_.TensorProduct.map ε ε
            (Coalgebra.comul (R := k) (A := M) ⁅x, m⁆)) =
        (TensorProduct.lid k k)
            (_root_.TensorProduct.map
              (ε.comp (LieModule.toEnd k L M x)) ε
              (Coalgebra.comul (R := k) (A := M) m)) +
          (TensorProduct.lid k k)
            (_root_.TensorProduct.map ε
              (ε.comp (LieModule.toEnd k L M x))
              (Coalgebra.comul (R := k) (A := M) m)) := by
    simpa [εε, ε] using h
  rw [hleft, hright, hleft] at h'
  change (ε.comp (LieModule.toEnd k L M x)) m = 0
  have hz : (0 : k) = (ε.comp (LieModule.toEnd k L M x)) m := by
    calc
      0 = (ε.comp (LieModule.toEnd k L M x)) m -
          (ε.comp (LieModule.toEnd k L M x)) m := by simp
      _ = ((ε.comp (LieModule.toEnd k L M x)) m +
            (ε.comp (LieModule.toEnd k L M x)) m) -
          (ε.comp (LieModule.toEnd k L M x)) m :=
        congrArg (fun z => z - (ε.comp (LieModule.toEnd k L M x)) m) h'
      _ = (ε.comp (LieModule.toEnd k L M x)) m := by abel
  exact hz.symm

end Coalgebra
