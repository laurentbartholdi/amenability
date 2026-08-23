/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Amenability.TwoSidedCoideal

/-!
# Coalgebras carrying a compatible Lie-module structure
-/

namespace HopfAmenability

universe u v w

/-- A coalgebra which is also a Lie module, with every Lie action operator a
coderivation and with zero counit. -/
class LieModuleCoalgebra
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
  counit_lie : ∀ x : L,
    Coalgebra.counit (R := k) (A := M) ∘ₗ LieModule.toEnd k L M x = 0

variable {k : Type u} {L : Type v} {M : Type w}
variable [Field k]
variable [LieRing L] [LieAlgebra k L]
variable [AddCommGroup M] [Module k M]
variable [LieRingModule L M] [LieModule k L M]
variable [Coalgebra k M] [LieModuleCoalgebra k L M]

/-- Pointwise form of the coderivation compatibility. -/
theorem comul_lie_apply (x : L) (m : M) :
    Coalgebra.comul (R := k) (A := M) ⁅x, m⁆ =
      (LieModule.toEnd k L M x).rTensor M
          (Coalgebra.comul (R := k) (A := M) m) +
        (LieModule.toEnd k L M x).lTensor M
          (Coalgebra.comul (R := k) (A := M) m) := by
  have h := congrArg (fun f : M →ₗ[k] TensorProduct k M M => f m)
    (LieModuleCoalgebra.comul_lie (k := k) (L := L) (M := M) x)
  simpa using h

/-- Pointwise form of the counit compatibility. -/
theorem counit_lie_apply (x : L) (m : M) :
    Coalgebra.counit (R := k) (A := M) ⁅x, m⁆ = 0 := by
  have h := congrArg (fun f : M →ₗ[k] k => f m)
    (LieModuleCoalgebra.counit_lie (k := k) (L := L) (M := M) x)
  simpa using h

end HopfAmenability
