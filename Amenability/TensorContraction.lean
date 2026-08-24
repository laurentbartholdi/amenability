/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Contraction of a tensor factor
-/

open TensorProduct

namespace TensorProduct

noncomputable section

universe u v w

variable {k : Type u} {M : Type v} {X : Type w}
variable [CommSemiring k]
variable [AddCommMonoid M] [Module k M]
variable [AddCommMonoid X] [Module k X]

/-- Contract the left tensor factor against a linear functional. -/
noncomputable def leftContract (f : M →ₗ[k] k) :
    M ⊗[k] X →ₗ[k] X :=
  (TensorProduct.lid k X).toLinearMap ∘ₗ f.rTensor X

@[simp]
theorem leftContract_tmul
    (f : M →ₗ[k] k) (m : M) (x : X) :
    TensorProduct.leftContract f (m ⊗ₜ[k] x) = f m • x := by
  rfl

/-- Contraction commutes with including a tensor square of submodules into
the ambient tensor square. -/
theorem leftContract_mapIncl
    (f : M →ₗ[k] k) (P : Submodule k M) (Q : Submodule k X)
    (z : P ⊗[k] Q) :
    leftContract f (TensorProduct.mapIncl P Q z) =
      Q.subtype (leftContract (f.comp P.subtype) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | tmul m x => rfl

end

end TensorProduct
