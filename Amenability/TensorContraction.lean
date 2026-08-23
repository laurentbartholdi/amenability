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

namespace UnifiedRounding

noncomputable section

universe u v w

variable {k : Type u} {M : Type v} {X : Type w}
variable [CommSemiring k]
variable [AddCommMonoid M] [Module k M]
variable [AddCommMonoid X] [Module k X]

/-- Contract the left tensor factor against a linear functional. -/
noncomputable def TensorProduct.leftContract (f : M →ₗ[k] k) :
    M ⊗[k] X →ₗ[k] X :=
  (TensorProduct.lid k X).toLinearMap ∘ₗ f.rTensor X

@[simp]
theorem TensorProduct.leftContract_tmul
    (f : M →ₗ[k] k) (m : M) (x : X) :
    TensorProduct.leftContract f (m ⊗ₜ[k] x) = f m • x := by
  rfl

end

end UnifiedRounding
