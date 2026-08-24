/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Convenience lemmas for bilinear images of submodules

These generic linear-algebra lemmas are candidates for upstreaming to Mathlib.
-/

namespace Submodule

universe u v w z

variable {k : Type u} {A : Type v} {B : Type w} {P : Type z}
variable [CommSemiring k]
variable [AddCommMonoid A] [Module k A]
variable [AddCommMonoid B] [Module k B]
variable [AddCommMonoid P] [Module k P]

/-- A bilinear image of two elements belongs to the bilinear image of the
submodules containing them. -/
theorem mem_map₂ (f : A →ₗ[k] B →ₗ[k] P)
    (X : Submodule k A) (Y : Submodule k B)
    {x : A} (hx : x ∈ X) {y : B} (hy : y ∈ Y) :
    f x y ∈ Submodule.map₂ f X Y := by
  rw [Submodule.map₂]
  exact Submodule.mem_iSup_of_mem ⟨x, hx⟩ ⟨y, hy, rfl⟩

end Submodule

