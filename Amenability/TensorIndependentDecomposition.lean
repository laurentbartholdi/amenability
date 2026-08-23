/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Tensor decompositions with an independent right family
-/

open Module

namespace TensorProduct

noncomputable section

universe u v w

variable {k : Type u} {M : Type v} {C : Type w}
variable [Field k]
variable [AddCommGroup M] [Module k M]
variable [AddCommGroup C] [Module k C]

/-- Every tensor admits a finite pure-tensor decomposition whose right factors
are linearly independent. -/
theorem exists_sum_tmul_linearlyIndependent_right (x : M ⊗[k] C) :
    ∃ (n : ℕ) (m : Fin n → M) (c : Fin n → C),
      LinearIndependent k c ∧ x = ∑ i, m i ⊗ₜ[k] c i := by
  obtain ⟨C', hC'fin, hx⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite
      ({x} : Set (M ⊗[k] C)) (Set.finite_singleton x)
  let _ : Module.Finite k C' := hC'fin
  rcases hx (Set.mem_singleton x) with ⟨y, hy⟩
  let e := Module.finBasis k C'
  let a : Fin (finrank k C') →₀ M :=
    TensorProduct.equivFinsuppOfBasisRight e y
  refine ⟨finrank k C', fun i => a i, fun i => (e i : C), ?_, ?_⟩
  · exact e.linearIndependent.map' C'.subtype C'.ker_subtype
  · rw [← hy]
    have hyBasis : y = ∑ i, a i ⊗ₜ[k] e i := by
      calc
        y = (TensorProduct.equivFinsuppOfBasisRight e).symm a := by
          exact (TensorProduct.equivFinsuppOfBasisRight e).symm_apply_apply y |>.symm
        _ = a.sum fun i mi => mi ⊗ₜ[k] e i := by simp
        _ = ∑ i, a i ⊗ₜ[k] e i := by
          classical
          rw [Finsupp.sum_fintype]
          intro i
          simp
    rw [hyBasis, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rfl

end

end TensorProduct
