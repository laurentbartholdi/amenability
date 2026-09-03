/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TensorFiltrationGraded

/-! # Total-degree leading symbols in a triple tensor product -/

open TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- Triples of nonnegative degrees having prescribed total degree. -/
abbrev TripleDegree (n : ℕ) :=
  {d : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    (d.1 : ℕ) + (d.2.1 : ℕ) + (d.2.2 : ℕ) = n}

/-- The sum of all total-degree-`n` triple leading-symbol coordinates. -/
def tripleGradedLeading (W : ℕ → Submodule k V) (n : ℕ) :
    V ⊗[k] (V ⊗[k] V) →ₗ[k]
      FiltrationGraded W ⊗[k] (FiltrationGraded W ⊗[k] FiltrationGraded W) :=
  ∑ d : TripleDegree n, TensorProduct.map
    (filtrationGradedLeading (k := k) W d.1.1)
    (TensorProduct.map
      (filtrationGradedLeading (k := k) W d.1.2.1)
      (filtrationGradedLeading (k := k) W d.1.2.2))

set_option maxHeartbeats 2000000 in
-- The finite sum is reduced to its unique matching degree triple.
@[simp]
theorem tripleGradedLeading_tmul
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (n i j l : ℕ) (hdeg : i + j + l = n)
    (x : W i) (y : W j) (z : W l) :
    tripleGradedLeading (k := k) W n
        ((x : V) ⊗ₜ[k] ((y : V) ⊗ₜ[k] (z : V))) =
      filtrationGradedLeading (k := k) W i x ⊗ₜ[k]
        (filtrationGradedLeading (k := k) W j y ⊗ₜ[k]
          filtrationGradedLeading (k := k) W l z) := by
  let d : TripleDegree n :=
    ⟨(⟨i, by omega⟩, ⟨j, by omega⟩, ⟨l, by omega⟩), hdeg⟩
  rw [tripleGradedLeading, LinearMap.sum_apply, Finset.sum_eq_single d]
  · simp [d]
  · intro e he hed
    have hlt : (e.1.1 : ℕ) < i ∨ (e.1.2.1 : ℕ) < j ∨
        (e.1.2.2 : ℕ) < l := by
      by_contra h
      push Not at h
      have heq := e.property
      have h1 : e.1.1 = d.1.1 := Fin.ext (by dsimp [d]; omega)
      have h2 : e.1.2.1 = d.1.2.1 := Fin.ext (by dsimp [d]; omega)
      have h3 : e.1.2.2 = d.1.2.2 := Fin.ext (by dsimp [d]; omega)
      apply hed
      apply Subtype.ext
      exact Prod.ext h1 (Prod.ext h2 h3)
    rcases hlt with hi | hj | hl
    · rw [TensorProduct.map_tmul,
        filtrationGradedLeading_eq_zero_of_lt W hW hi x x.property,
        zero_tmul]
    · rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
        filtrationGradedLeading_eq_zero_of_lt W hW hj y y.property,
        zero_tmul, tmul_zero]
    · rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
        filtrationGradedLeading_eq_zero_of_lt W hW hl z z.property,
        tmul_zero, tmul_zero]
  · simp

end

end HopfAmenability
