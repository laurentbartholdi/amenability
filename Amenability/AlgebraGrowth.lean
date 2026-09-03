/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubexponentialGrowth
import Amenability.HopfActionSubspace

/-! # Growth of associative algebras -/

open Coalgebra Module
namespace HopfAmenability
noncomputable section
universe u v
variable (k : Type u) [Field k]

/-- The unital left-multiplication balls of an associative algebra. -/
def associativeGrowthBall
    {A : Type v} [Ring A] [Algebra k A]
    (P : Submodule k A) : ℕ → Submodule k A
  | 0 => k ∙ (1 : A)
  | n + 1 => associativeGrowthBall P n ⊔ P * associativeGrowthBall P n

theorem finiteDimensional_associativeGrowthBall
    {A : Type v} [Ring A] [Algebra k A]
    (P : Submodule k A) [FiniteDimensional k P] (n : ℕ) :
    FiniteDimensional k (associativeGrowthBall k P n) := by
  induction n with
  | zero => rw [associativeGrowthBall]; infer_instance
  | succ n ih =>
      rw [associativeGrowthBall]
      let _ : FiniteDimensional k (associativeGrowthBall k P n) := ih
      have hmul : FiniteDimensional k
          (P * associativeGrowthBall k P n) := by
        rw [Submodule.mul_eq_map₂,
          TensorProduct.map₂_eq_range_lift_comp_mapIncl]
        exact Module.Finite.range _
      let _ := hmul
      infer_instance

/-- Subexponential growth with respect to one coefficient subspace. -/
def IsSubexponentialAlgebraGrowthWith
    {A : Type v} [Ring A] [Algebra k A] (P : Submodule k A) : Prop :=
  IsSubexponentialSequence
    (fun n => sfinrank k (associativeGrowthBall k P n))

/-- Every finite-dimensional coefficient subspace has subexponential balls. -/
def HasLocallySubexponentialAlgebraGrowth
    {A : Type v} [Ring A] [Algebra k A] : Prop :=
  ∀ P : Submodule k A, FiniteDimensional k P →
    IsSubexponentialAlgebraGrowthWith (k := k) P

/-- Compatibility alias for the former local algebra-growth terminology. -/
abbrev HasSubexponentialAlgebraGrowth
    {A : Type v} [Ring A] [Algebra k A] : Prop :=
  HasLocallySubexponentialAlgebraGrowth (k := k) (A := A)

/-- A finite-dimensional algebra has locally subexponential algebra growth. -/
theorem hasLocallySubexponentialAlgebraGrowth_of_finiteDimensional
    {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A] :
    HasLocallySubexponentialAlgebraGrowth (k := k) (A := A) := by
  intro P hP q hq
  let _ : FiniteDimensional k P := hP
  let C : ℚ := Module.finrank k A + 1
  refine ⟨C, by dsimp [C]; positivity, fun n => ?_⟩
  have hdim : sfinrank k (associativeGrowthBall k P n) ≤ Module.finrank k A :=
    Submodule.finrank_le _
  have hpow : (1 : ℚ) ≤ q ^ n := one_le_pow₀ hq.le
  calc
    (sfinrank k (associativeGrowthBall k P n) : ℚ) ≤ Module.finrank k A := by
      exact_mod_cast hdim
    _ ≤ C := by dsimp [C]; linarith
    _ ≤ C * q ^ n := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (by dsimp [C]; positivity)


end
end HopfAmenability
