/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Mathlib

/-! # Subexponential growth of sequences -/

namespace HopfAmenability
noncomputable section

/-- A natural-valued sequence has subexponential growth if it is bounded by
every rational exponential rate greater than one, up to a positive
multiplicative constant. -/
def IsSubexponentialSequence (a : ℕ → ℕ) : Prop :=
  ∀ q : ℚ, 1 < q →
    ∃ C : ℚ, 0 < C ∧ ∀ n : ℕ, (a n : ℚ) ≤ C * q ^ n

/-- On `[0,1]`, the binomial expansion is bounded linearly with the sum of
its nonconstant coefficients. -/
theorem one_add_pow_le_one_add_two_pow_sub_one_mul
    (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ∀ n : ℕ,
    (1 + x) ^ n ≤ 1 + ((2 : ℚ) ^ n - 1) * x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      have hbase : 0 ≤ 1 + x := by linarith
      have hmul := mul_le_mul_of_nonneg_right ih hbase
      have hxx : x * x ≤ x := by nlinarith
      calc
        (1 + x) ^ n * (1 + x) ≤
            (1 + (2 ^ n - 1) * x) * (1 + x) := hmul
        _ ≤ 1 + (2 ^ n * 2 - 1) * x := by
          have hp : (1 : ℚ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
          nlinarith

/-- Sampling a subexponential sequence along a fixed arithmetic dilation
preserves subexponential growth. -/
theorem IsSubexponentialSequence.comp_mul (a : ℕ → ℕ)
    (ha : IsSubexponentialSequence a) (d : ℕ) :
    IsSubexponentialSequence (fun n => a (d * n)) := by
  intro q hq
  by_cases hd : d = 0
  · subst d
    obtain ⟨C, hC, h⟩ := ha q hq
    refine ⟨C, hC, fun n => ?_⟩
    calc
      (a (0 * n) : ℚ) = a 0 := by simp
      _ ≤ C := by simpa using h 0
      _ ≤ C * q ^ n := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (one_le_pow₀ hq.le) hC.le
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let x : ℚ := (q - 1) / ((2 : ℚ) ^ d * q ^ d)
    have hq0 : 0 < q := by linarith
    have hden : 0 < (2 : ℚ) ^ d * q ^ d :=
      mul_pos (by positivity) (by positivity)
    have hx0 : 0 < x := div_pos (sub_pos.mpr hq) hden
    have hqd : q ≤ q ^ d := by
      have := pow_le_pow_right₀ hq.le (show 1 ≤ d by omega)
      simpa using this
    have hx1 : x ≤ 1 := by
      rw [div_le_one hden]
      have htwo : (1 : ℚ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      have := mul_le_mul htwo hqd (by positivity) (by norm_num)
      nlinarith
    let r : ℚ := 1 + x
    have hr : 1 < r := by dsimp [r]; linarith
    obtain ⟨C, hC, hbound⟩ := ha r hr
    refine ⟨C, hC, fun n => ?_⟩
    have hrd : r ^ d ≤ q := by
      have hp := one_add_pow_le_one_add_two_pow_sub_one_mul
        x hx0.le hx1 d
      have hcoef : ((2 : ℚ) ^ d - 1) * x ≤ q - 1 := by
        dsimp [x]
        rw [div_eq_mul_inv]
        have hpow2 : 0 ≤ (2 : ℚ) ^ d := pow_nonneg (by norm_num) _
        have hqpow : 1 ≤ q ^ d := one_le_pow₀ hq.le
        rw [show ((2 : ℚ) ^ d - 1) *
            ((q - 1) * ((2 : ℚ) ^ d * q ^ d)⁻¹) =
          (((2 : ℚ) ^ d - 1) * (q - 1)) /
            ((2 : ℚ) ^ d * q ^ d) by ring]
        rw [div_le_iff₀ hden]
        have hcoef2 : (2 : ℚ) ^ d - 1 ≤ 2 ^ d := by linarith
        have hmul := mul_le_mul_of_nonneg_right hcoef2 (sub_pos.mpr hq).le
        have hqd1 : 1 ≤ q ^ d := one_le_pow₀ hq.le
        nlinarith [mul_le_mul_of_nonneg_left hqd1
          (mul_nonneg hpow2 (sub_pos.mpr hq).le)]
      dsimp [r]
      linarith
    calc
      (a (d * n) : ℚ) ≤ C * r ^ (d * n) := hbound (d * n)
      _ = C * (r ^ d) ^ n := by rw [pow_mul]
      _ ≤ C * q ^ n := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hrd n) hC.le


/-- The elementary ratio test used to pass from a subexponential bound to
a Følner radius. -/
theorem exists_succ_le_mul_of_exponential_bound
    (a : ℕ → ℚ) (ha0 : 0 < a 0) (ε : ℚ) (hε : 0 < ε)
    (C : ℚ)
    (hbound : ∀ n : ℕ, a n ≤ C * (1 + ε / 2) ^ n) :
    ∃ n : ℕ, a (n + 1) ≤ (1 + ε) * a n := by
  by_contra h
  push Not at h
  have hr : 0 < 1 + ε := by linarith
  have hs : 0 < 1 + ε / 2 := by linarith
  have hrs : 1 < (1 + ε) / (1 + ε / 2) := by
    rw [one_lt_div hs]
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / a 0) hrs
  have hgrowth : ∀ m : ℕ, (1 + ε) ^ m * a 0 ≤ a m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        have hstep : (1 + ε) ^ m * (1 + ε) * a 0 < a (m + 1) := by
          calc
          (1 + ε) ^ m * (1 + ε) * a 0 =
              (1 + ε) * ((1 + ε) ^ m * a 0) := by ring
            _ ≤ (1 + ε) * a m := mul_le_mul_of_nonneg_left ih hr.le
            _ < a (m + 1) := h m
        exact hstep.le
  have hpow : C * (1 + ε / 2) ^ n < (1 + ε) ^ n * a 0 := by
    rw [div_pow] at hn
    exact (div_lt_div_iff₀ ha0 (pow_pos hs n)).mp hn
  have han : a n < (1 + ε) ^ n * a 0 :=
    lt_of_le_of_lt (hbound n) hpow
  exact (not_lt_of_ge (hgrowth n)) han


/-- A subexponential positive sequence has a Følner consecutive ratio. -/
theorem exists_succ_ratio_le_of_subexponential
    (a : ℕ → ℕ) (ha0 : 0 < a 0)
    (hsub : IsSubexponentialSequence a)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ n, (a (n + 1) : ℚ) ≤ (1 + ε) * a n := by
  obtain ⟨C, _hC, hbound⟩ := hsub (1 + ε / 2) (by linarith)
  exact exists_succ_le_mul_of_exponential_bound
    (fun n => (a n : ℚ)) (by exact_mod_cast ha0) ε hε C hbound


end
end HopfAmenability

