/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Mathlib

/-!
# Unified rounding: formal numerical core

This file isolates the two finite-dimensional numerical arguments used in the
coalgebraic rounding theorem:

1. `exists_ratio_le_of_weighted_average`: the final averaging/rounding step.
2. `layer_transfer`: the dimension bookkeeping in the filtered transfer lemma.
3. `RoundingCertificate`: a finite certificate from which the desired ratio
   follows immediately.

The genuinely coalgebraic part of the development is to construct such a
certificate from the density filtration `C_t(E)` and to prove
`F C_t(E) ≤ C_t(FE)`.

Current mathlib has coalgebras and bialgebras but no bundled `Subcoalgebra`,
so that interface must first be supplied locally (or upstreamed).
-/

open scoped BigOperators

namespace UnifiedRounding

section WeightedAverage

variable {ι : Type*} [Fintype ι]

/--
If nonnegative weights `w i` give positive total `a`-mass, and the weighted
average of `b` is at most `q` times the weighted average of `a`, then at some
index of positive weight and positive `a`-mass one has `b i ≤ q * a i`.

This is the finite form of the final integration argument in the rounding
proof.
-/
theorem exists_ratio_le_of_weighted_average
    (w a b : ι → ℚ) (q : ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i)
    (hmass : 0 < ∑ i, w i * a i)
    (havg : ∑ i, w i * b i ≤ q * ∑ i, w i * a i) :
    ∃ i, 0 < w i ∧ 0 < a i ∧ b i ≤ q * a i := by
  by_contra h
  push Not at h
  have hle : ∀ i, w i * (q * a i) ≤ w i * b i := by
    intro i
    by_cases hwi : w i = 0
    · simp [hwi]
    have hwi' : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hwi)
    by_cases hai : a i = 0
    · simp [hai, mul_nonneg (hw i) (hb i)]
    have hai' : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hai)
    have hnot : ¬ b i ≤ q * a i := not_le_of_gt (h i hwi' hai')
    exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hnot)) (hw i)
  have hex : ∃ i, w i * a i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hsumzero : (∑ i, w i * a i) = 0 := by
      simp [hzero]
    linarith
  obtain ⟨i₀, hi₀⟩ := hex
  have hwi₀ : w i₀ ≠ 0 := by
    intro hwi
    simp [hwi] at hi₀
  have hai₀ : a i₀ ≠ 0 := by
    intro hai
    simp [hai] at hi₀
  have hwi₀' : 0 < w i₀ := lt_of_le_of_ne (hw i₀) (Ne.symm hwi₀)
  have hai₀' : 0 < a i₀ := lt_of_le_of_ne (ha i₀) (Ne.symm hai₀)
  have hnot₀ : ¬ b i₀ ≤ q * a i₀ := not_le_of_gt (h i₀ hwi₀' hai₀')
  have hlt₀ : w i₀ * (q * a i₀) < w i₀ * b i₀ := by
    exact mul_lt_mul_of_pos_left (lt_of_not_ge hnot₀) hwi₀'
  have hsumlt :
      (∑ i, w i * (q * a i)) < ∑ i, w i * b i := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact hle i
    · exact ⟨i₀, Finset.mem_univ i₀, hlt₀⟩
  have hrearrange :
      (∑ i, w i * (q * a i)) = q * ∑ i, w i * a i := by
    calc
      (∑ i, w i * (q * a i))
          = ∑ i, q * (w i * a i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = q * ∑ i, w i * a i := by
              rw [Finset.mul_sum]
  rw [hrearrange] at hsumlt
  linarith

end WeightedAverage


section LayerTransfer

variable {ι : Type*} [Fintype ι]

/--
The numerical heart of the filtered transfer lemma.

`m i` is the dimension of the `i`-th graded piece of `J`;
`n i` bounds the corresponding graded piece of `N`.
If every graded piece loses at least a proportion `t`, then `J/N`
also loses at least that proportion.
-/
theorem layer_transfer
    (t J N : ℚ) (m n : ι → ℚ)
    (hJ : J = ∑ i, m i)
    (hN : N ≤ ∑ i, n i)
    (hsem : ∀ i, t * m i ≤ m i - n i) :
    t * J ≤ J - N := by
  have hs :
      ∑ i, t * m i ≤ ∑ i, (m i - n i) := by
    exact Finset.sum_le_sum fun i hi => hsem i
  have hleft : (∑ i, t * m i) = t * ∑ i, m i := by
    rw [Finset.mul_sum]
  have hright :
      (∑ i, (m i - n i)) = (∑ i, m i) - ∑ i, n i := by
    rw [Finset.sum_sub_distrib]
  rw [hleft, hright, ← hJ] at hs
  linarith

end LayerTransfer


/--
A finite certificate for the final rounding step.

In the coalgebraic proof, the indices are the intervals on which `C_t(E)` is
constant, `w` is interval length, `cDim` is `dim C_t(E)`, and `fcDim` is
`dim F C_t(E)`.
-/
structure RoundingCertificate (ι : Type*) [Fintype ι] where
  w : ι → ℚ
  cDim : ι → ℚ
  fcDim : ι → ℚ
  dimE : ℚ
  dimFE : ℚ
  w_nonneg : ∀ i, 0 ≤ w i
  cDim_nonneg : ∀ i, 0 ≤ cDim i
  fcDim_nonneg : ∀ i, 0 ≤ fcDim i
  dimE_pos : 0 < dimE
  mass : (∑ i, w i * cDim i) = dimE
  plus_mass : (∑ i, w i * fcDim i) ≤ dimFE

namespace RoundingCertificate

variable {ι : Type*} [Fintype ι]

/--
A finite rounding certificate produces an index with no larger expansion ratio.
-/
theorem exists_ratio_le (C : RoundingCertificate ι) :
    ∃ i, 0 < C.w i ∧ 0 < C.cDim i ∧
      C.fcDim i / C.cDim i ≤ C.dimFE / C.dimE := by
  let q : ℚ := C.dimFE / C.dimE
  have hmass : 0 < ∑ i, C.w i * C.cDim i := by
    rw [C.mass]
    exact C.dimE_pos
  have hqmass :
      q * (∑ i, C.w i * C.cDim i) = C.dimFE := by
    rw [C.mass]
    dsimp [q]
    exact div_mul_cancel₀ C.dimFE (ne_of_gt C.dimE_pos)
  have havg :
      (∑ i, C.w i * C.fcDim i) ≤
        q * ∑ i, C.w i * C.cDim i := by
    rw [hqmass]
    exact C.plus_mass
  obtain ⟨i, hwi, hci, hratio⟩ :=
    exists_ratio_le_of_weighted_average
      C.w C.cDim C.fcDim q
      C.w_nonneg C.cDim_nonneg C.fcDim_nonneg hmass havg
  refine ⟨i, hwi, hci, ?_⟩
  exact (div_le_iff₀ hci).2 hratio

end RoundingCertificate


/--
A convenient certificate for the filtered transfer argument.
-/
structure LayerCertificate (ι : Type*) [Fintype ι] where
  t : ℚ
  dimJ : ℚ
  dimN : ℚ
  jLayer : ι → ℚ
  nLayer : ι → ℚ
  dimJ_eq : dimJ = ∑ i, jLayer i
  dimN_le : dimN ≤ ∑ i, nLayer i
  semistable : ∀ i, t * jLayer i ≤ jLayer i - nLayer i

namespace LayerCertificate

variable {ι : Type*} [Fintype ι]

theorem quotient_bound (C : LayerCertificate ι) :
    C.t * C.dimJ ≤ C.dimJ - C.dimN :=
  layer_transfer C.t C.dimJ C.dimN C.jLayer C.nLayer
    C.dimJ_eq C.dimN_le C.semistable

end LayerCertificate

end UnifiedRounding
