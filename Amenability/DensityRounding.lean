/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.DensityFiltration
import Amenability.UnifiedRoundingCore

/-!
# Finite rounding from the density filtration

The density filtration has only finitely many relevant numerical profiles.
We enumerate their crossings in `[0,1]`, telescope the maximal density score
over the resulting intervals, and package the two mass estimates into a
`RoundingCertificate`.
-/

open Module

namespace UnifiedRounding

noncomputable section

universe u v w

variable {k : Type u} {V : Type v} {W : Type w}
variable [Field k]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- All numerical pairs `(dim(E ∩ C), dim C)` that can occur. -/
def possibleDensityProfiles
    (E : Submodule k V) : Finset (ℕ × ℕ) :=
  (Finset.range (finrank k E + 1)).product
    (Finset.range (finrank k V + 1))

/-- The parameter at which two profile score-lines with distinct slopes cross. -/
def densityProfileCrossing (p q : ℕ × ℕ) : ℚ :=
  ((p.1 : ℚ) - (q.1 : ℚ)) /
    ((p.2 : ℚ) - (q.2 : ℚ))

/-- The endpoints and all profile crossings lying in the unit interval. -/
noncomputable def densityBreakpoints
    (E : Submodule k V) : Finset ℚ := by
  classical
  exact
    ({0, 1} ∪
      (((possibleDensityProfiles E).product (possibleDensityProfiles E)).filter
        fun pq => pq.1.2 ≠ pq.2.2).image
          fun pq => densityProfileCrossing pq.1 pq.2).filter
      fun t => 0 ≤ t ∧ t ≤ 1

/-- Every subspace has one of the finite possible density profiles. -/
theorem densityProfile_mem_possibleDensityProfiles
    [FiniteDimensional k V]
    (E C : Submodule k V) :
    (intersectionRank E C, finrank k C) ∈ possibleDensityProfiles E := by
  have hr : intersectionRank E C < finrank k E + 1 :=
    Nat.lt_succ_of_le (Submodule.finrank_mono inf_le_left)
  have hd : finrank k C < finrank k V + 1 :=
    Nat.lt_succ_of_le (Submodule.finrank_le C)
  simpa [possibleDensityProfiles] using And.intro hr hd

@[simp]
theorem zero_mem_densityBreakpoints (E : Submodule k V) :
    0 ∈ densityBreakpoints E := by
  classical
  simp [densityBreakpoints]

@[simp]
theorem one_mem_densityBreakpoints (E : Submodule k V) :
    1 ∈ densityBreakpoints E := by
  classical
  simp [densityBreakpoints]

/-- There are at least the two distinct endpoints among the breakpoints. -/
theorem two_le_card_densityBreakpoints (E : Submodule k V) :
    2 ≤ (densityBreakpoints E).card := by
  classical
  have hsubset : ({0, 1} : Finset ℚ) ⊆ densityBreakpoints E := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact zero_mem_densityBreakpoints E
    · exact one_mem_densityBreakpoints E
  have hcard := Finset.card_le_card hsubset
  simpa using hcard

/-- Increasing enumeration of the density breakpoints. -/
noncomputable def densityBreakpointOrderEmb
    (E : Submodule k V) : Fin (densityBreakpoints E).card ↪o ℚ :=
  (densityBreakpoints E).orderEmbOfFin rfl

/-- A crossing of two possible profiles in `[0,1]` is a breakpoint. -/
theorem densityProfileCrossing_mem_densityBreakpoints
    (E : Submodule k V) {p q : ℕ × ℕ}
    (hp : p ∈ possibleDensityProfiles E)
    (hq : q ∈ possibleDensityProfiles E)
    (hd : p.2 ≠ q.2)
    (h0 : 0 ≤ densityProfileCrossing p q)
    (h1 : densityProfileCrossing p q ≤ 1) :
    densityProfileCrossing p q ∈ densityBreakpoints E := by
  classical
  simp only [densityBreakpoints, Finset.mem_filter]
  refine ⟨?_, h0, h1⟩
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hd⟩, rfl⟩

/-- Two breakpoints are adjacent when no breakpoint lies strictly between them. -/
def AreAdjacentDensityBreakpoints
    (E : Submodule k V) (s t : ℚ) : Prop :=
  s ∈ densityBreakpoints E ∧ t ∈ densityBreakpoints E ∧ s < t ∧
    ∀ u ∈ densityBreakpoints E, ¬ (s < u ∧ u < t)

theorem densityBreakpoint_mem_Icc
    (E : Submodule k V) {t : ℚ} (ht : t ∈ densityBreakpoints E) :
    0 ≤ t ∧ t ≤ 1 := by
  classical
  rw [densityBreakpoints, Finset.mem_filter] at ht
  exact ht.2

/-- On an open chamber, the right-end density subspace already maximizes at the left end. -/
theorem densitySubspace_isMaximizer_left_of_adjacent
    [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V)
    {s t : ℚ} (hadj : AreAdjacentDensityBreakpoints E s t) :
    IsDensityMaximizer 𝓛 E s (densitySubspace 𝓛 E t) := by
  let Cs := densitySubspace 𝓛 E s
  let Ct := densitySubspace 𝓛 E t
  have hsmax := densitySubspace_isLargestMaximizer 𝓛 E s
  have htmax := densitySubspace_isLargestMaximizer 𝓛 E t
  refine ⟨densitySubspace_admissible 𝓛 E t, ?_⟩
  intro D hD
  by_contra hnot
  have hDCt : densityScore E s Ct < densityScore E s D :=
    lt_of_not_ge hnot
  have hDCs : densityScore E s D ≤ densityScore E s Cs :=
    hsmax.1.2 D hD
  have hsstrict : densityScore E s Ct < densityScore E s Cs :=
    lt_of_lt_of_le hDCt hDCs
  have htweak : densityScore E t Cs ≤ densityScore E t Ct :=
    htmax.1.2 Cs hsmax.1.1
  have hdim : finrank k Cs ≠ finrank k Ct := by
    intro heq
    unfold densityScore at hsstrict htweak
    rw [heq] at hsstrict htweak
    linarith
  let p : ℕ × ℕ := (intersectionRank E Cs, finrank k Cs)
  let q : ℕ × ℕ := (intersectionRank E Ct, finrank k Ct)
  let u : ℚ := densityProfileCrossing p q
  have hp : p ∈ possibleDensityProfiles E :=
    densityProfile_mem_possibleDensityProfiles E Cs
  have hq : q ∈ possibleDensityProfiles E :=
    densityProfile_mem_possibleDensityProfiles E Ct
  have hpq : p.2 ≠ q.2 := by
    simpa [p, q] using hdim
  have hpqQ : (p.2 : ℚ) - (q.2 : ℚ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hpq)
  have hu_mul :
      u * ((p.2 : ℚ) - (q.2 : ℚ)) =
        (p.1 : ℚ) - (q.1 : ℚ) := by
    dsimp [u, densityProfileCrossing]
    exact div_mul_cancel₀ _ hpqQ
  have hst : s < t := hadj.2.2.1
  have hsu : s < u := by
    dsimp [Cs, Ct, p, q] at hsstrict htweak hu_mul
    unfold densityScore at hsstrict htweak
    nlinarith
  have hut : u ≤ t := by
    dsimp [Cs, Ct, p, q] at hsstrict htweak hu_mul
    unfold densityScore at hsstrict htweak
    nlinarith
  have hu0 : 0 ≤ u :=
    le_trans (densityBreakpoint_mem_Icc E hadj.1).1 (le_of_lt hsu)
  have hu1 : u ≤ 1 :=
    le_trans hut (densityBreakpoint_mem_Icc E hadj.2.1).2
  have humem : u ∈ densityBreakpoints E :=
    densityProfileCrossing_mem_densityBreakpoints E hp hq hpq hu0 hu1
  have hutEq : u = t := by
    apply le_antisymm hut
    by_contra htu
    have hut' : u < t := lt_of_not_ge htu
    exact hadj.2.2.2 u humem ⟨hsu, hut'⟩
  have hscoret : densityScore E t Cs = densityScore E t Ct := by
    dsimp [Cs, Ct, p, q] at hu_mul
    unfold densityScore
    rw [← hutEq]
    nlinarith
  have hCsMaxT : IsDensityMaximizer 𝓛 E t Cs := by
    refine ⟨hsmax.1.1, ?_⟩
    intro A hA
    calc
      densityScore E t A ≤ densityScore E t Ct := htmax.1.2 A hA
      _ = densityScore E t Cs := hscoret.symm
  have hCsCt : Cs ≤ Ct := htmax.2 Cs hCsMaxT
  have hCtCs : Ct ≤ Cs :=
    largestDensityMaximizer_antitone hst hsmax htmax
  have heq : Cs = Ct := le_antisymm hCsCt hCtCs
  exact (ne_of_lt hsstrict) (by rw [heq])

/-- The mass of one breakpoint interval is the drop of the maximal score. -/
theorem adjacent_density_mass_identity
    [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V)
    {s t : ℚ} (hadj : AreAdjacentDensityBreakpoints E s t) :
    (t - s) * (finrank k (densitySubspace 𝓛 E t) : ℚ) =
      maximalDensityScore 𝓛 E s - maximalDensityScore 𝓛 E t := by
  let Ct := densitySubspace 𝓛 E t
  have hsmax := densitySubspace_isMaximizer_left_of_adjacent 𝓛 E hadj
  have hscoreS : densityScore E s Ct = maximalDensityScore 𝓛 E s := by
    exact (hsmax.score_eq (densitySubspace_isMaximizer 𝓛 E s)).trans
      (densitySubspace_score 𝓛 E s)
  have hscoreT : densityScore E t Ct = maximalDensityScore 𝓛 E t :=
    densitySubspace_score 𝓛 E t
  rw [← hscoreS, ← hscoreT]
  unfold densityScore
  ring

/-- At parameter zero, a family containing an admissible hull of `E` has score `dim E`. -/
theorem maximalDensityScore_zero
    [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V)
    (hA : ∃ A : Submodule k V, 𝓛.admissible A ∧ E ≤ A) :
    maximalDensityScore 𝓛 E 0 = finrank k E := by
  obtain ⟨A, hAadm, hEA⟩ := hA
  have hlower := densityScore_le_maximalDensityScore 𝓛 E 0 hAadm
  have hEAinf : E ⊓ A = E := inf_eq_left.mpr hEA
  have hscoreA : densityScore E 0 A = (finrank k E : ℚ) := by
    rw [densityScore, zero_mul, sub_zero, intersectionRank, hEAinf]
  rw [hscoreA] at hlower
  obtain ⟨C, hCadm, hCscore⟩ := maximalDensityScore_realized 𝓛 E 0
  have hrank : intersectionRank E C ≤ finrank k E := by
    exact Submodule.finrank_mono inf_le_left
  have hupper : maximalDensityScore 𝓛 E 0 ≤ (finrank k E : ℚ) := by
    rw [← hCscore]
    rw [densityScore, zero_mul, sub_zero]
    exact_mod_cast hrank
  exact le_antisymm hupper hlower

/-- At parameter one, the maximal density score is zero. -/
theorem maximalDensityScore_one
    [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) :
    maximalDensityScore 𝓛 E 1 = 0 := by
  have hlower := densityScore_le_maximalDensityScore 𝓛 E 1 𝓛.bot_admissible
  rw [densityScore_bot] at hlower
  obtain ⟨C, hCadm, hCscore⟩ := maximalDensityScore_realized 𝓛 E 1
  have hrank : intersectionRank E C ≤ finrank k C :=
    Submodule.finrank_mono inf_le_right
  have hrankQ : (intersectionRank E C : ℚ) ≤ (finrank k C : ℚ) := by
    exact_mod_cast hrank
  have hupper : maximalDensityScore 𝓛 E 1 ≤ 0 := by
    rw [← hCscore, densityScore, one_mul]
    linarith
  exact le_antisymm hupper hlower

/-- Number of adjacent intervals in the ordered breakpoint set. -/
def densityIntervalCount (E : Submodule k V) : ℕ :=
  (densityBreakpoints E).card - 1

/-- Left endpoint of a breakpoint interval. -/
noncomputable def densityIntervalLeft
    (E : Submodule k V) (i : Fin (densityIntervalCount E)) : ℚ :=
  densityBreakpointOrderEmb E
    ⟨i.1, by
      have hi := i.2
      have hc := two_le_card_densityBreakpoints E
      dsimp [densityIntervalCount] at hi
      omega⟩

/-- Right endpoint of a breakpoint interval. -/
noncomputable def densityIntervalRight
    (E : Submodule k V) (i : Fin (densityIntervalCount E)) : ℚ :=
  densityBreakpointOrderEmb E
    ⟨i.1 + 1, by
      have hi := i.2
      have hc := two_le_card_densityBreakpoints E
      dsimp [densityIntervalCount] at hi
      omega⟩

/-- Consecutive values in the ordered enumeration are adjacent breakpoints. -/
theorem densityInterval_areAdjacent
    (E : Submodule k V) (i : Fin (densityIntervalCount E)) :
    AreAdjacentDensityBreakpoints E
      (densityIntervalLeft E i) (densityIntervalRight E i) := by
  let il : Fin (densityBreakpoints E).card :=
    ⟨i.1, by
      have hi := i.2
      dsimp [densityIntervalCount] at hi
      omega⟩
  let ir : Fin (densityBreakpoints E).card :=
    ⟨i.1 + 1, by
      have hi := i.2
      have hc := two_le_card_densityBreakpoints E
      dsimp [densityIntervalCount] at hi
      omega⟩
  change AreAdjacentDensityBreakpoints E
    (densityBreakpointOrderEmb E il) (densityBreakpointOrderEmb E ir)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.orderEmbOfFin_mem _ rfl il
  · exact Finset.orderEmbOfFin_mem _ rfl ir
  · exact (densityBreakpointOrderEmb E).strictMono (by simp [il, ir])
  · intro u hu hbetween
    have huRange : u ∈ Set.range (densityBreakpointOrderEmb E) := by
      rw [show Set.range (densityBreakpointOrderEmb E) =
        (densityBreakpoints E : Set ℚ) from Finset.range_orderEmbOfFin _ rfl]
      exact hu
    rcases huRange with ⟨j, rfl⟩
    have hlj : il < j :=
      (densityBreakpointOrderEmb E).lt_iff_lt.mp hbetween.1
    have hjr : j < ir :=
      (densityBreakpointOrderEmb E).lt_iff_lt.mp hbetween.2
    change i.1 < j.1 at hlj
    change j.1 < i.1 + 1 at hjr
    omega

/-- Elementary telescoping identity for adjacent differences. -/
theorem sum_range_adjacent_sub (f : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f i - f (i + 1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

def densityFirstIndex (E : Submodule k V) : Fin (densityBreakpoints E).card :=
  ⟨0, by have := two_le_card_densityBreakpoints E; omega⟩

def densityLastIndex (E : Submodule k V) : Fin (densityBreakpoints E).card :=
  ⟨(densityBreakpoints E).card - 1,
    by have := two_le_card_densityBreakpoints E; omega⟩

@[simp]
theorem densityBreakpointOrderEmb_first (E : Submodule k V) :
    densityBreakpointOrderEmb E (densityFirstIndex E) = 0 := by
  have hmem := Finset.orderEmbOfFin_mem
    (densityBreakpoints E) rfl (densityFirstIndex E)
  have hlower := (densityBreakpoint_mem_Icc E hmem).1
  have hzeroRange : (0 : ℚ) ∈ Set.range (densityBreakpointOrderEmb E) := by
    rw [show Set.range (densityBreakpointOrderEmb E) =
      (densityBreakpoints E : Set ℚ) from Finset.range_orderEmbOfFin _ rfl]
    exact zero_mem_densityBreakpoints E
  rcases hzeroRange with ⟨j, hj⟩
  have hle := (densityBreakpointOrderEmb E).monotone
    (show densityFirstIndex E ≤ j by
      apply Fin.le_iff_val_le_val.mpr
      simp [densityFirstIndex])
  rw [hj] at hle
  exact le_antisymm hle hlower

@[simp]
theorem densityBreakpointOrderEmb_last (E : Submodule k V) :
    densityBreakpointOrderEmb E (densityLastIndex E) = 1 := by
  have hmem := Finset.orderEmbOfFin_mem
    (densityBreakpoints E) rfl (densityLastIndex E)
  have hupper := (densityBreakpoint_mem_Icc E hmem).2
  have honeRange : (1 : ℚ) ∈ Set.range (densityBreakpointOrderEmb E) := by
    rw [show Set.range (densityBreakpointOrderEmb E) =
      (densityBreakpoints E : Set ℚ) from Finset.range_orderEmbOfFin _ rfl]
    exact one_mem_densityBreakpoints E
  rcases honeRange with ⟨j, hj⟩
  have hjle : j ≤ densityLastIndex E := by
    apply Fin.le_iff_val_le_val.mpr
    have hjlt := j.2
    have hc := two_le_card_densityBreakpoints E
    simp only [densityLastIndex]
    omega
  have hle := (densityBreakpointOrderEmb E).monotone hjle
  rw [hj] at hle
  exact le_antisymm hupper hle

/-- Breakpoint enumeration with a harmless default outside its finite range. -/
noncomputable def densityBreakpointValue
    (E : Submodule k V) (i : ℕ) : ℚ :=
  if hi : i < (densityBreakpoints E).card then
    densityBreakpointOrderEmb E ⟨i, hi⟩
  else 0

@[simp]
theorem densityBreakpointValue_zero (E : Submodule k V) :
    densityBreakpointValue E 0 = 0 := by
  have hc : 0 < (densityBreakpoints E).card := by
    have := two_le_card_densityBreakpoints E
    omega
  rw [densityBreakpointValue, dite_eq_left hc]
  exact densityBreakpointOrderEmb_first E

@[simp]
theorem densityBreakpointValue_intervalCount (E : Submodule k V) :
    densityBreakpointValue E (densityIntervalCount E) = 1 := by
  have hc : densityIntervalCount E < (densityBreakpoints E).card := by
    have := two_le_card_densityBreakpoints E
    dsimp [densityIntervalCount]
    omega
  rw [densityBreakpointValue, dite_eq_left hc]
  exact densityBreakpointOrderEmb_last E

theorem densityIntervalLeft_eq_value
    (E : Submodule k V) (i : Fin (densityIntervalCount E)) :
    densityIntervalLeft E i = densityBreakpointValue E i.1 := by
  have hi : i.1 < (densityBreakpoints E).card := by
    have hi' := i.2
    dsimp [densityIntervalCount] at hi'
    omega
  rw [densityBreakpointValue, dite_eq_left hi]
  rfl

theorem densityIntervalRight_eq_value
    (E : Submodule k V) (i : Fin (densityIntervalCount E)) :
    densityIntervalRight E i = densityBreakpointValue E (i.1 + 1) := by
  have hi : i.1 + 1 < (densityBreakpoints E).card := by
    have hi' := i.2
    have hc := two_le_card_densityBreakpoints E
    dsimp [densityIntervalCount] at hi'
    omega
  rw [densityBreakpointValue, dite_eq_left hi]
  rfl

/-- Exact mass identity for the source density filtration. -/
theorem density_source_mass
    [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V)
    (hA : ∃ A : Submodule k V, 𝓛.admissible A ∧ E ≤ A) :
    ∑ i : Fin (densityIntervalCount E),
        (densityIntervalRight E i - densityIntervalLeft E i) *
          (finrank k (densitySubspace 𝓛 E (densityIntervalRight E i)) : ℚ) =
      finrank k E := by
  calc
    ∑ i : Fin (densityIntervalCount E),
        (densityIntervalRight E i - densityIntervalLeft E i) *
          (finrank k (densitySubspace 𝓛 E (densityIntervalRight E i)) : ℚ) =
      ∑ i ∈ Finset.range (densityIntervalCount E),
        (maximalDensityScore 𝓛 E (densityBreakpointValue E i) -
          maximalDensityScore 𝓛 E (densityBreakpointValue E (i + 1))) := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            rw [dite_eq_left (Finset.mem_range.mp hi)]
            let j : Fin (densityIntervalCount E) := ⟨i, Finset.mem_range.mp hi⟩
            have hj := adjacent_density_mass_identity 𝓛 E
              (densityInterval_areAdjacent E j)
            simpa [j, densityIntervalLeft_eq_value,
              densityIntervalRight_eq_value] using hj
    _ = maximalDensityScore 𝓛 E (densityBreakpointValue E 0) -
        maximalDensityScore 𝓛 E
          (densityBreakpointValue E (densityIntervalCount E)) :=
      sum_range_adjacent_sub
        (fun i => maximalDensityScore 𝓛 E (densityBreakpointValue E i))
        (densityIntervalCount E)
    _ = finrank k E := by
      rw [densityBreakpointValue_zero, densityBreakpointValue_intervalCount,
        maximalDensityScore_zero 𝓛 E hA, maximalDensityScore_one]
      simp

/-- Any interval gives an upper mass bound for a second density filtration. -/
theorem density_interval_upper_bound
    [FiniteDimensional k W]
    (𝒜 : AdmissibleFamily k W) (E' : Submodule k W)
    {s t : ℚ} :
    (t - s) * (finrank k (densitySubspace 𝒜 E' t) : ℚ) ≤
      maximalDensityScore 𝒜 E' s - maximalDensityScore 𝒜 E' t := by
  let D := densitySubspace 𝒜 E' t
  have hs := densityScore_le_maximalDensityScore 𝒜 E' s
    (densitySubspace_admissible 𝒜 E' t)
  have ht : densityScore E' t D = maximalDensityScore 𝒜 E' t :=
    densitySubspace_score 𝒜 E' t
  dsimp [D] at hs ht ⊢
  rw [← ht]
  unfold densityScore at hs ⊢
  linarith

theorem maximalDensityScore_zero_le_finrank
    [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) :
    maximalDensityScore 𝓛 E 0 ≤ finrank k E := by
  obtain ⟨C, hCadm, hCscore⟩ := maximalDensityScore_realized 𝓛 E 0
  have hrank : intersectionRank E C ≤ finrank k E :=
    Submodule.finrank_mono inf_le_left
  have hrankQ : (intersectionRank E C : ℚ) ≤ (finrank k E : ℚ) := by
    exact_mod_cast hrank
  rw [← hCscore, densityScore, zero_mul, sub_zero]
  exact hrankQ

/-- Maximal-score drops telescope along another filtration's breakpoint grid. -/
theorem density_maximalScore_telescope
    [FiniteDimensional k W]
    (𝒜 : AdmissibleFamily k W) (E' : Submodule k W)
    (E : Submodule k V) :
    ∑ i : Fin (densityIntervalCount E),
        (maximalDensityScore 𝒜 E' (densityIntervalLeft E i) -
          maximalDensityScore 𝒜 E' (densityIntervalRight E i)) =
      maximalDensityScore 𝒜 E' 0 - maximalDensityScore 𝒜 E' 1 := by
  calc
    ∑ i : Fin (densityIntervalCount E),
        (maximalDensityScore 𝒜 E' (densityIntervalLeft E i) -
          maximalDensityScore 𝒜 E' (densityIntervalRight E i)) =
      ∑ i ∈ Finset.range (densityIntervalCount E),
        (maximalDensityScore 𝒜 E' (densityBreakpointValue E i) -
          maximalDensityScore 𝒜 E' (densityBreakpointValue E (i + 1))) := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            rw [dite_eq_left (Finset.mem_range.mp hi)]
            let j : Fin (densityIntervalCount E) := ⟨i, Finset.mem_range.mp hi⟩
            simp [densityIntervalLeft_eq_value,
              densityIntervalRight_eq_value]
    _ = maximalDensityScore 𝒜 E' (densityBreakpointValue E 0) -
        maximalDensityScore 𝒜 E'
          (densityBreakpointValue E (densityIntervalCount E)) :=
      sum_range_adjacent_sub
        (fun i => maximalDensityScore 𝒜 E' (densityBreakpointValue E i))
        (densityIntervalCount E)
    _ = maximalDensityScore 𝒜 E' 0 - maximalDensityScore 𝒜 E' 1 := by
      rw [densityBreakpointValue_zero, densityBreakpointValue_intervalCount]

/-- Upper mass estimate for any target density filtration on the source grid. -/
theorem density_target_upper_mass
    [FiniteDimensional k W]
    (𝒜 : AdmissibleFamily k W) (E' : Submodule k W)
    (E : Submodule k V) :
    ∑ i : Fin (densityIntervalCount E),
        (densityIntervalRight E i - densityIntervalLeft E i) *
          (finrank k (densitySubspace 𝒜 E' (densityIntervalRight E i)) : ℚ) ≤
      finrank k E' := by
  calc
    ∑ i : Fin (densityIntervalCount E),
        (densityIntervalRight E i - densityIntervalLeft E i) *
          (finrank k (densitySubspace 𝒜 E' (densityIntervalRight E i)) : ℚ) ≤
      ∑ i : Fin (densityIntervalCount E),
        (maximalDensityScore 𝒜 E' (densityIntervalLeft E i) -
          maximalDensityScore 𝒜 E' (densityIntervalRight E i)) := by
            exact Finset.sum_le_sum fun i _ => density_interval_upper_bound 𝒜 E'
    _ = maximalDensityScore 𝒜 E' 0 - maximalDensityScore 𝒜 E' 1 :=
      density_maximalScore_telescope 𝒜 E' E
    _ ≤ finrank k E' := by
      rw [maximalDensityScore_one]
      simpa using maximalDensityScore_zero_le_finrank 𝒜 E'

/-- A pointwise upper bound inherits the target upper mass estimate. -/
theorem sum_mul_le_sum_mul_of_nonneg_left
    {ι : Type*} [Fintype ι] (w x y : ι → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hxy : ∀ i, x i ≤ y i) :
    ∑ i, w i * x i ≤ ∑ i, w i * y i := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hw i)

/-- A pointwise upper bound inherits the target upper mass estimate. -/
theorem density_b_upper_mass
    [FiniteDimensional k W]
    (𝒜 : AdmissibleFamily k W) (E' : Submodule k W)
    (E : Submodule k V) (b : ℚ → ℚ)
    (hb_le : ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      b t ≤ finrank k (densitySubspace 𝒜 E' t)) :
    ∑ i : Fin (densityIntervalCount E),
        (densityIntervalRight E i - densityIntervalLeft E i) *
          b (densityIntervalRight E i) ≤ finrank k E' := by
  apply le_trans
    (sum_mul_le_sum_mul_of_nonneg_left
      (fun i : Fin (densityIntervalCount E) =>
        densityIntervalRight E i - densityIntervalLeft E i)
      (fun i => b (densityIntervalRight E i))
      (fun i => (finrank k
        (densitySubspace 𝒜 E' (densityIntervalRight E i)) : ℚ))
      (fun i => sub_nonneg.mpr (densityInterval_areAdjacent E i).2.2.1.le)
      (fun i => by
        have hi := densityBreakpoint_mem_Icc E
          (densityInterval_areAdjacent E i).2.1
        exact hb_le _ hi.1 hi.2))
  exact density_target_upper_mass 𝒜 E' E

/--
Finite weighted averaging for two density filtrations, using only the source
breakpoint grid.
-/
theorem exists_ratio_le_of_density_filtrations
    [FiniteDimensional k V] [FiniteDimensional k W]
    (𝓛 : AdmissibleFamily k V) (𝒜 : AdmissibleFamily k W)
    (E : Submodule k V) (E' : Submodule k W)
    (hE : E ≠ ⊥)
    (hA : ∃ A : Submodule k V, 𝓛.admissible A ∧ E ≤ A)
    (b : ℚ → ℚ)
    (hb_nonneg : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ b t)
    (hb_le : ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      b t ≤ finrank k (densitySubspace 𝒜 E' t)) :
    ∃ t ∈ densityBreakpoints E,
      0 < finrank k (densitySubspace 𝓛 E t) ∧
        b t / finrank k (densitySubspace 𝓛 E t) ≤
          finrank k E' / finrank k E := by
  have hdimE : (0 : ℚ) < finrank k E := by
    let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hplus :
      ∑ i : Fin (densityIntervalCount E),
          (densityIntervalRight E i - densityIntervalLeft E i) *
            b (densityIntervalRight E i) ≤ finrank k E' := by
    exact density_b_upper_mass 𝒜 E' E b hb_le
  let cert : RoundingCertificate (Fin (densityIntervalCount E)) := {
    w := fun i => densityIntervalRight E i - densityIntervalLeft E i
    cDim := fun i => finrank k (densitySubspace 𝓛 E (densityIntervalRight E i))
    fcDim := fun i => b (densityIntervalRight E i)
    dimE := finrank k E
    dimFE := finrank k E'
    w_nonneg := fun i => by
      exact sub_nonneg.mpr (densityInterval_areAdjacent E i).2.2.1.le
    cDim_nonneg := fun i => by
      exact_mod_cast (Nat.zero_le
        (finrank k (densitySubspace 𝓛 E (densityIntervalRight E i))))
    fcDim_nonneg := fun i => by
      have hi := densityBreakpoint_mem_Icc E
        (densityInterval_areAdjacent E i).2.1
      exact hb_nonneg _ hi.1 hi.2
    dimE_pos := hdimE
    mass := density_source_mass 𝓛 E hA
    plus_mass := hplus
  }
  obtain ⟨i, hwi, hci, hratio⟩ := cert.exists_ratio_le
  change (0 : ℚ) < finrank k
    (densitySubspace 𝓛 E (densityIntervalRight E i)) at hci
  change b (densityIntervalRight E i) /
      finrank k (densitySubspace 𝓛 E (densityIntervalRight E i)) ≤
    finrank k E' / finrank k E at hratio
  refine ⟨densityIntervalRight E i, ?_, ?_, ?_⟩
  · exact (densityInterval_areAdjacent E i).2.1
  · have hne : finrank k
        (densitySubspace 𝓛 E (densityIntervalRight E i)) ≠ 0 := by
      intro hz
      rw [hz] at hci
      norm_num at hci
    exact Nat.pos_of_ne_zero hne
  · exact hratio

end

end UnifiedRounding
