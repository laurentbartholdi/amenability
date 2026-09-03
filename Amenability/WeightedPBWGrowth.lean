/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.WeightedPBW

/-!
# Growth of weighted PBW words

This file supplies the combinatorial half of Smith's theorem: ordered
commutative words in a positively weighted alphabet have subexponential
growth when the number of letters of bounded weight does.
-/

namespace UniversalEnvelopingAlgebra

noncomputable section

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Ordered PBW words of total weight at most `n`. -/
abbrev BoundedWeightPBWWord {ι : Type u} [LinearOrder ι]
    (weight : ι → ℕ) (n : ℕ) :=
  {word : PBWWord ι // pbwListWeight weight word.1 ≤ n}

/-- Letters of weight at most `n`. -/
abbrev WeightSublevel {ι : Type u} (weight : ι → ℕ) (n : ℕ) :=
  {i : ι // weight i ≤ n}

theorem length_le_pbwListWeight_of_pos
    {ι : Type u} (weight : ι → ℕ) (hpos : ∀ i, 0 < weight i)
    (word : List ι) :
    word.length ≤ pbwListWeight weight word := by
  induction word with
  | nil => simp
  | cons i word ih =>
      rw [List.length_cons, pbwListWeight_cons]
      have hi : 1 ≤ weight i := hpos i
      omega

theorem weight_le_pbwListWeight_of_mem
    {ι : Type u} (weight : ι → ℕ) {i : ι} {word : List ι}
    (hi : i ∈ word) :
    weight i ≤ pbwListWeight weight word := by
  rw [pbwListWeight]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨i, hi, rfl⟩)

theorem pairwise_attach {ι : Type u} {r : ι → ι → Prop}
    {word : List ι} (hword : word.Pairwise r) :
    word.attach.Pairwise (fun i j ↦ r i.1 j.1) := by
  have hmap : (word.attach.map Subtype.val).Pairwise r := by
    simpa using hword
  rwa [List.pairwise_map] at hmap

/-- Replace every letter of a bounded weighted word by the corresponding
letter in the finite weight sublevel. -/
def boundedWeightPBWWordToBoundedPBWWord
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ) :
    BoundedWeightPBWWord weight n →
      BoundedPBWWord (ι := WeightSublevel weight n) n := fun word =>
  ⟨⟨(word.1.1.attach).map (fun i =>
      ⟨i.1, (weight_le_pbwListWeight_of_mem weight i.2).trans word.2⟩), by
        rw [List.pairwise_map]
        exact pairwise_attach word.1.2⟩,
    by
      simpa using (length_le_pbwListWeight_of_pos weight hpos word.1.1).trans
        word.2⟩

theorem boundedWeightPBWWordToBoundedPBWWord_injective
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ) :
    Function.Injective
      (boundedWeightPBWWordToBoundedPBWWord weight hpos n) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  have hlists := congrArg
    (fun w : BoundedPBWWord (ι := WeightSublevel weight n) n =>
      w.1.1.map Subtype.val) huv
  simpa [boundedWeightPBWWordToBoundedPBWWord] using hlists

@[instance_reducible]
noncomputable def fintypeBoundedWeightPBWWord
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ)
    [Fintype (WeightSublevel weight n)] :
    Fintype (BoundedWeightPBWWord weight n) :=
  Fintype.ofInjective
    (boundedWeightPBWWordToBoundedPBWWord weight hpos n)
    (boundedWeightPBWWordToBoundedPBWWord_injective weight hpos n)

/-- Multiplicity vector of a bounded weighted ordered word, restricted to
the finite alphabet that can occur in it. -/
def boundedWeightPBWExponent
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ)
    (word : BoundedWeightPBWWord weight n) :
    WeightSublevel weight n → Fin (n + 1) := fun i =>
  ⟨(word.1.1 : Multiset ι).count i.1, by
    have hcount : (word.1.1 : Multiset ι).count i.1 ≤ word.1.1.length := by
      simpa using Multiset.count_le_card i.1 (word.1.1 : Multiset ι)
    have hlength := length_le_pbwListWeight_of_pos weight hpos word.1.1
    omega⟩

theorem boundedWeightPBWExponent_injective
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ) :
    Function.Injective (boundedWeightPBWExponent weight hpos n) := by
  intro u v huv
  apply Subtype.ext
  apply (pbwWordEquivMultiset (ι := ι)).injective
  apply Multiset.ext.mpr
  intro i
  by_cases hi : weight i ≤ n
  · have hi' := congrFun huv (⟨i, hi⟩ : WeightSublevel weight n)
    simpa [pbwWordEquivMultiset, boundedWeightPBWExponent] using
      congrArg Fin.val hi'
  · have hiu : u.1.1.count i = 0 := by
      rw [List.count_eq_zero]
      intro himem
      exact hi ((weight_le_pbwListWeight_of_mem weight himem).trans u.2)
    have hiv : v.1.1.count i = 0 := by
      rw [List.count_eq_zero]
      intro himem
      exact hi ((weight_le_pbwListWeight_of_mem weight himem).trans v.2)
    simp [pbwWordEquivMultiset, hiu, hiv]

/-- The multiplicity vector records exactly the total word weight. -/
theorem sum_boundedWeightPBWExponent_mul_weight
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ)
    [Fintype (WeightSublevel weight n)]
    (word : BoundedWeightPBWWord weight n) :
    ∑ i : WeightSublevel weight n,
        (boundedWeightPBWExponent weight hpos n word i : ℕ) * weight i.1 =
      pbwListWeight weight word.1.1 := by
  classical
  let s : Multiset ι := word.1.1
  have hs : s.toFinset ⊆ Finset.univ.image
      (fun i : WeightSublevel weight n => i.1) := by
    intro i hi
    have himem : i ∈ word.1.1 := by simpa [s] using hi
    have hiweight := (weight_le_pbwListWeight_of_mem weight himem).trans word.2
    exact Finset.mem_image.mpr ⟨⟨i, hiweight⟩, Finset.mem_univ _, rfl⟩
  have hextra : ∀ i ∈ Finset.univ.image
      (fun i : WeightSublevel weight n => i.1), i ∉ s.toFinset →
      s.count i * weight i = 0 := by
    intro i _hi hi
    have hnot : i ∉ s := by
      simpa only [Multiset.mem_toFinset] using hi
    simp [Multiset.count_eq_zero_of_notMem hnot]
  have hsumSubset :
      ∑ i ∈ s.toFinset, s.count i * weight i =
        ∑ i ∈ Finset.univ.image
          (fun i : WeightSublevel weight n => i.1), s.count i * weight i :=
    Finset.sum_subset hs hextra
  change (∑ i ∈ (Finset.univ : Finset (WeightSublevel weight n)),
      (word.1.1 : Multiset ι).count i.1 * weight i.1) = _
  have himage :
      (∑ i ∈ Finset.univ.image
          (fun i : WeightSublevel weight n ↦ i.1),
          s.count i * weight i) =
        ∑ i : WeightSublevel weight n, s.count i.1 * weight i.1 := by
    rw [Finset.sum_image Subtype.val_injective.injOn]
  dsimp [s] at himage hsumSubset
  rw [← himage]
  rw [← hsumSubset]
  have hweighted := (Finset.sum_multiset_map_count s weight).symm
  simpa [s, pbwListWeight, nsmul_eq_mul] using hweighted

/-- Evaluating a word by a scalar weight factors over its multiplicity
vector. -/
theorem pow_pbwListWeight_eq_prod_exponent
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ)
    [Fintype (WeightSublevel weight n)]
    (t : ℚ) (word : BoundedWeightPBWWord weight n) :
    t ^ pbwListWeight weight word.1.1 =
      ∏ i : WeightSublevel weight n,
        (t ^ weight i.1) ^
          (boundedWeightPBWExponent weight hpos n word i : ℕ) := by
  rw [← sum_boundedWeightPBWExponent_mul_weight weight hpos n word,
    show t ^ (∑ i : WeightSublevel weight n,
        (boundedWeightPBWExponent weight hpos n word i : ℕ) * weight i.1) =
      ∏ i : WeightSublevel weight n,
        t ^ ((boundedWeightPBWExponent weight hpos n word i : ℕ) *
          weight i.1) by
        simpa using (Finset.prod_pow_eq_pow_sum Finset.univ
          (fun i : WeightSublevel weight n ↦
            (boundedWeightPBWExponent weight hpos n word i : ℕ) * weight i.1)
          t).symm]
  apply Finset.prod_congr rfl
  intro i _hi
  calc
    t ^ ((boundedWeightPBWExponent weight hpos n word i : ℕ) * weight i.1) =
        t ^ (weight i.1 *
          (boundedWeightPBWExponent weight hpos n word i : ℕ)) := by
      rw [Nat.mul_comm]
    _ = (t ^ weight i.1) ^
        (boundedWeightPBWExponent weight hpos n word i : ℕ) :=
      pow_mul t (weight i.1)
        (boundedWeightPBWExponent weight hpos n word i : ℕ)

/-- The weighted generating-function bound for bounded ordered words. -/
theorem card_mul_pow_le_prod_geom
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n : ℕ)
    [Fintype (WeightSublevel weight n)]
    [Fintype (BoundedWeightPBWWord weight n)]
    (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Fintype.card (BoundedWeightPBWWord weight n) : ℚ) * t ^ n ≤
      ∏ i : WeightSublevel weight n,
        ∑ e : Fin (n + 1), (t ^ weight i.1) ^ (e : ℕ) := by
  let exponent := boundedWeightPBWExponent weight hpos n
  let mass : (WeightSublevel weight n → Fin (n + 1)) → ℚ :=
    fun f => ∏ i, (t ^ weight i.1) ^ (f i : ℕ)
  calc
    (Fintype.card (BoundedWeightPBWWord weight n) : ℚ) * t ^ n =
        ∑ _word : BoundedWeightPBWWord weight n, t ^ n := by
      simp
    _ ≤ ∑ word : BoundedWeightPBWWord weight n,
        t ^ pbwListWeight weight word.1.1 := by
      apply Finset.sum_le_sum
      intro word _hword
      exact pow_le_pow_of_le_one ht0 ht1 word.2
    _ = ∑ word : BoundedWeightPBWWord weight n, mass (exponent word) := by
      apply Finset.sum_congr rfl
      intro word _hword
      exact pow_pbwListWeight_eq_prod_exponent weight hpos n t word
    _ ≤ ∑ f : WeightSublevel weight n → Fin (n + 1), mass f := by
      have himage :
          (∑ word : BoundedWeightPBWWord weight n, mass (exponent word)) =
            ∑ f ∈ Finset.univ.image exponent, mass f := by
        rw [Finset.sum_image
          (boundedWeightPBWExponent_injective weight hpos n).injOn]
      rw [himage]
      exact Finset.sum_le_univ_sum_of_nonneg fun f => by
        exact Finset.prod_nonneg fun i _ => pow_nonneg (pow_nonneg ht0 _) _
    _ = ∏ i : WeightSublevel weight n,
        ∑ e : Fin (n + 1), (t ^ weight i.1) ^ (e : ℕ) := by
      exact (Fintype.prod_sum fun
        (i : WeightSublevel weight n) (e : Fin (n + 1)) =>
          (t ^ weight i.1) ^ (e : ℕ)).symm

section RationalBounds

/-- The elementary union-bound estimate for a finite product. -/
theorem one_sub_sum_le_prod_one_sub {α : Type*} (s : Finset α)
    (f : α → ℚ) (hf0 : ∀ i ∈ s, 0 ≤ f i)
    (hf1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hi0 := hf0 i (Finset.mem_insert_self i s)
      have hi1 := hf1 i (Finset.mem_insert_self i s)
      have hs0 : 0 ≤ ∑ j ∈ s, f j := Finset.sum_nonneg fun j hj =>
        hf0 j (Finset.mem_insert_of_mem hj)
      have hprod := ih
        (fun j hj => hf0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => hf1 j (Finset.mem_insert_of_mem hj))
      have hfactor : 0 ≤ 1 - f i := sub_nonneg.mpr hi1
      calc
        1 - (f i + ∑ j ∈ s, f j) ≤
            (1 - ∑ j ∈ s, f j) * (1 - f i) := by
          nlinarith
        _ ≤ (∏ j ∈ s, (1 - f j)) * (1 - f i) :=
          mul_le_mul_of_nonneg_right hprod hfactor
        _ = (1 - f i) * ∏ j ∈ s, (1 - f j) := mul_comm _ _

/-- A finite geometric sum with ratio in `[0,1)` is bounded by its infinite
geometric sum. -/
theorem geom_sum_le_inv_one_sub (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (n : ℕ) :
    ∑ e : Fin (n + 1), t ^ (e : ℕ) ≤ (1 - t)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq (ne_of_lt ht1)]
  have hrewrite : (t ^ (n + 1) - 1) / (t - 1) =
      (1 - t ^ (n + 1)) / (1 - t) := by
    rw [show t ^ (n + 1) - 1 = -(1 - t ^ (n + 1)) by ring,
      show t - 1 = -(1 - t) by ring, neg_div_neg_eq]
  rw [hrewrite]
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  rw [div_eq_mul_inv]
  have hpow : 0 ≤ t ^ (n + 1) := pow_nonneg ht0 _
  have hone : 1 - t ^ (n + 1) ≤ 1 := by linarith
  have hinv : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr hden.le
  nlinarith

/-- If a finite collection of numbers in `[0,1]` has sum at most one half,
the product of their geometric denominators is at most two. -/
theorem prod_inv_one_sub_le_two {α : Type*} (s : Finset α)
    (f : α → ℚ) (hf0 : ∀ i ∈ s, 0 ≤ f i)
    (hf1 : ∀ i ∈ s, f i < 1)
    (hsum : ∑ i ∈ s, f i ≤ 1 / 2) :
    ∏ i ∈ s, (1 - f i)⁻¹ ≤ 2 := by
  classical
  have hprod : 1 / 2 ≤ ∏ i ∈ s, (1 - f i) := by
    calc
      1 / 2 ≤ 1 - ∑ i ∈ s, f i := by linarith
      _ ≤ _ := one_sub_sum_le_prod_one_sub s f hf0
        (fun i hi => (hf1 i hi).le)
  have hpositive : 0 < ∏ i ∈ s, (1 - f i) :=
    lt_of_lt_of_le (by norm_num) hprod
  rw [Finset.prod_inv_distrib]
  apply (inv_le_comm₀ hpositive (by norm_num : (0 : ℚ) < 2)).mpr
  nlinarith

/-- A weighted-word generating product is controlled by a fixed finite
low-weight factor and a factor two for a sufficiently small tail. -/
theorem prod_geom_le_fixed_mul_two
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (hpos : ∀ i, 0 < weight i) (n K : ℕ)
    [Fintype (WeightSublevel weight n)]
    [Fintype (WeightSublevel weight K)]
    [Nonempty (WeightSublevel weight K)]
    (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (htail : ∑ i : WeightSublevel weight n,
        (if K < weight i.1 then t ^ weight i.1 else 0) ≤ 1 / 2) :
    (∏ i : WeightSublevel weight n,
        ∑ e : Fin (n + 1), (t ^ weight i.1) ^ (e : ℕ)) ≤
      (∏ i : WeightSublevel weight K, (1 - t ^ weight i.1)⁻¹) * 2 := by
  classical
  let denom : WeightSublevel weight n → ℚ :=
    fun i => (1 - t ^ weight i.1)⁻¹
  let low : Finset (WeightSublevel weight n) :=
    Finset.univ.filter fun i => weight i.1 ≤ K
  let high : Finset (WeightSublevel weight n) :=
    Finset.univ.filter fun i => K < weight i.1
  have htPow0 (i : ι) : 0 ≤ t ^ weight i := pow_nonneg ht0 _
  have htPow1 (i : ι) : t ^ weight i < 1 := by
    exact pow_lt_one₀ ht0 ht1 (hpos i).ne'
  have hgeom : (∏ i : WeightSublevel weight n,
      ∑ e : Fin (n + 1), (t ^ weight i.1) ^ (e : ℕ)) ≤
      ∏ i : WeightSublevel weight n, denom i := by
    apply Finset.prod_le_prod
    · intro i _hi
      exact Finset.sum_nonneg fun e _ => pow_nonneg (pow_nonneg ht0 _) _
    · intro i _hi
      exact geom_sum_le_inv_one_sub (t ^ weight i.1)
        (htPow0 i.1) (htPow1 i.1) n
  have hsplit : (∏ i : WeightSublevel weight n, denom i) =
      (∏ i ∈ low, denom i) * (∏ i ∈ high, denom i) := by
    rw [show high = Finset.univ.filter
        (fun i : WeightSublevel weight n => ¬weight i.1 ≤ K) by
      ext i
      simp [high]]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i : WeightSublevel weight n => weight i.1 ≤ K) denom).symm
  have hlow : (∏ i ∈ low, denom i) ≤
      ∏ i : WeightSublevel weight K, (1 - t ^ weight i.1)⁻¹ := by
    let e : WeightSublevel weight n → WeightSublevel weight K := fun i =>
      if hi : weight i.1 ≤ K then ⟨i.1, hi⟩ else Classical.choice inferInstance
    have hein : Set.InjOn e low := by
      intro i hi j hj hij
      have hiK := (Finset.mem_filter.mp hi).2
      have hjK := (Finset.mem_filter.mp hj).2
      apply Subtype.ext
      calc
        i.1 = (e i).1 := by simp [e, hiK]
        _ = (e j).1 := congrArg Subtype.val hij
        _ = j.1 := by simp [e, hjK]
    have heq : (∏ i ∈ low, denom i) =
        ∏ j ∈ low.image e, (1 - t ^ weight j.1)⁻¹ := by
      rw [Finset.prod_image hein]
      apply Finset.prod_congr rfl
      intro i hi
      have hiK := (Finset.mem_filter.mp hi).2
      simp [e, denom, hiK]
    rw [heq]
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
    · intro i _hi
      exact inv_nonneg.mpr (by
        have := htPow1 i.1
        linarith)
    · intro i _hi _himage
      have hdenPos : 0 < 1 - t ^ weight i.1 :=
        sub_pos.mpr (htPow1 i.1)
      exact (one_le_inv₀ hdenPos).2 (by
        have := htPow0 i.1
        linarith)
  have hhigh : (∏ i ∈ high, denom i) ≤ 2 := by
    apply prod_inv_one_sub_le_two high
      (fun i => t ^ weight i.1)
    · intro i _hi
      exact htPow0 i.1
    · intro i _hi
      exact htPow1 i.1
    · dsimp [high]
      rw [Finset.sum_filter]
      exact htail
  calc
    (∏ i : WeightSublevel weight n,
        ∑ e : Fin (n + 1), (t ^ weight i.1) ^ (e : ℕ)) ≤
        ∏ i : WeightSublevel weight n, denom i := hgeom
    _ = (∏ i ∈ low, denom i) * (∏ i ∈ high, denom i) := hsplit
    _ ≤ (∏ i : WeightSublevel weight K,
        (1 - t ^ weight i.1)⁻¹) * 2 := by
      exact mul_le_mul hlow hhigh
        (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by
          have := htPow1 i.1
          linarith))
        (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by
          have := htPow1 i.1
          linarith))

/-- The tail mass of a weighted alphabet is bounded by the corresponding
sum of its cumulative counting function. -/
theorem weightTail_le_sum_card_sublevel
    {ι : Type u} [LinearOrder ι] (weight : ι → ℕ)
    (n K : ℕ) [Fintype (WeightSublevel weight n)]
    (t : ℚ) (ht0 : 0 ≤ t) :
    (∑ i : WeightSublevel weight n,
        if K < weight i.1 then t ^ weight i.1 else 0) ≤
      ∑ m ∈ Finset.Icc (K + 1) n,
        (Nat.card (WeightSublevel weight m) : ℚ) * t ^ m := by
  classical
  let s : Finset (WeightSublevel weight n) := Finset.univ
  have hmap : ∀ i ∈ s, weight i.1 ∈ Finset.range (n + 1) := by
    intro i _hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le i.2)
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun i : WeightSublevel weight n =>
      if K < weight i.1 then t ^ weight i.1 else 0)]
  dsimp [s]
  have hrhs : (∑ m ∈ Finset.Icc (K + 1) n,
      (Nat.card (WeightSublevel weight m) : ℚ) * t ^ m) =
      ∑ m ∈ Finset.range (n + 1),
        if K < m then (Nat.card (WeightSublevel weight m) : ℚ) * t ^ m
        else 0 := by
    have hsubset : Finset.Icc (K + 1) n ⊆ Finset.range (n + 1) := by
      intro m hm
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_Icc.mp hm).2)
    have hzero : ∀ m ∈ Finset.range (n + 1),
        m ∉ Finset.Icc (K + 1) n →
        (if K < m then
          (Nat.card (WeightSublevel weight m) : ℚ) * t ^ m else 0) = 0 := by
      intro m hmrange hmnot
      have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hmrange)
      have hm : m ≤ K := by
        by_contra h
        exact hmnot (Finset.mem_Icc.mpr ⟨by omega, hmn⟩)
      simp [hm]
    rw [← Finset.sum_subset hsubset hzero]
    apply Finset.sum_congr rfl
    intro m hm
    simp [Nat.lt_of_succ_le (Finset.mem_Icc.mp hm).1]
  rw [hrhs]
  apply Finset.sum_le_sum
  intro m hmrange
  by_cases hmK : K < m
  · simp only [hmK, ite_true]
    have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hmrange)
    let fiber := (Finset.univ : Finset (WeightSublevel weight n)).filter
      (fun i => weight i.1 = m)
    let e : {i // i ∈ fiber} → WeightSublevel weight m := fun i =>
      ⟨i.1.1, by
        have hi := (Finset.mem_filter.mp i.2).2
        simp [hi]⟩
    have he : Function.Injective e := by
      intro i j hij
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x => x.1) hij
    let inc : WeightSublevel weight m → WeightSublevel weight n :=
      fun i => ⟨i.1, i.2.trans hmn⟩
    let _ : Fintype (WeightSublevel weight m) :=
      Fintype.ofInjective inc (fun i j hij => by
        apply Subtype.ext
        exact congrArg (fun x => x.1) hij)
    have hcard : fiber.card ≤ Nat.card (WeightSublevel weight m) := by
      rw [← Fintype.card_coe]
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective e he
    have ht : 0 ≤ t ^ m := pow_nonneg ht0 _
    have hsum : (∑ i : WeightSublevel weight n with weight i.1 = m,
        if K < weight i.1 then t ^ weight i.1 else 0) =
        (fiber.card : ℚ) * t ^ m := by
      change (∑ i ∈ fiber,
        if K < weight i.1 then t ^ weight i.1 else 0) = _
      calc
        _ = ∑ _i ∈ fiber, t ^ m := by
          apply Finset.sum_congr rfl
          intro i hi
          have him := (Finset.mem_filter.mp hi).2
          simp [him, hmK]
        _ = (fiber.card : ℚ) * t ^ m := by simp
    rw [hsum]
    exact
      mul_le_mul_of_nonneg_right (show (fiber.card : ℚ) ≤
        Nat.card (WeightSublevel weight m) by exact_mod_cast hcard) ht
  · simp only [hmK, ite_false]
    have hzero : (∑ i : WeightSublevel weight n with weight i.1 = m,
        if K < weight i.1 then t ^ weight i.1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have him := (Finset.mem_filter.mp hi).2
      simp [him, hmK]
    rw [hzero]

/-- A finite tail of a nonnegative geometric series is bounded by its
infinite-tail value. -/
theorem geom_sum_Icc_le_tail (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (K n : ℕ) :
    ∑ m ∈ Finset.Icc (K + 1) n, x ^ m ≤ x ^ (K + 1) / (1 - x) := by
  by_cases hKn : K + 1 ≤ n
  · rw [show Finset.Icc (K + 1) n = Finset.Ico (K + 1) (n + 1) by
      ext m
      simp]
    have hmul := geom_sum_Ico_mul_neg x
      (show K + 1 ≤ n + 1 by omega)
    have hden : 0 < 1 - x := sub_pos.mpr hx1
    rw [le_div_iff₀ hden]
    rw [hmul]
    exact sub_le_self _ (pow_nonneg hx0 _)
  · have hempty : Finset.Icc (K + 1) n = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    exact div_nonneg (pow_nonneg hx0 _) (sub_nonneg.mpr hx1.le)

/-- An exponential bound for the cumulative alphabet count gives a
uniformly small weighted tail at every finite cutoff. -/
theorem exists_uniform_weightTail_le_half
    {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (weight : ι → ℕ)
    (hfinite : ∀ n, Finite (WeightSublevel weight n))
    (hcount : ∀ r : ℚ, 1 < r → ∃ C : ℚ, 0 < C ∧ ∀ m,
      (Nat.card (WeightSublevel weight m) : ℚ) ≤ C * r ^ m)
    (q : ℚ) (hq : 1 < q) :
    ∃ K : ℕ, Nonempty (WeightSublevel weight K) ∧ ∀ n : ℕ,
      (@Finset.univ (WeightSublevel weight n)
          (@Fintype.ofFinite _ (hfinite n))).sum
        (fun i => if K < weight i.1 then q⁻¹ ^ weight i.1 else 0) ≤ 1 / 2 := by
  let r : ℚ := (q + 1) / 2
  have hr1 : 1 < r := by dsimp [r]; linarith
  have hrq : r < q := by dsimp [r]; linarith
  obtain ⟨C, hC, hcountC⟩ := hcount r hr1
  let x : ℚ := r * q⁻¹
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hx0 : 0 < x := mul_pos (lt_trans (by norm_num) hr1) (inv_pos.mpr hq0)
  have hx1 : x < 1 := by
    dsimp [x]
    rw [← div_eq_mul_inv]
    exact (div_lt_one hq0).mpr hrq
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one
    (show 0 < (1 - x) / (2 * C) by positivity) hx1
  let i₀ : ι := Classical.choice inferInstance
  let K := max K₀ (weight i₀)
  refine ⟨K, ⟨⟨i₀, le_max_right _ _⟩⟩, ?_⟩
  intro n
  let _ : Fintype (WeightSublevel weight n) := Fintype.ofFinite _
  calc
    (∑ i : WeightSublevel weight n,
        if K < weight i.1 then q⁻¹ ^ weight i.1 else 0) ≤
        ∑ m ∈ Finset.Icc (K + 1) n,
          (Nat.card (WeightSublevel weight m) : ℚ) * q⁻¹ ^ m :=
      weightTail_le_sum_card_sublevel weight n K q⁻¹
        (inv_nonneg.mpr hq0.le)
    _ ≤ ∑ m ∈ Finset.Icc (K + 1) n, C * x ^ m := by
      apply Finset.sum_le_sum
      intro m hm
      have hpowq : 0 ≤ q⁻¹ ^ m := pow_nonneg (inv_nonneg.mpr hq0.le) _
      calc
        (Nat.card (WeightSublevel weight m) : ℚ) * q⁻¹ ^ m ≤
            (C * r ^ m) * q⁻¹ ^ m :=
          mul_le_mul_of_nonneg_right (hcountC m) hpowq
        _ = C * x ^ m := by simp [x, mul_pow, mul_assoc]
    _ = C * (∑ m ∈ Finset.Icc (K + 1) n, x ^ m) := by
      rw [Finset.mul_sum]
    _ ≤ C * (x ^ (K + 1) / (1 - x)) :=
      mul_le_mul_of_nonneg_left
        (geom_sum_Icc_le_tail x hx0.le hx1 K n) hC.le
    _ ≤ 1 / 2 := by
      have hpow : x ^ (K + 1) ≤ x ^ K₀ := by
        exact pow_le_pow_of_le_one hx0.le hx1.le (le_trans
          (le_max_left K₀ (weight i₀)) (Nat.le_succ K))
      have hsmall : x ^ (K + 1) < (1 - x) / (2 * C) :=
        lt_of_le_of_lt hpow hK₀
      have hden : 0 < 1 - x := sub_pos.mpr hx1
      have hmul : x ^ (K + 1) * (2 * C) < 1 - x :=
        (lt_div_iff₀ (by positivity : (0 : ℚ) < 2 * C)).mp hsmall
      have hreorder : C * x ^ (K + 1) * 2 < 1 - x := by
        calc
          C * x ^ (K + 1) * 2 = x ^ (K + 1) * (2 * C) := by ring
          _ < 1 - x := hmul
      rw [show C * (x ^ (K + 1) / (1 - x)) =
        (C * x ^ (K + 1)) / (1 - x) by ring]
      rw [div_le_iff₀ hden]
      nlinarith

/-- Smith's weighted PBW counting theorem: if the cumulative number of
letters of weight at most `n` is subexponential, then so is the number of
ordered words of total weight at most `n`. -/
theorem boundedWeightPBWWord_subexponential
    {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (weight : ι → ℕ) (hpos : ∀ i, 0 < weight i)
    (hfinite : ∀ n, Finite (WeightSublevel weight n))
    (hcount : ∀ r : ℚ, 1 < r → ∃ C : ℚ, 0 < C ∧ ∀ m,
      (Nat.card (WeightSublevel weight m) : ℚ) ≤ C * r ^ m) :
    ∀ q : ℚ, 1 < q → ∃ D : ℚ, 0 < D ∧ ∀ n,
      (Nat.card (BoundedWeightPBWWord weight n) : ℚ) ≤ D * q ^ n := by
  intro q hq
  obtain ⟨K, hKnonempty, htail⟩ :=
    exists_uniform_weightTail_le_half weight hfinite hcount q hq
  let _ : Fintype (WeightSublevel weight K) := Fintype.ofFinite _
  let t : ℚ := q⁻¹
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have ht0 : 0 < t := inv_pos.mpr hq0
  have ht1 : t < 1 := by
    dsimp [t]
    exact inv_lt_one_of_one_lt₀ hq
  let D : ℚ :=
    (∏ i : WeightSublevel weight K, (1 - t ^ weight i.1)⁻¹) * 2
  have hD : 0 < D := by
    dsimp [D]
    apply mul_pos
    · apply Finset.prod_pos
      intro i _hi
      exact inv_pos.mpr (sub_pos.mpr
        (pow_lt_one₀ ht0.le ht1 (hpos i.1).ne'))
    · norm_num
  refine ⟨D, hD, ?_⟩
  intro n
  let _ : Fintype (WeightSublevel weight n) := Fintype.ofFinite _
  let _ : Fintype (BoundedWeightPBWWord weight n) :=
    fintypeBoundedWeightPBWWord weight hpos n
  have hgen := card_mul_pow_le_prod_geom weight hpos n t ht0.le ht1.le
  have hprod := prod_geom_le_fixed_mul_two weight hpos n K t ht0.le ht1
    (by simpa [t, inv_pow] using htail n)
  have hmass : (Fintype.card (BoundedWeightPBWWord weight n) : ℚ) * t ^ n ≤
      D := hgen.trans (by simpa [D] using hprod)
  have hqpow : 0 ≤ q ^ n := pow_nonneg hq0.le _
  calc
    (Nat.card (BoundedWeightPBWWord weight n) : ℚ) =
        (Fintype.card (BoundedWeightPBWWord weight n) : ℚ) := by
      rw [Nat.card_eq_fintype_card]
    _ = ((Fintype.card (BoundedWeightPBWWord weight n) : ℚ) * t ^ n) *
        q ^ n := by
      dsimp [t]
      rw [inv_pow]
      field_simp
    _ ≤ D * q ^ n := mul_le_mul_of_nonneg_right hmass hqpow

end RationalBounds

section Enveloping

variable {k : Type*} {L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

/-- The finite family of ordered monomials of bounded weight. -/
def boundedWeightOrderedMonomial
    {ι : Type u} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (n : ℕ) :
    BoundedWeightPBWWord weight n → UniversalEnvelopingAlgebra k L :=
  fun word ↦ orderedMonomial b word.1

theorem orderedMonomialWeightFiltration_eq_span_range
    {ι : Type u} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (n : ℕ) :
    orderedMonomialWeightFiltration b weight n =
      Submodule.span k (Set.range (boundedWeightOrderedMonomial b weight n)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨word, hword, rfl⟩
    exact Submodule.subset_span ⟨⟨word, hword⟩, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨word, rfl⟩
    exact orderedMonomial_mem_weightFiltration b weight word.1 word.2

theorem finiteDimensional_orderedMonomialWeightFiltration
    {ι : Type u} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (n : ℕ)
    [Finite (BoundedWeightPBWWord weight n)] :
    FiniteDimensional k (orderedMonomialWeightFiltration b weight n) := by
  rw [orderedMonomialWeightFiltration_eq_span_range]
  exact Module.Finite.span_of_finite k (Set.toFinite _)

set_option maxHeartbeats 800000 in
-- Elaborating linear independence through the dependent weighted-word subtype is expensive.
/-- PBW linear independence identifies the dimension of a weighted
filtration term with the number of bounded weighted ordered words. -/
theorem finrank_orderedMonomialWeightFiltration
    {ι : Type u} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (n : ℕ)
    [Fintype (BoundedWeightPBWWord weight n)] :
    Module.finrank k (orderedMonomialWeightFiltration b weight n) =
      Fintype.card (BoundedWeightPBWWord weight n) := by
  rw [orderedMonomialWeightFiltration_eq_span_range]
  have hlin : LinearIndependent k
      (boundedWeightOrderedMonomial b weight n) :=
    by
      change LinearIndependent k
        (fun word : BoundedWeightPBWWord weight n ↦ orderedMonomial b word.1)
      exact (orderedMonomial_linearIndependent b).comp
        (fun word : BoundedWeightPBWWord weight n ↦ word.1)
        Subtype.val_injective
  exact finrank_span_eq_card hlin

end Enveloping

end

end UniversalEnvelopingAlgebra
