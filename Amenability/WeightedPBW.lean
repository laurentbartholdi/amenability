/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.UniversalEnvelopingPBW

/-!
# Weighted PBW filtrations

The ordinary PBW normalization decreases word length when it replaces an
inversion by a bracket.  More generally, it preserves any additive weight
for which every basis coordinate of a bracket has weight at most the sum of
the two input weights.  This is the PBW ingredient in Smith's growth theorem.
-/

namespace UniversalEnvelopingAlgebra

noncomputable section

universe u v w

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]

/-- Additive weight of a list of basis indices. -/
def pbwListWeight {ι : Type w} (weight : ι → ℕ) (word : List ι) : ℕ :=
  (word.map weight).sum

@[simp]
theorem pbwListWeight_nil {ι : Type w} (weight : ι → ℕ) :
    pbwListWeight weight [] = 0 := rfl

@[simp]
theorem pbwListWeight_cons {ι : Type w} (weight : ι → ℕ)
    (i : ι) (word : List ι) :
    pbwListWeight weight (i :: word) = weight i + pbwListWeight weight word := by
  simp [pbwListWeight]

theorem pbwListWeight_append {ι : Type w} (weight : ι → ℕ)
    (u v : List ι) :
    pbwListWeight weight (u ++ v) =
      pbwListWeight weight u + pbwListWeight weight v := by
  simp [pbwListWeight, List.sum_append]

theorem pbwListWeight_eq_of_perm {ι : Type w} (weight : ι → ℕ)
    {u v : List ι} (huv : u.Perm v) :
    pbwListWeight weight u = pbwListWeight weight v := by
  exact (huv.map weight).sum_eq

/-- Formal ordered PBW combinations of weight at most `n`. -/
def pbwNormalFormWeightFiltration {ι : Type w} [LinearOrder ι]
    (weight : ι → ℕ) (n : ℕ) : Submodule k (PBWWord ι →₀ k) :=
  Finsupp.supported k k {word | pbwListWeight weight word.1 ≤ n}

theorem pbwNormalFormWeightFiltration_mono
    {ι : Type w} [LinearOrder ι] (weight : ι → ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    pbwNormalFormWeightFiltration (k := k) weight m ≤
      pbwNormalFormWeightFiltration (k := k) weight n :=
  Finsupp.supported_mono fun _ h ↦ h.trans hmn

theorem single_mem_pbwNormalFormWeightFiltration
    {ι : Type w} [LinearOrder ι] (weight : ι → ℕ)
    (word : PBWWord ι) {n : ℕ}
    (hword : pbwListWeight weight word.1 ≤ n) :
    Finsupp.single word (1 : k) ∈
      pbwNormalFormWeightFiltration (k := k) weight n :=
  Finsupp.single_mem_supported k 1 hword

/-- The condition saying that Lie brackets do not increase additive basis
weight. -/
def BracketWeightCompatible {ι : Type w} [LinearOrder ι]
    (b : Module.Basis ι k L) (weight : ι → ℕ) : Prop :=
  ∀ i j l, l ∈ (b.repr ⁅b i, b j⁆).support →
    weight l ≤ weight i + weight j

/-- PBW normalization does not increase a bracket-compatible additive
weight. -/
theorem pbwNormalForm_mem_weightFiltration
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L) (weight : ι → ℕ)
    (hweight : BracketWeightCompatible b weight) (word : List ι) :
    pbwNormalForm b word ∈
      pbwNormalFormWeightFiltration (k := k) weight
        (pbwListWeight weight word) := by
  apply (InvImage.wf pbwWordMeasure Nat.lt_wfRel.wf).induction word
  intro word ih
  by_cases hword : word.Pairwise (· ≤ ·)
  · rw [pbwNormalForm_of_pairwise b hword]
    exact single_mem_pbwNormalFormWeightFiltration weight ⟨word, hword⟩ le_rfl
  · rw [pbwNormalForm_of_not_pairwise b hword]
    let d := chosenAdjacentInversion word hword
    apply Submodule.add_mem
    · have hperm : d.swapped.Perm word := d.swapped_perm
      rw [← pbwListWeight_eq_of_perm weight hperm]
      exact ih d.swapped d.swapped_measure_lt
    · apply Submodule.sum_mem
      intro l hl
      apply Submodule.smul_mem
      have hle : pbwListWeight weight (d.bracketWord l) ≤
          pbwListWeight weight word := by
        have hlweight := hweight d.left d.right l hl
        calc
          pbwListWeight weight (d.bracketWord l) =
              pbwListWeight weight d.pre +
                (weight l + pbwListWeight weight d.suffix) := by
            simp [AdjacentInversion.bracketWord, pbwListWeight_append]
          _ ≤ pbwListWeight weight d.pre +
              (weight d.left +
                (weight d.right + pbwListWeight weight d.suffix)) := by
            omega
          _ = pbwListWeight weight word := by
            conv_rhs => rw [d.word_eq]
            simp [pbwListWeight_append]
      exact pbwNormalFormWeightFiltration_mono weight hle
        (ih (d.bracketWord l) (d.bracketWord_measure_lt l))

/-- The span in the enveloping algebra of ordered PBW monomials of weight at
most `n`. -/
def orderedMonomialWeightFiltration
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (n : ℕ) :
    Submodule k (UniversalEnvelopingAlgebra k L) :=
  Submodule.span k {x | ∃ word : PBWWord ι,
    pbwListWeight weight word.1 ≤ n ∧ orderedMonomial b word = x}

theorem orderedMonomial_mem_weightFiltration
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (word : PBWWord ι) {n : ℕ}
    (hword : pbwListWeight weight word.1 ≤ n) :
    orderedMonomial b word ∈ orderedMonomialWeightFiltration b weight n :=
  Submodule.subset_span ⟨word, hword, rfl⟩

theorem orderedMonomialWeightFiltration_mono
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    orderedMonomialWeightFiltration b weight m ≤
      orderedMonomialWeightFiltration b weight n := by
  apply Submodule.span_mono
  rintro _ ⟨word, hword, rfl⟩
  exact ⟨word, hword.trans hmn, rfl⟩

theorem orderedMonomialLinearCombination_mem_weightFiltration
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) {z : PBWWord ι →₀ k} {n : ℕ}
    (hz : z ∈ pbwNormalFormWeightFiltration (k := k) weight n) :
    orderedMonomialLinearCombination b z ∈
      orderedMonomialWeightFiltration b weight n := by
  rw [pbwNormalFormWeightFiltration,
    Finsupp.supported_eq_span_single] at hz
  refine Submodule.span_induction (p := fun z _ =>
    orderedMonomialLinearCombination b z ∈
      orderedMonomialWeightFiltration b weight n) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨word, hword, rfl⟩
    change pbwListWeight weight word.1 ≤ n at hword
    change (Finsupp.linearCombination k (orderedMonomial b))
      (Finsupp.single word 1) ∈ _
    rw [Finsupp.linearCombination_single, one_smul]
    exact orderedMonomial_mem_weightFiltration b weight word hword
  · simp
  · intro x y _ _ hx hy
    simpa using Submodule.add_mem _ hx hy
  · intro r x _ hx
    simpa using Submodule.smul_mem _ r hx

/-- Straightening an arbitrary PBW monomial preserves its total weight. -/
theorem pbwMonomial_mem_weightFiltration
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (hweight : BracketWeightCompatible b weight)
    (word : List ι) :
    pbwMonomial b word ∈
      orderedMonomialWeightFiltration b weight
        (pbwListWeight weight word) := by
  rw [← orderedMonomialLinearCombination_pbwNormalForm b word]
  exact orderedMonomialLinearCombination_mem_weightFiltration b weight
    (pbwNormalForm_mem_weightFiltration b weight hweight word)

/-- Multiplication adds weighted PBW radii. -/
theorem mul_mem_orderedMonomialWeightFiltration
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) (hweight : BracketWeightCompatible b weight)
    {m n : ℕ} {x y : UniversalEnvelopingAlgebra k L}
    (hx : x ∈ orderedMonomialWeightFiltration b weight m)
    (hy : y ∈ orderedMonomialWeightFiltration b weight n) :
    x * y ∈ orderedMonomialWeightFiltration b weight (m + n) := by
  refine Submodule.span_induction₂
    (p := fun x y _ _ => x * y ∈
      orderedMonomialWeightFiltration b weight (m + n))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    change pbwMonomial b u.1 * pbwMonomial b v.1 ∈ _
    rw [← pbwMonomial_append]
    apply (orderedMonomialWeightFiltration_mono b weight ?_)
      (pbwMonomial_mem_weightFiltration b weight hweight (u.1 ++ v.1))
    rw [pbwListWeight_append]
    exact Nat.add_le_add hu hv
  · simp
  · simp
  · intro x y z _ _ _ hxz hyz
    simpa [add_mul] using Submodule.add_mem _ hxz hyz
  · intro x y z _ _ _ hxy hxz
    simpa [mul_add] using Submodule.add_mem _ hxy hxz
  · intro r x y _ _ hxy
    simpa [smul_mul_assoc] using Submodule.smul_mem _ r hxy
  · intro r x y _ _ hxy
    simpa [mul_smul_comm] using Submodule.smul_mem _ r hxy

/-- The weighted ordered-monomial filtration is exhaustive when all weights
are finite natural numbers. -/
theorem iSup_orderedMonomialWeightFiltration_eq_top
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) :
    ⨆ n : ℕ, orderedMonomialWeightFiltration b weight n = ⊤ := by
  rw [← orderedMonomialSpan_eq_top b]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply Submodule.span_mono
    rintro _ ⟨word, _hword, rfl⟩
    exact ⟨word, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨word, rfl⟩
    exact le_iSup (fun n : ℕ => orderedMonomialWeightFiltration b weight n)
      (pbwListWeight weight word)
      (orderedMonomial_mem_weightFiltration b weight word le_rfl)

/-- The weighted PBW filtration as an increasing sequence. -/
def orderedMonomialWeightFiltrationOrderHom
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ) :
    ℕ →o Submodule k (UniversalEnvelopingAlgebra k L) where
  toFun n := orderedMonomialWeightFiltration b weight n
  monotone' _ _ h := orderedMonomialWeightFiltration_mono b weight h

/-- A finite-dimensional coefficient space is contained in a single
weighted PBW filtration step. -/
theorem exists_le_orderedMonomialWeightFiltration_of_finite
    {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ)
    (P : Submodule k (UniversalEnvelopingAlgebra k L))
    [Module.Finite k P] :
    ∃ d : ℕ, P ≤ orderedMonomialWeightFiltration b weight d := by
  let N : ℕ →o Submodule k (UniversalEnvelopingAlgebra k L) :=
    { toFun := fun n => P ⊓ orderedMonomialWeightFiltration b weight n
      monotone' := fun _ _ hmn => inf_le_inf le_rfl
        (orderedMonomialWeightFiltration_mono b weight hmn) }
  have hsup : iSup N = P := by
    apply le_antisymm
    · exact iSup_le fun _ => inf_le_left
    · intro x hx
      have hxtop : x ∈ ⨆ n : ℕ,
          orderedMonomialWeightFiltration b weight n := by
        rw [iSup_orderedMonomialWeightFiltration_eq_top]
        trivial
      obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_chain
        (orderedMonomialWeightFiltrationOrderHom b weight) x).mp hxtop
      exact le_iSup N n ⟨hx, hn⟩
  have hfg : P.FG := (Submodule.fg_top P).mp Module.Finite.fg_top
  obtain ⟨d, hd⟩ := hfg.stabilizes_of_iSup_eq N hsup
  exact ⟨d, hd.trans_le inf_le_right⟩

end

end UniversalEnvelopingAlgebra
