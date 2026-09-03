/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubexponentialGrowth
import Amenability.AlgebraGrowth
import Amenability.LieGrowth
import Amenability.UniversalEnvelopingGeneration
import Amenability.AscendingFiltrationBasis
import Amenability.WeightedPBWGrowth

/-! # Growth of universal enveloping algebras -/

open Coalgebra Module
namespace HopfAmenability
noncomputable section
universe u v
variable (k : Type u) [Field k]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The index type of the basis adapted to the Lie-growth balls. -/
abbrev LieGrowthBasisIndex {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) :=
  AscendingBasisIndex (k := k) (lieGrowthBall k F)

/-- The exhaustive Lie-ball filtration has a basis graded by first
appearance in the filtration. -/
def lieGrowthBasis {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L)
    (hspan : LieSubalgebra.lieSpan k L (F : Set L) = ⊤) :
    Module.Basis (LieGrowthBasisIndex k F) k L :=
  ascendingFiltrationBasis (k := k) (lieGrowthBall k F)
    (fun _ _ h ↦ lieGrowthBall_mono k F h)
    (by
      change lieGrowthUnion k F = ⊤
      rw [lieGrowthUnion_eq_lieSpan, hspan]
      rfl)

/-- The shifted filtration degree of an adapted Lie-growth basis vector. -/
def lieGrowthBasisWeight {L : Type v} [LieRing L] [LieAlgebra k L]
    {F : Submodule k L} (i : LieGrowthBasisIndex k F) : ℕ :=
  i.1 + 1

theorem lieGrowthBasis_mem_growthBall
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L)
    (hspan : LieSubalgebra.lieSpan k L (F : Set L) = ⊤)
    (i : LieGrowthBasisIndex k F) :
    lieGrowthBasis k F hspan i ∈ lieGrowthBall k F i.1 :=
  ascendingFiltrationBasis_mem (k := k) (lieGrowthBall k F)
    (fun _ _ h ↦ lieGrowthBall_mono k F h)
    (by
      change lieGrowthUnion k F = ⊤
      rw [lieGrowthUnion_eq_lieSpan, hspan]
      rfl) i

/-- Lie brackets are compatible with the shifted degree on the adapted
Lie-growth basis. -/
theorem lieGrowthBasis_bracketWeightCompatible
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L)
    (hspan : LieSubalgebra.lieSpan k L (F : Set L) = ⊤)
    [LinearOrder (LieGrowthBasisIndex k F)] :
    UniversalEnvelopingAlgebra.BracketWeightCompatible
      (lieGrowthBasis k F hspan)
        (lieGrowthBasisWeight (k := k) (F := F)) := by
  intro i j l hl
  let b := lieGrowthBasis k F hspan
  have hbracket : ⁅b i, b j⁆ ∈ lieGrowthBall k F (i.1 + j.1 + 1) :=
    lie_bracket_growthBall k F i.1 j.1 (b i)
      (lieGrowthBasis_mem_growthBall k F hspan i) (b j)
      (lieGrowthBasis_mem_growthBall k F hspan j)
  have hspanbelow : Submodule.span k
      (b '' ascendingBasisBelow (k := k) (lieGrowthBall k F)
        (i.1 + j.1 + 1)) = lieGrowthBall k F (i.1 + j.1 + 1) :=
    span_ascendingBasisBelow_eq (k := k) (lieGrowthBall k F)
      (fun _ _ h ↦ lieGrowthBall_mono k F h)
      (by
        change lieGrowthUnion k F = ⊤
        rw [lieGrowthUnion_eq_lieSpan, hspan]
        rfl) _
  have hsupport := b.repr_support_subset_of_mem_span
    (ascendingBasisBelow (k := k) (lieGrowthBall k F)
      (i.1 + j.1 + 1)) (hspanbelow.symm ▸ hbracket)
  have hlDegree := hsupport hl
  change l.1 + 1 ≤ (i.1 + 1) + (j.1 + 1)
  change l.1 ≤ i.1 + j.1 + 1 at hlDegree
  omega

/-- Forgetting the positive shift sends a bounded weight sublevel into the
corresponding bounded-degree adapted-basis index. -/
def lieGrowthWeightSublevelToBelow
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) (n : ℕ) :
    UniversalEnvelopingAlgebra.WeightSublevel
        (lieGrowthBasisWeight (k := k) (F := F)) n →
      AscendingBasisBelowIndex (k := k) (lieGrowthBall k F) n :=
  fun i ↦ ⟨i.1, by
    have hi := i.2
    change i.1.1 + 1 ≤ n at hi
    omega⟩

theorem lieGrowthWeightSublevelToBelow_injective
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) (n : ℕ) :
    Function.Injective (lieGrowthWeightSublevelToBelow k F n) := by
  intro i j hij
  apply Subtype.ext
  exact congrArg
    (fun z : AscendingBasisBelowIndex (k := k) (lieGrowthBall k F) n ↦ z.1)
    hij

/-- Every bounded sublevel of the shifted Lie-growth weight is finite. -/
@[instance_reducible]
noncomputable def fintypeLieGrowthWeightSublevel
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) [FiniteDimensional k F] (n : ℕ) :
    Fintype (UniversalEnvelopingAlgebra.WeightSublevel
      (lieGrowthBasisWeight (k := k) (F := F)) n) := by
  let hfinite : ∀ r, FiniteDimensional k (lieGrowthBall k F r) :=
    fun r ↦ finiteDimensional_lieGrowthBall k F r
  letI : Fintype (AscendingBasisBelowIndex (k := k)
      (lieGrowthBall k F) n) :=
    fintypeAscendingBasisBelowIndex (k := k) (lieGrowthBall k F) n hfinite
  exact Fintype.ofInjective (lieGrowthWeightSublevelToBelow k F n)
    (lieGrowthWeightSublevelToBelow_injective k F n)

set_option linter.style.haveILetI false in
-- The local finite instances are the chosen instances occurring in the statement.
/-- The number of adapted Lie-basis letters of weight at most `n` is bounded
by the dimension of the `n`th Lie-growth ball. -/
theorem card_lieGrowthWeightSublevel_le
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) [FiniteDimensional k F] (n : ℕ) :
    @Fintype.card
        (UniversalEnvelopingAlgebra.WeightSublevel
          (lieGrowthBasisWeight (k := k) (F := F)) n)
        (fintypeLieGrowthWeightSublevel k F n) ≤
      sfinrank k (lieGrowthBall k F n) := by
  let hfinite : ∀ r, FiniteDimensional k (lieGrowthBall k F r) :=
    fun r ↦ finiteDimensional_lieGrowthBall k F r
  letI : Fintype (UniversalEnvelopingAlgebra.WeightSublevel
      (lieGrowthBasisWeight (k := k) (F := F)) n) :=
    fintypeLieGrowthWeightSublevel k F n
  letI : Fintype (AscendingBasisBelowIndex (k := k)
      (lieGrowthBall k F) n) :=
    fintypeAscendingBasisBelowIndex (k := k) (lieGrowthBall k F) n hfinite
  calc
    Fintype.card (UniversalEnvelopingAlgebra.WeightSublevel
        (lieGrowthBasisWeight (k := k) (F := F)) n) ≤
        Fintype.card (AscendingBasisBelowIndex (k := k)
          (lieGrowthBall k F) n) :=
      Fintype.card_le_of_injective _
        (lieGrowthWeightSublevelToBelow_injective k F n)
    _ = sfinrank k (lieGrowthBall k F n) := by
      exact card_ascendingBasisBelowIndex (k := k) (lieGrowthBall k F)
        (fun _ _ h ↦ lieGrowthBall_mono k F h) n hfinite


set_option linter.style.haveILetI false in
/-- The weighted PBW filtration attached to a subexponential Lie-growth
basis has subexponential dimension. -/
theorem isSubexponentialSequence_lieGrowthPBWFiltration
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) [FiniteDimensional k F]
    (hspan : LieSubalgebra.lieSpan k L (F : Set L) = ⊤)
    (hsub : IsSubexponentialSequence
      (fun n => sfinrank k (lieGrowthBall k F n)))
    [LinearOrder (LieGrowthBasisIndex k F)]
    [Nonempty (LieGrowthBasisIndex k F)] :
    IsSubexponentialSequence (fun n => sfinrank k
      (UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration
        (lieGrowthBasis k F hspan)
        (lieGrowthBasisWeight (k := k) (F := F)) n)) := by
  let weight := lieGrowthBasisWeight (k := k) (F := F)
  let b := lieGrowthBasis k F hspan
  have hfinite : ∀ n,
      Finite (UniversalEnvelopingAlgebra.WeightSublevel weight n) := by
    intro n
    exact @Finite.of_fintype _ (fintypeLieGrowthWeightSublevel k F n)
  have hcount : ∀ r : ℚ, 1 < r → ∃ C : ℚ, 0 < C ∧ ∀ m,
      (Nat.card (UniversalEnvelopingAlgebra.WeightSublevel weight m) : ℚ) ≤
        C * r ^ m := by
    intro r hr
    obtain ⟨C, hC, hball⟩ := hsub r hr
    refine ⟨C, hC, fun m => ?_⟩
    let _ : Fintype (UniversalEnvelopingAlgebra.WeightSublevel weight m) :=
      fintypeLieGrowthWeightSublevel k F m
    calc
      (Nat.card (UniversalEnvelopingAlgebra.WeightSublevel weight m) : ℚ) =
          Fintype.card (UniversalEnvelopingAlgebra.WeightSublevel weight m) := by
        rw [Nat.card_eq_fintype_card]
      _ ≤ sfinrank k (lieGrowthBall k F m) := by
        exact_mod_cast card_lieGrowthWeightSublevel_le k F m
      _ ≤ C * r ^ m := hball m
  have hwords := UniversalEnvelopingAlgebra.boundedWeightPBWWord_subexponential
    weight (fun i => by dsimp [weight, lieGrowthBasisWeight]; omega)
    hfinite hcount
  intro q hq
  obtain ⟨D, hD, hbound⟩ := hwords q hq
  refine ⟨D, hD, fun n => ?_⟩
  letI : Fintype (UniversalEnvelopingAlgebra.WeightSublevel weight n) :=
    fintypeLieGrowthWeightSublevel k F n
  letI : Fintype
      (UniversalEnvelopingAlgebra.BoundedWeightPBWWord weight n) :=
    UniversalEnvelopingAlgebra.fintypeBoundedWeightPBWWord weight
      (fun i => by dsimp [weight, lieGrowthBasisWeight]; omega) n
  letI : FiniteDimensional k
      (UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration b weight n) :=
    UniversalEnvelopingAlgebra.finiteDimensional_orderedMonomialWeightFiltration
      b weight n
  calc
    (sfinrank k
        (UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration
          b weight n) : ℚ) =
        Fintype.card
          (UniversalEnvelopingAlgebra.BoundedWeightPBWWord weight n) := by
      exact_mod_cast
        UniversalEnvelopingAlgebra.finrank_orderedMonomialWeightFiltration
          b weight n
    _ = Nat.card
        (UniversalEnvelopingAlgebra.BoundedWeightPBWWord weight n) := by
      rw [Nat.card_eq_fintype_card]
    _ ≤ D * q ^ n := hbound n

/-- Algebra balls generated inside weighted radius `d` stay inside weighted
radius `d*n`. -/
theorem associativeGrowthBall_le_orderedMonomialWeightFiltration
    {L : Type v} [LieRing L] [LieAlgebra k L]
    {ι : Type*} [LinearOrder ι] (b : Module.Basis ι k L)
    (weight : ι → ℕ)
    (hweight : UniversalEnvelopingAlgebra.BracketWeightCompatible b weight)
    (P : Submodule k (UniversalEnvelopingAlgebra k L)) (d : ℕ)
    (hP : P ≤ UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration
      b weight d) : ∀ n,
    associativeGrowthBall k P n ≤
      UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration
        b weight (d * n) := by
  intro n
  induction n with
  | zero =>
      rw [associativeGrowthBall]
      rw [Submodule.span_singleton_le_iff_mem]
      let word : UniversalEnvelopingAlgebra.PBWWord ι := ⟨[], by simp⟩
      have hword :=
        UniversalEnvelopingAlgebra.orderedMonomial_mem_weightFiltration
          b weight word (n := 0)
            (by
              change UniversalEnvelopingAlgebra.pbwListWeight weight
                ([] : List ι) ≤ 0
              simp [UniversalEnvelopingAlgebra.pbwListWeight])
      simpa [UniversalEnvelopingAlgebra.orderedMonomial,
        UniversalEnvelopingAlgebra.pbwMonomial, word] using hword
  | succ n ih =>
      rw [associativeGrowthBall, sup_le_iff]
      constructor
      · exact ih.trans
          (UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration_mono
            b weight (Nat.mul_le_mul_left d (Nat.le_succ n)))
      · rw [Submodule.mul_le]
        intro x hx y hy
        simpa only [Nat.mul_succ, Nat.add_comm] using
          (UniversalEnvelopingAlgebra.mul_mem_orderedMonomialWeightFiltration
            b weight hweight (hP hx) (ih hy))

set_option linter.style.haveILetI false in
/-- Smith's theorem in the form needed here: genuine subexponential Lie
growth gives subexponential growth of every finite coefficient filtration
in the universal enveloping algebra. -/
theorem hasSubexponentialAlgebraGrowth_uea_of_generatingSubspace
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) [FiniteDimensional k F]
    (hspan : LieSubalgebra.lieSpan k L (F : Set L) = ⊤)
    (hsub : IsSubexponentialSequence
      (fun n => sfinrank k (lieGrowthBall k F n)))
    [LinearOrder (LieGrowthBasisIndex k F)]
    [Nonempty (LieGrowthBasisIndex k F)] :
    HasSubexponentialAlgebraGrowth
      (k := k) (A := UniversalEnvelopingAlgebra k L) := by
  intro P hP
  let _ : FiniteDimensional k P := hP
  let b := lieGrowthBasis k F hspan
  let weight := lieGrowthBasisWeight (k := k) (F := F)
  have hweight : UniversalEnvelopingAlgebra.BracketWeightCompatible b weight :=
    lieGrowthBasis_bracketWeightCompatible k F hspan
  obtain ⟨d, hPd⟩ :=
    UniversalEnvelopingAlgebra.exists_le_orderedMonomialWeightFiltration_of_finite
      b weight P
  have hfiltration := isSubexponentialSequence_lieGrowthPBWFiltration
    k F hspan hsub
  have hscaled := hfiltration.comp_mul
    (fun n => sfinrank k
      (UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration
        b weight n)) d
  intro q hq
  obtain ⟨C, hC, hbound⟩ := hscaled q hq
  refine ⟨C, hC, fun n => ?_⟩
  letI : Fintype
      (UniversalEnvelopingAlgebra.WeightSublevel weight (d * n)) :=
    fintypeLieGrowthWeightSublevel k F (d * n)
  letI : Fintype
      (UniversalEnvelopingAlgebra.BoundedWeightPBWWord weight (d * n)) :=
    UniversalEnvelopingAlgebra.fintypeBoundedWeightPBWWord weight
      (fun i => by dsimp [weight, lieGrowthBasisWeight]; omega) (d * n)
  letI : FiniteDimensional k
      (UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration
        b weight (d * n)) :=
    UniversalEnvelopingAlgebra.finiteDimensional_orderedMonomialWeightFiltration
      b weight (d * n)
  have hle := associativeGrowthBall_le_orderedMonomialWeightFiltration
    k b weight hweight P d hPd n
  have hdim := Submodule.finrank_mono hle
  calc
    (sfinrank k (associativeGrowthBall k P n) : ℚ) ≤
        sfinrank k
          (UniversalEnvelopingAlgebra.orderedMonomialWeightFiltration
            b weight (d * n)) := by
      exact_mod_cast hdim
    _ ≤ C * q ^ n := hbound n

/-- For a unital coefficient space, the recursive associative ball is its submodule power. -/
theorem associativeGrowthBall_eq_pow_of_one_mem
    {A : Type v} [Ring A] [Algebra k A] (P : Submodule k A)
    (h1 : (1 : A) ∈ P) : ∀ n : ℕ, associativeGrowthBall k P n = P ^ n := by
  intro n
  induction n with
  | zero => rw [associativeGrowthBall, Submodule.pow_zero, Submodule.one_eq_span]
  | succ n ih =>
      rw [associativeGrowthBall, ih]
      cases n with
      | zero =>
          rw [Submodule.pow_zero, pow_one, Submodule.mul_one]
          exact sup_eq_right.mpr (by
            rw [Submodule.one_eq_span, Submodule.span_singleton_le_iff_mem]
            exact h1)
      | succ n =>
          apply le_antisymm
          · rw [sup_le_iff]
            exact ⟨fun x hx => by
              rw [Submodule.pow_succ]
              simpa only [mul_one] using Submodule.mul_mem_mul hx h1,
              by rw [← P.pow_succ' (Nat.succ_ne_zero n)]⟩
          · rw [P.pow_succ' (Nat.succ_ne_zero n)]
            exact le_sup_right

/-- The PBW inclusion sends a Lie ball into its associative word space. -/
theorem map_iota_lieGrowthBall_le_generator_pow
    {L : Type v} [LieRing L] [LieAlgebra k L] (F : Submodule k L) : ∀ n : ℕ,
    Submodule.map (UniversalEnvelopingAlgebra.ι k).toLinearMap (lieGrowthBall k F n) ≤
      ueaGeneratorSubspace (k := k) F ^ (n + 1) := by
  intro n
  induction n with
  | zero => rw [lieGrowthBall_zero, pow_one]; exact le_sup_right
  | succ n ih =>
      rw [lieGrowthBall_succ, lieExpansion, Submodule.map_sup, sup_le_iff]
      constructor
      · calc
          Submodule.map (UniversalEnvelopingAlgebra.ι k).toLinearMap
              (lieGrowthBall k F n) ≤
              ueaGeneratorSubspace (k := k) F ^ (n + 1) := ih
          _ ≤ ueaGeneratorSubspace (k := k) F ^ (n + 1 + 1) :=
            ueaGeneratorSubspace_pow_mono_nat F (by omega)
      · rw [lieActionSubspace_eq_map₂, Submodule.map_le_iff_le_comap]
        apply Submodule.map₂_le.2
        intro x hx y hy
        have hz : UniversalEnvelopingAlgebra.ι k ⁅x, y⁆ ∈
            ueaGeneratorSubspace (k := k) F ^ (n + 1 + 1) := by
          rw [LieHom.map_lie]
          apply Submodule.sub_mem
          · rw [(ueaGeneratorSubspace (k := k) F).pow_succ' (by omega : n + 1 ≠ 0)]
            exact Submodule.mul_mem_mul (Submodule.mem_sup_right ⟨x, hx, rfl⟩)
              (ih ⟨y, hy, rfl⟩)
          · rw [Submodule.pow_succ]
            exact Submodule.mul_mem_mul (ih ⟨y, hy, rfl⟩)
              (Submodule.mem_sup_right ⟨x, hx, rfl⟩)
        simpa [Submodule.mem_comap, lieActionBilinear] using hz

/-- Smith's converse comparison for one finite-dimensional generator. -/
theorem isSubexponential_lieGrowth_of_ueaGrowth
    {L : Type v} [LieRing L] [LieAlgebra k L] (F : Submodule k L)
    [FiniteDimensional k F]
    (hU : IsSubexponentialAlgebraGrowthWith (k := k) (ueaGeneratorSubspace (k := k) F)) :
    IsSubexponentialSequence (fun n => sfinrank k (lieGrowthBall k F n)) := by
  have h1 := one_mem_ueaGeneratorSubspace (k := k) F
  intro q hq
  obtain ⟨C, hC, hbound⟩ := hU q hq
  refine ⟨C * q, mul_pos hC (by linarith), fun n => ?_⟩
  let V := ueaGeneratorSubspace (k := k) F
  let _ : FiniteDimensional k V := finiteDimensional_ueaGeneratorSubspace F
  let B := lieGrowthBall k F n
  let T := associativeGrowthBall k V (n + 1)
  let f : B →ₗ[k] T :=
    ((UniversalEnvelopingAlgebra.ι k).toLinearMap.domRestrict B).codRestrict T
      (fun x => by
        dsimp [T, V]
        rw [associativeGrowthBall_eq_pow_of_one_mem k V h1]
        exact map_iota_lieGrowthBall_le_generator_pow k F n ⟨x, x.2, rfl⟩)
  have hf : Function.Injective f := fun x y hxy => by
    apply Subtype.ext
    apply UniversalEnvelopingAlgebra.iota_injective (k := k) (L := L)
    exact congrArg Subtype.val hxy
  let _ : FiniteDimensional k T := by
    dsimp [T]
    exact finiteDimensional_associativeGrowthBall (k := k) V (n + 1)
  have hdim : Module.finrank k B ≤ Module.finrank k T :=
    f.finrank_le_finrank_of_injective hf
  calc
    (sfinrank k (lieGrowthBall k F n) : ℚ) ≤ sfinrank k T := by exact_mod_cast hdim
    _ ≤ C * q ^ (n + 1) := hbound (n + 1)
    _ = (C * q) * q ^ n := by rw [pow_succ]; ring

/-- Smith's fixed-generator equivalence. -/
theorem isSubexponential_lieGrowth_iff_ueaGrowth_of_order
    {L : Type v} [LieRing L] [LieAlgebra k L] (F : Submodule k L)
    [FiniteDimensional k F] (hspan : LieSubalgebra.lieSpan k L (F : Set L) = ⊤)
    [LinearOrder (LieGrowthBasisIndex k F)] [Nonempty (LieGrowthBasisIndex k F)] :
    IsSubexponentialSequence (fun n => sfinrank k (lieGrowthBall k F n)) ↔
      IsSubexponentialAlgebraGrowthWith (k := k) (ueaGeneratorSubspace (k := k) F) := by
  constructor
  · intro h
    exact hasSubexponentialAlgebraGrowth_uea_of_generatingSubspace k F hspan h
      (ueaGeneratorSubspace (k := k) F) (finiteDimensional_ueaGeneratorSubspace F)
  · exact isSubexponential_lieGrowth_of_ueaGrowth k F

/-- Smith's fixed-generator equivalence, with all auxiliary PBW orderings
chosen internally. -/
theorem isSubexponential_lieGrowth_iff_ueaGrowth
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (F : Submodule k L) [FiniteDimensional k F]
    (hspan : LieSubalgebra.lieSpan k L (F : Set L) = ⊤) :
    IsSubexponentialSequence
        (fun n => sfinrank k (lieGrowthBall k F n)) ↔
      IsSubexponentialAlgebraGrowthWith (k := k)
        (ueaGeneratorSubspace (k := k) F) := by
  classical
  let β := LieGrowthBasisIndex k F
  let b := lieGrowthBasis k F hspan
  let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  cases isEmpty_or_nonempty β with
  | inr hnonempty =>
      let _ : Nonempty β := hnonempty
      exact isSubexponential_lieGrowth_iff_ueaGrowth_of_order k F hspan
  | inl hempty =>
      let _ : IsEmpty β := hempty
      let _ : Fintype β := Fintype.ofFinite β
      let _ : FiniteDimensional k L := Module.Finite.of_basis b
      let _ : FiniteDimensional k (UniversalEnvelopingAlgebra k L) := by
        exact Module.Finite.of_basis
          (UniversalEnvelopingAlgebra.orderedMonomialBasis b)
      constructor
      · intro _
        exact hasLocallySubexponentialAlgebraGrowth_of_finiteDimensional
          (k := k) (A := UniversalEnvelopingAlgebra k L)
          (ueaGeneratorSubspace (k := k) F)
            (finiteDimensional_ueaGeneratorSubspace F)
      · exact isSubexponential_lieGrowth_of_ueaGrowth k F

/-- Smith's theorem for a finitely generated Lie algebra: Lie growth is
subexponential exactly when all finite-dimensional coefficient filtrations
of its universal enveloping algebra are subexponential. -/
theorem hasSubexponentialLieGrowth_iff_uea
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (hfg : IsFinitelyGeneratedLieAlgebra (k := k) L) :
    HasSubexponentialLieGrowth k L ↔
      HasLocallySubexponentialAlgebraGrowth
        (k := k) (A := UniversalEnvelopingAlgebra k L) := by
  constructor
  · rintro ⟨F, hF, hspan, hsub⟩
    let _ : FiniteDimensional k F := hF
    let β := LieGrowthBasisIndex k F
    let b := lieGrowthBasis k F hspan
    let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
    cases isEmpty_or_nonempty β with
    | inl hempty =>
        let _ : IsEmpty β := hempty
        let _ : Fintype β := Fintype.ofFinite β
        let _ : FiniteDimensional k L := Module.Finite.of_basis b
        let _ : FiniteDimensional k (UniversalEnvelopingAlgebra k L) := by
          let bU := UniversalEnvelopingAlgebra.orderedMonomialBasis b
          exact Module.Finite.of_basis bU
        exact hasLocallySubexponentialAlgebraGrowth_of_finiteDimensional
          (k := k) (A := UniversalEnvelopingAlgebra k L)
    | inr hnonempty =>
        let _ : Nonempty β := hnonempty
        exact hasSubexponentialAlgebraGrowth_uea_of_generatingSubspace
          k F hspan hsub
  · intro hU
    obtain ⟨s, hs⟩ := hfg
    let F : Submodule k L := Submodule.span k (s : Set L)
    have hF : FiniteDimensional k F :=
      FiniteDimensional.span_of_finite k s.finite_toSet
    refine ⟨F, hF, ?_, ?_⟩
    · apply top_unique
      rw [← hs]
      exact LieSubalgebra.lieSpan_mono Submodule.subset_span
    · exact isSubexponential_lieGrowth_of_ueaGrowth k F
        (hU (ueaGeneratorSubspace (k := k) F)
          (finiteDimensional_ueaGeneratorSubspace F))

end
end HopfAmenability
