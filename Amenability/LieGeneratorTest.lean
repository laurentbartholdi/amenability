/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.LieAmenability
import Amenability.UniversalEnvelopingGeneration

/-!
# The Lie-algebra generator test

This file separates the manuscript definition of Lie amenability from
algebraic amenability of the regular universal-enveloping module.
-/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]

local notation "U" => UniversalEnvelopingAlgebra k L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Algebraic amenability of the left regular universal-enveloping module. -/
def IsAlgebraicallyAmenableLieAlgebra : Prop :=
  HasActionFolnerSubspaces (k := k) (H := U) (M := U)

/-- Lie amenability as defined in the manuscript.  Only finite-dimensional
subspaces of `L` are tested, and the witnesses are finite subcoalgebras of
`U(L)`.  The acting finite subcoalgebra is exactly `k·1 + ι(F)`, so its
action space is `E + F E`. -/
def IsAmenableLieAlgebra : Prop :=
  ∀ (F : Submodule k L), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ C : FiniteSubcoalgebra k U,
        C.carrier ≠ ⊥ ∧
          (sfinrank k (actionExpansion
              (Submodule.map
                (UniversalEnvelopingAlgebra.ι k).toLinearMap F) C.carrier) : ℚ) ≤
            (1 + ε) * finrank k C.carrier

/-- A subspace has a complement inside any containing subspace. -/
theorem exists_relative_complement (E V : Submodule k U) (hEV : E ≤ V) :
    ∃ B : Submodule k U, B ≤ V ∧ E ⊔ B = V ∧ E ⊓ B = ⊥ := by
  let E' : Submodule k V := E.comap V.subtype
  obtain ⟨B', hcompl⟩ := E'.exists_isCompl
  let B : Submodule k U := B'.map V.subtype
  refine ⟨B, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · have hmap := congrArg (Submodule.map V.subtype) hcompl.sup_eq_top
    rw [Submodule.map_sup, Submodule.map_top,
      Submodule.range_subtype, Submodule.map_comap_subtype,
      inf_eq_right.mpr hEV] at hmap
    exact hmap
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hyB, rfl⟩ := hx.2
    have hyE' : y ∈ E' := hx.1
    have hy0 : y ∈ (⊥ : Submodule k V) := by
      rw [← hcompl.inf_eq_bot]
      exact ⟨hyE', hyB⟩
    exact congrArg V.subtype (show y = 0 from hy0)

theorem finrank_relative_complement
    (E V B : Submodule k U)
    [FiniteDimensional k E] [FiniteDimensional k V]
    [FiniteDimensional k B]
    (hsup : E ⊔ B = V) (hinf : E ⊓ B = ⊥) :
    sfinrank k V = sfinrank k E + sfinrank k B := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq E B
  have hzero : Module.finrank k ↑(⊥ : Submodule k U) = 0 := by simp
  rw [hsup, hinf, hzero, add_zero] at hdim
  simpa only [sfinrank] using hdim

theorem submodule_mul_mono {P P' Q Q' : Submodule k U}
    (hP : P ≤ P') (hQ : Q ≤ Q') : P * Q ≤ P' * Q' := by
  apply Submodule.mul_le.2
  intro x hx y hy
  exact Submodule.mul_mem_mul (hP hx) (hQ hy)

/-- The span of the initial space and the first `n` translates of a boundary
complement. -/
def wordBoundarySpan (V E B : Submodule k U) : ℕ → Submodule k U
  | 0 => E
  | n + 1 => wordBoundarySpan V E B n ⊔ V ^ n * B

theorem pow_mul_le_wordBoundarySpan
    (V E B : Submodule k U)
    (hVE : V * E ≤ E ⊔ B) (n : ℕ) :
    V ^ n * E ≤ wordBoundarySpan V E B n := by
  induction n with
  | zero =>
      simp [wordBoundarySpan]
  | succ n ih =>
      rw [Submodule.pow_succ]
      calc
        (V ^ n * V) * E = V ^ n * (V * E) := mul_assoc _ _ _
        _ ≤ V ^ n * (E ⊔ B) := submodule_mul_mono le_rfl hVE
        _ = V ^ n * E ⊔ V ^ n * B := Submodule.mul_sup _ _ _
        _ ≤ wordBoundarySpan V E B n ⊔ V ^ n * B :=
          sup_le_sup_right ih _
        _ = wordBoundarySpan V E B (n + 1) := rfl

theorem finiteDimensional_wordBoundarySpan
    (V E B : Submodule k U)
    [FiniteDimensional k V] [FiniteDimensional k E]
    [FiniteDimensional k B] (n : ℕ) :
    FiniteDimensional k ↑(wordBoundarySpan V E B n) := by
  induction n with
  | zero => simpa [wordBoundarySpan]
  | succ n hn =>
      rw [wordBoundarySpan]
      let _ : FiniteDimensional k ↑(V ^ n) :=
        finiteDimensional_submodule_pow V n
      let _ : FiniteDimensional k ↑(V ^ n * B) :=
        finiteDimensional_mul _ _
      exact Submodule.finiteDimensional_sup _ _

theorem finrank_sup_le_add (P Q : Submodule k U)
    [FiniteDimensional k P] [FiniteDimensional k Q] :
    sfinrank k (P ⊔ Q) ≤ sfinrank k P + sfinrank k Q := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  simp only [sfinrank]
  omega

theorem finrank_wordBoundarySpan_le
    (V E B : Submodule k U)
    [FiniteDimensional k V] [FiniteDimensional k E]
    [FiniteDimensional k B] (n : ℕ) :
    sfinrank k (wordBoundarySpan V E B n) ≤
      sfinrank k E +
        (∑ i ∈ Finset.range n, sfinrank k V ^ i) * sfinrank k B := by
  induction n with
  | zero => simp [wordBoundarySpan]
  | succ n ih =>
      let _ : FiniteDimensional k ↑(wordBoundarySpan V E B n) :=
        finiteDimensional_wordBoundarySpan V E B n
      let _ : FiniteDimensional k ↑(V ^ n) :=
        finiteDimensional_submodule_pow V n
      let _ : FiniteDimensional k ↑(V ^ n * B) :=
        finiteDimensional_mul _ _
      calc
        sfinrank k (wordBoundarySpan V E B (n + 1)) =
            sfinrank k (wordBoundarySpan V E B n ⊔ V ^ n * B) := rfl
        _ ≤ sfinrank k (wordBoundarySpan V E B n) +
            sfinrank k (V ^ n * B) := finrank_sup_le_add _ _
        _ ≤ (sfinrank k E +
              (∑ i ∈ Finset.range n, sfinrank k V ^ i) * sfinrank k B) +
            (sfinrank k V ^ n) * sfinrank k B := by
          gcongr
          exact (finrank_submodule_mul_le (V ^ n) B).trans
            (Nat.mul_le_mul_right _ (finrank_submodule_pow_le V n))
        _ = sfinrank k E +
            (∑ i ∈ Finset.range (n + 1), sfinrank k V ^ i) *
              sfinrank k B := by
          rw [Finset.sum_range_succ]
          ring

/-- The hard direction of the generator test: a Følner subcoalgebra for a
finite Lie-generator space controls every bounded word space in `U(L)`. -/
theorem IsAmenableLieAlgebra.isAlgebraicallyAmenable
    (hL : IsAmenableLieAlgebra (k := k) (L := L)) :
    IsAlgebraicallyAmenableLieAlgebra (k := k) (L := L) := by
  intro P hP ε hε
  let _ : FiniteDimensional k P := hP
  obtain ⟨F, hF, n, hn, hPpow⟩ :=
    exists_ueaGeneratorSubspace_pow_containing P
  let _ : FiniteDimensional k F := hF
  let V := ueaGeneratorSubspace (k := k) F
  let _ : FiniteDimensional k V := finiteDimensional_ueaGeneratorSubspace F
  let S : ℕ := ∑ i ∈ Finset.range n, sfinrank k V ^ i
  have hSpos : 0 < S := by
    have hzero : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
    have hone : 0 < sfinrank k V ^ 0 := by simp
    exact lt_of_lt_of_le hone (Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) hzero)
  let δ : ℚ := ε / (S : ℚ)
  have hδ : 0 < δ := div_pos hε (by exact_mod_cast hSpos)
  obtain ⟨C, hC, hCratio⟩ := hL F hF δ hδ
  let E : Submodule k U := C.carrier
  let _ : FiniteDimensional k E := C.finiteDimensional
  have hVE : E ≤ V * E := by
    intro x hx
    have hm := Submodule.mul_mem_mul (one_mem_ueaGeneratorSubspace F) hx
    simpa using hm
  obtain ⟨B, hBVE, hEB, hEinfB⟩ := exists_relative_complement E (V * E) hVE
  let _ : FiniteDimensional k (V * E) := finiteDimensional_mul V E
  let _ : FiniteDimensional k B :=
    FiniteDimensional.of_injective (Submodule.inclusion hBVE)
      (Submodule.inclusion_injective hBVE)
  have hdimVE : sfinrank k (V * E) = sfinrank k E + sfinrank k B :=
    finrank_relative_complement E (V * E) B hEB hEinfB
  have hratioVE : (sfinrank k (V * E) : ℚ) ≤
      (1 + δ) * sfinrank k E := by
    have hVeq : V =
        (Submodule.map (UniversalEnvelopingAlgebra.ι k).toLinearMap F) ⊔
          (unitFiniteSubcoalgebra (k := k) (H := U)).carrier := by
      dsimp [V, ueaGeneratorSubspace]
      rw [sup_comm]
      rfl
    rw [← actionSubspace_regular_eq_mul, hVeq,
      actionSubspace_sup_unit_eq_actionExpansion]
    exact hCratio
  have hBbound : (sfinrank k B : ℚ) ≤ δ * sfinrank k E := by
    rw [hdimVE] at hratioVE
    push_cast at hratioVE
    linarith
  let W := wordBoundarySpan V E B n
  let _ : FiniteDimensional k W := finiteDimensional_wordBoundarySpan V E B n
  have hPE : actionExpansion P E ≤ W := by
    apply sup_le
    · have hE0 : E ≤ V ^ n * E := by
        intro x hx
        have hone0 : (1 : U) ∈ V ^ 0 := by
          rw [Submodule.pow_zero]
          exact Submodule.mem_one.mpr ⟨1, map_one (algebraMap k U)⟩
        have hone : (1 : U) ∈ V ^ n :=
          ueaGeneratorSubspace_pow_mono_nat F (Nat.zero_le n) hone0
        have hm := Submodule.mul_mem_mul hone hx
        simpa using hm
      exact hE0.trans (pow_mul_le_wordBoundarySpan V E B
        (by rw [hEB]) n)
    · rw [actionSubspace_regular_eq_mul]
      exact (submodule_mul_mono hPpow le_rfl).trans
        (pow_mul_le_wordBoundarySpan V E B
          (by rw [hEB]) n)
  refine ⟨E, hC, inferInstance, ?_⟩
  have hdim := Submodule.finrank_mono hPE
  have hWbound := finrank_wordBoundarySpan_le V E B n
  have hSE : (S : ℚ) * sfinrank k B ≤ ε * sfinrank k E := by
    calc
      (S : ℚ) * sfinrank k B ≤ (S : ℚ) * (δ * sfinrank k E) :=
        mul_le_mul_of_nonneg_left hBbound (by positivity)
      _ = ε * sfinrank k E := by
        change (S : ℚ) * ((ε / (S : ℚ)) * sfinrank k E) = _
        field_simp
  calc
    (sfinrank k (actionExpansion P E) : ℚ) ≤ sfinrank k W := by
      exact_mod_cast hdim
    _ ≤ sfinrank k E + S * sfinrank k B := by exact_mod_cast hWbound
    _ ≤ sfinrank k E + ε * sfinrank k E := by
      simpa only [add_comm] using add_le_add_left hSE (sfinrank k E : ℚ)
    _ = (1 + ε) * sfinrank k E := by ring

/-- Algebraic amenability immediately implies manuscript Lie amenability by
rounding and restricting the acting test space to `k·1 + ι(F)`. -/
theorem IsAlgebraicallyAmenableLieAlgebra.isAmenableLieAlgebra
    (hL : IsAlgebraicallyAmenableLieAlgebra (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  have hcoal : IsAmenableHopfModuleCoalgebra (k := k) (H := U) (M := U) :=
    HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra hL
  rw [IsAmenableLieAlgebra]
  intro F hF
  let _ : FiniteDimensional k F := hF
  intro ε hε
  exact hcoal
    (Submodule.map (UniversalEnvelopingAlgebra.ι k).toLinearMap F)
    (by infer_instance) ε hε

/-- **Generator test.** Manuscript Lie amenability is equivalent to algebraic
amenability of the regular universal-enveloping module. -/
theorem isAmenableLieAlgebra_iff_algebraicallyAmenable :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAlgebraicallyAmenableLieAlgebra (k := k) (L := L) :=
  ⟨IsAmenableLieAlgebra.isAlgebraicallyAmenable,
    IsAlgebraicallyAmenableLieAlgebra.isAmenableLieAlgebra⟩

/-- Compatibility name emphasizing the regular-action Følner formulation. -/
theorem isAmenableLieAlgebra_iff_regularActionFolner :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      HasActionFolnerSubspaces (k := k) (H := U) (M := U) :=
  isAmenableLieAlgebra_iff_algebraicallyAmenable

end

end HopfAmenability
