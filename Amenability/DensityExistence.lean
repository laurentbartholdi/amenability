/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.DensityLattice

/-!
# Existence of the density filtration

Although a finite-dimensional vector space over an infinite field has infinitely
many subspaces, the density score only depends on the finite pair

`(dim(E ∩ C), dim C)`.

This file maximizes over those finitely many possible numerical profiles, and
then chooses, among all score maximizers, one of maximal dimension.  Closure
under sums implies that this maximizer is the unique largest maximizer.
-/

open Module

namespace HopfAmenability

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/--
A finite set containing the density score of every subspace of `V`.
-/
noncomputable def possibleDensityScores
    (E : Submodule k V) (t : ℚ) : Finset ℚ := by
  classical
  exact
    ((Finset.range (finrank k E + 1)).product
      (Finset.range (finrank k V + 1))).image
      (fun p : ℕ × ℕ => (p.1 : ℚ) - t * (p.2 : ℚ))

theorem densityScore_mem_possibleDensityScores [FiniteDimensional k V]
    (E : Submodule k V) (t : ℚ) (C : Submodule k V) :
    densityScore E t C ∈ possibleDensityScores E t := by
  classical
  unfold possibleDensityScores
  rw [Finset.mem_image]
  refine ⟨(intersectionRank E C, finrank k C), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨
    by
      rw [Finset.mem_range]
      unfold intersectionRank
      simpa [Nat.succ_eq_add_one] using
        (Nat.lt_succ_of_le (Submodule.finrank_mono inf_le_left)),
    by
      rw [Finset.mem_range]
      simpa [Nat.succ_eq_add_one] using
        (Nat.lt_succ_of_le (Submodule.finrank_le C))
  ⟩

/--
The finite set of scores actually realized by admissible subspaces.
-/
noncomputable def realizedDensityScores
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) : Finset ℚ := by
  classical
  exact (possibleDensityScores E t).filter fun q =>
    ∃ C : Submodule k V,
      𝓛.admissible C ∧ densityScore E t C = q

@[simp]
theorem densityScore_bot
    (E : Submodule k V) (t : ℚ) :
    densityScore E t (⊥ : Submodule k V) = 0 := by
  simp [densityScore, intersectionRank]

theorem realizedDensityScores_nonempty [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    (realizedDensityScores 𝓛 E t).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp only [realizedDensityScores, Finset.mem_filter]
  constructor
  · simpa using densityScore_mem_possibleDensityScores E t (⊥ : Submodule k V)
  · exact ⟨⊥, 𝓛.bot_admissible, densityScore_bot E t⟩

/--
The largest density score realized by an admissible subspace.
-/
noncomputable def maximalDensityScore [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) : ℚ :=
  (realizedDensityScores 𝓛 E t).max'
    (realizedDensityScores_nonempty 𝓛 E t)

theorem maximalDensityScore_mem
    [FiniteDimensional k V] (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    maximalDensityScore 𝓛 E t ∈ realizedDensityScores 𝓛 E t := by
  exact Finset.max'_mem _ _

theorem densityScore_le_maximalDensityScore [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ)
    {C : Submodule k V} (hC : 𝓛.admissible C) :
    densityScore E t C ≤ maximalDensityScore 𝓛 E t := by
  classical
  have hmem :
      densityScore E t C ∈ realizedDensityScores 𝓛 E t := by
    simp only [realizedDensityScores, Finset.mem_filter]
    exact ⟨densityScore_mem_possibleDensityScores E t C,
      ⟨C, hC, rfl⟩⟩
  exact Finset.le_max' _ _ hmem

theorem maximalDensityScore_realized [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    ∃ C : Submodule k V,
      𝓛.admissible C ∧
      densityScore E t C = maximalDensityScore 𝓛 E t := by
  classical
  have hmem := maximalDensityScore_mem 𝓛 E t
  simp only [realizedDensityScores, Finset.mem_filter] at hmem
  exact hmem.2

/--
The finite set of dimensions of admissible subspaces realizing the maximal
density score.
-/
noncomputable def maximalDensityDimensions [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) : Finset ℕ := by
  classical
  exact (Finset.range (finrank k V + 1)).filter fun d =>
    ∃ C : Submodule k V,
      𝓛.admissible C ∧
      densityScore E t C = maximalDensityScore 𝓛 E t ∧
      finrank k C = d

theorem maximalDensityDimensions_nonempty [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    (maximalDensityDimensions 𝓛 E t).Nonempty := by
  classical
  obtain ⟨C, hC, hscore⟩ := maximalDensityScore_realized 𝓛 E t
  refine ⟨finrank k C, ?_⟩
  simp only [maximalDensityDimensions, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.lt_succ_of_le (Submodule.finrank_le C), ?_⟩
  exact ⟨C, hC, hscore, rfl⟩

/--
The largest dimension among density-score maximizers.
-/
noncomputable def maximalDensityDimension [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) : ℕ :=
  (maximalDensityDimensions 𝓛 E t).max'
    (maximalDensityDimensions_nonempty 𝓛 E t)

theorem maximalDensityDimension_mem [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    maximalDensityDimension 𝓛 E t ∈ maximalDensityDimensions 𝓛 E t := by
  exact Finset.max'_mem _ _

theorem maximalDensityDimension_realized [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    ∃ C : Submodule k V,
      𝓛.admissible C ∧
      densityScore E t C = maximalDensityScore 𝓛 E t ∧
      finrank k C = maximalDensityDimension 𝓛 E t := by
  classical
  have hmem := maximalDensityDimension_mem 𝓛 E t
  simp only [maximalDensityDimensions, Finset.mem_filter] at hmem
  exact hmem.2

/--
The chosen largest density maximizer.
-/
noncomputable def densitySubspace [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    Submodule k V :=
  Classical.choose (maximalDensityDimension_realized 𝓛 E t)

theorem densitySubspace_admissible [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    𝓛.admissible (densitySubspace 𝓛 E t) := by
  exact (Classical.choose_spec
    (maximalDensityDimension_realized 𝓛 E t)).1

theorem densitySubspace_score [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    densityScore E t (densitySubspace 𝓛 E t) =
      maximalDensityScore 𝓛 E t := by
  exact (Classical.choose_spec
    (maximalDensityDimension_realized 𝓛 E t)).2.1

theorem densitySubspace_finrank [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    finrank k (densitySubspace 𝓛 E t) =
      maximalDensityDimension 𝓛 E t := by
  exact (Classical.choose_spec
    (maximalDensityDimension_realized 𝓛 E t)).2.2

theorem densitySubspace_isMaximizer [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    IsDensityMaximizer 𝓛 E t (densitySubspace 𝓛 E t) := by
  refine ⟨densitySubspace_admissible 𝓛 E t, ?_⟩
  intro D hD
  calc
    densityScore E t D ≤ maximalDensityScore 𝓛 E t :=
      densityScore_le_maximalDensityScore 𝓛 E t hD
    _ = densityScore E t (densitySubspace 𝓛 E t) :=
      (densitySubspace_score 𝓛 E t).symm

theorem finrank_le_maximalDensityDimension [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ)
    {C : Submodule k V}
    (hC : IsDensityMaximizer 𝓛 E t C) :
    finrank k C ≤ maximalDensityDimension 𝓛 E t := by
  classical
  have hscore :
      densityScore E t C = maximalDensityScore 𝓛 E t := by
    apply le_antisymm
    · exact densityScore_le_maximalDensityScore 𝓛 E t hC.1
    · rw [← densitySubspace_score 𝓛 E t]
      exact hC.2 (densitySubspace 𝓛 E t)
        (densitySubspace_admissible 𝓛 E t)
  have hmem :
      finrank k C ∈ maximalDensityDimensions 𝓛 E t := by
    simp only [maximalDensityDimensions, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Submodule.finrank_le C),
      ⟨C, hC.1, hscore, rfl⟩⟩
  exact Finset.le_max' _ _ hmem

/--
The chosen `densitySubspace` is the unique largest density-score maximizer.
-/
theorem densitySubspace_isLargestMaximizer [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    IsLargestDensityMaximizer 𝓛 E t (densitySubspace 𝓛 E t) := by
  have hC := densitySubspace_isMaximizer 𝓛 E t
  refine ⟨hC, ?_⟩
  intro D hD
  have hsup : IsDensityMaximizer 𝓛 E t
      (densitySubspace 𝓛 E t ⊔ D) :=
    hC.sup hD
  have hdim :
      sfinrank k (densitySubspace 𝓛 E t ⊔ D) ≤
        finrank k (densitySubspace 𝓛 E t) := by
    calc
      sfinrank k (densitySubspace 𝓛 E t ⊔ D)
          ≤ maximalDensityDimension 𝓛 E t :=
            finrank_le_maximalDensityDimension 𝓛 E t hsup
      _ = finrank k (densitySubspace 𝓛 E t) :=
            (densitySubspace_finrank 𝓛 E t).symm
  have heq :
      densitySubspace 𝓛 E t =
        densitySubspace 𝓛 E t ⊔ D := by
    exact Submodule.eq_of_le_of_finrank_le le_sup_left hdim
  calc
    D ≤ densitySubspace 𝓛 E t ⊔ D := le_sup_right
    _ = densitySubspace 𝓛 E t := heq.symm

/--
The density filtration is decreasing in the parameter.
-/
theorem densitySubspace_antitone [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) :
    Antitone fun t : ℚ => densitySubspace 𝓛 E t := by
  intro s t hst
  rcases hst.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact largestDensityMaximizer_antitone hlt
      (densitySubspace_isLargestMaximizer 𝓛 E s)
      (densitySubspace_isLargestMaximizer 𝓛 E t)

/--
The chosen density subspace satisfies the semistability inequality.
-/
theorem densitySubspace_semistable [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ)
    {B : Submodule k V} (hB : 𝓛.admissible B) :
    t * ((finrank k (densitySubspace 𝓛 E t) : ℚ) -
      (finrank k B : ℚ)) ≤
      (intersectionRank E (densitySubspace 𝓛 E t) : ℚ) -
        (intersectionRank E B : ℚ) := by
  exact (densitySubspace_isMaximizer 𝓛 E t).semistable hB

end HopfAmenability
