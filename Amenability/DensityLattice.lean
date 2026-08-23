/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubmoduleFinrank
import Mathlib

/-!
# The lattice-theoretic part of unified rounding

This file formalizes the part of the density-filtration argument that only uses
a finite-dimensional lattice of admissible subspaces.

Later, `Subcoalgebra.lean` will instantiate `AdmissibleFamily` with the
subcoalgebras of a fixed finite-dimensional ambient coalgebra.
-/

open Module

namespace UnifiedRounding

universe u v

variable (k : Type u) (V : Type v)
variable [Field k] [AddCommGroup V] [Module k V] --[FiniteDimensional k V]

/--
A family of subspaces closed under `⊥`, sum, and intersection.

For the rounding theorem, the admissible subspaces will be the subcoalgebras
of a fixed finite-dimensional ambient coalgebra.
-/
structure AdmissibleFamily where
  admissible : Submodule k V → Prop
  bot_admissible : admissible ⊥
  sup_admissible :
    ∀ {C D : Submodule k V}, admissible C → admissible D → admissible (C ⊔ D)
  inf_admissible :
    ∀ {C D : Submodule k V}, admissible C → admissible D → admissible (C ⊓ D)

variable {k V}

/-- The rank term `dim(E ∩ C)`. -/
noncomputable def intersectionRank
    (E C : Submodule k V) : ℕ :=
  sfinrank k (E ⊓ C)

/--
The density-filtration score
`dim(E ∩ C) - t * dim(C)`, with values in `ℚ`.
-/
noncomputable def densityScore
    (E : Submodule k V) (t : ℚ) (C : Submodule k V) : ℚ :=
  (intersectionRank E C : ℚ) - t * (finrank k C : ℚ)

/--
The function `C ↦ dim(E ∩ C)` is supermodular.
-/
theorem intersectionRank_supermodular [FiniteDimensional k V]
    (E C D : Submodule k V) :
    intersectionRank E C + intersectionRank E D ≤
      intersectionRank E (C ⊔ D) + intersectionRank E (C ⊓ D) := by
  have hsup :
      (E ⊓ C) ⊔ (E ⊓ D) ≤ E ⊓ (C ⊔ D) := by
    exact sup_le
      (le_inf inf_le_left (inf_le_right.trans le_sup_left))
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))
  have hdim_sup :
      sfinrank k ((E ⊓ C) ⊔ (E ⊓ D)) ≤
        sfinrank k (E ⊓ (C ⊔ D)) :=
    Submodule.finrank_mono hsup
  have hmod :=
    Submodule.finrank_sup_add_finrank_inf_eq (E ⊓ C) (E ⊓ D)
  have hinf :
      (E ⊓ C) ⊓ (E ⊓ D) = E ⊓ (C ⊓ D) := by
    simp [inf_left_comm, inf_comm]
  rw [hinf] at hmod
  simp only [intersectionRank, sfinrank] at *
  omega

/--
The density score is supermodular.
-/
theorem densityScore_supermodular [FiniteDimensional k V]
    (E : Submodule k V) (t : ℚ) (C D : Submodule k V) :
    densityScore E t C + densityScore E t D ≤
      densityScore E t (C ⊔ D) + densityScore E t (C ⊓ D) := by
  have hrNat := intersectionRank_supermodular E C D
  have hr :
      (intersectionRank E C : ℚ) + (intersectionRank E D : ℚ) ≤
        (intersectionRank E (C ⊔ D) : ℚ) +
          (intersectionRank E (C ⊓ D) : ℚ) := by
    exact_mod_cast hrNat
  have hdNat := Submodule.finrank_sup_add_finrank_inf_eq C D
  have hd :
      (sfinrank k (C ⊔ D) : ℚ) + (sfinrank k (C ⊓ D) : ℚ) =
        (finrank k C : ℚ) + (finrank k D : ℚ) := by
    exact_mod_cast hdNat
  calc
    densityScore E t C + densityScore E t D
        = ((intersectionRank E C : ℚ) + (intersectionRank E D : ℚ)) -
            t * ((finrank k C : ℚ) + (finrank k D : ℚ)) := by
          unfold densityScore
          ring
    _ ≤ ((intersectionRank E (C ⊔ D) : ℚ) + (intersectionRank E (C ⊓ D) : ℚ)) -
          t * ((finrank k C : ℚ) + (finrank k D : ℚ)) := by
          nlinarith [hr]
    _ = ((intersectionRank E (C ⊔ D) : ℚ) + (intersectionRank E (C ⊓ D) : ℚ)) -
          t * ((sfinrank k (C ⊔ D) : ℚ) +
            (sfinrank k (C ⊓ D) : ℚ)) := by
          rw [hd]
    _ = densityScore E t (C ⊔ D) + densityScore E t (C ⊓ D) := by
          unfold densityScore
          ring

variable (𝓛 : AdmissibleFamily k V)

/-- `C` maximizes the density score among admissible subspaces. -/
def IsDensityMaximizer
    (E : Submodule k V) (t : ℚ) (C : Submodule k V) : Prop :=
  𝓛.admissible C ∧
    ∀ D : Submodule k V, 𝓛.admissible D →
      densityScore E t D ≤ densityScore E t C

/--
`C` is the largest density-score maximizer.
-/
def IsLargestDensityMaximizer
    (E : Submodule k V) (t : ℚ) (C : Submodule k V) : Prop :=
  IsDensityMaximizer 𝓛 E t C ∧
    ∀ D : Submodule k V, IsDensityMaximizer 𝓛 E t D → D ≤ C

variable {𝓛}

/--
Two density-score maximizers have the same score.
-/
theorem IsDensityMaximizer.score_eq
    {E : Submodule k V} {t : ℚ} {C D : Submodule k V}
    (hC : IsDensityMaximizer 𝓛 E t C)
    (hD : IsDensityMaximizer 𝓛 E t D) :
    densityScore E t C = densityScore E t D := by
  exact le_antisymm (hD.2 C hC.1) (hC.2 D hD.1)

/--
The sum of two maximizers is again a maximizer.

This is the supermodularity step that gives the existence of a unique largest
maximizer once existence of a maximizer is known.
-/
theorem IsDensityMaximizer.sup [FiniteDimensional k V]
    {E : Submodule k V} {t : ℚ} {C D : Submodule k V}
    (hC : IsDensityMaximizer 𝓛 E t C)
    (hD : IsDensityMaximizer 𝓛 E t D) :
    IsDensityMaximizer 𝓛 E t (C ⊔ D) := by
  have hsup_adm := 𝓛.sup_admissible hC.1 hD.1
  have hinf_adm := 𝓛.inf_admissible hC.1 hD.1
  have hCD : densityScore E t C = densityScore E t D :=
    hC.score_eq hD
  have hsuper := densityScore_supermodular E t C D
  have hsup_le := hC.2 (C ⊔ D) hsup_adm
  have hinf_le := hC.2 (C ⊓ D) hinf_adm
  have hC_le_sup :
      densityScore E t C ≤ densityScore E t (C ⊔ D) := by
    linarith
  have hsup_eq :
      densityScore E t (C ⊔ D) = densityScore E t C :=
    le_antisymm hsup_le hC_le_sup
  refine ⟨hsup_adm, ?_⟩
  intro X hX
  calc
    densityScore E t X ≤ densityScore E t C := hC.2 X hX
    _ = densityScore E t (C ⊔ D) := hsup_eq.symm

/--
A density maximizer is semistable with respect to every admissible subspace
contained in it.
-/
theorem IsDensityMaximizer.semistable
    {E : Submodule k V} {t : ℚ} {C B : Submodule k V}
    (hC : IsDensityMaximizer 𝓛 E t C)
    (hB_adm : 𝓛.admissible B) :
    t * ((finrank k C : ℚ) - (finrank k B : ℚ)) ≤
      (intersectionRank E C : ℚ) - (intersectionRank E B : ℚ) := by
  have h := hC.2 B hB_adm
  unfold densityScore at h
  linarith

/--
If `C_s` and `C_t` are largest maximizers and `s < t`, then `C_t ≤ C_s`.
-/
theorem largestDensityMaximizer_antitone [FiniteDimensional k V]
    {E : Submodule k V} {s t : ℚ} {Cs Ct : Submodule k V}
    (hst : s < t)
    (hs : IsLargestDensityMaximizer 𝓛 E s Cs)
    (ht : IsLargestDensityMaximizer 𝓛 E t Ct) :
    Ct ≤ Cs := by
  let I : Submodule k V := Cs ⊓ Ct
  let S : Submodule k V := Cs ⊔ Ct
  have hI_adm : 𝓛.admissible I := by
    exact 𝓛.inf_admissible hs.1.1 ht.1.1
  have hS_adm : 𝓛.admissible S := by
    exact 𝓛.sup_admissible hs.1.1 ht.1.1
  have hsS := hs.1.2 S hS_adm
  have htI := ht.1.2 I hI_adm
  have hrNat := intersectionRank_supermodular E Cs Ct
  have hr :
      (intersectionRank E Cs : ℚ) + (intersectionRank E Ct : ℚ) ≤
        (intersectionRank E S : ℚ) + (intersectionRank E I : ℚ) := by
    simpa [S, I] using (show
      (intersectionRank E Cs : ℚ) + (intersectionRank E Ct : ℚ) ≤
        (intersectionRank E (Cs ⊔ Ct) : ℚ) +
          (intersectionRank E (Cs ⊓ Ct) : ℚ) by
      exact_mod_cast hrNat)
  have hdNat := Submodule.finrank_sup_add_finrank_inf_eq Cs Ct
  have hd :
      (finrank k S : ℚ) + (finrank k I : ℚ) =
        (finrank k Cs : ℚ) + (finrank k Ct : ℚ) := by
    simpa [S, I] using (show
      (sfinrank k (Cs ⊔ Ct) : ℚ) + (sfinrank k (Cs ⊓ Ct) : ℚ) =
        (finrank k Cs : ℚ) + (finrank k Ct : ℚ) by
      exact_mod_cast hdNat)
  have hIleNat : finrank k I ≤ finrank k Ct := by
    exact Submodule.finrank_mono (by
      dsimp [I]
      exact inf_le_right)
  have hIle : (finrank k I : ℚ) ≤ (finrank k Ct : ℚ) := by
    exact_mod_cast hIleNat
  unfold densityScore at hsS htI
  have hdim :
      (finrank k I : ℚ) = (finrank k Ct : ℚ) := by
    apply le_antisymm hIle
    by_contra hlt
    have hlt' : (finrank k I : ℚ) < (finrank k Ct : ℚ) := lt_of_not_ge hlt
    have hsum := add_le_add hsS htI
    have hrank :
        0 ≤ (intersectionRank E S : ℚ) + (intersectionRank E I : ℚ) -
          ((intersectionRank E Cs : ℚ) + (intersectionRank E Ct : ℚ)) := by
      linarith [hr]
    have hdim' :
        (finrank k S : ℚ) + (finrank k I : ℚ) =
          (finrank k Cs : ℚ) + (finrank k Ct : ℚ) := hd
    have hpos :
        0 < (t - s) * ((finrank k Ct : ℚ) - (finrank k I : ℚ)) := by
      exact mul_pos (sub_pos.mpr hst) (sub_pos.mpr hlt')
    nlinarith [hsum, hrank, hdim']
  have hdimNat : finrank k I = finrank k Ct := by
    exact_mod_cast hdim
  have hIeq : I = Ct := by
    apply Submodule.eq_of_le_of_finrank_eq
    · dsimp [I]
      exact inf_le_right
    · exact hdimNat
  rw [← hIeq]
  dsimp [I]
  exact inf_le_left

/--
Largest density maximizers are unique.
-/
theorem largestDensityMaximizer_unique
    {E : Submodule k V} {t : ℚ} {C D : Submodule k V}
    (hC : IsLargestDensityMaximizer 𝓛 E t C)
    (hD : IsLargestDensityMaximizer 𝓛 E t D) :
    C = D := by
  exact le_antisymm (hD.2 C hC.1) (hC.2 D hD.1)

/--
If `D ≤ C` and both are maximizers at the same parameter `t`, then the
parameter is the slope of the jump from `C` to `D`.
-/
theorem maximizer_jump_identity
    {E : Submodule k V} {t : ℚ} {C D : Submodule k V}
--    (hDC : D ≤ C)
    (hC : IsDensityMaximizer 𝓛 E t C)
    (hD : IsDensityMaximizer 𝓛 E t D) :
    t * ((finrank k C : ℚ) - (finrank k D : ℚ)) =
      (intersectionRank E C : ℚ) - (intersectionRank E D : ℚ) := by
  have hscore := hC.score_eq hD
  unfold densityScore at hscore
  linarith

end UnifiedRounding
