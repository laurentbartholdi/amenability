/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.DensityExistence

/-!
# Basic properties of the density filtration

The function `densitySubspace 𝓛 E t` is the unique largest admissible
subspace maximizing

`dim(E ∩ C) - t * dim C`.

This file records the filtration properties that will be used by the
coalgebraic transfer argument.
-/

open Module

namespace UnifiedRounding

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/--
The maximal density score is nonnegative, since the zero subspace is
admissible and has score zero.
-/
theorem densitySubspace_score_nonneg [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ) :
    0 ≤ densityScore E t (densitySubspace 𝓛 E t) := by
  have hmax := densitySubspace_isMaximizer 𝓛 E t
  simpa using hmax.2 (⊥ : Submodule k V) 𝓛.bot_admissible

/--
For `t > 1`, the density subspace is zero.
-/
theorem densitySubspace_eq_bot_of_one_lt [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) {t : ℚ}
    (ht : 1 < t) :
    densitySubspace 𝓛 E t = ⊥ := by
  let C := densitySubspace 𝓛 E t
  by_contra hC
  have hCne : C ≠ (⊥ : Submodule k V) := by
    simpa [C] using hC
  have hdposNat : 0 < finrank k C := by
    have hlt : (⊥ : Submodule k V) < C :=
      bot_lt_iff_ne_bot.mpr hCne
    simpa using Submodule.finrank_strictMono hlt
  have hdpos : (0 : ℚ) < (finrank k C : ℚ) := by
    exact_mod_cast hdposNat
  have hrNat :
      intersectionRank E C ≤ finrank k C := by
    exact Submodule.finrank_mono inf_le_right
  have hr :
      (intersectionRank E C : ℚ) ≤ (finrank k C : ℚ) := by
    exact_mod_cast hrNat
  have hscore :
      0 ≤ densityScore E t C := by
    simpa [C] using densitySubspace_score_nonneg 𝓛 E t
  unfold densityScore at hscore
  nlinarith

/--
Equivalently, a nonzero member of the density filtration can occur only for
parameters `t ≤ 1`.
-/
theorem parameter_le_one_of_densitySubspace_ne_bot [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) {t : ℚ}
    (hC : densitySubspace 𝓛 E t ≠ ⊥) :
    t ≤ 1 := by
  by_contra ht
  push Not at ht
  exact hC (densitySubspace_eq_bot_of_one_lt 𝓛 E ht)

/--
The filtration is decreasing.
-/
theorem densityFiltration_antitone [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) :
    Antitone fun t : ℚ => densitySubspace 𝓛 E t :=
  densitySubspace_antitone 𝓛 E

/--
The pointwise semistability inequality for the density filtration.
-/
theorem densityFiltration_semistable [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V) (E : Submodule k V) (t : ℚ)
    {B : Submodule k V} (hB : 𝓛.admissible B) :
    t * ((finrank k (densitySubspace 𝓛 E t) : ℚ) -
      (finrank k B : ℚ)) ≤
      (intersectionRank E (densitySubspace 𝓛 E t) : ℚ) -
        (intersectionRank E B : ℚ) :=
  densitySubspace_semistable 𝓛 E t hB

/--
If two nested admissible subspaces maximize at the same parameter, the
parameter satisfies the jump-slope identity.
-/
theorem density_jump_identity [FiniteDimensional k V]
    (𝓛 : AdmissibleFamily k V)
    {E : Submodule k V} {t : ℚ} {C D : Submodule k V}
    (hC : IsDensityMaximizer 𝓛 E t C)
    (hD : IsDensityMaximizer 𝓛 E t D) :
    t * ((finrank k C : ℚ) - (finrank k D : ℚ)) =
      (intersectionRank E C : ℚ) - (intersectionRank E D : ℚ) :=
  maximizer_jump_identity hC hD

end UnifiedRounding
