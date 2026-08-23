/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.DensityFiltration

/-!
# From the transfer inequality to density-filtration functoriality

This file isolates the lattice-theoretic step in the rounding argument.

Suppose `D` is the largest density maximizer for `E` at parameter `t`.
Let `C` be another admissible subspace and let `U ≤ E ∩ C`. If the
transfer inequality
```
t (dim C - dim (C ∩ D))
  ≤ dim U - dim (U ∩ (C ∩ D))
```
holds, then `C ≤ D`.

The proof is independent of coalgebras. The transfer inequality first
implies that the density score of `C` is at least the score of `C ∩ D`.
Supermodularity then forces `C ⊔ D` to be another maximizer, and the
largest-maximizer property gives `C ≤ D`.
-/

open Module

namespace UnifiedRounding

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/--
If `U ≤ E ∩ C` and `B ≤ C`, then the codimension of `U ∩ B` in `U`
is at most the codimension of `E ∩ B` in `E ∩ C`.

This is the elementary dimension comparison used to pass from the
transferred estimate on `U` to an estimate for the density score.
-/
theorem finrank_sub_inf_le_intersectionRank_sub
    {E U B C : Submodule k V}
    (hUE : U ≤ E)
    (hUC : U ≤ C)
    (hBC : B ≤ C) :
    (finrank k U : ℚ) -
        (sfinrank k (U ⊓ B) : ℚ) ≤
      (intersectionRank E C : ℚ) -
        (intersectionRank E B : ℚ) := by
  let X : Submodule k V := E ⊓ C
  let Y : Submodule k V := E ⊓ B
  have hUX : U ≤ X := le_inf hUE hUC
  have hYX : Y ≤ X := by
    exact le_inf inf_le_left (inf_le_right.trans hBC)
  have hsup : U ⊔ Y ≤ X := sup_le hUX hYX
  have hsupNat :
      sfinrank k (U ⊔ Y) ≤ finrank k X :=
    Submodule.finrank_mono hsup
  have hsupQ :
      (sfinrank k (U ⊔ Y) : ℚ) ≤
        (finrank k X : ℚ) := by
    exact_mod_cast hsupNat
  have hmodNat :=
    Submodule.finrank_sup_add_finrank_inf_eq U Y
  have hmodQ :
      (sfinrank k (U ⊔ Y) : ℚ) +
          (sfinrank k (U ⊓ Y) : ℚ) =
        (finrank k U : ℚ) + (finrank k Y : ℚ) := by
    exact_mod_cast hmodNat
  have hUY :
      U ⊓ Y = U ⊓ B := by
    apply le_antisymm
    · exact inf_le_inf_left U inf_le_right
    · refine le_inf inf_le_left ?_
      exact le_inf (inf_le_left.trans hUE) inf_le_right
  change
    (finrank k U : ℚ) -
        (sfinrank k (U ⊓ B) : ℚ) ≤
      (finrank k X : ℚ) - (finrank k Y : ℚ)
  rw [← hUY]
  linarith

/--
The transfer estimate against the intersection with a largest density
maximizer forces containment in that maximizer.
-/
theorem le_of_transfer_to_largestDensityMaximizer
    (𝓛 : AdmissibleFamily k V)
    {E U C D : Submodule k V}
    {t : ℚ}
    (hD : IsLargestDensityMaximizer 𝓛 E t D)
    (hC : 𝓛.admissible C)
    (hUE : U ≤ E)
    (hUC : U ≤ C)
    (htransfer :
      t * ((finrank k C : ℚ) -
        (sfinrank k (C ⊓ D) : ℚ)) ≤
      (finrank k U : ℚ) -
        (sfinrank k (U ⊓ (C ⊓ D)) : ℚ)) :
    C ≤ D := by
  let B : Submodule k V := C ⊓ D
  have hB : 𝓛.admissible B := by
    exact 𝓛.inf_admissible hC hD.1.1
  have hcodim :
      (finrank k U : ℚ) -
          (sfinrank k (U ⊓ B) : ℚ) ≤
        (intersectionRank E C : ℚ) -
          (intersectionRank E B : ℚ) := by
    exact finrank_sub_inf_le_intersectionRank_sub
      hUE hUC inf_le_left
  have hscoreBC :
      densityScore E t B ≤ densityScore E t C := by
    have ht :
        t * ((finrank k C : ℚ) - (finrank k B : ℚ)) ≤
          (intersectionRank E C : ℚ) -
            (intersectionRank E B : ℚ) := by
      dsimp [B] at htransfer ⊢
      linarith
    unfold densityScore
    linarith
  have hsupAdm : 𝓛.admissible (D ⊔ C) :=
    𝓛.sup_admissible hD.1.1 hC
  have hsuper :=
    densityScore_supermodular E t D C
  have hinf :
      D ⊓ C = B := by
    simp [B, inf_comm]
  rw [hinf] at hsuper
  have hDleSup :
      densityScore E t D ≤ densityScore E t (D ⊔ C) := by
    linarith
  have hSupLeD :
      densityScore E t (D ⊔ C) ≤ densityScore E t D :=
    hD.1.2 (D ⊔ C) hsupAdm
  have hscoreSup :
      densityScore E t (D ⊔ C) = densityScore E t D :=
    le_antisymm hSupLeD hDleSup
  have hSupMax :
      IsDensityMaximizer 𝓛 E t (D ⊔ C) := by
    refine ⟨hsupAdm, ?_⟩
    intro Z hZ
    calc
      densityScore E t Z ≤ densityScore E t D :=
        hD.1.2 Z hZ
      _ = densityScore E t (D ⊔ C) :=
        hscoreSup.symm
  have hSupLe : D ⊔ C ≤ D :=
    hD.2 (D ⊔ C) hSupMax
  exact le_sup_right.trans hSupLe

/--
A convenient form with the canonical `densitySubspace` as target.
-/
theorem le_densitySubspace_of_transfer
    (𝓛 : AdmissibleFamily k V)
    {E U C : Submodule k V}
    (t : ℚ)
    (hC : 𝓛.admissible C)
    (hUE : U ≤ E)
    (hUC : U ≤ C)
    (htransfer :
      t * ((finrank k C : ℚ) -
        (finrank k
          (C ⊓ densitySubspace 𝓛 E t : Submodule k V) : ℚ)) ≤
      (finrank k U : ℚ) -
        (finrank k
          (U ⊓ (C ⊓ densitySubspace 𝓛 E t) :
            Submodule k V) : ℚ)) :
    C ≤ densitySubspace 𝓛 E t := by
  exact le_of_transfer_to_largestDensityMaximizer
    𝓛
    (densitySubspace_isLargestMaximizer 𝓛 E t)
    hC hUE hUC htransfer

end UnifiedRounding
