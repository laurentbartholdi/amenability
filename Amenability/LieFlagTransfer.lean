/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.LieCodimOneTransfer
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Transfer along finite-dimensional flags of Lie subspaces
-/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {L : Type v} {M : Type w}
variable [Field k]
variable [LieRing L] [LieAlgebra k L]
variable [AddCommGroup M] [Module k M]
variable [LieRingModule L M] [LieModule k L M]
variable [Coalgebra k M] [Coalgebra.IsLieModuleCoalgebra k L M]

/-- Every nonzero finite-dimensional Lie subspace contains a
codimension-one subspace. -/
theorem exists_lieSubspace_finrank_add_one
    (F : Submodule k L) [FiniteDimensional k F] (hF : F ≠ ⊥) :
    ∃ F' : Submodule k L,
      F' ≤ F ∧ sfinrank k F = sfinrank k F' + 1 := by
  let : Nontrivial F := Submodule.nontrivial_iff_ne_bot.mpr hF
  obtain ⟨x : F, hx⟩ := exists_ne (0 : F)
  obtain ⟨ell : Module.Dual k F, hell⟩ :=
    Module.Projective.exists_dual_eq_one k hx
  let P : Submodule k F := LinearMap.ker ell
  let F' : Submodule k L := ambientImage F P
  refine ⟨F', ?_, ?_⟩
  · rintro y ⟨z, -, rfl⟩
    exact z.2
  · have hnell : ell ≠ 0 := by
      intro hzero
      have : ell x = 0 := by rw [hzero]; rfl
      rw [hell] at this
      exact one_ne_zero this
    have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hnell
    change finrank k F = finrank k F' + 1
    rw [show finrank k F' = finrank k P by
      exact finrank_ambientImage F P]
    exact hdim.symm

theorem ambientImage_lieStepDenominator
    (F' F : Submodule k L) [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (D : Submodule k M) (hDle : D ≤ lieExpansion F C.carrier) :
    ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
        (lieStepDenominator F' F C
          (D.comap (lieExpansionFiniteSubcoalgebra F C).carrier.subtype)) =
      D ⊔ lieExpansion F' C.carrier := by
  have hDimage :
      ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
          (D.comap (lieExpansionFiniteSubcoalgebra F C).carrier.subtype) = D :=
    ambientImage_comap_eq_of_le _ D hDle
  rw [lieStepDenominator, ambientImage_sup,
    hDimage,
    ambientImage_lieLowerExpansionSubspace F' F hFF C]

theorem ambientImage_lieStepUNumerator
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k M) (hDle : D ≤ lieExpansion F C.carrier) :
    ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
        (lieStepUNumerator F C U
          (D.comap (lieExpansionFiniteSubcoalgebra F C).carrier.subtype)) =
      D ⊔ lieExpansion F (ambientImage C.carrier U) := by
  have hDimage :
      ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
          (D.comap (lieExpansionFiniteSubcoalgebra F C).carrier.subtype) = D :=
    ambientImage_comap_eq_of_le _ D hDle
  rw [lieStepUNumerator, ambientImage_sup,
    hDimage,
    ambientImage_lieStepUSubspace F F le_rfl C U]

theorem ambientImage_lieStepUDenominator
    (F' F : Submodule k L) [FiniteDimensional k F]
    (hFF : F' ≤ F) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier)
    (D : Submodule k M) (hDle : D ≤ lieExpansion F C.carrier) :
    ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
        (lieStepUDenominator F' F C U
          (D.comap (lieExpansionFiniteSubcoalgebra F C).carrier.subtype)) =
      D ⊔ lieExpansion F' (ambientImage C.carrier U) := by
  have hDimage :
      ambientImage (lieExpansionFiniteSubcoalgebra F C).carrier
          (D.comap (lieExpansionFiniteSubcoalgebra F C).carrier.subtype) = D :=
    ambientImage_comap_eq_of_le _ D hDle
  rw [lieStepUDenominator, ambientImage_sup,
    hDimage,
    ambientImage_lieStepUSubspace F' F hFF C U]

/-- Ambient form of the codimension-one Lie transfer step. -/
theorem lieCodimOne_transfer_step_ambient
    (F' F : Submodule k L)
    [FiniteDimensional k F'] [FiniteDimensional k F]
    (hFF : F' ≤ F) (hdim : sfinrank k F = sfinrank k F' + 1)
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k M) (hDle : D ≤ lieExpansion F C.carrier)
    (hD : IsSubcoalgebra (k := k) D) (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B)) :
    t * ((sfinrank k (lieExpansion F C.carrier) : ℚ) -
        sfinrank k (D ⊔ lieExpansion F' C.carrier)) ≤
      (sfinrank k (D ⊔
          lieExpansion F (ambientImage C.carrier U)) : ℚ) -
        sfinrank k (D ⊔
          lieExpansion F' (ambientImage C.carrier U)) := by
  let A := lieExpansionFiniteSubcoalgebra F C
  let Dint := D.comap A.carrier.subtype
  have hDimage : ambientImage A.carrier Dint = D :=
    ambientImage_comap_eq_of_le A.carrier D hDle
  have hDint : IsSubcoalgebra (k := k) Dint := by
    apply (isSubcoalgebra_ambientImage_iff A.carrier A.isSubcoalgebra Dint).mp
    rw [hDimage]
    exact hD
  have hstep := lieCodimOne_transfer_step
    F' F hFF hdim C U Dint hDint t hsem
  unfold sfinrank at hstep ⊢
  rw [← finrank_ambientImage A.carrier
      (lieStepDenominator F' F C Dint),
    ambientImage_lieStepDenominator F' F hFF C D hDle,
    ← finrank_ambientImage A.carrier
      (lieStepUNumerator F C U Dint),
    ambientImage_lieStepUNumerator F C U D hDle,
    ← finrank_ambientImage A.carrier
      (lieStepUDenominator F' F C U Dint),
    ambientImage_lieStepUDenominator F' F hFF C U D hDle] at hstep
  exact hstep

/-- Transfer along an arbitrary finite-dimensional flag of Lie subspaces. -/
theorem lie_transfer_ambient
    (F : Submodule k L) [FiniteDimensional k F]
    (C : FiniteSubcoalgebra k M) (U : Submodule k C.carrier)
    (D : Submodule k M) (hDle : D ≤ lieExpansion F C.carrier)
    (hD : IsSubcoalgebra (k := k) D) (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B)) :
    t * ((sfinrank k (lieExpansion F C.carrier) : ℚ) - sfinrank k D) ≤
      (sfinrank k (lieExpansion F (ambientImage C.carrier U)) : ℚ) -
        sfinrank k (lieExpansion F (ambientImage C.carrier U) ⊓ D) := by
  induction hn : finrank k F using Nat.strong_induction_on generalizing F D with
  | h n ih =>
    let : FiniteDimensional k (lieExpansion F C.carrier) :=
      finiteDimensional_lieExpansion F C.carrier
    let inclusionD : D →ₗ[k] lieExpansion F C.carrier :=
      LinearMap.codRestrict (lieExpansion F C.carrier) D.subtype
        (fun x => hDle x.2)
    let : FiniteDimensional k D :=
      FiniteDimensional.of_injective inclusionD (by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : lieExpansion F C.carrier => (z : M)) hxy)
    by_cases hn0 : n = 0
    · have hF : F = ⊥ := by
        exact Submodule.finrank_eq_zero.mp (hn.trans hn0)
      subst F
      let B : Submodule k C.carrier := D.comap C.carrier.subtype
      have hDleC : D ≤ C.carrier := by simpa using hDle
      have hBimage : ambientImage C.carrier B = D :=
        ambientImage_comap_eq_of_le C.carrier D hDleC
      have hB : IsSubcoalgebra (k := k) B := by
        apply (isSubcoalgebra_ambientImage_iff C.carrier C.isSubcoalgebra B).mp
        rw [hBimage]
        exact hD
      have hs := hsem B hB
      have hdimB : finrank k B = sfinrank k D := by
        rw [← hBimage]
        exact (finrank_ambientImage C.carrier B).symm
      have hinterImage :
          ambientImage C.carrier (U ⊓ B) =
            ambientImage C.carrier U ⊓ D := by
        rw [ambientImage_inf, hBimage]
      have hinterDim : sfinrank k (U ⊓ B) =
          sfinrank k (ambientImage C.carrier U ⊓ D) := by
        rw [← hinterImage]
        exact (finrank_ambientImage C.carrier (U ⊓ B)).symm
      have hdimU : finrank k U = sfinrank k (ambientImage C.carrier U) :=
        (finrank_ambientImage C.carrier U).symm
      simpa [hdimB, hinterDim, hdimU] using hs
    · have hF : F ≠ ⊥ := by
        intro hbot
        subst F
        have : n = 0 := by simpa using hn.symm
        exact hn0 this
      obtain ⟨F', hFF, hdim⟩ := exists_lieSubspace_finrank_add_one F hF
      let inclusion : F' →ₗ[k] F :=
        LinearMap.codRestrict F F'.subtype (fun x => hFF x.2)
      let : FiniteDimensional k F' :=
        FiniteDimensional.of_injective inclusion (by
          intro x y hxy
          apply Subtype.ext
          exact congrArg (fun z : F => (z : L)) hxy)
      let FC' : Submodule k M := lieExpansion F' C.carrier
      let FU' : Submodule k M :=
        lieExpansion F' (ambientImage C.carrier U)
      let FU : Submodule k M :=
        lieExpansion F (ambientImage C.carrier U)
      let : FiniteDimensional k FC' :=
        finiteDimensional_lieExpansion F' C.carrier
      let : FiniteDimensional k (ambientImage C.carrier U) :=
        Module.Finite.equiv (ambientImageEquiv C.carrier U)
      let : FiniteDimensional k FU' :=
        finiteDimensional_lieExpansion F' (ambientImage C.carrier U)
      let : FiniteDimensional k FU :=
        finiteDimensional_lieExpansion F (ambientImage C.carrier U)
      let D' : Submodule k M := D ⊓ FC'
      have hF'lt : finrank k F' < n := by
        change finrank k F = finrank k F' + 1 at hdim
        omega
      have hD'le : D' ≤ lieExpansion F' C.carrier := inf_le_right
      have hD' : IsSubcoalgebra (k := k) D' :=
        hD.inf_of_tensorSquareIntersection tensorSquareIntersectionProperty
          (C.isSubcoalgebra.lieExpansion F')
      have hprev := ih (finrank k F') hF'lt F' D' hD'le hD' rfl
      have hstep := lieCodimOne_transfer_step_ambient
        F' F hFF hdim C U D hDle hD t hsem
      have hleftNat := Submodule.finrank_sup_add_finrank_inf_eq D FC'
      have hleftQ :
          (sfinrank k (D ⊔ FC') : ℚ) + sfinrank k (D ⊓ FC') =
            sfinrank k D + sfinrank k FC' := by
        exact_mod_cast hleftNat
      have hleft :
          ((sfinrank k (lieExpansion F C.carrier) : ℚ) -
              sfinrank k (D ⊔ FC')) +
            ((sfinrank k FC' : ℚ) - sfinrank k (D ⊓ FC')) =
          (sfinrank k (lieExpansion F C.carrier) : ℚ) - sfinrank k D := by
        linarith
      have hFU'FU : FU' ≤ FU :=
        lieExpansion_mono_left hFF (ambientImage C.carrier U)
      have hinter : FU' ⊓ (D ⊓ FC') = FU' ⊓ D := by
        calc
          FU' ⊓ (D ⊓ FC') = (FU' ⊓ D) ⊓ FC' := by ac_rfl
          _ = FU' ⊓ D := inf_eq_left.mpr (inf_le_left.trans (by
            exact lieExpansion_mono_right F' (by
              rintro x ⟨u, -, rfl⟩
              exact u.2)))
      have hmodUNat := Submodule.finrank_sup_add_finrank_inf_eq D FU
      have hmodU'Nat := Submodule.finrank_sup_add_finrank_inf_eq D FU'
      have hmodU :
          (sfinrank k (D ⊔ FU) : ℚ) + sfinrank k (D ⊓ FU) =
            sfinrank k D + sfinrank k FU := by
        exact_mod_cast hmodUNat
      have hmodU' :
          (sfinrank k (D ⊔ FU') : ℚ) + sfinrank k (D ⊓ FU') =
            sfinrank k D + sfinrank k FU' := by
        exact_mod_cast hmodU'Nat
      have hright :
          ((sfinrank k (D ⊔ FU) : ℚ) - sfinrank k (D ⊔ FU')) +
            ((sfinrank k FU' : ℚ) - sfinrank k (FU' ⊓ (D ⊓ FC'))) =
          (sfinrank k FU : ℚ) - sfinrank k (FU ⊓ D) := by
        rw [hinter, inf_comm FU' D, inf_comm FU D]
        linarith
      change t * ((sfinrank k (lieExpansion F C.carrier) : ℚ) -
          sfinrank k D) ≤ (sfinrank k FU : ℚ) - sfinrank k (FU ⊓ D)
      rw [← hleft, ← hright, mul_add]
      exact add_le_add (by simpa [FC', FU', FU] using hstep)
        (by simpa [FC', FU', D'] using hprev)

end

end HopfAmenability
