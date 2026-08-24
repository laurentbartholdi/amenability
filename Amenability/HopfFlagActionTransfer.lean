/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.HopfCodimOneActionTransfer
import Amenability.CompleteSubcoalgebraFlag

/-!
# Hopf action transfer along complete subcoalgebra flags
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

open PrimalTransfer

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]


omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_actionLowerSubspace_flag
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier) :
    ambientImage (A.act C).carrier
        (actionLowerSubspace A' A C) = actionSubspace A'.carrier C.carrier := by
  unfold actionLowerSubspace
  exact ambientImage_comap_eq_of_le _ _
    (actionSubspace_mono_left hAA _)

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_actionLowerUSubspace
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier) :
    ambientImage (A.act C).carrier
        (actionLowerUSubspace A' A C U) =
      actionSubspace A'.carrier (ambientImage C.carrier U) := by
  unfold actionLowerUSubspace
  apply ambientImage_comap_eq_of_le
  have hU : ambientImage C.carrier U ≤ C.carrier := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  exact (actionSubspace_mono_left hAA _).trans
    (actionSubspace_mono_right A.carrier hU)

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_actionStepDenominator
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k M) (hDle : D ≤ (A.act C).carrier) :
    ambientImage (A.act C).carrier
        (actionStepDenominator A' A C
          (D.comap (A.act C).carrier.subtype)) =
      D ⊔ (actionSubspace A'.carrier C.carrier) := by
  rw [actionStepDenominator, ambientImage_sup,
    ambientImage_comap_eq_of_le _ D hDle,
    ambientImage_actionLowerSubspace_flag A' A C hAA]

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_actionStepUNumerator
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier)
    (D : Submodule k M) (hDle : D ≤ (A.act C).carrier) :
    ambientImage (A.act C).carrier
        (actionStepUNumerator A' A C U
          (D.comap (A.act C).carrier.subtype)) =
      D ⊔ (actionSubspace A.carrier (ambientImage C.carrier U)) := by
  rw [actionStepUNumerator, ambientImage_sup,
    ambientImage_comap_eq_of_le _ D hDle,
    ambientImage_actionUSubspace]

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_actionStepUDenominator
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k M) (hDle : D ≤ (A.act C).carrier) :
    ambientImage (A.act C).carrier
        (actionStepUDenominator A' A C U
          (D.comap (A.act C).carrier.subtype)) =
      D ⊔ (actionSubspace A'.carrier (ambientImage C.carrier U)) := by
  rw [actionStepUDenominator, ambientImage_sup,
    ambientImage_comap_eq_of_le _ D hDle,
    ambientImage_actionLowerUSubspace A' A C hAA U]

/-- Ambient form of the primal codimension-one transfer step. -/
theorem actionCodimOne_transfer_step_ambient
    (A' A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hAA : A'.carrier ≤ A.carrier)
    (hdim : finrank k A.carrier = finrank k A'.carrier + 1)
    (U : Submodule k C.carrier)
    (D : Submodule k M)
    (hDle : D ≤ (A.act C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (finrank k U : ℚ) -
          sfinrank k (U ⊓ B)) :
    t * ((sfinrank k (actionSubspace A.carrier C.carrier) : ℚ) -
        sfinrank k (D ⊔ (actionSubspace A'.carrier C.carrier))) ≤
      (sfinrank k (D ⊔
        (actionSubspace A.carrier (ambientImage C.carrier U)) : Submodule k M) : ℚ) -
        sfinrank k (D ⊔
          (actionSubspace A'.carrier (ambientImage C.carrier U)) : Submodule k M) := by
  let AC := A.act C
  let Dint := D.comap AC.carrier.subtype
  have hDimage : ambientImage AC.carrier Dint = D :=
    ambientImage_comap_eq_of_le AC.carrier D hDle
  have hDint : IsSubcoalgebra (k := k) Dint := by
    apply (isSubcoalgebra_ambientImage_iff AC.carrier AC.isSubcoalgebra Dint).1
    rw [hDimage]
    exact hD
  have hstep := actionCodimOne_transfer_step
    A' A C hAA hdim U Dint hDint t hsem
  simp only [sfinrank] at hstep ⊢
  rw [← finrank_ambientImage AC.carrier
      (actionStepDenominator A' A C Dint),
    ambientImage_actionStepDenominator A' A C hAA D hDle,
    ← finrank_ambientImage AC.carrier
      (actionStepUNumerator A' A C U Dint),
    ambientImage_actionStepUNumerator A' A C U D hDle,
    ← finrank_ambientImage AC.carrier
      (actionStepUDenominator A' A C U Dint),
    ambientImage_actionStepUDenominator A' A C hAA U D hDle] at hstep
  exact hstep

/-- The primal transfer inequality along a complete subcoalgebra flag, with
the comparison subcoalgebra living in the ambient Hopf algebra. -/
theorem action_transfer_of_completeFlag_ambient
    (A : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (hflag : HasCompleteSubcoalgebraFlag A)
    (U : Submodule k C.carrier)
    (D : Submodule k M)
    (hDle : D ≤ actionSubspace A.carrier C.carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (finrank k U : ℚ) -
          sfinrank k (U ⊓ B)) :
    t * ((sfinrank k (actionSubspace A.carrier C.carrier) : ℚ) - sfinrank k D) ≤
      (sfinrank k (actionSubspace A.carrier (ambientImage C.carrier U)) : ℚ) -
        sfinrank k ((actionSubspace A.carrier (ambientImage C.carrier U)) ⊓ D :
          Submodule k M) := by
  let inclusion : D →ₗ[k] (A.act C).carrier :=
    LinearMap.codRestrict (A.act C).carrier D.subtype
      (fun d => hDle d.2)
  let : FiniteDimensional k D :=
    FiniteDimensional.of_injective inclusion (by
      intro x y hxy
      exact Subtype.ext
        (congrArg (fun z : (A.act C).carrier => (z : M)) hxy))
  induction hflag generalizing D with
  | @bot A0 hA =>
      have hD0 : D = ⊥ := by
        rw [eq_bot_iff]
        simpa [hA] using hDle
      rw [hA, hD0]
      simp only [actionSubspace_bot_left]
      simp
  | @step A' A0 hflag hAA hdim ih =>
      let AC' : Submodule k M := actionSubspace A'.carrier C.carrier
      let AU' : Submodule k M := actionSubspace A'.carrier (ambientImage C.carrier U)
      let AU : Submodule k M := actionSubspace A0.carrier (ambientImage C.carrier U)
      let D' : Submodule k M := D ⊓ AC'
      have hD'le : D' ≤ actionSubspace A'.carrier C.carrier := by
        exact inf_le_right
      have hD' : IsSubcoalgebra (k := k) D' := by
        exact hD.inf (A'.act C).isSubcoalgebra
      have hprev := ih D' hD'le hD'
      have hstep := actionCodimOne_transfer_step_ambient
        A' A0 C hAA hdim U D hDle hD t hsem
      have hleftNat := Submodule.finrank_sup_add_finrank_inf_eq D AC'
      have hleftQ :
          (sfinrank k (D ⊔ AC') : ℚ) + sfinrank k (D ⊓ AC') =
            sfinrank k D + sfinrank k AC' := by
        exact_mod_cast hleftNat
      have hleft :
          ((sfinrank k (actionSubspace A0.carrier C.carrier) : ℚ) -
              sfinrank k (D ⊔ AC')) +
            ((sfinrank k AC' : ℚ) -
              sfinrank k (D ⊓ AC')) =
          (sfinrank k (actionSubspace A0.carrier C.carrier) : ℚ) - sfinrank k D := by
        linarith
      have hUambient : ambientImage C.carrier U ≤ C.carrier := by
        rintro x ⟨u, -, rfl⟩
        exact u.2
      have hAU'AU : AU' ≤ AU := actionSubspace_mono_left hAA _
      have hAU'AC' : AU' ≤ AC' :=
        actionSubspace_mono_right A'.carrier hUambient
      let incAU : AU →ₗ[k] (A0.act C).carrier :=
        LinearMap.codRestrict (A0.act C).carrier AU.subtype
          (fun x => actionSubspace_mono_right A0.carrier hUambient x.2)
      let incAU' : AU' →ₗ[k] (A'.act C).carrier :=
        LinearMap.codRestrict (A'.act C).carrier AU'.subtype
          (fun x => hAU'AC' x.2)
      let : FiniteDimensional k AU :=
        FiniteDimensional.of_injective incAU (by
          intro x y hxy
          exact Subtype.ext
            (congrArg (fun z : (A0.act C).carrier => (z : M)) hxy))
      let : FiniteDimensional k AU' :=
        FiniteDimensional.of_injective incAU' (by
          intro x y hxy
          exact Subtype.ext
            (congrArg (fun z : (A'.act C).carrier => (z : M)) hxy))
      have hinter : AU' ⊓ (D ⊓ AC') = AU' ⊓ D := by
        calc
          AU' ⊓ (D ⊓ AC') = (AU' ⊓ D) ⊓ AC' := by ac_rfl
          _ = AU' ⊓ D := inf_eq_left.2 (inf_le_left.trans hAU'AC')
      have hmodUNat := Submodule.finrank_sup_add_finrank_inf_eq D AU
      have hmodU'Nat := Submodule.finrank_sup_add_finrank_inf_eq D AU'
      have hmodU :
          (sfinrank k (D ⊔ AU) : ℚ) + sfinrank k (D ⊓ AU) =
            sfinrank k D + sfinrank k AU := by
        exact_mod_cast hmodUNat
      have hmodU' :
          (sfinrank k (D ⊔ AU') : ℚ) + sfinrank k (D ⊓ AU') =
            sfinrank k D + sfinrank k AU' := by
        exact_mod_cast hmodU'Nat
      have hinfComm : D ⊓ AU = AU ⊓ D := inf_comm D AU
      have hinfComm' : D ⊓ AU' = AU' ⊓ D := inf_comm D AU'
      have hright :
          ((sfinrank k (D ⊔ AU) : ℚ) - sfinrank k (D ⊔ AU')) +
            ((sfinrank k AU' : ℚ) -
              sfinrank k (AU' ⊓ (D ⊓ AC'))) =
          (sfinrank k AU : ℚ) - sfinrank k (AU ⊓ D) := by
        rw [hinter, ← hinfComm, ← hinfComm']
        linarith
      change t * ((sfinrank k (actionSubspace A0.carrier C.carrier) : ℚ) - sfinrank k D) ≤
        (sfinrank k AU : ℚ) - sfinrank k (AU ⊓ D)
      rw [← hleft, ← hright]
      rw [mul_add]
      exact add_le_add hstep (by simpa [AC', AU', D'] using hprev)


end

end HopfAmenability
