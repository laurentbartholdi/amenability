/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CodimOneCoalgebraStep

/-!
# Primal transfer along complete subcoalgebra flags
-/

open Coalgebra Module TensorProduct

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

namespace PrimalTransfer

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_lowerProductSubspace
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) :
    ambientImage (FiniteSubcoalgebra.mul A C).carrier
        (lowerProductSubspace A' A C) = A'.carrier * C.carrier := by
  unfold lowerProductSubspace
  exact ambientImage_comap_eq_of_le _ _
    (subcoalgebra_mul_mono hAA le_rfl)

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_lowerUSubspace
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier) :
    ambientImage (FiniteSubcoalgebra.mul A C).carrier
        (lowerUSubspace A' A C U) =
      A'.carrier * ambientImage C.carrier U := by
  unfold lowerUSubspace
  apply ambientImage_comap_eq_of_le
  have hU : ambientImage C.carrier U ≤ C.carrier := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  exact (subcoalgebra_mul_mono hAA le_rfl).trans
    (subcoalgebra_mul_mono le_rfl hU)

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_stepDenominator
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (D : Submodule k H) (hDle : D ≤ (FiniteSubcoalgebra.mul A C).carrier) :
    ambientImage (FiniteSubcoalgebra.mul A C).carrier
        (stepDenominator A' A C
          (D.comap (FiniteSubcoalgebra.mul A C).carrier.subtype)) =
      D ⊔ (A'.carrier * C.carrier) := by
  rw [stepDenominator, ambientImage_sup,
    ambientImage_comap_eq_of_le _ D hDle,
    ambientImage_lowerProductSubspace A' A C hAA]

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_stepUNumerator
    (A' A C : FiniteSubcoalgebra k H)
    (U : Submodule k C.carrier)
    (D : Submodule k H) (hDle : D ≤ (FiniteSubcoalgebra.mul A C).carrier) :
    ambientImage (FiniteSubcoalgebra.mul A C).carrier
        (stepUNumerator A' A C U
          (D.comap (FiniteSubcoalgebra.mul A C).carrier.subtype)) =
      D ⊔ (A.carrier * ambientImage C.carrier U) := by
  rw [stepUNumerator, ambientImage_sup,
    ambientImage_comap_eq_of_le _ D hDle,
    ambientImage_leftProductSubspace]

omit [Coalgebra.IsCocomm k H] in
theorem ambientImage_stepUDenominator
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier) (U : Submodule k C.carrier)
    (D : Submodule k H) (hDle : D ≤ (FiniteSubcoalgebra.mul A C).carrier) :
    ambientImage (FiniteSubcoalgebra.mul A C).carrier
        (stepUDenominator A' A C U
          (D.comap (FiniteSubcoalgebra.mul A C).carrier.subtype)) =
      D ⊔ (A'.carrier * ambientImage C.carrier U) := by
  rw [stepUDenominator, ambientImage_sup,
    ambientImage_comap_eq_of_le _ D hDle,
    ambientImage_lowerUSubspace A' A C hAA U]

/-- Ambient form of the primal codimension-one transfer step. -/
theorem codimOne_transfer_step_ambient
    (A' A C : FiniteSubcoalgebra k H)
    (hAA : A'.carrier ≤ A.carrier)
    (hdim : finrank k A.carrier = finrank k A'.carrier + 1)
    (U : Submodule k C.carrier)
    (D : Submodule k H)
    (hDle : D ≤ (FiniteSubcoalgebra.mul A C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - finrank k B) ≤
        (finrank k U : ℚ) -
          sfinrank k (U ⊓ B)) :
    t * ((finrank k (A.carrier * C.carrier) : ℚ) -
        sfinrank k (D ⊔ (A'.carrier * C.carrier))) ≤
      (finrank k (D ⊔
        (A.carrier * ambientImage C.carrier U) : Submodule k H) : ℚ) -
        finrank k (D ⊔
          (A'.carrier * ambientImage C.carrier U) : Submodule k H) := by
  let AC := FiniteSubcoalgebra.mul A C
  let Dint := D.comap AC.carrier.subtype
  have hDimage : ambientImage AC.carrier Dint = D :=
    ambientImage_comap_eq_of_le AC.carrier D hDle
  have hDint : IsSubcoalgebra (k := k) Dint := by
    apply (isSubcoalgebra_ambientImage_iff AC.carrier AC.isSubcoalgebra Dint).1
    rw [hDimage]
    exact hD
  have hstep := codimOne_transfer_step
    A' A C hAA hdim U Dint hDint t hsem
  rw [← finrank_ambientImage AC.carrier
      (stepDenominator A' A C Dint),
    ambientImage_stepDenominator A' A C hAA D hDle,
    ← finrank_ambientImage AC.carrier
      (stepUNumerator A' A C U Dint),
    ambientImage_stepUNumerator A' A C U D hDle,
    ← finrank_ambientImage AC.carrier
      (stepUDenominator A' A C U Dint),
    ambientImage_stepUDenominator A' A C hAA U D hDle] at hstep
  exact hstep

/-- A complete flag of finite subcoalgebras, expressed recursively so that
successive codimension-one transfer steps require no index bookkeeping. -/
inductive HasCompleteSubcoalgebraFlag : FiniteSubcoalgebra k H → Prop
  | bot {A : FiniteSubcoalgebra k H} (hA : A.carrier = ⊥) :
      HasCompleteSubcoalgebraFlag A
  | step {A' A : FiniteSubcoalgebra k H}
      (hflag : HasCompleteSubcoalgebraFlag A')
      (hAA : A'.carrier ≤ A.carrier)
      (hdim : finrank k A.carrier = finrank k A'.carrier + 1) :
      HasCompleteSubcoalgebraFlag A

/-- The primal transfer inequality along a complete subcoalgebra flag, with
the comparison subcoalgebra living in the ambient Hopf algebra. -/
theorem transfer_of_completeFlag_ambient
    (A C : FiniteSubcoalgebra k H)
    (hflag : HasCompleteSubcoalgebraFlag A)
    (U : Submodule k C.carrier)
    (D : Submodule k H)
    (hDle : D ≤ A.carrier * C.carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - finrank k B) ≤
        (finrank k U : ℚ) -
          sfinrank k (U ⊓ B)) :
    t * ((finrank k (A.carrier * C.carrier) : ℚ) - finrank k D) ≤
      (finrank k (A.carrier * ambientImage C.carrier U) : ℚ) -
        finrank k ((A.carrier * ambientImage C.carrier U) ⊓ D :
          Submodule k H) := by
  let inclusion : D →ₗ[k] (FiniteSubcoalgebra.mul A C).carrier :=
    LinearMap.codRestrict (FiniteSubcoalgebra.mul A C).carrier D.subtype
      (fun d => hDle d.2)
  let : FiniteDimensional k D :=
    FiniteDimensional.of_injective inclusion (by
      intro x y hxy
      exact Subtype.ext
        (congrArg (fun z : (FiniteSubcoalgebra.mul A C).carrier => (z : H)) hxy))
  induction hflag generalizing D with
  | @bot A0 hA =>
      have hD0 : D = ⊥ := by
        rw [eq_bot_iff]
        simpa [hA] using hDle
      rw [hA, hD0]
      rw [Submodule.bot_mul, Submodule.bot_mul]
      simp
  | @step A' A0 hflag hAA hdim ih =>
      let AC' : Submodule k H := A'.carrier * C.carrier
      let AU' : Submodule k H := A'.carrier * ambientImage C.carrier U
      let AU : Submodule k H := A0.carrier * ambientImage C.carrier U
      let D' : Submodule k H := D ⊓ AC'
      have hD'le : D' ≤ A'.carrier * C.carrier := by
        exact inf_le_right
      have hD' : IsSubcoalgebra (k := k) D' := by
        exact hD.inf (FiniteSubcoalgebra.mul A' C).isSubcoalgebra
      have hprev := ih D' hD'le hD'
      have hstep := codimOne_transfer_step_ambient
        A' A0 C hAA hdim U D hDle hD t hsem
      have hleftNat := Submodule.finrank_sup_add_finrank_inf_eq D AC'
      have hleftQ :
          (sfinrank k (D ⊔ AC') : ℚ) + sfinrank k (D ⊓ AC') =
            finrank k D + finrank k AC' := by
        exact_mod_cast hleftNat
      have hleft :
          ((finrank k (A0.carrier * C.carrier) : ℚ) -
              sfinrank k (D ⊔ AC')) +
            ((finrank k AC' : ℚ) -
              sfinrank k (D ⊓ AC')) =
          (finrank k (A0.carrier * C.carrier) : ℚ) - finrank k D := by
        linarith
      have hUambient : ambientImage C.carrier U ≤ C.carrier := by
        rintro x ⟨u, -, rfl⟩
        exact u.2
      have hAU'AU : AU' ≤ AU := subcoalgebra_mul_mono hAA le_rfl
      have hAU'AC' : AU' ≤ AC' :=
        subcoalgebra_mul_mono le_rfl hUambient
      let incAU : AU →ₗ[k] (FiniteSubcoalgebra.mul A0 C).carrier :=
        LinearMap.codRestrict (FiniteSubcoalgebra.mul A0 C).carrier AU.subtype
          (fun x => subcoalgebra_mul_mono le_rfl hUambient x.2)
      let incAU' : AU' →ₗ[k] (FiniteSubcoalgebra.mul A' C).carrier :=
        LinearMap.codRestrict (FiniteSubcoalgebra.mul A' C).carrier AU'.subtype
          (fun x => hAU'AC' x.2)
      let : FiniteDimensional k AU :=
        FiniteDimensional.of_injective incAU (by
          intro x y hxy
          exact Subtype.ext
            (congrArg (fun z : (FiniteSubcoalgebra.mul A0 C).carrier => (z : H)) hxy))
      let : FiniteDimensional k AU' :=
        FiniteDimensional.of_injective incAU' (by
          intro x y hxy
          exact Subtype.ext
            (congrArg (fun z : (FiniteSubcoalgebra.mul A' C).carrier => (z : H)) hxy))
      have hinter : AU' ⊓ (D ⊓ AC') = AU' ⊓ D := by
        calc
          AU' ⊓ (D ⊓ AC') = (AU' ⊓ D) ⊓ AC' := by ac_rfl
          _ = AU' ⊓ D := inf_eq_left.2 (inf_le_left.trans hAU'AC')
      have hmodUNat := Submodule.finrank_sup_add_finrank_inf_eq D AU
      have hmodU'Nat := Submodule.finrank_sup_add_finrank_inf_eq D AU'
      have hmodU :
          (sfinrank k (D ⊔ AU) : ℚ) + sfinrank k (D ⊓ AU) =
            finrank k D + finrank k AU := by
        exact_mod_cast hmodUNat
      have hmodU' :
          (sfinrank k (D ⊔ AU') : ℚ) + sfinrank k (D ⊓ AU') =
            finrank k D + finrank k AU' := by
        exact_mod_cast hmodU'Nat
      have hinfComm : D ⊓ AU = AU ⊓ D := inf_comm D AU
      have hinfComm' : D ⊓ AU' = AU' ⊓ D := inf_comm D AU'
      have hright :
          ((sfinrank k (D ⊔ AU) : ℚ) - sfinrank k (D ⊔ AU')) +
            ((finrank k AU' : ℚ) -
              sfinrank k (AU' ⊓ (D ⊓ AC'))) =
          (finrank k AU : ℚ) - sfinrank k (AU ⊓ D) := by
        rw [hinter, ← hinfComm, ← hinfComm']
        linarith
      change t * ((finrank k (A0.carrier * C.carrier) : ℚ) - finrank k D) ≤
        (finrank k AU : ℚ) - sfinrank k (AU ⊓ D)
      rw [← hleft, ← hright]
      rw [mul_add]
      exact add_le_add hstep (by simpa [AC', AU', D'] using hprev)

/-- Internal form of transfer along a complete flag. -/
theorem transfer_of_completeFlag
    (A C : FiniteSubcoalgebra k H)
    (hflag : HasCompleteSubcoalgebraFlag A)
    (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul A C).carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - finrank k B) ≤
        (finrank k U : ℚ) -
          sfinrank k (U ⊓ B)) :
    t * ((finrank k (FiniteSubcoalgebra.mul A C).carrier : ℚ) -
        finrank k D) ≤
      (finrank k (leftProductSubspace A C U) : ℚ) -
        finrank k (leftProductSubspace A C U ⊓ D :
          Submodule k (FiniteSubcoalgebra.mul A C).carrier) := by
  let AC := FiniteSubcoalgebra.mul A C
  let Damb := ambientImage AC.carrier D
  have hDamble : Damb ≤ AC.carrier := by
    rintro x ⟨d, -, rfl⟩
    exact d.2
  have hDamb : IsSubcoalgebra (k := k) Damb := by
    apply (isSubcoalgebra_ambientImage_iff AC.carrier AC.isSubcoalgebra D).2
    exact hD
  have hamb := transfer_of_completeFlag_ambient
    A C hflag U Damb hDamble hDamb t hsem
  have hUimage : ambientImage AC.carrier (leftProductSubspace A C U) =
      A.carrier * ambientImage C.carrier U :=
    ambientImage_leftProductSubspace A C U
  have hinterImage :
      ambientImage AC.carrier (leftProductSubspace A C U) ⊓ Damb =
        ambientImage AC.carrier (leftProductSubspace A C U ⊓ D) := by
    change ambientImage AC.carrier (leftProductSubspace A C U) ⊓
        ambientImage AC.carrier D = _
    rw [← ambientImage_inf]
  rw [← hUimage, hinterImage,
    finrank_ambientImage AC.carrier D,
    finrank_ambientImage AC.carrier (leftProductSubspace A C U),
    finrank_ambientImage AC.carrier (leftProductSubspace A C U ⊓ D)] at hamb
  exact hamb

end PrimalTransfer

end

end UnifiedRounding
