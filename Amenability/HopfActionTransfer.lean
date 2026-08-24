/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.HopfModuleCoalgebraBaseChange
import Amenability.HopfFlagActionTransfer
import Amenability.FiniteSubcoalgebraBaseChange
import Amenability.CocommutativeSplittingFlag

/-!
# Unconditional transfer for Hopf actions
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

attribute [local instance] baseChangeModule_inst baseChange_actionTower
  baseChangeIsHopfModuleCoalgebra

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

/-- The ambient action-transfer inequality, obtained over a splitting field
of the acting finite subcoalgebra and descended numerically. -/
theorem finiteSubcoalgebra_action_transfer_ambient
    (F : FiniteSubcoalgebra k H) (C : FiniteSubcoalgebra k M)
    (U : Submodule k C.carrier)
    (D : Submodule k M)
    (hDle : D ≤ actionSubspace F.carrier C.carrier)
    (hD : IsSubcoalgebra (k := k) D)
    (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B)) :
    t * ((sfinrank k (actionSubspace F.carrier C.carrier) : ℚ) -
        sfinrank k D) ≤
      (sfinrank k
          (actionSubspace F.carrier (ambientImage C.carrier U)) : ℚ) -
        sfinrank k
          (actionSubspace F.carrier (ambientImage C.carrier U) ⊓ D) := by
  let K := CoalgebraSplittingField (k := k) (C := F.carrier)
  obtain ⟨FK, hFK, hflag⟩ := exists_baseChange_completeSubcoalgebraFlag F
  let CK := C.baseChange K
  let UK := C.baseChangeSubspace K U
  let DK := baseChangeSubspace (k := k) K D
  have hsemK : ∀ B : Submodule K CK.carrier,
      IsSubcoalgebra (k := K) B →
      t * ((finrank K CK.carrier : ℚ) - sfinrank K B) ≤
        (sfinrank K UK : ℚ) - sfinrank K (UK ⊓ B) := by
    intro B hB
    exact C.semistable_baseChange U t hsem B hB
  have hDK : IsSubcoalgebra (k := K) DK :=
    isSubcoalgebra_baseChangeSubspace D hD
  have hDKle : DK ≤ actionSubspace FK.carrier CK.carrier := by
    rw [hFK]
    change baseChangeSubspace (k := k) K D ≤
      actionSubspace
        (baseChangeSubspace (k := k) K F.carrier)
        (baseChangeSubspace (k := k) K C.carrier)
    rw [actionSubspace_baseChange]
    exact baseChangeSubspace_mono hDle
  have htransfer := action_transfer_of_completeFlag_ambient
    FK CK hflag UK DK hDKle hDK t hsemK
  let Uamb := ambientImage C.carrier U
  let FC := actionSubspace F.carrier C.carrier
  let FU := actionSubspace F.carrier Uamb
  have hCKcarrier : CK.carrier = baseChangeSubspace (k := k) K C.carrier := rfl
  have hUKamb : ambientImage CK.carrier UK =
      baseChangeSubspace (k := k) K Uamb :=
    C.ambientImage_baseChangeSubspace_internal U
  have hFC : actionSubspace FK.carrier CK.carrier =
      baseChangeSubspace (k := k) K FC := by
    rw [hFK, hCKcarrier, actionSubspace_baseChange]
  have hFU : actionSubspace FK.carrier (ambientImage CK.carrier UK) =
      baseChangeSubspace (k := k) K FU := by
    rw [hFK, hUKamb, actionSubspace_baseChange]
  let inclusion : D →ₗ[k] FC :=
    LinearMap.codRestrict FC D.subtype (fun d => hDle d.2)
  let : FiniteDimensional k D :=
    FiniteDimensional.of_injective inclusion (by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : FC => (z : M)) hxy))
  let : FiniteDimensional k Uamb :=
    Module.Finite.equiv (ambientImageEquiv C.carrier U)
  let : FiniteDimensional k FC := finiteDimensional_actionSubspace _ _
  let : FiniteDimensional k FU := finiteDimensional_actionSubspace _ _
  have hFCdim := sfinrank_baseChangeSubspace (K := K) FC
  have hFUdim := sfinrank_baseChangeSubspace (K := K) FU
  have hDdim := sfinrank_baseChangeSubspace (K := K) D
  have hInfDim := sfinrank_inf_baseChangeSubspace (K := K) FU D
  rw [hFC, hFU] at htransfer
  dsimp [DK] at htransfer
  unfold sfinrank at hFCdim hFUdim hDdim hInfDim
  rw [hFCdim, hFUdim, hDdim, hInfDim] at htransfer
  exact htransfer

end

end HopfAmenability
