/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.FiniteSubcoalgebraBaseChange
import Amenability.CocommutativeSplittingFlag
import Amenability.PrimalFlagTransfer
import Amenability.FiniteSubcoalgebraProduct
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Unconditional primal finite-subcoalgebra transfer
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

/-- The ambient finite-subcoalgebra transfer inequality, proved after a finite
splitting-field extension and descended only at the level of dimensions. -/
theorem finiteSubcoalgebra_transfer_ambient
    (F C : FiniteSubcoalgebra k H)
    (U : Submodule k C.carrier)
    (D : Submodule k H)
    (hDFC : D ≤ F.carrier * C.carrier)
    (t : ℚ)
    (hD : IsSubcoalgebra (k := k) D)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B)) :
    t * ((finrank k (F.carrier * C.carrier) : ℚ) - finrank k D) ≤
      (finrank k (F.carrier * ambientImage C.carrier U) : ℚ) -
        finrank k ((F.carrier * ambientImage C.carrier U) ⊓ D :
          Submodule k H) := by
  let K := CoalgebraSplittingField (k := k) (C := F.carrier)
  obtain ⟨FK, hFK, hflag⟩ :=
    exists_baseChange_completeSubcoalgebraFlag F
  let CK := C.baseChange K
  let UK := C.baseChangeSubspace K U
  let DK := baseChangeSubspace (k := k) K D
  have hsemK : ∀ B : Submodule K CK.carrier,
      IsSubcoalgebra (k := K) (H := CK.carrier) B →
      t * ((finrank K CK.carrier : ℚ) - finrank K B) ≤
        (finrank K UK : ℚ) -
          finrank K (UK ⊓ B : Submodule K CK.carrier) := by
    intro B hB
    exact C.semistable_baseChange U t hsem B hB
  have hDK : IsSubcoalgebra (k := K) DK :=
    isSubcoalgebra_baseChangeSubspace D hD
  have hDKle : DK ≤ FK.carrier * CK.carrier := by
    dsimp [CK]
    rw [hFK, ← baseChangeSubspace_mul]
    dsimp [DK]
    exact baseChangeSubspace_mono hDFC
  have htransfer := PrimalTransfer.transfer_of_completeFlag_ambient
    FK CK hflag UK DK hDKle hDK t hsemK
  let Uamb := ambientImage C.carrier U
  let FC : Submodule k H := F.carrier * C.carrier
  let FU : Submodule k H := F.carrier * Uamb
  have hprodC : FK.carrier * CK.carrier =
      baseChangeSubspace (k := k) K FC := by
    dsimp [CK, FC]
    rw [hFK, baseChangeSubspace_mul]
  have hUKamb : ambientImage CK.carrier UK =
      baseChangeSubspace (k := k) K Uamb := by
    exact C.ambientImage_baseChangeSubspace_internal U
  have hprodU : FK.carrier * ambientImage CK.carrier UK =
      baseChangeSubspace (k := k) K FU := by
    rw [hFK, hUKamb]
    dsimp [FU, Uamb]
    rw [baseChangeSubspace_mul]
  let : FiniteDimensional k FC := by
    dsimp [FC]
    exact finiteDimensional_mul F.carrier C.carrier
  let inclusion : D →ₗ[k] FC :=
    LinearMap.codRestrict FC D.subtype (fun d ↦ hDFC d.2)
  let : FiniteDimensional k D :=
    FiniteDimensional.of_injective inclusion (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : FC ↦ (z : H)) hxy)
  let : FiniteDimensional k Uamb :=
    Module.Finite.equiv (ambientImageEquiv C.carrier U)
  let : FiniteDimensional k FU := by
    dsimp [FU]
    exact finiteDimensional_mul F.carrier Uamb
  have hFCdim := sfinrank_baseChangeSubspace (K := K) FC
  have hFUdim := sfinrank_baseChangeSubspace (K := K) FU
  have hDdim := sfinrank_baseChangeSubspace (K := K) D
  have hInfDim := sfinrank_inf_baseChangeSubspace (K := K) FU D
  rw [hprodC, hprodU] at htransfer
  dsimp [DK] at htransfer
  unfold sfinrank at hFCdim hFUdim hDdim hInfDim
  rw [hFCdim, hFUdim, hDdim, hInfDim] at htransfer
  exact htransfer

end

end HopfAmenability
