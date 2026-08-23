/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.FiniteSubcoalgebraTransfer
import Amenability.SubcoalgebraAmbient

/-!
# The finite-subcoalgebra transfer inequality in the ambient coalgebra

This file accepts the comparison subcoalgebra as a subspace of the ambient
Hopf algebra and transports it to the internal subtype `FC` only for the
application of `finiteSubcoalgebra_transfer`.
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

namespace SplitDualFiltration

variable
    (F C : FiniteSubcoalgebra k H)
    (S : SplitDualFiltration k F.Dual)

omit [IsCocomm k H] in
/-- The internal left-product subspace has the expected ambient image. -/
theorem ambientImage_leftProductSubspace
    (U : Submodule k C.carrier) :
    ambientImage (FiniteSubcoalgebra.mul F C).carrier
        (FiniteSubcoalgebra.leftProductSubspace F C U) =
      F.carrier * ambientImage C.carrier U := by
  let e := ambientImageEquiv C.carrier U
  have hmap :
      ∀ z : F.carrier ⊗[k] U,
        (((FiniteSubcoalgebra.leftProductMap F C U z :
            (FiniteSubcoalgebra.mul F C).carrier) : H)) =
          Submodule.mulMap' F.carrier (ambientImage C.carrier U)
            (TensorProduct.map LinearMap.id e.toLinearMap z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y => rfl
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    rw [← Submodule.mulMap_range]
    exact ⟨TensorProduct.map LinearMap.id e.toLinearMap z, (hmap z).symm⟩
  · intro hx
    rw [← Submodule.mulMap_range] at hx
    rcases hx with ⟨z, rfl⟩
    obtain ⟨z', hz'⟩ :=
      (TensorProduct.map_bijective
        (f := LinearMap.id) (g := e.toLinearMap)
        Function.bijective_id e.bijective).2 z
    refine ⟨FiniteSubcoalgebra.leftProductMap F C U z', ⟨z', rfl⟩, ?_⟩
    change
      ((FiniteSubcoalgebra.leftProductMap F C U z' :
        (FiniteSubcoalgebra.mul F C).carrier) : H) =
        Submodule.mulMap' F.carrier (ambientImage C.carrier U) z
    rw [hmap, hz']

include S in
/-- The transfer inequality with the comparison subcoalgebra living in `H`. -/
theorem finiteSubcoalgebra_transfer_ambient
    (U : Submodule k C.carrier)
    (D : Submodule k H)
    (hDFC : D ≤ (FiniteSubcoalgebra.mul F C).carrier)
    (t : ℚ)
    (hD : IsSubcoalgebra (k := k) D)
    (hsem :
      ∀ B : Submodule k C.carrier,
        IsSubcoalgebra (k := k) B →
          t *
              ((finrank k C.carrier : ℚ) -
                (finrank k B : ℚ)) ≤
            (finrank k U : ℚ) -
              (finrank k
                (U ⊓ B : Submodule k C.carrier) : ℚ)) :
    t *
        ((finrank k (FiniteSubcoalgebra.mul F C).carrier : ℚ) -
          (finrank k D : ℚ)) ≤
      (finrank k
        (ambientImage (FiniteSubcoalgebra.mul F C).carrier
          (FiniteSubcoalgebra.leftProductSubspace F C U)) : ℚ) -
        (finrank k
          (ambientImage (FiniteSubcoalgebra.mul F C).carrier
              (FiniteSubcoalgebra.leftProductSubspace F C U) ⊓ D :
            Submodule k H) : ℚ) := by
  let FC := FiniteSubcoalgebra.mul F C
  let D' : Submodule k FC.carrier := D.comap FC.carrier.subtype
  have hDimage : ambientImage FC.carrier D' = D := by
    exact ambientImage_comap_eq_of_le FC.carrier D hDFC
  have hD' : IsSubcoalgebra (k := k) D' := by
    apply (isSubcoalgebra_ambientImage_iff FC.carrier FC.isSubcoalgebra D').1
    rw [hDimage]
    exact hD
  have htransfer := S.finiteSubcoalgebra_transfer F C U D' t hD' hsem
  have hintersection :
      ambientImage FC.carrier
          (FiniteSubcoalgebra.leftProductSubspace F C U ⊓ D') =
        ambientImage FC.carrier
            (FiniteSubcoalgebra.leftProductSubspace F C U) ⊓ D := by
    rw [ambientImage_inf, hDimage]
  rw [← finrank_ambientImage FC.carrier D'] at htransfer
  rw [← finrank_ambientImage FC.carrier
    (FiniteSubcoalgebra.leftProductSubspace F C U)] at htransfer
  rw [← finrank_ambientImage FC.carrier
    (FiniteSubcoalgebra.leftProductSubspace F C U ⊓ D')] at htransfer
  rw [hDimage, hintersection] at htransfer
  simpa [FC] using htransfer

end SplitDualFiltration

end

end HopfAmenability
