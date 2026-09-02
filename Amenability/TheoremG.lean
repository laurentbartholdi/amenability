/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremD
import Amenability.TheoremE

/-! # Theorem G: permanence properties for amenable Lie algebras -/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L] [CharZero k]

/-- The universal-enveloping sequence of a Lie ideal, packaged as the
intrinsic cleft exact sequence required by Theorem E. -/
noncomputable def LieIdeal.ueaCleftExactSequence
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (I : LieIdeal k L) (bQ : Basis β k (L ⧸ I)) (bI : Basis α k I) :
    CleftExactSequence (k := k)
      (UniversalEnvelopingAlgebra k I)
      (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k (L ⧸ I)) where
  inclusion :=
    { toAlgHom := ueaMap (LieIdeal.inclusionLieHom I)
      map_counit := (ueaMapCoalgHom (LieIdeal.inclusionLieHom I)).counit_comp
      map_comul := (ueaMapCoalgHom (LieIdeal.inclusionLieHom I)).map_comp_comul }
  projection :=
    { toAlgHom := ueaMap (LieIdeal.quotientMkLieHom I)
      map_counit := (ueaMapCoalgHom (LieIdeal.quotientMkLieHom I)).counit_comp
      map_comul := (ueaMapCoalgHom (LieIdeal.quotientMkLieHom I)).map_comp_comul }
  inclusion_injective := ueaMap_injective (LieIdeal.inclusionLieHom I)
    (fun x y h => Subtype.ext h)
  projection_surjective := ueaMap_surjective (LieIdeal.quotientMkLieHom I)
    (LieIdeal.quotientMkLieHom_surjective I)
  projection_inclusion := fun a => DFunLike.congr_fun
    (LieIdeal.pbwMap_quotient_comp_ideal I) a
  coalgebraSection := LieIdeal.ueaLinearSectionCoalgHom I bQ bI
  projection_section := LieIdeal.pbwMap_comp_ueaLinearSection I bQ bI
  section_one := by
    let word : UniversalEnvelopingAlgebra.PBWWord β := ⟨[], by simp⟩
    change LieIdeal.ueaLinearSection I bQ bI
      (UniversalEnvelopingAlgebra.orderedMonomial bQ word) = 1
    rw [LieIdeal.ueaLinearSection_orderedMonomial]
    simp [LieIdeal.liftedQuotientMonomial, word]
  coinvariants := by
    let inc := ueaMap (LieIdeal.inclusionLieHom I)
    let proj := ueaMap (LieIdeal.quotientMkLieHom I)
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      change (((TensorProduct.map LinearMap.id proj.toLinearMap).comp
          (Coalgebra.comul (R := k)
            (A := UniversalEnvelopingAlgebra k L))) -
        (TensorProduct.mk k (UniversalEnvelopingAlgebra k L)
          (UniversalEnvelopingAlgebra k (L ⧸ I))).flip 1) (inc a) = 0
      rw [LinearMap.sub_apply, sub_eq_zero]
      rw [LinearMap.comp_apply]
      rw [show Coalgebra.comul (R := k) (inc a) =
          TensorProduct.map inc.toLinearMap inc.toLinearMap
            (Coalgebra.comul (R := k) a) from
        (CoalgHomClass.map_comp_comul_apply
          (ueaMapCoalgHom (LieIdeal.inclusionLieHom I)) a).symm]
      have hcounit (y : UniversalEnvelopingAlgebra k I) :
          proj (inc y) = algebraMap k _ (Coalgebra.counit (R := k) y) :=
        DFunLike.congr_fun (LieIdeal.pbwMap_quotient_comp_ideal I) y
      have hmap (z : UniversalEnvelopingAlgebra k I ⊗[k]
          UniversalEnvelopingAlgebra k I) :
          TensorProduct.map LinearMap.id proj.toLinearMap
              (TensorProduct.map inc.toLinearMap inc.toLinearMap z) =
            TensorProduct.map inc.toLinearMap
              (Algebra.linearMap k
                (UniversalEnvelopingAlgebra k (L ⧸ I)))
                (Coalgebra.counit (R := k).lTensor _ z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
            simpa only [map_add] using congrArg₂ (fun p q => p + q) hx hy
        | tmul x y =>
            simp only [TensorProduct.map_tmul, LinearMap.id_apply,
              LinearMap.lTensor_tmul]
            rw [show proj.toLinearMap (inc.toLinearMap y) =
                algebraMap k (UniversalEnvelopingAlgebra k (L ⧸ I))
                  (Coalgebra.counit (R := k) y) from
              hcounit y]
            simp
      rw [hmap]
      rw [Coalgebra.lTensor_counit_comul]
      simp
    · intro b hb
      let p : HopfAlgebraHom (k := k)
          (H := UniversalEnvelopingAlgebra k L)
          (UniversalEnvelopingAlgebra k (L ⧸ I)) :=
        { toAlgHom := proj
          map_counit := (ueaMapCoalgHom
            (LieIdeal.quotientMkLieHom I)).counit_comp
          map_comul := (ueaMapCoalgHom
            (LieIdeal.quotientMkLieHom I)).map_comp_comul }
      change b ∈ rightCoinvariants p at hb
      have hleft := leftCoaction_eq_of_mem_rightCoinvariants p b hb
      let θ := LieIdeal.extensionPBWCoalgEquiv I bQ bI
      let θinv := θ.symm.toLinearMap
      let a : UniversalEnvelopingAlgebra k I :=
        (TensorProduct.lid k (UniversalEnvelopingAlgebra k I))
          (Coalgebra.counit (R := k).rTensor _ (θinv b))
      have htransport :
          TensorProduct.map proj.toLinearMap θinv
              (Coalgebra.comul (R := k) b) =
            TensorProduct.map LinearMap.id θinv
              (TensorProduct.map proj.toLinearMap LinearMap.id
                (Coalgebra.comul (R := k) b)) := by
        have hmaps := LinearMap.congr_fun
          (TensorProduct.map_comp LinearMap.id θinv
            proj.toLinearMap LinearMap.id)
          (Coalgebra.comul (R := k) b)
        simpa only [LinearMap.id_comp, LinearMap.comp_id,
          LinearMap.comp_apply] using hmaps
      have hR := LinearMap.congr_fun
        (LieIdeal.extensionCoactionRetraction_eq_symm I bQ bI) b
      change LieIdeal.middleCounitContraction I
          (TensorProduct.map proj.toLinearMap θinv
            (Coalgebra.comul (R := k) b)) = θinv b at hR
      rw [htransport, hleft] at hR
      have hmiddle : LieIdeal.middleCounitContraction I
          (1 ⊗ₜ[k] θinv b) = 1 ⊗ₜ[k] a := by
        change LinearMap.lTensor _
            ((TensorProduct.lid k _).toLinearMap.comp
              (Coalgebra.counit (R := k).rTensor _))
              (1 ⊗ₜ[k] θinv b) = _
        rw [LinearMap.lTensor_tmul, LinearMap.comp_apply]
        rfl
      have hz : θinv b = 1 ⊗ₜ[k] a := by
        rw [TensorProduct.map_tmul, LinearMap.id_apply] at hR
        exact hR.symm.trans hmiddle
      refine ⟨a, ?_⟩
      change inc a = b
      have hinc : inc =
          UniversalEnvelopingAlgebra.pbwMap
            (LieIdeal.inclusionLieHom I) := by
        apply UniversalEnvelopingAlgebra.hom_ext
        apply DFunLike.ext _ _
        intro x
        change ueaMap (LieIdeal.inclusionLieHom I)
            (UniversalEnvelopingAlgebra.ι k x) =
          UniversalEnvelopingAlgebra.pbwMap (LieIdeal.inclusionLieHom I)
            (UniversalEnvelopingAlgebra.ι k x)
        rw [ueaMap_iota, UniversalEnvelopingAlgebra.pbwMap_iota]
      calc
        inc a = θ (1 ⊗ₜ[k] a) := by
          rw [hinc]
          rw [LieIdeal.extensionPBWCoalgEquiv_apply,
            LieIdeal.extensionPBWMap_tmul]
          have hsone : LieIdeal.ueaLinearSection I bQ bI 1 = 1 := by
            let word : UniversalEnvelopingAlgebra.PBWWord β := ⟨[], by simp⟩
            change LieIdeal.ueaLinearSection I bQ bI
              (UniversalEnvelopingAlgebra.orderedMonomial bQ word) = 1
            rw [LieIdeal.ueaLinearSection_orderedMonomial]
            simp [LieIdeal.liftedQuotientMonomial, word]
          rw [hsone, one_mul]
        _ = θ (θinv b) := by rw [hz]
        _ = b := θ.apply_symm_apply b

/-- The backward extension implication for Lie algebras, factored through
the cleft Hopf-extension theorem. -/
theorem isAmenableLieAlgebra_extension_of_components
    (I : LieIdeal k L)
    (hI : IsAmenableLieAlgebra (k := k) (L := I))
    (hQ : IsAmenableLieAlgebra (k := k) (L := L ⧸ I)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  classical
  let α := Module.Basis.ofVectorSpaceIndex k I
  let β := Module.Basis.ofVectorSpaceIndex k (L ⧸ I)
  let bI : Basis α k I := Module.Basis.ofVectorSpace k I
  let bQ : Basis β k (L ⧸ I) := Module.Basis.ofVectorSpace k (L ⧸ I)
  let _ : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  let e := LieIdeal.ueaCleftExactSequence I bQ bI
  rw [isAmenableLieAlgebra_iff_isAmenableHopfAlgebra]
  apply isAmenableHopfAlgebra_cleftExtension_of_components e
  · exact isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mp hI
  · exact isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mp hQ

/-- Public backward extension clause of Theorem G. -/
theorem isAmenableLieAlgebra_extension
    (I : LieIdeal k L)
    (hI : IsAmenableLieAlgebra (k := k) (L := I))
    (hQ : IsAmenableLieAlgebra (k := k) (L := L ⧸ I)) :
    IsAmenableLieAlgebra (k := k) (L := L) :=
  isAmenableLieAlgebra_extension_of_components I hI hQ

/-- The Lie-extension clause of Theorem G in iff form, obtained from the
Hopf cleft-extension equivalence. -/
theorem isAmenableLieAlgebra_extension_iff (I : LieIdeal k L) :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAmenableLieAlgebra (k := k) (L := I) ∧
        IsAmenableLieAlgebra (k := k) (L := L ⧸ I) := by
  constructor
  · exact IsAmenableLieAlgebra.extension_components I
  · rintro ⟨hI, hQ⟩
    exact isAmenableLieAlgebra_extension_of_components I hI hQ

#check isAmenableLieAlgebra_of_locallySubexponentialGrowth
#check isAmenableLieAlgebra_of_injective
#check isAmenableLieAlgebra_quotient
#check isAmenableLieAlgebra_extension_iff
#check isAmenableLieAlgebra_directedUnion

end

end HopfAmenability
