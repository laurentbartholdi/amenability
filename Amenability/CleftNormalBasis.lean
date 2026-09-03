/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfExactSequence
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Normal-basis infrastructure for cleft Hopf extensions

This file derives the convolution identities and coinvariant projections
used to prove the normal-basis theorem. No normal-basis equivalence is taken
as an assumption here.
-/

open Coalgebra LinearMap TensorProduct WithConv

namespace HopfAmenability

noncomputable section

universe u v w x

variable {k : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [Field k]
variable [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
variable [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
variable [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C]

variable (e : CleftExactSequence (k := k) A B C)

/-- Comultiplication, bundled as a Hopf morphism in the cocommutative case. -/
def comulHopfAlgebraHom :
    HopfAlgebraHom (k := k) (H := B) (B ⊗[k] B) where
  toAlgHom := (Bialgebra.comulBialgHom k B).toAlgHom
  map_counit := (Bialgebra.comulBialgHom k B).counit_comp
  map_comul := (Bialgebra.comulBialgHom k B).map_comp_comul

omit [Coalgebra.IsCocomm k B] in
/-- Hopf algebra morphisms commute with antipodes. -/
theorem HopfAlgebraHom.map_antipode
    {D : Type*} [Ring D] [HopfAlgebra k D]
    (f : HopfAlgebraHom (k := k) (H := B) D) :
  f.toAlgHom.toLinearMap.comp (HopfAlgebra.antipode k) =
      (HopfAlgebra.antipode k).comp f.toAlgHom.toLinearMap := by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv
    (a := toConv f.toAlgHom.toLinearMap)
  · calc
      toConv (f.toAlgHom.toLinearMap.comp (HopfAlgebra.antipode k)) *
          toConv f.toAlgHom.toLinearMap =
          toConv (f.toAlgHom.toLinearMap.comp (HopfAlgebra.antipode k)) *
            toConv (f.toAlgHom.toLinearMap.comp LinearMap.id) := by rfl
      _ = 1 := by
        apply WithConv.ofConv_injective
        calc
          _ = f.toAlgHom.toLinearMap.comp
              (toConv (HopfAlgebra.antipode k (A := B)) *
                toConv (LinearMap.id : B →ₗ[k] B)).ofConv := by
                  simpa only [WithConv.ofConv_toConv] using
                    (algHom_comp_convMul_distrib f.toAlgHom
                      (toConv (HopfAlgebra.antipode k (A := B)))
                      (toConv (LinearMap.id : B →ₗ[k] B))).symm
          _ = f.toAlgHom.toLinearMap.comp
              (1 : WithConv (B →ₗ[k] B)).ofConv := by
                rw [LinearMap.antipode_mul_id]
          _ = (1 : WithConv (B →ₗ[k] D)).ofConv :=
            LinearMap.algHom_comp_convOne f.toAlgHom
  · let fc : B →ₗc[k] D := {
      toLinearMap := f.toAlgHom.toLinearMap
      counit_comp := f.map_counit
      map_comp_comul := f.map_comul }
    apply WithConv.ofConv_injective
    calc
      (toConv f.toAlgHom.toLinearMap *
          toConv ((HopfAlgebra.antipode k).comp f.toAlgHom.toLinearMap)).ofConv =
          (toConv (LinearMap.id : D →ₗ[k] D) *
            toConv (HopfAlgebra.antipode k (A := D))).ofConv.comp
              fc.toLinearMap := by
                rw [convMul_comp_coalgHom_distrib]
                rfl
      _ = (1 : WithConv (D →ₗ[k] D)).ofConv.comp fc.toLinearMap := by
        rw [LinearMap.id_mul_antipode]
      _ = (1 : WithConv (B →ₗ[k] D)).ofConv :=
            LinearMap.convOne_comp_coalgHom fc

/-- In a cocommutative Hopf algebra, comultiplication commutes with the
antipode into the tensor-product Hopf algebra. -/
theorem comul_comp_antipode :
    (Coalgebra.comul (R := k) (A := B)).comp
        (HopfAlgebra.antipode k) =
      (HopfAlgebra.antipode k (A := B ⊗[k] B)).comp
        (Coalgebra.comul (R := k) (A := B)) := by
  have h := HopfAlgebraHom.map_antipode
    (f := comulHopfAlgebraHom (k := k) (B := B))
  change (Coalgebra.comul (R := k) (A := B)).comp
      (HopfAlgebra.antipode k) =
    (HopfAlgebra.antipode k (A := B ⊗[k] B)).comp
      (Coalgebra.comul (R := k) (A := B)) at h
  exact h

omit [Coalgebra.IsCocomm k B] in
/-- The three-fold antipode cancellation identity
`∑ S(b₍₁₎) b₍₂₎ ⊗ b₍₃₎ = 1 ⊗ b`. -/
theorem antipode_cancel_first_three (b : B) :
    TensorProduct.map
        (LinearMap.mul' k B ∘ₗ
          TensorProduct.map (HopfAlgebra.antipode k) LinearMap.id)
        LinearMap.id
      (((Coalgebra.comul (R := k) (A := B)).rTensor B)
        (Coalgebra.comul (R := k) b)) =
      1 ⊗ₜ[k] b := by
  let f : B ⊗[k] B →ₗ[k] B := LinearMap.mul' k B ∘ₗ
    TensorProduct.map (HopfAlgebra.antipode k) LinearMap.id
  have hf : f.comp (Coalgebra.comul (R := k) (A := B)) =
      (Algebra.linearMap k B).comp
        (Coalgebra.counit (R := k) (A := B)) := by
    simpa only [f, LinearMap.rTensor, LinearMap.comp_assoc] using
      (HopfAlgebra.mul_antipode_rTensor_comul (R := k) (A := B))
  change (f.rTensor B)
    (((Coalgebra.comul (R := k) (A := B)).rTensor B)
      (Coalgebra.comul (R := k) b)) = _
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hf,
    LinearMap.rTensor_comp, LinearMap.comp_apply,
    Coalgebra.rTensor_counit_comul]
  simp

omit [Coalgebra.IsCocomm k B] [Coalgebra.IsCocomm k C] in
/-- Antipode cancellation after applying a Hopf morphism to the first two
legs of the iterated coproduct. -/
theorem HopfAlgebraHom.antipode_cancel_first_three
    (p : HopfAlgebraHom (k := k) (H := B) C) (b : B) :
    TensorProduct.map
      (LinearMap.mul' k C ∘ₗ TensorProduct.map
        ((HopfAlgebra.antipode k).comp p.toAlgHom.toLinearMap)
        p.toAlgHom.toLinearMap) LinearMap.id
      (((Coalgebra.comul (R := k) (A := B)).rTensor B)
        (Coalgebra.comul (R := k) b)) = 1 ⊗ₜ[k] b := by
  let fB : B ⊗[k] B →ₗ[k] B := LinearMap.mul' k B ∘ₗ
    TensorProduct.map (HopfAlgebra.antipode k) LinearMap.id
  let fC : B ⊗[k] B →ₗ[k] C := LinearMap.mul' k C ∘ₗ
    TensorProduct.map ((HopfAlgebra.antipode k).comp
      p.toAlgHom.toLinearMap) p.toAlgHom.toLinearMap
  have hpS := HopfAlgebraHom.map_antipode (f := p)
  have hmaps :
      (TensorProduct.map p.toAlgHom.toLinearMap
        (LinearMap.id : B →ₗ[k] B)).comp
          (TensorProduct.map fB (LinearMap.id : B →ₗ[k] B)) =
        TensorProduct.map fC (LinearMap.id : B →ₗ[k] B) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw =>
        simpa only [map_add] using congrArg₂ (fun x y => x + y) hz hw
    | tmul xy z =>
      induction xy using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (fun x y => x + y) hx hy
      | tmul x y =>
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, fB, fC,
          LinearMap.mul'_apply, LinearMap.id_apply]
        apply congrArg (fun q : C => q ⊗ₜ[k] z)
        change p.toAlgHom ((HopfAlgebra.antipode k x) * y) = _
        rw [map_mul]
        exact congrArg₂ (fun x y => x * y)
          (LinearMap.congr_fun hpS x) rfl
  have h := congrArg (fun z =>
    TensorProduct.map p.toAlgHom.toLinearMap LinearMap.id z)
    (HopfAmenability.antipode_cancel_first_three (k := k) b)
  change (TensorProduct.map p.toAlgHom.toLinearMap LinearMap.id)
      ((TensorProduct.map fB LinearMap.id)
        (((Coalgebra.comul (R := k) (A := B)).rTensor B)
          (Coalgebra.comul (R := k) b))) = _ at h
  rw [← LinearMap.comp_apply, hmaps] at h
  change (TensorProduct.map fC LinearMap.id)
      (((Coalgebra.comul (R := k) (A := B)).rTensor B)
        (Coalgebra.comul (R := k) b)) = _ at h
  simpa [fC] using h

/-- The Hopf projection bundled as a coalgebra morphism. -/
def CleftExactSequence.projectionCoalgHom : B →ₗc[k] C where
  toLinearMap := e.projection.toAlgHom.toLinearMap
  counit_comp := e.projection.map_counit
  map_comp_comul := e.projection.map_comul

/-- The convolution inverse `S_B ∘ σ` of the coalgebra section. -/
def CleftExactSequence.sectionAntipode : C →ₗ[k] B :=
  (HopfAlgebra.antipode k).comp e.coalgebraSection.toLinearMap

theorem CleftExactSequence.sectionAntipode_conv_section :
    toConv e.sectionAntipode * toConv e.coalgebraSection.toLinearMap = 1 := by
  apply WithConv.ofConv_injective
  calc
    (toConv e.sectionAntipode *
        toConv e.coalgebraSection.toLinearMap).ofConv =
        (toConv (HopfAlgebra.antipode k (A := B)) *
          toConv (LinearMap.id : B →ₗ[k] B)).ofConv.comp
            e.coalgebraSection.toLinearMap := by
              rw [convMul_comp_coalgHom_distrib]
              rfl
    _ = (1 : WithConv (B →ₗ[k] B)).ofConv.comp
          e.coalgebraSection.toLinearMap := by rw [LinearMap.antipode_mul_id]
    _ = (1 : WithConv (C →ₗ[k] B)).ofConv :=
      LinearMap.convOne_comp_coalgHom e.coalgebraSection

theorem CleftExactSequence.section_conv_sectionAntipode :
    toConv e.coalgebraSection.toLinearMap * toConv e.sectionAntipode = 1 := by
  apply WithConv.ofConv_injective
  calc
    (toConv e.coalgebraSection.toLinearMap *
        toConv e.sectionAntipode).ofConv =
        (toConv (LinearMap.id : B →ₗ[k] B) *
          toConv (HopfAlgebra.antipode k (A := B))).ofConv.comp
            e.coalgebraSection.toLinearMap := by
              rw [convMul_comp_coalgHom_distrib]
              rfl
    _ = (1 : WithConv (B →ₗ[k] B)).ofConv.comp
          e.coalgebraSection.toLinearMap := by rw [LinearMap.id_mul_antipode]
    _ = (1 : WithConv (C →ₗ[k] B)).ofConv :=
      LinearMap.convOne_comp_coalgHom e.coalgebraSection

/-- The left-coinvariant projection
`ℓ(b) = ∑ (S ∘ σ ∘ π)(b₍₁₎) b₍₂₎`. -/
def CleftExactSequence.leftCoinvariantProjection : B →ₗ[k] B :=
  LinearMap.mul' k B ∘ₗ
    TensorProduct.map
      (e.sectionAntipode.comp e.projection.toAlgHom.toLinearMap)
      LinearMap.id ∘ₗ
    Coalgebra.comul

/-- The right normal-basis multiplication map before restricting its second
factor to the kernel Hopf algebra. -/
def CleftExactSequence.rightNormalBasisRaw : C ⊗[k] B →ₗ[k] B :=
  LinearMap.mul' k B ∘ₗ
    TensorProduct.map e.coalgebraSection.toLinearMap LinearMap.id

@[simp]
theorem CleftExactSequence.rightNormalBasisRaw_tmul (c : C) (b : B) :
    e.rightNormalBasisRaw (c ⊗ₜ[k] b) = e.coalgebraSection c * b :=
  rfl

/-- The raw inverse formula
`b ↦ ∑ π(b₍₁₎) ⊗ ℓ(b₍₂₎)`. -/
def CleftExactSequence.rightNormalBasisRawInverse : B →ₗ[k] C ⊗[k] B :=
  TensorProduct.map e.projection.toAlgHom.toLinearMap
      e.leftCoinvariantProjection ∘ₗ
    Coalgebra.comul

theorem CleftExactSequence.rightNormalBasisRaw_comp_inverse :
    e.rightNormalBasisRaw.comp e.rightNormalBasisRawInverse = LinearMap.id := by
  let f : B →ₗ[k] B :=
    e.coalgebraSection.toLinearMap.comp e.projection.toAlgHom.toLinearMap
  let g : B →ₗ[k] B :=
    e.sectionAntipode.comp e.projection.toAlgHom.toLinearMap
  have hfg : toConv f * toConv g = 1 := by
    apply WithConv.ofConv_injective
    calc
      (toConv f * toConv g).ofConv =
          (toConv e.coalgebraSection.toLinearMap *
            toConv e.sectionAntipode).ofConv.comp
              e.projection.toAlgHom.toLinearMap := by
                simpa [f, g, CleftExactSequence.projectionCoalgHom] using
                  (convMul_comp_coalgHom_distrib
                    (toConv e.coalgebraSection.toLinearMap)
                    (toConv e.sectionAntipode) e.projectionCoalgHom).symm
      _ = (1 : WithConv (C →ₗ[k] B)).ofConv.comp
            e.projection.toAlgHom.toLinearMap := by
              rw [congrArg WithConv.ofConv e.section_conv_sectionAntipode]
      _ = (1 : WithConv (B →ₗ[k] B)).ofConv :=
        by
          apply LinearMap.ext
          intro b
          change algebraMap k B
              (Coalgebra.counit (R := k) (e.projection.toAlgHom b)) =
            algebraMap k B (Coalgebra.counit (R := k) b)
          rw [show Coalgebra.counit (R := k) (e.projection.toAlgHom b) =
              Coalgebra.counit (R := k) b from
            LinearMap.congr_fun e.projection.map_counit b]
  calc
    e.rightNormalBasisRaw.comp e.rightNormalBasisRawInverse =
        (toConv f *
          (toConv g * toConv (LinearMap.id : B →ₗ[k] B))).ofConv := by
            apply LinearMap.ext
            intro b
            simp only [LinearMap.convMul_apply]
            simp only [CleftExactSequence.rightNormalBasisRaw,
              CleftExactSequence.rightNormalBasisRawInverse,
              CleftExactSequence.leftCoinvariantProjection,
              LinearMap.comp_apply, f, g]
            hopf_tensor_induction Coalgebra.comul (R := k) b with b₁ b₂
            simp [LinearMap.convMul_apply]
    _ = (toConv (LinearMap.id : B →ₗ[k] B)).ofConv := by
      rw [← mul_assoc, hfg, one_mul]
    _ = LinearMap.id := rfl

/-- The left `C`-coaction on `B`. -/
def CleftExactSequence.leftCoaction : B →ₗ[k] C ⊗[k] B :=
  TensorProduct.map e.projection.toAlgHom.toLinearMap LinearMap.id ∘ₗ
    Coalgebra.comul

/-- The trivial left coaction `b ↦ 1 ⊗ b`. -/
def leftTrivialCoaction : B →ₗ[k] C ⊗[k] B :=
  TensorProduct.mk k C B 1

@[simp]
theorem CleftExactSequence.projection_section_apply (c : C) :
    e.projection.toAlgHom (e.coalgebraSection c) = c := by
  exact LinearMap.congr_fun e.projection_section c

@[simp]
theorem CleftExactSequence.projection_section_linear_apply (c : C) :
    e.projection.toAlgHom (e.coalgebraSection.toLinearMap c) = c := by
  change (e.projection.toAlgHom.toLinearMap.comp
    e.coalgebraSection.toLinearMap) c = c
  rw [e.projection_section]
  rfl

/-- The four-leg cancellation identity specialized to the cleft section. -/
theorem CleftExactSequence.leftProjection_cancel_four (b : B) :
    let f : B ⊗[k] B →ₗ[k] C := LinearMap.mul' k C ∘ₗ
      TensorProduct.map
        ((HopfAlgebra.antipode k).comp
          e.projection.toAlgHom.toLinearMap)
        e.projection.toAlgHom.toLinearMap
    let g : B →ₗ[k] B := e.sectionAntipode.comp
      e.projection.toAlgHom.toLinearMap
    TensorProduct.map LinearMap.id
        (LinearMap.mul' k B ∘ₗ TensorProduct.map g LinearMap.id)
      (TensorProduct.map LinearMap.id
        (Coalgebra.comul (R := k) (A := B))
        (TensorProduct.map f LinearMap.id
          (((Coalgebra.comul (R := k) (A := B)).rTensor B)
            (Coalgebra.comul (R := k) b)))) =
      1 ⊗ₜ[k] e.leftCoinvariantProjection b := by
  dsimp only
  have h := congrArg (fun z =>
    TensorProduct.map LinearMap.id
      (LinearMap.mul' k B ∘ₗ TensorProduct.map
        (e.sectionAntipode.comp e.projection.toAlgHom.toLinearMap)
        LinearMap.id)
      (TensorProduct.map LinearMap.id
        (Coalgebra.comul (R := k) (A := B)) z))
    (e.projection.antipode_cancel_first_three b)
  simpa [CleftExactSequence.leftCoinvariantProjection] using h

/-- The contraction of the four coproduct legs used in the coinvariance
calculation. -/
def CleftExactSequence.leftProjectionFourMap :
    (B ⊗[k] B) ⊗[k] (B ⊗[k] B) →ₗ[k] C ⊗[k] B :=
  let f : B ⊗[k] B →ₗ[k] C := LinearMap.mul' k C ∘ₗ
    TensorProduct.map
      ((HopfAlgebra.antipode k).comp e.projection.toAlgHom.toLinearMap)
      e.projection.toAlgHom.toLinearMap
  let g : B →ₗ[k] B := e.sectionAntipode.comp
    e.projection.toAlgHom.toLinearMap
  TensorProduct.map f
    (LinearMap.mul' k B ∘ₗ TensorProduct.map g LinearMap.id)

/-- The iterated-map expression in `leftProjection_cancel_four` is the
four-leg contraction after applying comultiplication to both tensor legs. -/
theorem CleftExactSequence.leftProjectionFourMap_map_comul_comul :
    (TensorProduct.map LinearMap.id
        (LinearMap.mul' k B ∘ₗ TensorProduct.map
          (e.sectionAntipode.comp e.projection.toAlgHom.toLinearMap)
          LinearMap.id)).comp
      ((TensorProduct.map LinearMap.id
        (Coalgebra.comul (R := k) (A := B))).comp
        ((TensorProduct.map
          (LinearMap.mul' k C ∘ₗ TensorProduct.map
            ((HopfAlgebra.antipode k).comp
              e.projection.toAlgHom.toLinearMap)
            e.projection.toAlgHom.toLinearMap)
          LinearMap.id).comp
          ((Coalgebra.comul (R := k) (A := B)).rTensor B))) =
    e.leftProjectionFourMap.comp
      (TensorProduct.map (Coalgebra.comul (R := k) (A := B))
        (Coalgebra.comul (R := k) (A := B))) := by
  ext x y
  simp [CleftExactSequence.leftProjectionFourMap]

/-- Expanding the coaction of the convolution projection gives the same
four-leg contraction, now fed by the tensor-product coalgebra coproduct. -/
theorem CleftExactSequence.leftCoaction_mul_sectionAntipode :
    e.leftCoaction.comp
        (LinearMap.mul' k B ∘ₗ TensorProduct.map
          (e.sectionAntipode.comp e.projection.toAlgHom.toLinearMap)
          LinearMap.id) =
      e.leftProjectionFourMap.comp
        (Coalgebra.comul (R := k) (A := B ⊗[k] B)) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (fun x y => x + y) hz hw
  | tmul b₁ b₂ =>
    simp only [CleftExactSequence.leftCoaction,
      CleftExactSequence.leftProjectionFourMap,
      CleftExactSequence.sectionAntipode, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply]
    rw [Bialgebra.comul_mul]
    rw [TensorProduct.comul_tmul]
    have hs := LinearMap.congr_fun
      (comul_comp_antipode (k := k) (B := B))
      (e.coalgebraSection.toLinearMap
        (e.projection.toAlgHom.toLinearMap b₁))
    change Coalgebra.comul (R := k)
        (HopfAlgebra.antipode k
          (e.coalgebraSection.toLinearMap
            (e.projection.toAlgHom.toLinearMap b₁))) =
      HopfAlgebra.antipode k (A := B ⊗[k] B)
        (Coalgebra.comul (R := k)
          (e.coalgebraSection.toLinearMap
            (e.projection.toAlgHom.toLinearMap b₁))) at hs
    rw [hs]
    have hsection : Coalgebra.comul (R := k)
        (e.coalgebraSection.toLinearMap
          (e.projection.toAlgHom.toLinearMap b₁)) =
        TensorProduct.map e.coalgebraSection.toLinearMap
          e.coalgebraSection.toLinearMap
            (Coalgebra.comul (R := k)
              (e.projection.toAlgHom.toLinearMap b₁)) :=
      (LinearMap.congr_fun e.coalgebraSection.map_comp_comul
        (e.projection.toAlgHom.toLinearMap b₁)).symm
    rw [hsection]
    have hp : Coalgebra.comul (R := k)
        (e.projection.toAlgHom.toLinearMap b₁) =
        TensorProduct.map e.projection.toAlgHom.toLinearMap
          e.projection.toAlgHom.toLinearMap
            (Coalgebra.comul (R := k) b₁) :=
      (LinearMap.congr_fun e.projection.map_comul b₁).symm
    rw [hp]
    hopf_tensor_induction Coalgebra.comul (R := k) b₁ with x₁ x₂
    hopf_tensor_induction Coalgebra.comul (R := k) b₂ with y₁ y₂
    simp only [TensorProduct.antipode_def,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      AlgebraTensorModule.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, map_mul, LinearMap.id_coe,
      id_eq, AlgebraTensorModule.tensorTensorTensorComm_tmul,
      LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_toLinearMap,
      LinearMap.mul'_apply]
    have hmapS : e.projection.toAlgHom
        (HopfAlgebra.antipode k
          (e.coalgebraSection.toLinearMap
            (e.projection.toAlgHom x₁))) =
        HopfAlgebra.antipode k
          (e.projection.toAlgHom
            (e.coalgebraSection.toLinearMap
              (e.projection.toAlgHom x₁))) := by
      exact LinearMap.congr_fun
        (HopfAlgebraHom.map_antipode e.projection)
        (e.coalgebraSection.toLinearMap
          (e.projection.toAlgHom x₁))
    rw [hmapS, e.projection_section_linear_apply]

/-- The projection `ℓ` takes values in the left coinvariants. -/
theorem CleftExactSequence.leftCoaction_leftCoinvariantProjection (b : B) :
    e.leftCoaction (e.leftCoinvariantProjection b) =
      1 ⊗ₜ[k] e.leftCoinvariantProjection b := by
  let m : B ⊗[k] B →ₗ[k] B := LinearMap.mul' k B ∘ₗ
    TensorProduct.map
      (e.sectionAntipode.comp e.projection.toAlgHom.toLinearMap)
      LinearMap.id
  calc
    e.leftCoaction (e.leftCoinvariantProjection b) =
        (e.leftCoaction.comp m) (Coalgebra.comul (R := k) b) := by
      rfl
    _ = e.leftProjectionFourMap
        (Coalgebra.comul (R := k) (A := B ⊗[k] B)
          (Coalgebra.comul (R := k) b)) := by
      exact LinearMap.congr_fun e.leftCoaction_mul_sectionAntipode
        (Coalgebra.comul (R := k) b)
    _ = e.leftProjectionFourMap
        (TensorProduct.map (Coalgebra.comul (R := k) (A := B))
          (Coalgebra.comul (R := k) (A := B))
            (Coalgebra.comul (R := k) b)) := by
      apply congrArg e.leftProjectionFourMap
      exact (LinearMap.congr_fun
        (Coalgebra.comulCoalgHom k B).map_comp_comul b).symm
    _ = 1 ⊗ₜ[k] e.leftCoinvariantProjection b := by
      change (e.leftProjectionFourMap.comp
        (TensorProduct.map (Coalgebra.comul (R := k) (A := B))
          (Coalgebra.comul (R := k) (A := B))))
          (Coalgebra.comul (R := k) b) = _
      rw [← LinearMap.congr_fun
        e.leftProjectionFourMap_map_comul_comul
        (Coalgebra.comul (R := k) b)]
      exact e.leftProjection_cancel_four b

/-- In the cocommutative setting, the left-coinvariant projection also lies
in the right coinvariants used in the exactness hypothesis. -/
theorem CleftExactSequence.leftCoinvariantProjection_mem (b : B) :
    e.leftCoinvariantProjection b ∈ rightCoinvariants e.projection := by
  let x := e.leftCoinvariantProjection b
  have hleft : e.leftCoaction x = 1 ⊗ₜ[k] x :=
    e.leftCoaction_leftCoinvariantProjection b
  have hnat (z : B ⊗[k] B) :
      TensorProduct.map LinearMap.id e.projection.toAlgHom.toLinearMap
          ((TensorProduct.comm k B B).toLinearMap z) =
        (TensorProduct.comm k C B).toLinearMap
          (TensorProduct.map e.projection.toAlgHom.toLinearMap
            LinearMap.id z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (fun a b => a + b) hz hw
    | tmul y z => simp
  have hright :
      TensorProduct.map LinearMap.id e.projection.toAlgHom.toLinearMap
          (Coalgebra.comul (R := k) x) = x ⊗ₜ[k] 1 := by
    calc
      _ = TensorProduct.map LinearMap.id e.projection.toAlgHom.toLinearMap
          ((TensorProduct.comm k B B).toLinearMap
            (Coalgebra.comul (R := k) x)) := by
              exact congrArg
                (TensorProduct.map LinearMap.id
                  e.projection.toAlgHom.toLinearMap)
                (Coalgebra.comm_comul k x).symm
      _ = (TensorProduct.comm k C B).toLinearMap
          (TensorProduct.map e.projection.toAlgHom.toLinearMap LinearMap.id
            (Coalgebra.comul (R := k) x)) := hnat _
      _ = (TensorProduct.comm k C B).toLinearMap (1 ⊗ₜ[k] x) := by
        exact congrArg (TensorProduct.comm k C B).toLinearMap hleft
      _ = x ⊗ₜ[k] 1 := by simp
  change ((TensorProduct.map LinearMap.id
      e.projection.toAlgHom.toLinearMap).comp
        (Coalgebra.comul (R := k) (A := B)) -
      (TensorProduct.mk k B C).flip 1) x = 0
  simp [LinearMap.sub_apply, hright]

/-- The coinvariant projection, with codomain restricted to the image of the
kernel inclusion. -/
def CleftExactSequence.leftCoinvariantProjectionRange :
    B →ₗ[k] LinearMap.range e.inclusion.toAlgHom.toLinearMap :=
  e.leftCoinvariantProjection.codRestrict
    (LinearMap.range e.inclusion.toAlgHom.toLinearMap) fun b => by
      rw [e.coinvariants]
      exact e.leftCoinvariantProjection_mem b

/-- The `A`-valued coinvariant projection obtained from exactness and the
injectivity of the kernel inclusion. -/
def CleftExactSequence.leftCoinvariantLift : B →ₗ[k] A :=
  (LinearEquiv.ofInjective e.inclusion.toAlgHom.toLinearMap
    e.inclusion_injective).symm.toLinearMap.comp
      e.leftCoinvariantProjectionRange

@[simp]
theorem CleftExactSequence.inclusion_leftCoinvariantLift (b : B) :
    e.inclusion.toAlgHom.toLinearMap (e.leftCoinvariantLift b) =
      e.leftCoinvariantProjection b := by
  change e.inclusion.toAlgHom.toLinearMap
      ((LinearEquiv.ofInjective e.inclusion.toAlgHom.toLinearMap
        e.inclusion_injective).symm (e.leftCoinvariantProjectionRange b)) = _
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective e.inclusion.toAlgHom.toLinearMap
      e.inclusion_injective).apply_symm_apply
        (e.leftCoinvariantProjectionRange b))

/-- The derived right normal-basis multiplication map. -/
def CleftExactSequence.rightNormalBasisMap : C ⊗[k] A →ₗ[k] B :=
  e.rightNormalBasisRaw.comp
    (TensorProduct.map LinearMap.id e.inclusion.toAlgHom.toLinearMap)

@[simp]
theorem CleftExactSequence.rightNormalBasisMap_tmul (c : C) (a : A) :
    e.rightNormalBasisMap (c ⊗ₜ[k] a) =
      e.coalgebraSection c * e.inclusion a :=
  rfl

/-- The inverse formula `b ↦ ∑ π(b₍₁₎) ⊗ ℓ(b₍₂₎)`, with the
coinvariant second leg lifted uniquely to `A`. -/
def CleftExactSequence.rightNormalBasisInverse : B →ₗ[k] C ⊗[k] A :=
  TensorProduct.map e.projection.toAlgHom.toLinearMap
      e.leftCoinvariantLift ∘ₗ
    Coalgebra.comul

theorem CleftExactSequence.rightNormalBasisMap_comp_inverse :
    e.rightNormalBasisMap.comp e.rightNormalBasisInverse = LinearMap.id := by
  apply LinearMap.ext
  intro b
  have hraw := LinearMap.congr_fun e.rightNormalBasisRaw_comp_inverse b
  change e.rightNormalBasisRaw (e.rightNormalBasisRawInverse b) = b at hraw
  have hmaps :
      (TensorProduct.map LinearMap.id
          e.inclusion.toAlgHom.toLinearMap).comp
          (TensorProduct.map e.projection.toAlgHom.toLinearMap
            e.leftCoinvariantLift) =
        TensorProduct.map e.projection.toAlgHom.toLinearMap
          e.leftCoinvariantProjection := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (fun u v => u + v) hx hy
    | tmul x y => rw [LinearMap.comp_apply, TensorProduct.map_tmul,
        TensorProduct.map_tmul,
        LinearMap.id_coe, id_eq, e.inclusion_leftCoinvariantLift,
        TensorProduct.map_tmul]
  change e.rightNormalBasisRaw
      (TensorProduct.map LinearMap.id e.inclusion.toAlgHom.toLinearMap
        (e.rightNormalBasisInverse b)) = b
  calc
    _ = e.rightNormalBasisRaw (e.rightNormalBasisRawInverse b) := by
      apply congrArg e.rightNormalBasisRaw
      change ((TensorProduct.map LinearMap.id
          e.inclusion.toAlgHom.toLinearMap).comp
            (TensorProduct.map e.projection.toAlgHom.toLinearMap
              e.leftCoinvariantLift)) (Coalgebra.comul (R := k) b) = _
      rw [hmaps]
      rfl
    _ = b := hraw

theorem CleftExactSequence.leftCoinvariantProjection_section_mul_inclusion
    (c : C) (a : A) :
    e.leftCoinvariantProjection (e.coalgebraSection c * e.inclusion a) =
      algebraMap k B (Coalgebra.counit (R := k) c) * e.inclusion a := by
  let u : C →ₗ[k] B := e.sectionAntipode
  let v : C →ₗ[k] B := e.coalgebraSection.toLinearMap
  let j : A →ₗ[k] B := e.inclusion.toAlgHom.toLinearMap
  have huv : toConv u * toConv v = 1 := by
    simpa [u, v] using e.sectionAntipode_conv_section
  have honej : (1 : WithConv (A →ₗ[k] B)) * toConv j = toConv j := one_mul _
  calc
    e.leftCoinvariantProjection (e.coalgebraSection c * e.inclusion a) =
        (toConv u * toConv v).ofConv c *
          ((1 : WithConv (A →ₗ[k] B)) * toConv j).ofConv a := by
      simp only [CleftExactSequence.leftCoinvariantProjection,
        LinearMap.comp_apply, LinearMap.convMul_apply, u, v, j]
      rw [Bialgebra.comul_mul]
      have hs : Coalgebra.comul (R := k) (e.coalgebraSection c) =
          TensorProduct.map e.coalgebraSection.toLinearMap
            e.coalgebraSection.toLinearMap (Coalgebra.comul (R := k) c) :=
        (LinearMap.congr_fun e.coalgebraSection.map_comp_comul c).symm
      have hi : Coalgebra.comul (R := k) (e.inclusion a) =
          TensorProduct.map e.inclusion.toAlgHom.toLinearMap
            e.inclusion.toAlgHom.toLinearMap (Coalgebra.comul (R := k) a) :=
        (LinearMap.congr_fun e.inclusion.map_comul a).symm
      rw [hs, hi]
      hopf_tensor_induction Coalgebra.comul (R := k) c with c₁ c₂
      hopf_tensor_induction Coalgebra.comul (R := k) a with a₁ a₂
      simp only [TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, LinearMap.coe_comp,
        AlgHom.coe_toLinearMap, Function.comp_apply, map_mul,
        LinearMap.id_coe, id_eq,
        LinearMap.mul'_apply, LinearMap.convOne_apply]
      rw [e.projection_section_linear_apply, e.projection_inclusion]
      rw [show c₁ * algebraMap k C (Coalgebra.counit (R := k) a₁) =
          Coalgebra.counit (R := k) a₁ • c₁ by
        rw [Algebra.smul_def]
        exact (Algebra.commutes _ _).symm]
      rw [← Algebra.smul_def, map_smul]
      rw [Algebra.smul_def]
      let r := Coalgebra.counit (R := k) a₁
      let x := e.sectionAntipode c₁
      let y := e.coalgebraSection.toLinearMap c₂
      let z := e.inclusion.toAlgHom a₂
      change (algebraMap k B r * x) * (y * z) =
        (x * y) * (r • z)
      calc
        _ = algebraMap k B r * ((x * y) * z) := by simp only [mul_assoc]
        _ = ((x * y) * z) * algebraMap k B r := Algebra.commutes r _
        _ = (x * y) * (z * algebraMap k B r) := by simp only [mul_assoc]
        _ = _ := by rw [Algebra.smul_def, ← Algebra.commutes r z]
    _ = algebraMap k B (Coalgebra.counit (R := k) c) * e.inclusion a := by
      rw [huv, honej]
      rfl

theorem CleftExactSequence.leftCoinvariantLift_section_mul_inclusion
    (c : C) (a : A) :
    e.leftCoinvariantLift (e.coalgebraSection c * e.inclusion a) =
      Coalgebra.counit (R := k) c • a := by
  apply e.inclusion_injective
  change e.inclusion.toAlgHom.toLinearMap
      (e.leftCoinvariantLift (e.coalgebraSection c * e.inclusion a)) =
    e.inclusion.toAlgHom.toLinearMap (Coalgebra.counit (R := k) c • a)
  rw [e.inclusion_leftCoinvariantLift,
    e.leftCoinvariantProjection_section_mul_inclusion]
  simp [Algebra.smul_def]

theorem CleftExactSequence.leftCoinvariantLift_sectionLinear_mul_inclusion
    (c : C) (a : A) :
    e.leftCoinvariantLift
        (e.coalgebraSection.toLinearMap c * e.inclusion a) =
      Coalgebra.counit (R := k) c • a := by
  change e.leftCoinvariantLift
      (e.coalgebraSection c * e.inclusion a) = _
  exact e.leftCoinvariantLift_section_mul_inclusion c a

theorem CleftExactSequence.rightNormalBasisInverse_map_tmul
    (c : C) (a : A) :
    e.rightNormalBasisInverse (e.rightNormalBasisMap (c ⊗ₜ[k] a)) =
      c ⊗ₜ[k] a := by
  change (TensorProduct.map e.projection.toAlgHom.toLinearMap
      e.leftCoinvariantLift)
      (Coalgebra.comul (R := k)
        (e.coalgebraSection c * e.inclusion a)) = c ⊗ₜ[k] a
  rw [Bialgebra.comul_mul]
  have hs : Coalgebra.comul (R := k) (e.coalgebraSection c) =
      TensorProduct.map e.coalgebraSection.toLinearMap
        e.coalgebraSection.toLinearMap (Coalgebra.comul (R := k) c) :=
    (LinearMap.congr_fun e.coalgebraSection.map_comp_comul c).symm
  have hi : Coalgebra.comul (R := k) (e.inclusion a) =
      TensorProduct.map e.inclusion.toAlgHom.toLinearMap
        e.inclusion.toAlgHom.toLinearMap (Coalgebra.comul (R := k) a) :=
    (LinearMap.congr_fun e.inclusion.map_comul a).symm
  rw [hs, hi]
  have hc : (TensorProduct.rid k C)
      (Coalgebra.counit (R := k).lTensor C
        (Coalgebra.comul (R := k) c)) = c := by simp
  have ha : (TensorProduct.lid k A)
      (Coalgebra.counit (R := k).rTensor A
        (Coalgebra.comul (R := k) a)) = a := by simp
  conv_rhs => rw [← hc, ← ha]
  hopf_tensor_induction Coalgebra.comul (R := k) c with c₁ c₂
  hopf_tensor_induction Coalgebra.comul (R := k) a with a₁ a₂
  simp only [TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, map_mul,
    LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul, LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul, TensorProduct.tmul_smul]
  rw [e.projection_section_linear_apply, e.projection_inclusion,
    e.leftCoinvariantLift_sectionLinear_mul_inclusion]
  rw [show c₁ * algebraMap k C (Coalgebra.counit (R := k) a₁) =
      Coalgebra.counit (R := k) a₁ • c₁ by
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm]
  calc
    _ = (Coalgebra.counit (R := k) c₂ •
          (Coalgebra.counit (R := k) a₁ • c₁)) ⊗ₜ[k] a₂ := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    _ = _ := by
      apply congrArg (fun z : C => z ⊗ₜ[k] a₂)
      exact smul_comm _ _ _

theorem CleftExactSequence.rightNormalBasisInverse_comp_map :
    e.rightNormalBasisInverse.comp e.rightNormalBasisMap = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun u v => u + v) hx hy
  | tmul c a => exact e.rightNormalBasisInverse_map_tmul c a

/-- The right normal-basis linear equivalence derived from intrinsic
cleft-exact-sequence data. -/
def CleftExactSequence.rightNormalBasisLinearEquiv :
    C ⊗[k] A ≃ₗ[k] B where
  toLinearMap := e.rightNormalBasisMap
  invFun := e.rightNormalBasisInverse
  left_inv := LinearMap.congr_fun e.rightNormalBasisInverse_comp_map
  right_inv := LinearMap.congr_fun e.rightNormalBasisMap_comp_inverse

/-- The derived normal-basis multiplication map as a coalgebra morphism. -/
noncomputable def CleftExactSequence.rightNormalBasisCoalgHom :
    C ⊗[k] A →ₗc[k] B :=
  (Bialgebra.mulCoalgHom k B).comp
    (Coalgebra.TensorProduct.map e.coalgebraSection
      e.inclusion.toCoalgHom)

@[simp]
theorem CleftExactSequence.rightNormalBasisCoalgHom_tmul
    (c : C) (a : A) :
    e.rightNormalBasisCoalgHom (c ⊗ₜ[k] a) =
      e.coalgebraSection c * e.inclusion a :=
  rfl

/-- The right normal-basis coalgebra equivalence, proved from the intrinsic
cleft data rather than stored as an assumption. -/
noncomputable def CleftExactSequence.rightNormalBasis :
    C ⊗[k] A ≃ₗc[k] B :=
  CoalgEquiv.ofBijective
    (f := e.rightNormalBasisCoalgHom)
    (by
      have hfun : (e.rightNormalBasisCoalgHom : C ⊗[k] A → B) =
          e.rightNormalBasisLinearEquiv := by
        funext z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
            simpa only [map_add] using congrArg₂ (fun u v => u + v) hx hy
        | tmul c a => rfl
      rw [hfun]
      exact e.rightNormalBasisLinearEquiv.bijective)

@[simp]
theorem CleftExactSequence.rightNormalBasis_tmul (c : C) (a : A) :
    e.rightNormalBasis (c ⊗ₜ[k] a) =
      e.coalgebraSection c * e.inclusion a :=
  rfl

@[simp]
theorem CleftExactSequence.rightNormalBasis_linear_tmul (c : C) (a : A) :
    e.rightNormalBasis.toLinearMap (c ⊗ₜ[k] a) =
      e.coalgebraSection.toLinearMap c * e.inclusion.toAlgHom a :=
  rfl

@[simp]
theorem CleftExactSequence.rightNormalBasis_symm_sectionLinear_mul_inclusion
    (c : C) (a : A) :
    e.rightNormalBasis.symm
        (e.coalgebraSection.toLinearMap c * e.inclusion.toAlgHom a) =
      c ⊗ₜ[k] a := by
  rw [← e.rightNormalBasis_linear_tmul]
  exact e.rightNormalBasis.symm_apply_apply _

@[simp]
theorem CleftExactSequence.rightNormalBasis_symm_section_mul_inclusion
    (c : C) (a : A) :
    e.rightNormalBasis.symm (e.coalgebraSection c * e.inclusion a) =
      c ⊗ₜ[k] a := by
  rw [← e.rightNormalBasis_tmul]
  exact e.rightNormalBasis.symm_apply_apply _

/-- Under the right normal-basis coordinates, the quotient map is counit on
the kernel factor. -/
theorem CleftExactSequence.projection_rightNormalBasis_tmul
    (c : C) (a : A) :
    e.projection.toAlgHom (e.rightNormalBasis (c ⊗ₜ[k] a)) =
      Coalgebra.counit (R := k) a • c := by
  change e.projection.toAlgHom
      (e.coalgebraSection c * e.inclusion a) = _
  rw [map_mul, e.projection_section_apply, e.projection_inclusion]
  rw [Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

/-- In right normal-basis coordinates, the left quotient coaction is the
regular coaction on the `C` factor. -/
theorem CleftExactSequence.leftCoaction_rightNormalBasis_tmul
    (c : C) (a : A) :
    e.leftCoaction (e.rightNormalBasis (c ⊗ₜ[k] a)) =
      (TensorProduct.map LinearMap.id e.rightNormalBasis.toLinearMap)
        ((TensorProduct.assoc k C C A)
          (Coalgebra.comul (R := k) c ⊗ₜ[k] a)) := by
  change (TensorProduct.map e.projection.toAlgHom.toLinearMap LinearMap.id)
      (Coalgebra.comul (R := k)
        (e.coalgebraSection c * e.inclusion a)) = _
  rw [Bialgebra.comul_mul]
  have hs : Coalgebra.comul (R := k) (e.coalgebraSection c) =
      TensorProduct.map e.coalgebraSection.toLinearMap
        e.coalgebraSection.toLinearMap (Coalgebra.comul (R := k) c) :=
    (LinearMap.congr_fun e.coalgebraSection.map_comp_comul c).symm
  have hi : Coalgebra.comul (R := k) (e.inclusion a) =
      TensorProduct.map e.inclusion.toAlgHom.toLinearMap
        e.inclusion.toAlgHom.toLinearMap (Coalgebra.comul (R := k) a) :=
    (LinearMap.congr_fun e.inclusion.map_comul a).symm
  rw [hs, hi]
  have ha : (TensorProduct.lid k A)
      (Coalgebra.counit (R := k).rTensor A
        (Coalgebra.comul (R := k) a)) = a := by simp
  conv_rhs => rw [← ha]
  hopf_tensor_induction Coalgebra.comul (R := k) c with c₁ c₂
  hopf_tensor_induction Coalgebra.comul (R := k) a with a₁ a₂
  simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, map_mul,
    e.projection_section_linear_apply, e.projection_inclusion,
    LinearMap.id_coe, id_eq, LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul, TensorProduct.assoc_tmul]
  rw [show c₁ * algebraMap k C (Coalgebra.counit (R := k) a₁) =
      Coalgebra.counit (R := k) a₁ • c₁ by
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm]
  rw [e.rightNormalBasis_linear_tmul, map_smul, mul_smul_comm,
    TensorProduct.tmul_smul]
  rw [TensorProduct.smul_tmul']


end

end HopfAmenability
