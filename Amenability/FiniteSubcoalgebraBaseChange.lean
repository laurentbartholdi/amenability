/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CoalgebraBaseChange
import Amenability.CompleteSubcoalgebraFlag
import Amenability.SubcoalgebraCoalgHom
import Amenability.SubcoalgebraAmbient
import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Finite subcoalgebras under scalar extension
-/

open Coalgebra Module TensorProduct

namespace UnifiedRounding

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {H : Type w}
variable [Field k] [Field K] [Algebra k K]
variable [AddCommGroup H] [Module k H] [Coalgebra k H]

namespace FiniteSubcoalgebra

/-- Scalar extension of a finite subcoalgebra. -/
noncomputable def baseChange (C : FiniteSubcoalgebra k H) (K : Type v)
    [Field K] [Algebra k K] : FiniteSubcoalgebra K (K ⊗[k] H) where
  carrier := UnifiedRounding.baseChangeSubspace (k := k) K C.carrier
  isSubcoalgebra := isSubcoalgebra_baseChangeSubspace C.carrier C.isSubcoalgebra
  finiteDimensional := by
    let f := C.carrier.subtype.baseChange K
    exact FiniteDimensional.of_surjective f.rangeRestrict (by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩)

@[simp]
theorem baseChange_carrier (C : FiniteSubcoalgebra k H) :
    (C.baseChange K).carrier =
      UnifiedRounding.baseChangeSubspace (k := k) K C.carrier := rfl

/-- The canonical scalar-extended inclusion into the ambient coalgebra. -/
noncomputable def baseChangeInclusion (C : FiniteSubcoalgebra k H) :
    K ⊗[k] C.carrier →ₗc[K] K ⊗[k] H :=
  Coalgebra.TensorProduct.map (CoalgHom.id K K)
    (subcoalgebraInclusion C.carrier C.isSubcoalgebra)

theorem baseChangeInclusion_toLinearMap (C : FiniteSubcoalgebra k H) :
    (C.baseChangeInclusion (K := K)).toLinearMap =
      C.carrier.subtype.baseChange K := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz hz'
  | tmul a x => rfl

/-- The scalar extension is coalgebra-equivalent to the carrier of its image. -/
noncomputable def baseChangeCarrierEquiv (C : FiniteSubcoalgebra k H) :
    K ⊗[k] C.carrier ≃ₗc[K] (C.baseChange K).carrier := by
  let f : K ⊗[k] C.carrier →ₗc[K] (C.baseChange K).carrier :=
    CoalgHom.codRestrictSubcoalgebra
      (C.baseChangeInclusion (K := K)) (C.baseChange K).carrier
      (C.baseChange K).isSubcoalgebra (fun z ↦ by
        change (C.baseChangeInclusion (K := K)) z ∈
          LinearMap.range (C.carrier.subtype.baseChange K)
        rw [← C.baseChangeInclusion_toLinearMap]
        exact ⟨z, rfl⟩)
  have hinc : Function.Injective (C.baseChangeInclusion (K := K)) := by
    rw [show Function.Injective (C.baseChangeInclusion (K := K)) ↔
      Function.Injective (C.baseChangeInclusion (K := K)).toLinearMap from Iff.rfl,
      C.baseChangeInclusion_toLinearMap]
    exact Module.Flat.lTensor_preserves_injective_linearMap
      C.carrier.subtype C.carrier.injective_subtype
  refine CoalgEquiv.ofBijective (f := f) ⟨?_, ?_⟩
  · intro x y hxy
    apply hinc
    exact congrArg Subtype.val hxy
  · intro y
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    dsimp [f]
    change (C.baseChangeInclusion (K := K)).toLinearMap x = (y : K ⊗[k] H)
    rw [C.baseChangeInclusion_toLinearMap]
    exact hx

@[simp]
theorem coe_baseChangeCarrierEquiv
    (C : FiniteSubcoalgebra k H) (x : K ⊗[k] C.carrier) :
    (((C.baseChangeCarrierEquiv (K := K)) x :
      (C.baseChange K).carrier) : K ⊗[k] H) =
      C.carrier.subtype.baseChange K x := by
  unfold baseChangeCarrierEquiv
  rfl

/-- Scalar extension of an internal subspace, transported to the image carrier. -/
noncomputable def baseChangeSubspace
    (C : FiniteSubcoalgebra k H) (K : Type v)
    [Field K] [Algebra k K] (U : Submodule k C.carrier) :
    Submodule K (C.baseChange K).carrier :=
  (UnifiedRounding.baseChangeSubspace (k := k) K U).map
    (C.baseChangeCarrierEquiv (K := K)).toLinearMap

theorem sfinrank_baseChangeSubspace_internal
    (C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) :
    finrank K (C.baseChangeSubspace K U) = finrank k U := by
  calc
    finrank K (C.baseChangeSubspace K U) =
        finrank K (UnifiedRounding.baseChangeSubspace (k := k) K U) :=
      (C.baseChangeCarrierEquiv (K := K)).toLinearEquiv.finrank_map_eq _
    _ = finrank k U := UnifiedRounding.sfinrank_baseChangeSubspace U

theorem ambientImage_baseChangeSubspace_internal
    (C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) :
    ambientImage (C.baseChange K).carrier (C.baseChangeSubspace K U) =
      UnifiedRounding.baseChangeSubspace (k := k) K
        (ambientImage C.carrier U) := by
  let e := ambientImageEquiv C.carrier U
  let eK := LinearEquiv.baseChange k K U (ambientImage C.carrier U) e
  ext z
  constructor
  · rintro ⟨y, ⟨x, ⟨q, rfl⟩, rfl⟩, rfl⟩
    refine ⟨eK q, ?_⟩
    induction q using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add q q' hq hq' => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hq hq'
    | tmul a u => rfl
  · rintro ⟨q, rfl⟩
    let q' := eK.symm q
    refine ⟨(C.baseChangeCarrierEquiv (K := K))
      (U.subtype.baseChange K q'), ?_, ?_⟩
    · exact ⟨U.subtype.baseChange K q', ⟨q', rfl⟩, rfl⟩
    · change ((((C.baseChangeCarrierEquiv (K := K))
          (U.subtype.baseChange K q')) : (C.baseChange K).carrier) :
          K ⊗[k] H) = _
      rw [coe_baseChangeCarrierEquiv]
      change C.carrier.subtype.baseChange K (U.subtype.baseChange K q') =
        (ambientImage C.carrier U).subtype.baseChange K q
      subst q'
      induction q using TensorProduct.induction_on with
      | zero => simp [eK]
      | add q q' hq hq' => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hq hq'
      | tmul a u =>
          simp only [eK, LinearEquiv.baseChange_symm_tmul,
            LinearMap.baseChange_tmul]
          congr 1
          have hu := coe_ambientImageEquiv C.carrier U (e.symm u)
          rw [e.apply_symm_apply] at hu
          exact hu.symm

end FiniteSubcoalgebra

/-- Scalar extension preserves the dimension of intersections. -/
theorem sfinrank_inf_baseChangeSubspace
    {V : Type w} [AddCommGroup V] [Module k V]
    (P Q : Submodule k V)
    [FiniteDimensional k P] [FiniteDimensional k Q] :
    sfinrank K
        (baseChangeSubspace (k := k) K P ⊓
          baseChangeSubspace (k := k) K Q) =
      sfinrank k (P ⊓ Q) := by
  let PQ : Submodule k V := P ⊔ Q
  let : FiniteDimensional k PQ := by infer_instance
  let : FiniteDimensional K (baseChangeSubspace (k := k) K P) := by
    rw [baseChangeSubspace]
    infer_instance
  let : FiniteDimensional K (baseChangeSubspace (k := k) K Q) := by
    rw [baseChangeSubspace]
    infer_instance
  have hk := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hK := Submodule.finrank_sup_add_finrank_inf_eq
    (baseChangeSubspace (k := k) K P) (baseChangeSubspace (k := k) K Q)
  rw [← baseChangeSubspace_sup] at hK
  have hPdim := sfinrank_baseChangeSubspace (K := K) P
  have hQdim := sfinrank_baseChangeSubspace (K := K) Q
  have hPQdim := sfinrank_baseChangeSubspace (K := K) PQ
  dsimp [PQ] at hPQdim
  unfold sfinrank at *
  omega

section Algebra

variable {A : Type w} [Ring A] [Algebra k A]

/-- Products of subspaces commute with scalar extension. -/
theorem baseChangeSubspace_mul (P Q : Submodule k A) :
    UnifiedRounding.baseChangeSubspace (k := k) K
        (P * Q : Submodule k A) =
      (UnifiedRounding.baseChangeSubspace (k := k) K P :
        Submodule K (K ⊗[k] A)) *
        (UnifiedRounding.baseChangeSubspace (k := k) K Q :
          Submodule K (K ⊗[k] A)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        rw [map_add]
        exact Submodule.add_mem _ hz hz'
    | tmul a r =>
        have hr : (r : A) ∈ LinearMap.range (Submodule.mulMap P Q) := by
          rw [Submodule.mulMap_range]
          exact r.2
        rcases hr with ⟨q, hq⟩
        change a ⊗ₜ[k] (r : A) ∈ _
        rw [← hq]
        clear hq r
        induction q using TensorProduct.induction_on with
        | zero => simp
        | add q q' hq hq' => simpa only [map_add, tmul_add] using
            (Submodule.add_mem _ hq hq')
        | tmul p q =>
            have hp : a ⊗ₜ[k] (p : A) ∈ baseChangeSubspace (k := k) K P :=
              ⟨a ⊗ₜ[k] p, rfl⟩
            have hq : (1 : K) ⊗ₜ[k] (q : A) ∈
                baseChangeSubspace (k := k) K Q :=
              ⟨(1 : K) ⊗ₜ[k] q, rfl⟩
            convert Submodule.mul_mem_mul hp hq using 1
            all_goals simp
  · rw [← Submodule.mulMap_range]
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simpa only [map_add] using Submodule.add_mem _ hz hz'
    | tmul x y =>
        rcases x.2 with ⟨qx, hqx⟩
        rcases y.2 with ⟨qy, hqy⟩
        have hmul (qx : K ⊗[k] P) (qy : K ⊗[k] Q) :
            (P.subtype.baseChange K qx) * (Q.subtype.baseChange K qy) ∈
              UnifiedRounding.baseChangeSubspace (k := k) K (P * Q) := by
          induction qx using TensorProduct.induction_on with
          | zero => simp
          | add qx qx' hx hx' =>
              simpa only [map_add, add_mul] using
                (Submodule.add_mem _ hx hx')
          | tmul a p =>
              induction qy using TensorProduct.induction_on with
              | zero => simp
              | add qy qy' hy hy' =>
                  simpa only [map_add, mul_add] using
                    (Submodule.add_mem _ hy hy')
              | tmul b q =>
                  refine ⟨(a * b) ⊗ₜ[k]
                    (⟨(p : A) * (q : A), Submodule.mul_mem_mul p.2 q.2⟩ : P * Q), ?_⟩
                  simp
        change (x : K ⊗[k] A) * (y : K ⊗[k] A) ∈ _
        rw [← hqx, ← hqy]
        exact hmul qx qy

end Algebra

namespace FiniteSubcoalgebra

variable [FiniteDimensional k K] [Coalgebra.IsCocomm k H]

/-- Semistability transported to the carrier of a base-changed finite subcoalgebra. -/
theorem semistable_baseChange
    (C : FiniteSubcoalgebra k H) (U : Submodule k C.carrier) (t : ℚ)
    (hsem : ∀ B : Submodule k C.carrier,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C.carrier : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B))
    (B : Submodule K (C.baseChange K).carrier)
    (hB : IsSubcoalgebra (k := K) (H := (C.baseChange K).carrier) B) :
    t * ((finrank K (C.baseChange K).carrier : ℚ) - finrank K B) ≤
      (finrank K (C.baseChangeSubspace K U) : ℚ) -
        finrank K (C.baseChangeSubspace K U ⊓ B :
          Submodule K (C.baseChange K).carrier) := by
  let e := C.baseChangeCarrierEquiv (K := K)
  let U₀ := UnifiedRounding.baseChangeSubspace (k := k) K U
  let Z : Submodule K (K ⊗[k] C.carrier) := B.map e.symm.toLinearMap
  have hZ : IsSubcoalgebra (k := K) Z :=
    hB.map_coalgHom e.symm.toCoalgHom
  have hmain := UnifiedRounding.semistable_baseChange
    (K := K) U t hsem Z hZ
  have hZmap : Z.map e.toLinearMap = B := by
    ext x
    constructor
    · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
      rw [show e.toLinearMap (e.symm.toLinearMap b) = b from
        e.apply_symm_apply b]
      exact hb
    · intro hx
      refine ⟨e.symm x, ⟨x, hx, rfl⟩, ?_⟩
      exact e.apply_symm_apply x
  have hUmap : U₀.map e.toLinearMap = C.baseChangeSubspace K U := rfl
  have hInfMap : (U₀ ⊓ Z).map e.toLinearMap =
      C.baseChangeSubspace K U ⊓ B := by
    calc
      _ = U₀.map e.toLinearMap ⊓ Z.map e.toLinearMap :=
        by
          apply le_antisymm
          · rintro _ ⟨x, hx, rfl⟩
            exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
          · rintro y ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
            have hxz : x = z := e.injective (hxy.trans hzy.symm)
            subst z
            exact ⟨x, ⟨hx, hz⟩, hxy⟩
      _ = _ := by rw [hUmap, hZmap]
  have hCKdim : finrank K (K ⊗[k] C.carrier) =
      finrank K (C.baseChange K).carrier := e.toLinearEquiv.finrank_eq
  have hZdim : finrank K Z = finrank K B := by
    rw [← hZmap]
    exact (e.toLinearEquiv.finrank_map_eq Z).symm
  have hUdim : finrank K U₀ = finrank K (C.baseChangeSubspace K U) := by
    rw [← hUmap]
    exact (e.toLinearEquiv.finrank_map_eq U₀).symm
  have hInfDim : finrank K (U₀ ⊓ Z : Submodule K (K ⊗[k] C.carrier)) =
      finrank K (C.baseChangeSubspace K U ⊓ B :
        Submodule K (C.baseChange K).carrier) := by
    rw [← hInfMap]
    exact (e.toLinearEquiv.finrank_map_eq (U₀ ⊓ Z)).symm
  dsimp [U₀] at hUdim hInfDim
  unfold sfinrank at hmain
  rw [hCKdim, hZdim, hUdim, hInfDim] at hmain
  convert hmain using 1
  congr 1

end FiniteSubcoalgebra

end

end UnifiedRounding
