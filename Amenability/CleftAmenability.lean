/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.CleftNormalBasis
import Amenability.HopfModuleMap
import Amenability.TheoremB
import Amenability.TheoremD

/-!
# Amenability of cleft Hopf extensions

This file proves the Følner theorem for the intrinsic cleft-exact-sequence
data.  Its normal-basis equivalence is derived in `CleftNormalBasis`.
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w x

variable {k : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [Field k]
variable [Ring A] [HopfAlgebra k A] [IsCocomm k A]
variable [Ring B] [HopfAlgebra k B] [IsCocomm k B]
variable [Ring C] [HopfAlgebra k C] [IsCocomm k C]
variable (e : CleftExactSequence (k := k) A B C)

/-- Contract the middle `C` factor in `C ⊗ (C ⊗ A)` by the counit. -/
def CleftExactSequence.middleCounitContraction
    (_e : CleftExactSequence (k := k) A B C) :
    C ⊗[k] (C ⊗[k] A) →ₗ[k] C ⊗[k] A :=
  LinearMap.lTensor C
    ((TensorProduct.lid k A).toLinearMap.comp
      (Coalgebra.counit (R := k).rTensor A))

@[simp]
theorem CleftExactSequence.middleCounitContraction_tmul
    (c d : C) (a : A) :
    e.middleCounitContraction (c ⊗ₜ[k] (d ⊗ₜ[k] a)) =
      c ⊗ₜ[k] (Coalgebra.counit (R := k) d • a) := by
  simp [CleftExactSequence.middleCounitContraction]

/-- Applying the inverse normal-basis map to the second coaction factor and
then contracting recovers the inverse normal-basis coordinates. -/
theorem CleftExactSequence.coactionRetraction_eq_inverse :
    e.middleCounitContraction.comp
        ((TensorProduct.map LinearMap.id
          e.rightNormalBasis.symm.toLinearMap).comp e.leftCoaction) =
      e.rightNormalBasis.symm.toLinearMap := by
  apply LinearMap.ext
  intro b
  obtain ⟨z, rfl⟩ := e.rightNormalBasis.surjective b
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simpa only [map_add] using congrArg₂ (fun p q => p + q) hz hz'
  | tmul c a =>
      simp only [LinearMap.comp_apply]
      change e.middleCounitContraction
          (TensorProduct.map LinearMap.id
            e.rightNormalBasis.symm.toLinearMap
              (e.leftCoaction (e.rightNormalBasis (c ⊗ₜ[k] a)))) = _
      rw [e.leftCoaction_rightNormalBasis_tmul]
      have hr : e.rightNormalBasis.symm.toLinearMap
          (e.rightNormalBasis.toLinearEquiv (c ⊗ₜ[k] a)) = c ⊗ₜ[k] a :=
        e.rightNormalBasis.symm_apply_apply _
      rw [hr]
      have hc : (TensorProduct.rid k C)
          (Coalgebra.counit (R := k).lTensor C
            (Coalgebra.comul (R := k) c)) = c := by simp
      conv_rhs => rw [← hc]
      hopf_tensor_induction Coalgebra.comul (R := k) c with c₁ c₂
      have hinv : e.rightNormalBasis.symm.toLinearMap
          (e.coalgebraSection.toLinearMap c₂ * e.inclusion.toAlgHom a) =
            c₂ ⊗ₜ[k] a := by
        change e.rightNormalBasis.symm
          (e.coalgebraSection c₂ * e.inclusion a) = c₂ ⊗ₜ[k] a
        rw [← e.rightNormalBasis_tmul]
        exact e.rightNormalBasis.symm_apply_apply _
      simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul,
        LinearMap.id_coe, id_eq, e.rightNormalBasis_linear_tmul]
      rw [hinv]
      simp [CleftExactSequence.middleCounitContraction,
        TensorProduct.smul_tmul]

/-- If the quotient coaction of `b` has first tensor factor in `P`, then the
inverse normal-basis coordinates of `b` lie in `P ⊗ A`. -/
theorem CleftExactSequence.rightNormalBasis_symm_mem_of_leftCoaction_mem
    (P : Submodule k C) (b : B)
    (hb : e.leftCoaction b ∈ tensorProductSubspace P ⊤) :
    e.rightNormalBasis.symm b ∈ tensorProductSubspace P ⊤ := by
  let transported : C ⊗[k] B →ₗ[k] C ⊗[k] (C ⊗[k] A) :=
    TensorProduct.map LinearMap.id e.rightNormalBasis.symm.toLinearMap
  have htransported : transported (e.leftCoaction b) ∈
      tensorProductSubspace P ⊤ := by
    apply (show tensorProductSubspace P ⊤ ≤
      (tensorProductSubspace P ⊤).comap transported by
        apply Submodule.map₂_le.2
        intro c hc y hy
        change transported (c ⊗ₜ[k] y) ∈ tensorProductSubspace P ⊤
        rw [TensorProduct.map_tmul]
        exact Submodule.mem_map₂ (TensorProduct.mk k _ _) P ⊤ hc trivial)
    exact hb
  have hcontracted : e.middleCounitContraction
      (transported (e.leftCoaction b)) ∈ tensorProductSubspace P ⊤ := by
    let Good : Submodule k (C ⊗[k] (C ⊗[k] A)) :=
      (tensorProductSubspace P ⊤).comap e.middleCounitContraction
    apply (show tensorProductSubspace P ⊤ ≤ Good by
      apply Submodule.map₂_le.2
      intro c hc z hz
      change e.middleCounitContraction (c ⊗ₜ[k] z) ∈
        tensorProductSubspace P ⊤
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' =>
          simpa only [TensorProduct.tmul_add, map_add] using
            (tensorProductSubspace P ⊤).add_mem hz hz'
      | tmul d a =>
          rw [e.middleCounitContraction_tmul]
          exact Submodule.mem_map₂ (TensorProduct.mk k _ _) P ⊤ hc trivial)
    exact htransported
  have hret := LinearMap.congr_fun e.coactionRetraction_eq_inverse b
  change e.middleCounitContraction (transported (e.leftCoaction b)) =
    e.rightNormalBasis.symm.toLinearMap b at hret
  change e.rightNormalBasis.symm.toLinearMap b ∈ tensorProductSubspace P ⊤
  rw [← hret]
  exact hcontracted

/-- The quotient coaction of `b σ(c)` has first factor in the product of
the quotient image of the coefficient coalgebra with `P`. -/
theorem CleftExactSequence.leftCoaction_mul_section_mem
    (F : FiniteSubcoalgebra k B) (P : FiniteSubcoalgebra k C)
    (b : B) (hb : b ∈ F.carrier) (c : C) (hc : c ∈ P.carrier) :
    e.leftCoaction (b * e.coalgebraSection c) ∈
      tensorProductSubspace
        (actionSubspace
          (F.carrier.map e.projection.toAlgHom.toLinearMap) P.carrier) ⊤ := by
  obtain ⟨zb, hzb⟩ := F.isSubcoalgebra hb
  obtain ⟨zc, hzc⟩ := P.isSubcoalgebra hc
  change TensorProduct.map e.projection.toAlgHom.toLinearMap LinearMap.id
      (Coalgebra.comul (R := k) (b * e.coalgebraSection c)) ∈ _
  rw [Bialgebra.comul_mul]
  rw [show Coalgebra.comul (R := k) (e.coalgebraSection c) =
      TensorProduct.map e.coalgebraSection.toLinearMap
        e.coalgebraSection.toLinearMap (Coalgebra.comul (R := k) c) from
    (CoalgHomClass.map_comp_comul_apply e.coalgebraSection c).symm]
  rw [← hzb, ← hzc]
  clear hzb hzc hb hc b c
  induction zb using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, add_mul]
      exact (tensorProductSubspace _ _).add_mem hp hq
  | tmul b₁ b₂ =>
      induction zc using TensorProduct.induction_on with
      | zero => simp
      | add p q hp hq =>
          simp only [map_add, mul_add]
          exact (tensorProductSubspace _ _).add_mem hp hq
      | tmul c₁ c₂ =>
          simp only [TensorProduct.map_tmul,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [show e.projection.toAlgHom.toLinearMap
              (F.carrier.subtype b₁ *
                e.coalgebraSection.toLinearMap (P.carrier.subtype c₁)) =
                e.projection.toAlgHom (F.carrier.subtype b₁) *
                  e.projection.toAlgHom
                    (e.coalgebraSection.toLinearMap
                      (P.carrier.subtype c₁)) from
            map_mul e.projection.toAlgHom _ _]
          simp only [LinearMap.id_apply]
          change (e.projection.toAlgHom (b₁ : B) *
              e.projection.toAlgHom (e.coalgebraSection.toLinearMap (c₁ : C))) ⊗ₜ[k]
                ((b₂ : B) * e.coalgebraSection.toLinearMap (c₂ : C)) ∈
            tensorProductSubspace
              (actionSubspace
                (F.carrier.map e.projection.toAlgHom.toLinearMap) P.carrier) ⊤
          rw [e.projection_section_linear_apply]
          apply Submodule.mem_map₂ (TensorProduct.mk k _ _)
          · rw [actionSubspace_eq_map₂]
            exact Submodule.mem_map₂
              (Algebra.lsmul k k C).toLinearMap
              (F.carrier.map e.projection.toAlgHom.toLinearMap) P.carrier
              ⟨b₁, b₁.2, rfl⟩ c₁.2
          · trivial

/-- Multiplying a finite quotient section by a finite coefficient
subcoalgebra introduces only finitely many kernel coordinates. -/
theorem CleftExactSequence.exists_finite_extension_defect
    (F : FiniteSubcoalgebra k B) (P : FiniteSubcoalgebra k C) :
    ∃ D : Submodule k A, FiniteDimensional k D ∧
      (actionSubspace F.carrier
          (P.carrier.map e.coalgebraSection.toLinearMap)).map
            e.rightNormalBasis.symm.toLinearMap ≤
        tensorProductSubspace
          (actionSubspace
            (F.carrier.map e.projection.toAlgHom.toLinearMap) P.carrier) D := by
  let X : Submodule k B :=
    actionSubspace F.carrier
      (P.carrier.map e.coalgebraSection.toLinearMap)
  let θinv := e.rightNormalBasis.symm.toLinearMap
  let X' := X.map θinv
  let Pplus : Submodule k C :=
    actionSubspace
      (F.carrier.map e.projection.toAlgHom.toLinearMap) P.carrier
  let _ : FiniteDimensional k X := by
    dsimp [X]
    exact finiteDimensional_actionSubspace _ _
  let _ : FiniteDimensional k X' := by
    dsimp [X']
    infer_instance
  have hX' : X' ≤ tensorProductSubspace Pplus ⊤ := by
    rintro _ ⟨b, hb, rfl⟩
    apply e.rightNormalBasis_symm_mem_of_leftCoaction_mem Pplus
    change b ∈ actionSubspace F.carrier
      (P.carrier.map e.coalgebraSection.toLinearMap) at hb
    rw [actionSubspace_eq_map₂] at hb
    let Good : Submodule k B :=
      (tensorProductSubspace Pplus ⊤).comap e.leftCoaction
    apply (show Submodule.map₂
        (Algebra.lsmul k k B).toLinearMap F.carrier
        (P.carrier.map e.coalgebraSection.toLinearMap) ≤ Good by
      apply Submodule.map₂_le.2
      intro b hb y hy
      rcases hy with ⟨c, hc, rfl⟩
      exact e.leftCoaction_mul_section_mem F P b hb c hc) hb
  obtain ⟨D, hDfd, hD⟩ :=
    exists_finite_right_tensor_support Pplus X' hX'
  exact ⟨D, hDfd, hD⟩

/-- Right multiplication by a kernel coefficient acts only on the kernel
factor of right normal-basis coordinates. -/
theorem CleftExactSequence.rightNormalBasis_symm_mul_inclusion_mem
    (P : Submodule k C) (D E : Submodule k A)
    (z : C ⊗[k] A) (hz : z ∈ tensorProductSubspace P D)
    (a : A) (ha : a ∈ E) :
    e.rightNormalBasis.symm
        (e.rightNormalBasis z * e.inclusion a) ∈
      tensorProductSubspace P (actionSubspace D E) := by
  rw [tensorProductSubspace_eq_range_mapIncl] at hz
  obtain ⟨zDE, rfl⟩ := hz
  induction zDE using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, add_mul]
      exact (tensorProductSubspace P (actionSubspace D E)).add_mem hp hq
  | tmul c d =>
      change e.rightNormalBasis.symm
          ((e.coalgebraSection c * e.inclusion d) * e.inclusion a) ∈ _
      rw [mul_assoc, ← map_mul]
      rw [e.rightNormalBasis_symm_section_mul_inclusion]
      apply Submodule.mem_map₂ (TensorProduct.mk k _ _)
      · exact c.2
      · rw [actionSubspace_eq_map₂]
        exact Submodule.mem_map₂
          (Algebra.lsmul k k A).toLinearMap D E d.2 ha

/-- Amenability of the middle algebra passes to the quotient in a cleft
exact sequence. -/
theorem CleftExactSequence.isAmenableHopfAlgebra_quotient
    (e : CleftExactSequence (k := k) A B C)
    (hB : IsAmenableHopfAlgebra (k := k) (H := B)) :
    IsAmenableHopfAlgebra (k := k) (H := C) := by
  let _ : Module B C := Module.compHom C e.projection.toAlgHom.toRingHom
  let _ : IsScalarTower k B C :=
    IsScalarTower.of_algebraMap_smul fun r c => by
      change e.projection.toAlgHom (algebraMap k B r) * c = r • c
      rw [e.projection.toAlgHom.commutes, Algebra.smul_def]
  let act : B ⊗[k] C →ₗc[k] C :=
    (Bialgebra.mulCoalgHom k C).comp
      (CoalgHom.tensorMapStruct e.projectionCoalgHom (CoalgHom.id k C))
  have hact : hopfModuleAction (k := k) (H := B) (M := C) =
      act.toLinearMap := by
    ext b c
    change e.projection.toAlgHom b * c = act (b ⊗ₜ[k] c)
    rfl
  let _ : IsHopfModuleCoalgebra k B C := by
    refine { counit_action := ?_, comul_action := ?_ }
    · rw [hact]
      exact act.counit_comp
    · rw [hact]
      exact act.map_comp_comul.symm
  have hmoduleMap : IsHopfModuleMap (H := B)
      e.projectionCoalgHom.toLinearMap := by
    intro b c
    change e.projection.toAlgHom (b * c) =
      e.projection.toAlgHom b * e.projection.toAlgHom c
    exact map_mul _ _ _
  have hCmodule : IsAmenableHopfModuleCoalgebra
      (k := k) (H := B) (M := C) :=
    IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom
      e.projectionCoalgHom hmoduleMap e.projection_surjective hB
  apply isAmenableHopfAlgebra_iff_algebraicallyAmenable.mpr
  have hrestricted := hCmodule.hasActionFolnerSubspaces
  intro P hP ε hε
  let _ : FiniteDimensional k P := hP
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
    e.projection.toAlgHom.toLinearMap
      (LinearMap.range_eq_top.2 e.projection_surjective)
  let F : Submodule k B := P.map s
  let _ : FiniteDimensional k F := by dsimp [F]; infer_instance
  obtain ⟨E, hE, hEfd, hEratio⟩ :=
    hrestricted F inferInstance ε hε
  have hs_apply (c : C) : e.projection.toAlgHom (s c) = c := by
    exact LinearMap.congr_fun hs c
  have haction : actionSubspace F E = actionSubspace P E := by
    rw [actionSubspace_eq_map₂, actionSubspace_eq_map₂]
    apply le_antisymm
    · apply Submodule.map₂_le.2
      rintro _ ⟨p, hp, rfl⟩ c hc
      change e.projection.toAlgHom (s p) * c ∈ _
      rw [hs_apply]
      exact Submodule.mem_map₂ (Algebra.lsmul k k C).toLinearMap P E hp hc
    · apply Submodule.map₂_le.2
      intro p hp c hc
      have hsp : s p ∈ F := ⟨p, hp, rfl⟩
      have hm := Submodule.mem_map₂
        (Algebra.lsmul k k C).toLinearMap F E hsp hc
      change e.projection.toAlgHom (s p) * c ∈ _ at hm
      rwa [hs_apply] at hm
  refine ⟨E, hE, hEfd, ?_⟩
  change (sfinrank k (E ⊔ actionSubspace P E) : ℚ) ≤
    (1 + ε) * sfinrank k E
  change (sfinrank k (E ⊔ actionSubspace F E) : ℚ) ≤
    (1 + ε) * sfinrank k E at hEratio
  rwa [haction] at hEratio

end

end HopfAmenability
