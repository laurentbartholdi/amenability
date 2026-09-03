/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.CleftAmenability
import Amenability.TheoremD

/-! # Theorem E: amenability and cleft Hopf extensions -/

open Coalgebra Module TensorProduct
namespace HopfAmenability
noncomputable section
universe u v w x
variable {k : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [Field k]
variable [Ring A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
variable [Ring B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
variable [Ring C] [HopfAlgebra k C] [Coalgebra.IsCocomm k C]

/-- The direct direction of Theorem E: amenability of the kernel and
quotient implies amenability of the middle Hopf algebra.  This proof uses
only the derived normal basis and the two component Følner conditions. -/
theorem isAmenableHopfAlgebra_cleftExtension_of_components
    (e : CleftExactSequence (k := k) A B C)
    (hA : IsAmenableHopfAlgebra (k := k) (H := A))
    (hC : IsAmenableHopfAlgebra (k := k) (H := C)) :
    IsAmenableHopfAlgebra (k := k) (H := B) := by
  apply HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
  intro F hF ε hε
  classical
  let δ : ℚ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδε : 3 * δ ≤ ε := by
    have := min_le_left (ε / 3) (1 : ℚ)
    dsimp [δ]
    linarith
  have hsq : (1 + δ) ^ 2 ≤ 1 + ε := by
    nlinarith [sq_nonneg δ]
  let _ : FiniteDimensional k F := hF
  let F₁ : Submodule k B := F ⊔ Submodule.span k {1}
  let _ : FiniteDimensional k F₁ := by dsimp [F₁]; infer_instance
  obtain ⟨Fcoal, hF₁coal⟩ :=
    Coalgebra.exists_finiteSubcoalgebra_containing_submodule F₁
  have hFFcoal : F ≤ Fcoal.carrier := le_sup_left.trans hF₁coal
  have h1Fcoal : (1 : B) ∈ Fcoal.carrier := by
    apply hF₁coal
    exact (le_sup_right : Submodule.span k {1} ≤ F₁)
      (Submodule.subset_span (Set.mem_singleton 1))
  let G : Submodule k C :=
    Fcoal.carrier.map e.projection.toAlgHom.toLinearMap
  let _ : FiniteDimensional k G := by dsimp [G]; infer_instance
  have h1G : (1 : C) ∈ G := by
    exact ⟨1, h1Fcoal, by
      change e.projection.toAlgHom 1 = 1
      rw [map_one]⟩
  obtain ⟨P, hP, hPratio₀⟩ := hC G inferInstance δ hδ
  have hPratio :
      (sfinrank k (actionSubspace G P.carrier) : ℚ) ≤
        (1 + δ) * sfinrank k P.carrier := by
    rw [actionExpansion_eq_actionSubspace_of_one_mem h1G] at hPratio₀
    exact hPratio₀
  obtain ⟨D, hDfd, hdefect⟩ :=
    e.exists_finite_extension_defect Fcoal P
  let _ : FiniteDimensional k D := hDfd
  obtain ⟨Q, hQ, hQratio⟩ := hA D inferInstance δ hδ
  let Pplus : Submodule k C := actionSubspace G P.carrier
  let Qplus : Submodule k A := actionExpansion D Q.carrier
  let _ : FiniteDimensional k Pplus := by
    dsimp [Pplus]
    exact finiteDimensional_actionSubspace _ _
  let _ : FiniteDimensional k Qplus := by
    dsimp [Qplus]
    exact finiteDimensional_actionExpansion _ _
  let E₀ := tensorProductSubspace P.carrier Q.carrier
  let θ := e.rightNormalBasis.toLinearEquiv
  let E : Submodule k B := E₀.map θ.toLinearMap
  let Target₀ := tensorProductSubspace Pplus Qplus
  let Target : Submodule k B := Target₀.map θ.toLinearMap
  let _ : FiniteDimensional k E₀ := by
    dsimp [E₀]
    exact finiteDimensional_tensorProductSubspace P.carrier Q.carrier
  let _ : FiniteDimensional k E := by dsimp [E]; infer_instance
  let _ : FiniteDimensional k Target₀ := by
    dsimp [Target₀]
    exact finiteDimensional_tensorProductSubspace Pplus Qplus
  let _ : FiniteDimensional k Target := by dsimp [Target]; infer_instance
  have hP_Pplus : P.carrier ≤ Pplus := by
    intro p hp
    change p ∈ actionSubspace G P.carrier
    rw [actionSubspace_eq_map₂]
    simpa using Submodule.mem_map₂
      (Algebra.lsmul k k C).toLinearMap G P.carrier h1G hp
  have hQ_Qplus : Q.carrier ≤ Qplus := le_sup_left
  have hETarget : E ≤ Target := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    exact tensorProductSubspace_mono hP_Pplus hQ_Qplus hz
  have haction : actionSubspace F E ≤ Target := by
    rw [actionSubspace_eq_map₂]
    apply Submodule.map₂_le.2
    intro f hf x hx
    rcases hx with ⟨z, hz, rfl⟩
    change z ∈ tensorProductSubspace P.carrier Q.carrier at hz
    rw [tensorProductSubspace_eq_range_mapIncl] at hz
    obtain ⟨zPQ, rfl⟩ := hz
    induction zPQ using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simp only [map_add]
        exact Target.add_mem hz hz'
    | tmul p q =>
        have hprod : f * e.coalgebraSection p ∈
            actionSubspace Fcoal.carrier
              (P.carrier.map e.coalgebraSection.toLinearMap) := by
          rw [actionSubspace_eq_map₂]
          exact Submodule.mem_map₂
            (Algebra.lsmul k k B).toLinearMap Fcoal.carrier
            (P.carrier.map e.coalgebraSection.toLinearMap)
            (hFFcoal hf) ⟨p, p.2, rfl⟩
        have hzD := hdefect (Submodule.mem_map_of_mem hprod)
        have hmul := e.rightNormalBasis_symm_mul_inclusion_mem
          Pplus D Q.carrier
          (e.rightNormalBasis.symm (f * e.coalgebraSection p)) hzD q q.2
        rw [e.rightNormalBasis.apply_symm_apply] at hmul
        have hmul' : e.rightNormalBasis.symm
            (f * e.rightNormalBasis (p ⊗ₜ[k] q)) ∈ Target₀ := by
          rw [e.rightNormalBasis_tmul, ← mul_assoc]
          exact tensorProductSubspace_mono le_rfl
            (le_sup_right : actionSubspace D Q.carrier ≤ Qplus) hmul
        exact ⟨_, hmul', e.rightNormalBasis.apply_symm_apply _⟩
  have hexpansion : actionExpansion F E ≤ Target := sup_le hETarget haction
  have hdimE : sfinrank k E =
      sfinrank k P.carrier * sfinrank k Q.carrier := by
    rw [show sfinrank k E = sfinrank k E₀ by exact θ.finrank_map_eq E₀]
    exact sfinrank_tensorProductSubspace P.carrier Q.carrier
  have hdimTarget : sfinrank k Target =
      sfinrank k Pplus * sfinrank k Qplus := by
    rw [show sfinrank k Target = sfinrank k Target₀ by
      exact θ.finrank_map_eq Target₀]
    exact sfinrank_tensorProductSubspace Pplus Qplus
  have hdimExpansion : sfinrank k (actionExpansion F E) ≤
      sfinrank k Target := Submodule.finrank_mono hexpansion
  have hnonzero : E ≠ ⊥ := by
    intro hbot
    have hzero : sfinrank k E = 0 := by simp [hbot, sfinrank]
    rw [hdimE] at hzero
    have hPpos : 0 < sfinrank k P.carrier := by
      let _ : Nontrivial P.carrier := Submodule.nontrivial_iff_ne_bot.mpr hP
      exact Module.finrank_pos
    have hQpos : 0 < sfinrank k Q.carrier := by
      let _ : Nontrivial Q.carrier := Submodule.nontrivial_iff_ne_bot.mpr hQ
      exact Module.finrank_pos
    exact (Nat.mul_ne_zero (Nat.ne_of_gt hPpos) (Nat.ne_of_gt hQpos))
      (hdimE ▸ hzero)
  refine ⟨E, hnonzero, inferInstance, ?_⟩
  calc
    (sfinrank k (actionExpansion F E) : ℚ) ≤ sfinrank k Target := by
      exact_mod_cast hdimExpansion
    _ = (sfinrank k Pplus : ℚ) * sfinrank k Qplus := by
      rw [hdimTarget]
      norm_num
    _ ≤ ((1 + δ) * sfinrank k P.carrier) *
        ((1 + δ) * sfinrank k Q.carrier) := by
      apply mul_le_mul hPratio hQratio <;> positivity
    _ = (1 + δ) ^ 2 *
        ((sfinrank k P.carrier : ℚ) * sfinrank k Q.carrier) := by ring
    _ ≤ (1 + ε) *
        ((sfinrank k P.carrier : ℚ) * sfinrank k Q.carrier) := by
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (1 + ε) * sfinrank k E := by rw [hdimE]; norm_num

/-- The easy direction of Theorem E: the kernel and quotient of an
amenable middle Hopf algebra are amenable. -/
theorem CleftExactSequence.amenable_components
    (e : CleftExactSequence (k := k) A B C)
    (hB : IsAmenableHopfAlgebra (k := k) (H := B)) :
    IsAmenableHopfAlgebra (k := k) (H := A) ∧
      IsAmenableHopfAlgebra (k := k) (H := C) := by
  constructor
  · let i : HopfSubalgebraEmbedding (k := k) (H := B) A :=
      { e.inclusion with injective := e.inclusion_injective }
    exact isAmenableHopfAlgebra_of_hopfSubalgebra i hB
  · exact e.isAmenableHopfAlgebra_quotient hB

/-- **Theorem E (cleft Hopf extensions).** The middle algebra in a cleft
exact sequence is amenable exactly when its kernel and quotient are. -/
theorem cleftExactSequence_amenable_iff
    (e : CleftExactSequence (k := k) A B C) :
    IsAmenableHopfAlgebra (k := k) (H := B) ↔
      IsAmenableHopfAlgebra (k := k) (H := A) ∧
        IsAmenableHopfAlgebra (k := k) (H := C) := by
  constructor
  · exact e.amenable_components
  · rintro ⟨hA, hC⟩
    exact isAmenableHopfAlgebra_cleftExtension_of_components e hA hC

/-- Public spelling of Theorem E. -/
theorem isAmenableHopfAlgebra_cleftExtension_iff
    (e : CleftExactSequence (k := k) A B C) :
    IsAmenableHopfAlgebra (k := k) (H := B) ↔
      IsAmenableHopfAlgebra (k := k) (H := A) ∧
        IsAmenableHopfAlgebra (k := k) (H := C) :=
  cleftExactSequence_amenable_iff e


end
end HopfAmenability
