/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.AugmentationGradedHopf

/-! # Hopf-module coalgebra structure on the augmentation associated graded -/

open Coalgebra TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

private theorem augmentationGraded_counit_action_of_mk
    (i j : ℕ)
    (h : augmentationFiltration (k := k) (H := H) i)
    (m : augmentationModuleFiltration (k := k) (H := H) (M := M) j) :
    Coalgebra.counit (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))
        (DirectSum.of
            (fun q => AugmentationGradedHopfPiece (k := k) (H := H) q)
            i (Submodule.Quotient.mk h) •
          DirectSum.of
            (fun q => AugmentationGradedModulePiece (k := k) (H := H) (M := M) q)
            j (Submodule.Quotient.mk m)) =
      Coalgebra.counit (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H))
          (DirectSum.of
            (fun q => AugmentationGradedHopfPiece (k := k) (H := H) q)
            i (Submodule.Quotient.mk h)) *
        Coalgebra.counit (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M))
          (DirectSum.of
            (fun q => AugmentationGradedModulePiece (k := k) (H := H) (M := M) q)
            j (Submodule.Quotient.mk m)) := by
  rw [DirectSum.Gmodule.of_smul_of]
  change augmentationGradedCounit (k := k) (H := H) (M := M)
      (DirectSum.of _ (i + j)
        (augmentationGradedAction (k := k) (H := H) (M := M) i j
          (Submodule.Quotient.mk h) (Submodule.Quotient.mk m))) = _
  rw [augmentationGradedAction_mk]
  by_cases hij : i + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    rw [augmentationGradedHopf_counit_of_zero]
    rw [augmentationGradedCounit_of_zero]
    change Coalgebra.counit (R := k) (A := M) ((h : H) • (m : M)) =
      Coalgebra.counit (R := k) (A := H) h *
        augmentationGradedCounit (k := k) (H := H) (M := M)
          (DirectSum.of _ 0 (Submodule.Quotient.mk m))
    rw [augmentationGradedCounit_of_zero]
    exact counit_smul (k := k) (H := H) (M := M) h m
  · rw [augmentationGradedCounit_of_ne_zero (i + j) hij]
    rcases (show i ≠ 0 ∨ j ≠ 0 by omega) with hi | hj
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      rw [augmentationGradedHopf_counit_of_succ]
      simp
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      change 0 = _ * augmentationGradedCounit (k := k) (H := H) (M := M)
        (DirectSum.of _ (d + 1) (Submodule.Quotient.mk m))
      rw [augmentationGradedCounit_of_succ]
      simp

theorem augmentationGraded_counit_smul
    (h : AugmentationGradedHopf (k := k) (H := H))
    (m : AugmentationGradedModule (k := k) (H := H) (M := M)) :
    Coalgebra.counit (R := k) (A := AugmentationGradedModule
        (k := k) (H := H) (M := M)) (h • m) =
      Coalgebra.counit (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H)) h *
        Coalgebra.counit (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M)) m := by
  induction h using DirectSum.induction_on generalizing m with
  | zero => simp
  | add h h' hh hh' => simp only [add_smul, map_add, hh, hh', add_mul]
  | of i h =>
      induction m using DirectSum.induction_on with
      | zero => simp
      | add m m' hm hm' => simp only [smul_add, map_add, hm, hm', mul_add]
      | of j m =>
          induction h using Submodule.Quotient.induction_on with
          | _ h =>
              induction m using Submodule.Quotient.induction_on with
              | _ m =>
                  exact augmentationGraded_counit_action_of_mk
                    (k := k) (H := H) (M := M) i j h m

private def moduleTensorSymbol (n : ℕ) :
    tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := M)) n →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M) :=
  (gradedTensorInclusion (k := k) (H := H) (M := M) n).comp
    (tensorFiltrationCoordinates (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := M)) n)

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
@[simp]
private theorem moduleTensorSymbol_mapIncl_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x : augmentationModuleFiltration (k := k) (H := H) (M := M) i)
    (y : augmentationModuleFiltration (k := k) (H := H) (M := M) (n - i)) :
    moduleTensorSymbol (k := k) (H := H) (M := M) n
        ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), by
          rw [tensorFiltration]
          exact Submodule.mem_iSup_of_mem i ⟨x ⊗ₜ[k] y, rfl⟩⟩ =
      DirectSum.of _ (i : ℕ) (Submodule.Quotient.mk x) ⊗ₜ[k]
        DirectSum.of _ (n - i) (Submodule.Quotient.mk y) := by
  rw [moduleTensorSymbol, LinearMap.comp_apply]
  rw [tensorFiltrationCoordinates_mapIncl_tmul
      (augmentationModuleFiltration (k := k) (H := H) (M := M))
      (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M)),
    gradedTensorInclusion_of_tmul]

private def tensorDiagonalAction :
    (H ⊗[k] H) ⊗[k] (M ⊗[k] M) →ₗ[k] M ⊗[k] M :=
  (TensorProduct.map
      (hopfModuleAction (k := k) (H := H) (M := M))
      (hopfModuleAction (k := k) (H := H) (M := M))).comp
    (TensorProduct.tensorTensorTensorComm k H H M M).toLinearMap

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
@[simp]
private theorem tensorDiagonalAction_tmul_tmul
    (h₁ h₂ : H) (m₁ m₂ : M) :
    tensorDiagonalAction (k := k) (H := H) (M := M)
        ((h₁ ⊗ₜ[k] h₂) ⊗ₜ[k] (m₁ ⊗ₜ[k] m₂)) =
      (h₁ • m₁) ⊗ₜ[k] (h₂ • m₂) := by
  simp [tensorDiagonalAction, TensorProduct.tensorTensorTensorComm_tmul,
    hopfModuleAction_tmul]

set_option maxHeartbeats 4000000 in
-- Nested tensor-filtration inductions track four homogeneous factors.
omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
private theorem tensorDiagonalAction_mem (p q : ℕ)
    (dh : H ⊗[k] H)
    (hdh : dh ∈ tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) p)
    (dm : M ⊗[k] M)
    (hdm : dm ∈ tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := M)) q) :
    tensorDiagonalAction (k := k) (H := H) (M := M) (dh ⊗ₜ[k] dm) ∈
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := M)) (p + q) := by
  let WH : ℕ → Submodule k H :=
    augmentationModuleFiltration (k := k) (H := H) (M := H)
  let WM : ℕ → Submodule k M :=
    augmentationModuleFiltration (k := k) (H := H) (M := M)
  have main : ∀ (a : H ⊗[k] H) (ha : a ∈ tensorFiltration (k := k) WH p)
      (b : M ⊗[k] M) (hb : b ∈ tensorFiltration (k := k) WM q),
      tensorDiagonalAction (k := k) (H := H) (M := M) (a ⊗ₜ[k] b) ∈
        tensorFiltration (k := k) WM (p + q) := by
    intro a ha b hb
    induction ha using Submodule.iSup_induction' with
    | mem i a hai =>
        rcases hai with ⟨a', rfl⟩
        induction a' with
        | zero => simp [tensorDiagonalAction]
        | add a₁ a₂ ha₁ ha₂ =>
            simpa [add_tmul, map_add] using Submodule.add_mem _ ha₁ ha₂
        | tmul h₁ h₂ =>
            induction hb using Submodule.iSup_induction' with
            | mem j b hbj =>
                rcases hbj with ⟨b', rfl⟩
                induction b' with
                | zero => simp [tensorDiagonalAction]
                | add b₁ b₂ hb₁ hb₂ =>
                    simpa [tmul_add, map_add] using Submodule.add_mem _ hb₁ hb₂
                | tmul m₁ m₂ =>
                    let r : Fin (p + q + 1) := ⟨(i : ℕ) + (j : ℕ), by omega⟩
                    have hright : p + q - (r : ℕ) =
                        (p - (i : ℕ)) + (q - (j : ℕ)) := by
                      dsimp [r]
                      omega
                    change tensorDiagonalAction (k := k) (H := H) (M := M)
                        (((h₁ : H) ⊗ₜ[k] (h₂ : H)) ⊗ₜ[k]
                          ((m₁ : M) ⊗ₜ[k] (m₂ : M))) ∈ _
                    rw [tensorDiagonalAction_tmul_tmul]
                    apply Submodule.mem_iSup_of_mem r
                    refine ⟨(⟨(h₁ : H) • (m₁ : M), ?_⟩ : WM r) ⊗ₜ[k]
                        (⟨(h₂ : H) • (m₂ : M), ?_⟩ : WM (p + q - r)), ?_⟩
                    · exact augmentationFiltration_action_le (k := k) (H := H) (M := M) i j
                        (product_mem_actionSubspace
                          (by
                            have hh := h₁.property
                            change (h₁ : H) ∈ augmentationModuleFiltration
                              (k := k) (H := H) (M := H) i at hh
                            rwa [regular_augmentationModuleFiltration_eq] at hh)
                          m₁.property)
                    · rw [hright]
                      exact augmentationFiltration_action_le (k := k) (H := H) (M := M)
                        (p - i) (q - j)
                        (product_mem_actionSubspace
                          (by
                            have hh := h₂.property
                            change (h₂ : H) ∈ augmentationModuleFiltration
                              (k := k) (H := H) (M := H) (p - i) at hh
                            rwa [regular_augmentationModuleFiltration_eq] at hh)
                          m₂.property)
                    · simp [TensorProduct.mapIncl]
            | zero => simp [tensorDiagonalAction]
            | add b₁ b₂ hb₁ hb₂ hb₁' hb₂' =>
                simpa [tmul_add, map_add] using Submodule.add_mem _ hb₁' hb₂'
    | zero => simp [tensorDiagonalAction]
    | add a₁ a₂ ha₁ ha₂ ha₁' ha₂' =>
        simpa [add_tmul, map_add] using Submodule.add_mem _ ha₁' ha₂'
  exact main dh hdh dm hdm

private def filteredTensorDiagonalAction (p q : ℕ) :
    tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) p ⊗[k]
        tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := M)) q →ₗ[k]
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := M)) (p + q) :=
  ((tensorDiagonalAction (k := k) (H := H) (M := M)).comp
      (TensorProduct.map
        (tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) p).subtype
        (tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := M)) q).subtype)).codRestrict _
    (by
      intro t
      induction t with
      | zero => exact Submodule.zero_mem _
      | add a b ha hb => simpa using Submodule.add_mem _ ha hb
      | tmul a b =>
          exact tensorDiagonalAction_mem (k := k) (H := H) (M := M)
            p q a a.property b b.property)

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
@[simp]
private theorem filteredTensorDiagonalAction_tmul (p q : ℕ)
    (a : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) p)
    (b : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := M)) q) :
    filteredTensorDiagonalAction (k := k) (H := H) (M := M) p q (a ⊗ₜ[k] b) =
      ⟨tensorDiagonalAction (k := k) (H := H) (M := M)
          ((a : H ⊗[k] H) ⊗ₜ[k] (b : M ⊗[k] M)),
        tensorDiagonalAction_mem (k := k) (H := H) (M := M)
          p q a a.property b b.property⟩ := by
  rfl

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
private theorem augmentationGradedModule_mk_heq'
    {p q : ℕ} (hpq : p = q)
    (x : augmentationModuleFiltration (k := k) (H := H) (M := M) p)
    (y : augmentationModuleFiltration (k := k) (H := H) (M := M) q)
    (hxy : (x : M) = y) :
    HEq (Submodule.Quotient.mk x :
        AugmentationGradedModulePiece (k := k) (H := H) (M := M) p)
      (Submodule.Quotient.mk y :
        AugmentationGradedModulePiece (k := k) (H := H) (M := M) q) := by
  subst q
  apply heq_of_eq
  apply congrArg Submodule.Quotient.mk
  exact Subtype.ext hxy

private def gradedTensorDiagonalAction :
    (AugmentationGradedHopf (k := k) (H := H) ⊗[k]
        AugmentationGradedHopf (k := k) (H := H)) ⊗[k]
      (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M)) →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M) :=
  tensorDiagonalAction (k := k)
    (H := AugmentationGradedHopf (k := k) (H := H))
    (M := AugmentationGradedModule (k := k) (H := H) (M := M))

set_option maxHeartbeats 6000000 in
-- Passing to total leading symbols intertwines the diagonal tensor action.
omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
private theorem tensorSymbol_diagonalAction_linear (p q : ℕ) :
    (moduleTensorSymbol (k := k) (H := H) (M := M) (p + q)).comp
        (filteredTensorDiagonalAction (k := k) (H := H) (M := M) p q) =
      (gradedTensorDiagonalAction (k := k) (H := H) (M := M)).comp
        (TensorProduct.map
          (regularTensorSymbol (k := k) (H := H) p)
          (moduleTensorSymbol (k := k) (H := H) (M := M) q)) := by
  apply TensorProduct.ext'
  intro a b
  let WH : ℕ → Submodule k H :=
    augmentationModuleFiltration (k := k) (H := H) (M := H)
  let WM : ℕ → Submodule k M :=
    augmentationModuleFiltration (k := k) (H := H) (M := M)
  let TH (r : ℕ) := tensorFiltration (k := k) WH r
  let TM (r : ℕ) := tensorFiltration (k := k) WM r
  let σH (r : ℕ) := regularTensorSymbol (k := k) (H := H) r
  let σM (r : ℕ) := moduleTensorSymbol (k := k) (H := H) (M := M) r
  let A : TH p →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M) :=
    (σM (p + q)).comp
      ((filteredTensorDiagonalAction (k := k) (H := H) (M := M) p q).comp
        ((TensorProduct.mk k (TH p) (TM q)).flip b))
  let B : TH p →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M) :=
    (gradedTensorDiagonalAction (k := k) (H := H) (M := M)).comp
      ((TensorProduct.mk k _ _).flip (σM q b) |>.comp (σH p))
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (dh : H ⊗[k] H) (hdh : dh ∈ TH p),
        A ⟨dh, hdh⟩ = B ⟨dh, hdh⟩ := by
      intro dh hdh
      induction hdh using Submodule.iSup_induction' with
      | mem i dh hi =>
          rcases hi with ⟨u, rfl⟩
          let incH : WH i ⊗[k] WH (p - i) →ₗ[k] TH p :=
            (TensorProduct.mapIncl (WH i) (WH (p - i))).codRestrict _
              (fun u => Submodule.mem_iSup_of_mem i ⟨u, rfl⟩)
          have hincH : A.comp incH = B.comp incH := by
            apply TensorProduct.ext'
            intro h₁ h₂
            let dh₀ : TH p := incH (h₁ ⊗ₜ[k] h₂)
            let C : TM q →ₗ[k]
                AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
                  AugmentationGradedModule (k := k) (H := H) (M := M) :=
              (σM (p + q)).comp
                ((filteredTensorDiagonalAction (k := k) (H := H) (M := M) p q).comp
                  (TensorProduct.mk k (TH p) (TM q) dh₀))
            let D : TM q →ₗ[k]
                AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
                  AugmentationGradedModule (k := k) (H := H) (M := M) :=
              (gradedTensorDiagonalAction (k := k) (H := H) (M := M)).comp
                ((TensorProduct.mk k _ _ (σH p dh₀)).comp (σM q))
            have hCD : C = D := by
              apply LinearMap.ext
              intro s
              have hsecond : ∀ (dm : M ⊗[k] M) (hdm : dm ∈ TM q),
                  C ⟨dm, hdm⟩ = D ⟨dm, hdm⟩ := by
                intro dm hdm
                induction hdm using Submodule.iSup_induction' with
                | mem j dm hj =>
                    rcases hj with ⟨v, rfl⟩
                    let incM : WM j ⊗[k] WM (q - j) →ₗ[k] TM q :=
                      (TensorProduct.mapIncl (WM j) (WM (q - j))).codRestrict _
                        (fun v => Submodule.mem_iSup_of_mem j ⟨v, rfl⟩)
                    have hpure : C.comp incM = D.comp incM := by
                      apply TensorProduct.ext'
                      intro m₁ m₂
                      let r : Fin (p + q + 1) := ⟨(i : ℕ) + (j : ℕ), by omega⟩
                      have hright : p + q - (r : ℕ) =
                          (p - (i : ℕ)) + (q - (j : ℕ)) := by
                        dsimp [r]
                        omega
                      have hh₁ : (h₁ : H) ∈ augmentationFiltration (k := k) (H := H) i := by
                        have hh := h₁.property
                        change (h₁ : H) ∈ augmentationModuleFiltration
                          (k := k) (H := H) (M := H) i at hh
                        rwa [regular_augmentationModuleFiltration_eq] at hh
                      have hh₂ : (h₂ : H) ∈
                          augmentationFiltration (k := k) (H := H) (p - i) := by
                        have hh := h₂.property
                        change (h₂ : H) ∈ augmentationModuleFiltration
                          (k := k) (H := H) (M := H) (p - i) at hh
                        rwa [regular_augmentationModuleFiltration_eq] at hh
                      have hm₁ : (h₁ : H) • (m₁ : M) ∈ WM r :=
                        augmentationFiltration_action_le (k := k) (H := H) (M := M) i j
                          (product_mem_actionSubspace hh₁ m₁.property)
                      have hm₂ : (h₂ : H) • (m₂ : M) ∈ WM (p + q - r) := by
                        rw [hright]
                        exact augmentationFiltration_action_le (k := k) (H := H) (M := M)
                          (p - i) (q - j)
                          (product_mem_actionSubspace hh₂ m₂.property)
                      change σM (p + q)
                          (filteredTensorDiagonalAction (k := k) (H := H) (M := M) p q
                            (dh₀ ⊗ₜ[k] incM (m₁ ⊗ₜ[k] m₂))) =
                        gradedTensorDiagonalAction (k := k) (H := H) (M := M)
                          (σH p dh₀ ⊗ₜ[k] σM q (incM (m₁ ⊗ₜ[k] m₂)))
                      rw [filteredTensorDiagonalAction_tmul]
                      have houtmem : tensorDiagonalAction (k := k) (H := H) (M := M)
                            ((dh₀ : H ⊗[k] H) ⊗ₜ[k]
                              (incM (m₁ ⊗ₜ[k] m₂) : M ⊗[k] M)) ∈ TM (p + q) :=
                        (filteredTensorDiagonalAction (k := k) (H := H) (M := M)
                          p q (dh₀ ⊗ₜ[k] incM (m₁ ⊗ₜ[k] m₂))).property
                      have hout : (⟨tensorDiagonalAction (k := k) (H := H) (M := M)
                            ((dh₀ : H ⊗[k] H) ⊗ₜ[k]
                              (incM (m₁ ⊗ₜ[k] m₂) : M ⊗[k] M)), houtmem⟩ :
                              TM (p + q)) =
                          ⟨TensorProduct.mapIncl (WM r) (WM (p + q - r))
                            ((⟨(h₁ : H) • (m₁ : M), hm₁⟩ : WM r) ⊗ₜ[k]
                              (⟨(h₂ : H) • (m₂ : M), hm₂⟩ : WM (p + q - r))),
                            Submodule.mem_iSup_of_mem r ⟨_, rfl⟩⟩ := by
                        apply Subtype.ext
                        change tensorDiagonalAction (k := k) (H := H) (M := M)
                            (((h₁ : H) ⊗ₜ[k] (h₂ : H)) ⊗ₜ[k]
                              ((m₁ : M) ⊗ₜ[k] (m₂ : M))) = _
                        rw [tensorDiagonalAction_tmul_tmul]
                        simp [TensorProduct.mapIncl]
                      rw [hout, moduleTensorSymbol_mapIncl_tmul]
                      change _ = gradedTensorDiagonalAction (k := k) (H := H) (M := M)
                        (regularTensorSymbol (k := k) (H := H) p
                            ⟨TensorProduct.mapIncl _ _ (h₁ ⊗ₜ[k] h₂), _⟩ ⊗ₜ[k]
                          moduleTensorSymbol (k := k) (H := H) (M := M) q
                            ⟨TensorProduct.mapIncl _ _ (m₁ ⊗ₜ[k] m₂), _⟩)
                      rw [regularTensorSymbol_mapIncl_tmul,
                        moduleTensorSymbol_mapIncl_tmul]
                      change _ = tensorDiagonalAction (k := k)
                        (H := AugmentationGradedHopf (k := k) (H := H))
                        (M := AugmentationGradedModule (k := k) (H := H) (M := M)) _
                      rw [tensorDiagonalAction_tmul_tmul,
                        DirectSum.Gmodule.of_smul_of, DirectSum.Gmodule.of_smul_of]
                      change _ = DirectSum.of _ ((i : ℕ) + (j : ℕ))
                          (augmentationGradedAction (k := k) (H := H) (M := M) i j
                            (Submodule.Quotient.mk ⟨h₁, hh₁⟩)
                            (Submodule.Quotient.mk m₁)) ⊗ₜ[k]
                        DirectSum.of _ ((p - (i : ℕ)) + (q - (j : ℕ)))
                          (augmentationGradedAction (k := k) (H := H) (M := M)
                            (p - i) (q - j)
                            (Submodule.Quotient.mk ⟨h₂, hh₂⟩)
                            (Submodule.Quotient.mk m₂))
                      rw [augmentationGradedAction_mk, augmentationGradedAction_mk]
                      apply congrArg₂ (fun u v => u ⊗ₜ[k] v)
                      · rfl
                      · apply DirectSum.of_eq_of_gradedMonoid_eq
                        apply Sigma.ext hright
                        exact augmentationGradedModule_mk_heq'
                          (k := k) (H := H) (M := M) hright _ _ rfl
                    exact LinearMap.congr_fun hpure v
                | zero => exact C.map_zero.trans D.map_zero.symm
                | add u v hu hv hu' hv' =>
                    change C (⟨u, hu⟩ + ⟨v, hv⟩) = D (⟨u, hu⟩ + ⟨v, hv⟩)
                    rw [map_add, map_add, hu', hv']
              exact hsecond s s.property
            exact LinearMap.congr_fun hCD b
          exact LinearMap.congr_fun hincH u
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add u v hu hv hu' hv' =>
          change A (⟨u, hu⟩ + ⟨v, hv⟩) = B (⟨u, hu⟩ + ⟨v, hv⟩)
          rw [map_add, map_add, hu', hv']
    exact hmain t t.property
  exact LinearMap.congr_fun hAB a

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
private theorem tensorSymbol_diagonalAction (p q : ℕ)
    (dh : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) p)
    (dm : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := M)) q) :
    moduleTensorSymbol (k := k) (H := H) (M := M) (p + q)
        (filteredTensorDiagonalAction (k := k) (H := H) (M := M) p q
          (dh ⊗ₜ[k] dm)) =
      gradedTensorDiagonalAction (k := k) (H := H) (M := M)
        (regularTensorSymbol (k := k) (H := H) p dh ⊗ₜ[k]
          moduleTensorSymbol (k := k) (H := H) (M := M) q dm) := by
  have h := LinearMap.congr_fun
    (tensorSymbol_diagonalAction_linear (k := k) (H := H) (M := M) p q)
    (dh ⊗ₜ[k] dm)
  simpa using h

private theorem augmentationGraded_comul_action_of_mk
    (i j : ℕ)
    (h : augmentationFiltration (k := k) (H := H) i)
    (m : augmentationModuleFiltration (k := k) (H := H) (M := M) j) :
    Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))
        (DirectSum.of
            (fun r => AugmentationGradedHopfPiece (k := k) (H := H) r)
            i (Submodule.Quotient.mk h) •
          DirectSum.of
            (fun r => AugmentationGradedModulePiece (k := k) (H := H) (M := M) r)
            j (Submodule.Quotient.mk m)) =
      TensorProduct.map
          (hopfModuleAction (k := k)
            (H := AugmentationGradedHopf (k := k) (H := H))
            (M := AugmentationGradedModule (k := k) (H := H) (M := M)))
          (hopfModuleAction (k := k)
            (H := AugmentationGradedHopf (k := k) (H := H))
            (M := AugmentationGradedModule (k := k) (H := H) (M := M)))
        (Coalgebra.comul (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H) ⊗[k]
            AugmentationGradedModule (k := k) (H := H) (M := M))
          (DirectSum.of
              (fun r => AugmentationGradedHopfPiece (k := k) (H := H) r)
              i (Submodule.Quotient.mk h) ⊗ₜ[k]
            DirectSum.of
              (fun r => AugmentationGradedModulePiece (k := k) (H := H) (M := M) r)
              j (Submodule.Quotient.mk m))) := by
  rw [DirectSum.Gmodule.of_smul_of]
  change augmentationGradedComul (k := k) (H := H) (M := M)
      (DirectSum.of _ (i + j)
        (augmentationGradedAction (k := k) (H := H) (M := M) i j
          (Submodule.Quotient.mk h) (Submodule.Quotient.mk m))) = _
  rw [augmentationGradedAction_mk, augmentationGradedComul_of_mk,
    TensorProduct.comul_tmul]
  rw [augmentationGradedHopf_comul_of_mk]
  rw [show Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))
        (DirectSum.of
          (fun r => AugmentationGradedModulePiece (k := k) (H := H) (M := M) r)
          j (Submodule.Quotient.mk m)) =
      gradedTensorInclusion (k := k) (H := H) (M := M) j
        (tensorFiltrationCoordinates (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := M)) j
          ⟨Coalgebra.comul (R := k) (A := M) m,
            augmentationModuleFiltration_comul (k := k) (H := H) (M := M)
              j m m.property⟩) by
      exact augmentationGradedComul_of_mk (k := k) (H := H) (M := M) j m]
  let dh : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) i :=
    ⟨Coalgebra.comul (R := k) (A := H) h,
      augmentationModuleFiltration_comul (k := k) (H := H) (M := H) i h (by
        rw [regular_augmentationModuleFiltration_eq]
        exact h.property)⟩
  let dm : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := M)) j :=
    ⟨Coalgebra.comul (R := k) (A := M) m,
      augmentationModuleFiltration_comul (k := k) (H := H) (M := M) j m m.property⟩
  change moduleTensorSymbol (k := k) (H := H) (M := M) (i + j)
      ⟨Coalgebra.comul (R := k) (A := M) ((h : H) • (m : M)), _⟩ =
    gradedTensorDiagonalAction (k := k) (H := H) (M := M)
      (regularTensorSymbol (k := k) (H := H) i dh ⊗ₜ[k]
        moduleTensorSymbol (k := k) (H := H) (M := M) j dm)
  have hsym := tensorSymbol_diagonalAction (k := k) (H := H) (M := M) i j dh dm
  let lhs : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := M)) (i + j) :=
    ⟨Coalgebra.comul (R := k) (A := M) ((h : H) • (m : M)),
      augmentationModuleFiltration_comul (k := k) (H := H) (M := M) (i + j)
        ((h : H) • (m : M)) (augmentationFiltration_action_le
          (k := k) (H := H) (M := M) i j
          (product_mem_actionSubspace h.property m.property))⟩
  change moduleTensorSymbol (k := k) (H := H) (M := M) (i + j) lhs = _
  have hinput : lhs =
      filteredTensorDiagonalAction (k := k) (H := H) (M := M) i j (dh ⊗ₜ[k] dm) := by
    apply Subtype.ext
    change Coalgebra.comul (R := k) (A := M) ((h : H) • (m : M)) = _
    rw [comul_smul, TensorProduct.comul_tmul]
    rfl
  rw [hinput]
  exact hsym

theorem augmentationGraded_comul_smul
    (h : AugmentationGradedHopf (k := k) (H := H))
    (m : AugmentationGradedModule (k := k) (H := H) (M := M)) :
    Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M)) (h • m) =
      TensorProduct.map
          (hopfModuleAction (k := k)
            (H := AugmentationGradedHopf (k := k) (H := H))
            (M := AugmentationGradedModule (k := k) (H := H) (M := M)))
          (hopfModuleAction (k := k)
            (H := AugmentationGradedHopf (k := k) (H := H))
            (M := AugmentationGradedModule (k := k) (H := H) (M := M)))
        (Coalgebra.comul (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H) ⊗[k]
            AugmentationGradedModule (k := k) (H := H) (M := M)) (h ⊗ₜ[k] m)) := by
  induction h using DirectSum.induction_on generalizing m with
  | zero => simp
  | add h h' hh hh' =>
      simpa only [add_smul, map_add, add_tmul] using
        congrArg₂ (fun x y => x + y) (hh m) (hh' m)
  | of i h =>
      induction m using DirectSum.induction_on with
      | zero => simp
      | add m m' hm hm' =>
          simpa only [smul_add, map_add, tmul_add] using
            congrArg₂ (fun x y => x + y) hm hm'
      | of j m =>
          induction h using Submodule.Quotient.induction_on with
          | _ h =>
              induction m using Submodule.Quotient.induction_on with
              | _ m =>
                  exact augmentationGraded_comul_action_of_mk
                    (k := k) (H := H) (M := M) i j h m

set_option maxHeartbeats 1000000 in
-- Extensionality unfolds the two induced graded coalgebra structures.
noncomputable instance augmentationGradedIsHopfModuleCoalgebra :
    IsHopfModuleCoalgebra k
      (AugmentationGradedHopf (k := k) (H := H))
      (AugmentationGradedModule (k := k) (H := H) (M := M)) where
  counit_action := by
    apply TensorProduct.ext'
    intro h m
    simpa [mul_comm] using augmentationGraded_counit_smul
      (k := k) (H := H) (M := M) h m
  comul_action := by
    apply TensorProduct.ext'
    intro h m
    exact augmentationGraded_comul_smul
      (k := k) (H := H) (M := M) h m

end

end HopfAmenability
