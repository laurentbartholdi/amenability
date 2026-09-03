/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.AssociatedGradedCoalgebra

/-! # Hopf structure on the augmentation associated graded -/

open Coalgebra TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]

/-- The degreewise identification of the ideal-power and regular-module
augmentation quotients. -/
noncomputable def augmentationGradedRegularPieceEquiv (n : ℕ) :
    AugmentationGradedHopfPiece (k := k) (H := H) n ≃ₗ[k]
      AugmentationGradedModulePiece (k := k) (H := H) (M := H) n := by
  let e : augmentationFiltration (k := k) (H := H) n ≃ₗ[k]
      augmentationModuleFiltration (k := k) (H := H) (M := H) n :=
    LinearEquiv.ofEq _ _ (regular_augmentationModuleFiltration_eq
      (k := k) (H := H) n).symm
  apply Submodule.Quotient.equiv _ _ e
  ext x
  simp [e, regular_augmentationModuleFiltration_eq]

/-- The regular-module realization of the augmentation associated graded is
linearly identical to the associated graded defined from ideal powers. -/
noncomputable def augmentationGradedRegularEquiv :
    AugmentationGradedHopf (k := k) (H := H) ≃ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := H) :=
  DirectSum.congrLinearEquiv fun n =>
    augmentationGradedRegularPieceEquiv (k := k) (H := H) n

@[simp]
theorem augmentationGradedRegularEquiv_of_mk (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) n) :
    augmentationGradedRegularEquiv (k := k) (H := H)
        (DirectSum.of _ n (Submodule.Quotient.mk x)) =
      DirectSum.of _ n (Submodule.Quotient.mk
        (⟨x, by
          rw [regular_augmentationModuleFiltration_eq]
          exact x.property⟩ :
          augmentationModuleFiltration (k := k) (H := H) (M := H) n)) := by
  change (augmentationGradedRegularEquiv (k := k) (H := H)).toLinearMap
      (DirectSum.of _ n (Submodule.Quotient.mk x)) = _
  rw [augmentationGradedRegularEquiv,
    DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_of]
  rfl

@[simp]
theorem augmentationGradedRegularEquiv_symm_of_mk (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) n) :
    (augmentationGradedRegularEquiv (k := k) (H := H)).symm
        (DirectSum.of _ n (Submodule.Quotient.mk
          (⟨x, by
            rw [regular_augmentationModuleFiltration_eq]
            exact x.property⟩ :
            augmentationModuleFiltration (k := k) (H := H) (M := H) n))) =
      DirectSum.of _ n (Submodule.Quotient.mk x) := by
  apply (augmentationGradedRegularEquiv (k := k) (H := H)).injective
  rw [LinearEquiv.apply_symm_apply, augmentationGradedRegularEquiv_of_mk]

/-- The coalgebra on the associated graded Hopf algebra, transported along
the canonical identification with the regular-module construction. -/
noncomputable instance augmentationGradedHopfCoalgebra :
    Coalgebra k (AugmentationGradedHopf (k := k) (H := H)) :=
  (augmentationGradedRegularEquiv (k := k) (H := H)).coalgebra k

@[simp]
theorem augmentationGradedHopf_counit_of_zero
    (x : augmentationFiltration (k := k) (H := H) 0) :
    Coalgebra.counit (R := k)
        (A := AugmentationGradedHopf (k := k) (H := H))
        (DirectSum.of _ 0 (Submodule.Quotient.mk x)) =
      Coalgebra.counit (R := k) (A := H) x := by
  change augmentationGradedCounit (k := k) (H := H) (M := H)
      (augmentationGradedRegularEquiv (k := k) (H := H)
        (DirectSum.of _ 0 (Submodule.Quotient.mk x))) = _
  rw [augmentationGradedRegularEquiv_of_mk,
    augmentationGradedCounit_of_zero]

@[simp]
theorem augmentationGradedHopf_counit_of_succ (n : ℕ)
    (x : AugmentationGradedHopfPiece (k := k) (H := H) (n + 1)) :
    Coalgebra.counit (R := k)
        (A := AugmentationGradedHopf (k := k) (H := H))
        (DirectSum.of _ (n + 1) x) = 0 := by
  change augmentationGradedCounit (k := k) (H := H) (M := H)
      (augmentationGradedRegularEquiv (k := k) (H := H)
        (DirectSum.of _ (n + 1) x)) = 0
  change augmentationGradedCounit (k := k) (H := H) (M := H)
      ((DirectSum.congrLinearEquiv fun n =>
        augmentationGradedRegularPieceEquiv (k := k) (H := H) n)
        (DirectSum.of _ (n + 1) x)) = 0
  let u : ∀ m, AugmentationGradedHopfPiece (k := k) (H := H) m ≃ₗ[k]
      AugmentationGradedModulePiece (k := k) (H := H) (M := H) m :=
    fun m => augmentationGradedRegularPieceEquiv (k := k) (H := H) m
  change augmentationGradedCounit (k := k) (H := H) (M := H)
      ((DirectSum.congrLinearEquiv u) (DirectSum.of _ (n + 1) x)) = 0
  rw [show (DirectSum.congrLinearEquiv u) (DirectSum.of _ (n + 1) x) =
      DirectSum.lmap (fun m => (u m).toLinearMap) (DirectSum.of _ (n + 1) x) by
      exact congrFun (DirectSum.coe_congrLinearEquiv u) _]
  rw [DirectSum.lmap_of, augmentationGradedCounit_of_succ]

theorem augmentationGradedHopf_counit_of_ne_zero (n : ℕ) (hn : n ≠ 0)
    (x : AugmentationGradedHopfPiece (k := k) (H := H) n) :
    Coalgebra.counit (R := k)
        (A := AugmentationGradedHopf (k := k) (H := H))
        (DirectSum.of _ n x) = 0 := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => exact augmentationGradedHopf_counit_of_succ n x

theorem augmentationGradedHopf_counit_one :
    Coalgebra.counit (R := k)
      (A := AugmentationGradedHopf (k := k) (H := H)) 1 = 1 := by
  rw [DirectSum.one_def]
  change Coalgebra.counit (R := k)
      (A := AugmentationGradedHopf (k := k) (H := H))
      (DirectSum.of _ 0 (Submodule.Quotient.mk
        (⟨1, by rw [augmentationFiltration_zero]; exact Submodule.mem_top⟩ :
          augmentationFiltration (k := k) (H := H) 0))) = 1
  rw [augmentationGradedHopf_counit_of_zero]
  simp

theorem augmentationGradedHopf_counit_mul
    (a b : AugmentationGradedHopf (k := k) (H := H)) :
    Coalgebra.counit (R := k) (A := AugmentationGradedHopf (k := k) (H := H))
        (a * b) =
      Coalgebra.counit (R := k) (A := AugmentationGradedHopf (k := k) (H := H)) a *
        Coalgebra.counit (R := k) (A := AugmentationGradedHopf (k := k) (H := H)) b := by
  induction a using DirectSum.induction_on generalizing b with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_mul]
  | of i a =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb', mul_add]
      | of j b =>
          induction a using Submodule.Quotient.induction_on with
          | _ x =>
              induction b using Submodule.Quotient.induction_on with
              | _ y =>
                  rw [DirectSum.of_mul_of]
                  change Coalgebra.counit (R := k)
                      (A := AugmentationGradedHopf (k := k) (H := H))
                      (DirectSum.of _ (i + j)
                        (augmentationGradedMul (k := k) (H := H) i j
                          (Submodule.Quotient.mk x) (Submodule.Quotient.mk y))) = _
                  rw [augmentationGradedMul_mk]
                  by_cases hij : i + j = 0
                  · have hi : i = 0 := by omega
                    have hj : j = 0 := by omega
                    subst i
                    subst j
                    simp [Bialgebra.counit_mul]
                  · have hlhs : Coalgebra.counit (R := k)
                        (A := AugmentationGradedHopf (k := k) (H := H))
                        (DirectSum.of _ (i + j)
                          (Submodule.Quotient.mk ⟨(x : H) * y,
                            augmentationFiltration_mul_le i j
                              (Submodule.mul_mem_mul x.property y.property)⟩)) = 0 := by
                      exact augmentationGradedHopf_counit_of_ne_zero (i + j) hij _
                    rw [hlhs]
                    rcases (show i ≠ 0 ∨ j ≠ 0 by omega) with hi | hj
                    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
                      rw [augmentationGradedHopf_counit_of_succ]
                      simp
                    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
                      rw [augmentationGradedHopf_counit_of_succ]
                      simp

theorem augmentationGradedRegularEquiv_map_comul
    (a : AugmentationGradedHopf (k := k) (H := H)) :
    TensorProduct.map
        (augmentationGradedRegularEquiv (k := k) (H := H)).toLinearMap
        (augmentationGradedRegularEquiv (k := k) (H := H)).toLinearMap
        (Coalgebra.comul (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H)) a) =
      Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := H))
        (augmentationGradedRegularEquiv (k := k) (H := H) a) := by
  change TensorProduct.map
      (augmentationGradedRegularEquiv (k := k) (H := H)).toLinearMap
      (augmentationGradedRegularEquiv (k := k) (H := H)).toLinearMap
      (TensorProduct.map
        (augmentationGradedRegularEquiv (k := k) (H := H)).symm.toLinearMap
        (augmentationGradedRegularEquiv (k := k) (H := H)).symm.toLinearMap
        (Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := H))
          (augmentationGradedRegularEquiv (k := k) (H := H) a))) = _
  rw [TensorProduct.map_map]
  simp

/-- Reinterpret regular-module tensor symbols as tensors of the actual
augmentation-graded Hopf algebra. -/
def augmentationGradedHopfTensorInclusion (n : ℕ) :
    (DirectSum (Fin (n + 1)) fun i =>
      AugmentationGradedModulePiece (k := k) (H := H) (M := H) i ⊗[k]
        AugmentationGradedModulePiece (k := k) (H := H) (M := H) (n - i)) →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) ⊗[k]
        AugmentationGradedHopf (k := k) (H := H) :=
  (TensorProduct.map
    (augmentationGradedRegularEquiv (k := k) (H := H)).symm.toLinearMap
    (augmentationGradedRegularEquiv (k := k) (H := H)).symm.toLinearMap).comp
      (gradedTensorInclusion (k := k) (H := H) (M := H) n)

@[simp]
theorem augmentationGradedHopfTensorInclusion_of_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x : augmentationFiltration (k := k) (H := H) i)
    (y : augmentationFiltration (k := k) (H := H) (n - i)) :
    augmentationGradedHopfTensorInclusion (k := k) (H := H) n
        (DirectSum.of _ i
          (Submodule.Quotient.mk
              (⟨x, by rw [regular_augmentationModuleFiltration_eq]; exact x.property⟩ :
                augmentationModuleFiltration (k := k) (H := H) (M := H) i) ⊗ₜ[k]
            Submodule.Quotient.mk
              (⟨y, by rw [regular_augmentationModuleFiltration_eq]; exact y.property⟩ :
                augmentationModuleFiltration (k := k) (H := H) (M := H) (n - i)))) =
      DirectSum.of _ (i : ℕ) (Submodule.Quotient.mk x) ⊗ₜ[k]
        DirectSum.of _ (n - i) (Submodule.Quotient.mk y) := by
  rw [augmentationGradedHopfTensorInclusion, LinearMap.comp_apply,
    gradedTensorInclusion_of_tmul, TensorProduct.map_tmul]
  apply congrArg₂ (fun a b => a ⊗ₜ[k] b)
  · exact augmentationGradedRegularEquiv_symm_of_mk
      (k := k) (H := H) i x
  · exact augmentationGradedRegularEquiv_symm_of_mk
      (k := k) (H := H) (n - i) y

@[simp]
theorem augmentationGradedHopfTensorInclusion_of_regular_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x : augmentationModuleFiltration (k := k) (H := H) (M := H) i)
    (y : augmentationModuleFiltration (k := k) (H := H) (M := H) (n - i)) :
    augmentationGradedHopfTensorInclusion (k := k) (H := H) n
        (DirectSum.of _ i
          (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y)) =
      DirectSum.of _ (i : ℕ)
          (Submodule.Quotient.mk
            (⟨x, by rw [← regular_augmentationModuleFiltration_eq]; exact x.property⟩ :
              augmentationFiltration (k := k) (H := H) i)) ⊗ₜ[k]
        DirectSum.of _ (n - i)
          (Submodule.Quotient.mk
            (⟨y, by rw [← regular_augmentationModuleFiltration_eq]; exact y.property⟩ :
              augmentationFiltration (k := k) (H := H) (n - i))) := by
  exact augmentationGradedHopfTensorInclusion_of_tmul
    (k := k) (H := H) n i
    ⟨x, by rw [← regular_augmentationModuleFiltration_eq]; exact x.property⟩
    ⟨y, by rw [← regular_augmentationModuleFiltration_eq]; exact y.property⟩

@[simp]
theorem augmentationGradedHopf_comul_of_mk (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) n) :
    Coalgebra.comul (R := k)
        (A := AugmentationGradedHopf (k := k) (H := H))
        (DirectSum.of _ n (Submodule.Quotient.mk x)) =
      augmentationGradedHopfTensorInclusion (k := k) (H := H) n
        (tensorFiltrationCoordinates (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) n
          ⟨Coalgebra.comul (R := k) (A := H) x,
            augmentationModuleFiltration_comul (k := k) (H := H) (M := H) n
              x (by
                rw [regular_augmentationModuleFiltration_eq]
                exact x.property)⟩) := by
  let e := augmentationGradedRegularEquiv (k := k) (H := H)
  apply (TensorProduct.map_bijective e.bijective e.bijective).injective
  rw [augmentationGradedRegularEquiv_map_comul,
    augmentationGradedRegularEquiv_of_mk]
  change augmentationGradedComul (k := k) (H := H) (M := H)
      (DirectSum.of _ n (Submodule.Quotient.mk
        (⟨x, by
          rw [regular_augmentationModuleFiltration_eq]
          exact x.property⟩ :
          augmentationModuleFiltration (k := k) (H := H) (M := H) n))) = _
  rw [augmentationGradedComul_of_mk]
  simp [augmentationGradedHopfTensorInclusion, e, TensorProduct.map_map]

/-- Under the regular-module identification, multiplication is the graded
regular action. -/
theorem augmentationGradedRegularEquiv_mul
    (a b : AugmentationGradedHopf (k := k) (H := H)) :
    augmentationGradedRegularEquiv (k := k) (H := H) (a * b) =
      a • augmentationGradedRegularEquiv (k := k) (H := H) b := by
  induction a using DirectSum.induction_on generalizing b with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, add_smul, ha, ha']
  | of i a =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, smul_add, hb, hb']
      | of j b =>
          induction a using Submodule.Quotient.induction_on with
          | _ x =>
              induction b using Submodule.Quotient.induction_on with
              | _ y =>
                  rw [DirectSum.of_mul_of]
                  change augmentationGradedRegularEquiv (k := k) (H := H)
                      (DirectSum.of _ (i + j)
                        (augmentationGradedMul (k := k) (H := H) i j
                          (Submodule.Quotient.mk x) (Submodule.Quotient.mk y))) = _
                  rw [augmentationGradedMul_mk,
                    augmentationGradedRegularEquiv_of_mk]
                  rw [augmentationGradedRegularEquiv_of_mk]
                  rw [DirectSum.Gmodule.of_smul_of]
                  change _ = DirectSum.of _ (i + j)
                    (augmentationGradedAction (k := k) (H := H) (M := H) i j
                      (Submodule.Quotient.mk x)
                      (Submodule.Quotient.mk ⟨y, by
                        rw [regular_augmentationModuleFiltration_eq]
                        exact y.property⟩))
                  rw [augmentationGradedAction_mk]
                  rfl

theorem augmentationGradedHopf_comul_one :
    Coalgebra.comul (R := k)
      (A := AugmentationGradedHopf (k := k) (H := H)) 1 = 1 := by
  rw [DirectSum.one_def]
  change Coalgebra.comul (R := k)
      (A := AugmentationGradedHopf (k := k) (H := H))
      (DirectSum.of _ 0 (Submodule.Quotient.mk
        (⟨1, by rw [augmentationFiltration_zero]; exact Submodule.mem_top⟩ :
          augmentationFiltration (k := k) (H := H) 0))) = 1
  rw [augmentationGradedHopf_comul_of_mk]
  let z : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) 0 :=
    ⟨Coalgebra.comul (R := k) (A := H) (1 : H),
      augmentationModuleFiltration_comul (k := k) (H := H) (M := H) 0
        (1 : H) (by
          rw [regular_augmentationModuleFiltration_eq,
            augmentationFiltration_zero]
          exact Submodule.mem_top)⟩
  let x : augmentationModuleFiltration (k := k) (H := H) (M := H) 0 :=
    ⟨1, by
      rw [regular_augmentationModuleFiltration_eq, augmentationFiltration_zero]
      exact Submodule.mem_top⟩
  have hmap : TensorProduct.mapIncl
      (augmentationModuleFiltration (k := k) (H := H) (M := H) 0)
      (augmentationModuleFiltration (k := k) (H := H) (M := H) 0)
      (x ⊗ₜ[k] x) ∈
        tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) 0 := by
    rw [tensorFiltration]
    apply Submodule.mem_iSup_of_mem (⟨0, by omega⟩ : Fin 1)
    exact ⟨x ⊗ₜ[k] x, rfl⟩
  have hmem : (1 : H) ⊗ₜ[k] (1 : H) ∈
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) 0 := by
    simpa [TensorProduct.mapIncl, x] using hmap
  have hz : z = ⟨(1 : H) ⊗ₜ[k] (1 : H), hmem⟩ := by
    apply Subtype.ext
    simp [z, Algebra.TensorProduct.one_def]
  have hzx : (⟨(1 : H) ⊗ₜ[k] (1 : H), hmem⟩ :
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) 0) =
      ⟨TensorProduct.mapIncl
        (augmentationModuleFiltration (k := k) (H := H) (M := H) 0)
        (augmentationModuleFiltration (k := k) (H := H) (M := H) 0)
        (x ⊗ₜ[k] x), hmap⟩ := by
    apply Subtype.ext
    simp [TensorProduct.mapIncl, x]
  change augmentationGradedHopfTensorInclusion (k := k) (H := H) 0
      (tensorFiltrationCoordinates (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) 0 z) = 1
  rw [hz]
  rw [hzx]
  have hcoords := tensorFiltrationCoordinates_mapIncl_tmul (k := k)
    (augmentationModuleFiltration (k := k) (H := H) (M := H))
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := H))
    0 (⟨0, by omega⟩ : Fin 1) x x
  have hincl := congrArg
    (augmentationGradedHopfTensorInclusion (k := k) (H := H) 0) hcoords
  change augmentationGradedHopfTensorInclusion (k := k) (H := H) 0
      (tensorFiltrationCoordinates (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) 0
        ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] x), hmap⟩) = 1
  calc
    _ = augmentationGradedHopfTensorInclusion (k := k) (H := H) 0
        (DirectSum.of _ (⟨0, by omega⟩ : Fin 1)
          (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk x)) := by
      simpa only [Fin.isValue, Nat.zero_sub] using hincl
    _ = 1 := by
      rw [augmentationGradedHopfTensorInclusion_of_regular_tmul]
      rw [Algebra.TensorProduct.one_def]
      apply congrArg₂ (fun a b => a ⊗ₜ[k] b)
      · rw [DirectSum.one_def]
        rfl
      · rw [DirectSum.one_def]
        rfl

/-- The total-degree tensor leading-symbol map for the regular filtration. -/
def regularTensorSymbol (n : ℕ) :
    tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) n →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) ⊗[k]
        AugmentationGradedHopf (k := k) (H := H) :=
  (augmentationGradedHopfTensorInclusion (k := k) (H := H) n).comp
    (tensorFiltrationCoordinates (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) n)

@[simp]
theorem regularTensorSymbol_mapIncl_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x : augmentationModuleFiltration (k := k) (H := H) (M := H) i)
    (y : augmentationModuleFiltration (k := k) (H := H) (M := H) (n - i)) :
    regularTensorSymbol (k := k) (H := H) n
        ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), by
          rw [tensorFiltration]
          exact Submodule.mem_iSup_of_mem i ⟨x ⊗ₜ[k] y, rfl⟩⟩ =
      DirectSum.of _ (i : ℕ)
          (Submodule.Quotient.mk
            (⟨x, by
              rw [← regular_augmentationModuleFiltration_eq]
              exact x.property⟩ : augmentationFiltration (k := k) (H := H) i)) ⊗ₜ[k]
        DirectSum.of _ (n - i)
          (Submodule.Quotient.mk
            (⟨y, by
              rw [← regular_augmentationModuleFiltration_eq]
              exact y.property⟩ : augmentationFiltration (k := k) (H := H) (n - i))) := by
  rw [regularTensorSymbol, LinearMap.comp_apply]
  have hcoords := tensorFiltrationCoordinates_mapIncl_tmul (k := k)
    (augmentationModuleFiltration (k := k) (H := H) (M := H))
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := H)) n i x y
  rw [hcoords, augmentationGradedHopfTensorInclusion_of_regular_tmul]

private theorem regularModuleFiltration_mul_le (i j : ℕ) :
    augmentationModuleFiltration (k := k) (H := H) (M := H) i *
        augmentationModuleFiltration (k := k) (H := H) (M := H) j ≤
      augmentationModuleFiltration (k := k) (H := H) (M := H) (i + j) := by
  rw [regular_augmentationModuleFiltration_eq,
    regular_augmentationModuleFiltration_eq,
    regular_augmentationModuleFiltration_eq]
  exact augmentationFiltration_mul_le (k := k) (H := H) i j

private theorem augmentationGradedHopf_mk_heq
    {p q : ℕ} (hpq : p = q)
    (x : augmentationFiltration (k := k) (H := H) p)
    (y : augmentationFiltration (k := k) (H := H) q)
    (hxy : (x : H) = y) :
    HEq (Submodule.Quotient.mk x :
        AugmentationGradedHopfPiece (k := k) (H := H) p)
      (Submodule.Quotient.mk y :
        AugmentationGradedHopfPiece (k := k) (H := H) q) := by
  subst q
  apply heq_of_eq
  apply congrArg Submodule.Quotient.mk
  exact Subtype.ext hxy

private theorem regularTensorFiltration_mul_le (m n : ℕ) :
    tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) m *
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) n ≤
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) (m + n) :=
  tensorFiltration_mul_le (k := k) (H := H) _
    (regularModuleFiltration_mul_le (k := k) (H := H)) m n

private def filteredRegularTensorMul (m n : ℕ) :
    tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) m ⊗[k]
        tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) n →ₗ[k]
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) (m + n) :=
  ((LinearMap.mul' k (H ⊗[k] H)).comp
      (TensorProduct.map
        (tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) m).subtype
        (tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := H)) n).subtype)).codRestrict _
    (by
      intro t
      induction t with
      | zero => exact Submodule.zero_mem _
      | add a b ha hb => simpa using Submodule.add_mem _ ha hb
      | tmul a b =>
          exact regularTensorFiltration_mul_le (k := k) (H := H) m n
            (Submodule.mul_mem_mul a.property b.property))

@[simp]
private theorem filteredRegularTensorMul_tmul (m n : ℕ)
    (a : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) m)
    (b : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) n) :
    filteredRegularTensorMul (k := k) (H := H) m n (a ⊗ₜ[k] b) =
      ⟨(a : H ⊗[k] H) * b,
        regularTensorFiltration_mul_le (k := k) (H := H) m n
          (Submodule.mul_mem_mul a.property b.property)⟩ := by
  rfl

set_option maxHeartbeats 4000000 in
-- Multiplication of total leading symbols is checked on four filtered factors.
private theorem regularTensorSymbol_mul_linear (m n : ℕ) :
    (regularTensorSymbol (k := k) (H := H) (m + n)).comp
        (filteredRegularTensorMul (k := k) (H := H) m n) =
      (LinearMap.mul' k
        (AugmentationGradedHopf (k := k) (H := H) ⊗[k]
          AugmentationGradedHopf (k := k) (H := H))).comp
        (TensorProduct.map
          (regularTensorSymbol (k := k) (H := H) m)
          (regularTensorSymbol (k := k) (H := H) n)) := by
  apply TensorProduct.ext'
  intro a b
  let W : ℕ → Submodule k H :=
    augmentationModuleFiltration (k := k) (H := H) (M := H)
  let T (r : ℕ) := tensorFiltration (k := k) W r
  let σ (r : ℕ) := regularTensorSymbol (k := k) (H := H) r
  let A : T m →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) ⊗[k]
        AugmentationGradedHopf (k := k) (H := H) :=
    (σ (m + n)).comp ((filteredRegularTensorMul (k := k) (H := H) m n).comp
      (TensorProduct.mk k (T m) (T n) |>.flip b))
  let B : T m →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) ⊗[k]
        AugmentationGradedHopf (k := k) (H := H) :=
    (LinearMap.mulRight k (σ n b)).comp (σ m)
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : H ⊗[k] H) (hv : v ∈ T m),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem i v hvi =>
          rcases hvi with ⟨q, rfl⟩
          let inc : W i ⊗[k] W (m - i) →ₗ[k] T m :=
            (TensorProduct.mapIncl (W i) (W (m - i))).codRestrict _
              (fun q => Submodule.mem_iSup_of_mem i ⟨q, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro x y
            let p : T m := inc (x ⊗ₜ[k] y)
            let C : T n →ₗ[k]
                AugmentationGradedHopf (k := k) (H := H) ⊗[k]
                  AugmentationGradedHopf (k := k) (H := H) :=
              (σ (m + n)).comp
                ((filteredRegularTensorMul (k := k) (H := H) m n).comp
                  (TensorProduct.mk k (T m) (T n) p))
            let D : T n →ₗ[k]
                AugmentationGradedHopf (k := k) (H := H) ⊗[k]
                  AugmentationGradedHopf (k := k) (H := H) :=
              (LinearMap.mulLeft k (σ m p)).comp (σ n)
            have hCD : C = D := by
              apply LinearMap.ext
              intro s
              have hsecond : ∀ (w : H ⊗[k] H) (hw : w ∈ T n),
                  C ⟨w, hw⟩ = D ⟨w, hw⟩ := by
                intro w hw
                induction hw using Submodule.iSup_induction' with
                | mem j w hwj =>
                    rcases hwj with ⟨q', rfl⟩
                    let inc' : W j ⊗[k] W (n - j) →ₗ[k] T n :=
                      (TensorProduct.mapIncl (W j) (W (n - j))).codRestrict _
                        (fun q' => Submodule.mem_iSup_of_mem j ⟨q', rfl⟩)
                    have hpure : C.comp inc' = D.comp inc' := by
                      apply TensorProduct.ext'
                      intro x' y'
                      let r : Fin (m + n + 1) :=
                        ⟨(i : ℕ) + (j : ℕ), by omega⟩
                      have hright : m + n - (r : ℕ) =
                          (m - (i : ℕ)) + (n - (j : ℕ)) := by
                        dsimp [r]
                        omega
                      have hxmul : (x : H) * x' ∈ W r :=
                        regularModuleFiltration_mul_le (k := k) (H := H) i j
                          (Submodule.mul_mem_mul x.property x'.property)
                      have hymul : (y : H) * y' ∈ W (m + n - r) := by
                        rw [hright]
                        exact regularModuleFiltration_mul_le (k := k) (H := H)
                          (m - i) (n - j)
                          (Submodule.mul_mem_mul y.property y'.property)
                      have hprod : (p : H ⊗[k] H) * (inc' (x' ⊗ₜ[k] y') : H ⊗[k] H) =
                          TensorProduct.mapIncl (W r) (W (m + n - r))
                            ((⟨(x : H) * x', hxmul⟩ : W r) ⊗ₜ[k]
                              (⟨(y : H) * y', hymul⟩ : W (m + n - r))) := by
                        change ((x : H) ⊗ₜ[k] (y : H)) *
                            ((x' : H) ⊗ₜ[k] (y' : H)) = _
                        simp [TensorProduct.mapIncl]
                      change σ (m + n)
                          (filteredRegularTensorMul (k := k) (H := H) m n
                            (p ⊗ₜ[k] inc' (x' ⊗ₜ[k] y'))) =
                        σ m p * σ n (inc' (x' ⊗ₜ[k] y'))
                      rw [filteredRegularTensorMul_tmul]
                      have hsub : (⟨(p : H ⊗[k] H) * inc' (x' ⊗ₜ[k] y'),
                          regularTensorFiltration_mul_le (k := k) (H := H) m n
                            (Submodule.mul_mem_mul p.property
                              (inc' (x' ⊗ₜ[k] y')).property)⟩ : T (m + n)) =
                          ⟨TensorProduct.mapIncl (W r) (W (m + n - r))
                            ((⟨(x : H) * x', hxmul⟩ : W r) ⊗ₜ[k]
                              (⟨(y : H) * y', hymul⟩ : W (m + n - r))),
                            Submodule.mem_iSup_of_mem r ⟨_, rfl⟩⟩ := by
                        apply Subtype.ext
                        exact hprod
                      rw [hsub]
                      rw [regularTensorSymbol_mapIncl_tmul]
                      change _ = regularTensorSymbol (k := k) (H := H) m
                          ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩ *
                        regularTensorSymbol (k := k) (H := H) n
                          ⟨TensorProduct.mapIncl _ _ (x' ⊗ₜ[k] y'), _⟩
                      rw [regularTensorSymbol_mapIncl_tmul,
                        regularTensorSymbol_mapIncl_tmul]
                      simp only [Algebra.TensorProduct.tmul_mul_tmul,
                        DirectSum.of_mul_of]
                      apply congrArg₂ (fun u v => u ⊗ₜ[k] v)
                      · apply DirectSum.of_eq_of_gradedMonoid_eq
                        apply Sigma.ext rfl
                        change HEq ((Submodule.Quotient.mk
                            (⟨(x : H) * x', _⟩ :
                              augmentationFiltration (k := k) (H := H) (i + j))) :
                            AugmentationGradedHopfPiece (k := k) (H := H) (i + j))
                          (augmentationGradedMul (k := k) (H := H) i j
                            (Submodule.Quotient.mk (⟨x, by
                              rw [← regular_augmentationModuleFiltration_eq]
                              exact x.property⟩ : augmentationFiltration
                                (k := k) (H := H) i))
                            (Submodule.Quotient.mk (⟨x', by
                              rw [← regular_augmentationModuleFiltration_eq]
                              exact x'.property⟩ : augmentationFiltration
                                (k := k) (H := H) j)))
                        rw [augmentationGradedMul_mk]
                      · apply DirectSum.of_eq_of_gradedMonoid_eq
                        apply Sigma.ext hright
                        change HEq (Submodule.Quotient.mk
                            (⟨(y : H) * y', _⟩ : augmentationFiltration
                              (k := k) (H := H) (m + n - r)))
                          (augmentationGradedMul (k := k) (H := H)
                            (m - i) (n - j)
                            (Submodule.Quotient.mk (⟨y, by
                              rw [← regular_augmentationModuleFiltration_eq]
                              exact y.property⟩ : augmentationFiltration
                                (k := k) (H := H) (m - i)))
                            (Submodule.Quotient.mk (⟨y', by
                              rw [← regular_augmentationModuleFiltration_eq]
                              exact y'.property⟩ : augmentationFiltration
                                (k := k) (H := H) (n - j))))
                        rw [augmentationGradedMul_mk]
                        exact augmentationGradedHopf_mk_heq
                          (k := k) (H := H) hright _ _ rfl
                    exact LinearMap.congr_fun hpure q'
                | zero => exact C.map_zero.trans D.map_zero.symm
                | add u v hu hv hu' hv' =>
                    change C (⟨u, hu⟩ + ⟨v, hv⟩) = D (⟨u, hu⟩ + ⟨v, hv⟩)
                    rw [map_add, map_add, hu', hv']
              exact hsecond s s.property
            exact LinearMap.congr_fun hCD b
          exact LinearMap.congr_fun hinc q
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add u v hu hv hu' hv' =>
          change A (⟨u, hu⟩ + ⟨v, hv⟩) = B (⟨u, hu⟩ + ⟨v, hv⟩)
          rw [map_add, map_add, hu', hv']
    exact hmain t t.property
  exact LinearMap.congr_fun hAB a

private theorem regularTensorSymbol_mul (m n : ℕ)
    (a : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) m)
    (b : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) n) :
    regularTensorSymbol (k := k) (H := H) (m + n)
        (filteredRegularTensorMul (k := k) (H := H) m n (a ⊗ₜ[k] b)) =
      regularTensorSymbol (k := k) (H := H) m a *
        regularTensorSymbol (k := k) (H := H) n b := by
  have h := LinearMap.congr_fun
    (regularTensorSymbol_mul_linear (k := k) (H := H) m n) (a ⊗ₜ[k] b)
  simpa using h

theorem augmentationGradedHopf_comul_mul
    (a b : AugmentationGradedHopf (k := k) (H := H)) :
    Coalgebra.comul (R := k)
        (A := AugmentationGradedHopf (k := k) (H := H)) (a * b) =
      Coalgebra.comul (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H)) a *
        Coalgebra.comul (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H)) b := by
  induction a using DirectSum.induction_on generalizing b with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_mul]
  | of i a =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb', mul_add]
      | of j b =>
          induction a using Submodule.Quotient.induction_on with
          | _ x =>
              induction b using Submodule.Quotient.induction_on with
              | _ y =>
                  rw [DirectSum.of_mul_of]
                  change Coalgebra.comul (R := k)
                      (A := AugmentationGradedHopf (k := k) (H := H))
                      (DirectSum.of _ (i + j)
                        (augmentationGradedMul (k := k) (H := H) i j
                          (Submodule.Quotient.mk x) (Submodule.Quotient.mk y))) = _
                  rw [augmentationGradedMul_mk,
                    augmentationGradedHopf_comul_of_mk,
                    augmentationGradedHopf_comul_of_mk,
                    augmentationGradedHopf_comul_of_mk]
                  let dx : tensorFiltration (k := k)
                      (augmentationModuleFiltration (k := k) (H := H) (M := H)) i :=
                    ⟨Coalgebra.comul (R := k) (A := H) x,
                      augmentationModuleFiltration_comul
                        (k := k) (H := H) (M := H) i x (by
                          rw [regular_augmentationModuleFiltration_eq]
                          exact x.property)⟩
                  let dy : tensorFiltration (k := k)
                      (augmentationModuleFiltration (k := k) (H := H) (M := H)) j :=
                    ⟨Coalgebra.comul (R := k) (A := H) y,
                      augmentationModuleFiltration_comul
                        (k := k) (H := H) (M := H) j y (by
                          rw [regular_augmentationModuleFiltration_eq]
                          exact y.property)⟩
                  change regularTensorSymbol (k := k) (H := H) (i + j)
                      ⟨Coalgebra.comul (R := k) (A := H) ((x : H) * y), _⟩ =
                    regularTensorSymbol (k := k) (H := H) i dx *
                      regularTensorSymbol (k := k) (H := H) j dy
                  have hmul := regularTensorSymbol_mul (k := k) (H := H) i j dx dy
                  rw [filteredRegularTensorMul_tmul] at hmul
                  convert hmul using 1
                  apply congrArg (regularTensorSymbol (k := k) (H := H) (i + j))
                  apply Subtype.ext
                  exact Bialgebra.comul_mul (R := k) (x : H) y

noncomputable instance augmentationGradedHopfBialgebra :
    Bialgebra k (AugmentationGradedHopf (k := k) (H := H)) :=
  Bialgebra.mk' k _ augmentationGradedHopf_counit_one
    (fun {a b} => augmentationGradedHopf_counit_mul a b)
    augmentationGradedHopf_comul_one
    (fun {a b} => augmentationGradedHopf_comul_mul a b)

private def augmentationGradedHopfLeading (n : ℕ) :
    H →ₗ[k] AugmentationGradedHopf (k := k) (H := H) :=
  filtrationGradedLeading (k := k)
    (augmentationFiltration (k := k) (H := H)) n

@[simp]
private theorem augmentationGradedHopfLeading_apply (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) n) :
    augmentationGradedHopfLeading (k := k) (H := H) n x =
      DirectSum.of _ n (Submodule.Quotient.mk x) :=
  filtrationGradedLeading_apply (k := k)
    (augmentationFiltration (k := k) (H := H)) n x

set_option maxHeartbeats 4000000 in
-- The induced antipode contracts each total-degree tensor symbol as upstairs.
private theorem gradedAntipode_rTensor_mul_on_regularTensorFiltration
    (n : ℕ) (z : H ⊗[k] H)
    (hz : z ∈ tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) n) :
    LinearMap.mul' k (AugmentationGradedHopf (k := k) (H := H))
        ((augmentationGradedAntipode (k := k) (H := H)).rTensor _
          (regularTensorSymbol (k := k) (H := H) n ⟨z, hz⟩)) =
      augmentationGradedHopfLeading (k := k) (H := H) n
        (LinearMap.mul' k H ((HopfAlgebra.antipode k).rTensor H z)) := by
  let W : ℕ → Submodule k H :=
    augmentationModuleFiltration (k := k) (H := H) (M := H)
  let A : tensorFiltration (k := k) W n →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) :=
    (LinearMap.mul' k _).comp
      ((augmentationGradedAntipode (k := k) (H := H)).rTensor _ |>.comp
        (regularTensorSymbol (k := k) (H := H) n))
  let B : tensorFiltration (k := k) W n →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) :=
    (augmentationGradedHopfLeading (k := k) (H := H) n).comp
      ((LinearMap.mul' k H).comp
        (((HopfAlgebra.antipode k).rTensor H).comp
          (tensorFiltration (k := k) W n).subtype))
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : H ⊗[k] H) (hv : v ∈ tensorFiltration (k := k) W n),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem i v hvi =>
          rcases hvi with ⟨q, rfl⟩
          let inc : W i ⊗[k] W (n - i) →ₗ[k] tensorFiltration (k := k) W n :=
            (TensorProduct.mapIncl (W i) (W (n - i))).codRestrict _
              (fun q => Submodule.mem_iSup_of_mem i ⟨q, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro x y
            have hi : (i : ℕ) + (n - i) = n :=
              Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.isLt)
            have hxS : HopfAlgebra.antipode k (x : H) ∈
                augmentationFiltration (k := k) (H := H) i := by
              apply augmentationFiltration_antipode (k := k) (H := H) i
              have hx := x.property
              change (x : H) ∈ augmentationModuleFiltration
                (k := k) (H := H) (M := H) i at hx
              rwa [regular_augmentationModuleFiltration_eq] at hx
            have hy : (y : H) ∈ augmentationFiltration (k := k) (H := H) (n - i) := by
              have hy' := y.property
              change (y : H) ∈ augmentationModuleFiltration
                (k := k) (H := H) (M := H) (n - i) at hy'
              rwa [regular_augmentationModuleFiltration_eq] at hy'
            have hprod : HopfAlgebra.antipode k (x : H) * y ∈
                augmentationFiltration (k := k) (H := H) n := by
              have hp := augmentationFiltration_mul_le (k := k) (H := H) i (n - i)
                (Submodule.mul_mem_mul hxS hy)
              simpa only [hi] using hp
            change LinearMap.mul' k _
                ((augmentationGradedAntipode (k := k) (H := H)).rTensor _
                  (regularTensorSymbol (k := k) (H := H) n
                    ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩)) = _
            rw [regularTensorSymbol_mapIncl_tmul, LinearMap.rTensor_tmul,
              augmentationGradedAntipode_of_mk, LinearMap.mul'_apply,
              DirectSum.of_mul_of]
            change DirectSum.of _ ((i : ℕ) + (n - i))
                (augmentationGradedMul (k := k) (H := H) i (n - i)
                  (Submodule.Quotient.mk ⟨HopfAlgebra.antipode k (x : H), hxS⟩)
                  (Submodule.Quotient.mk ⟨y, hy⟩)) =
              augmentationGradedHopfLeading (k := k) (H := H) n
                (HopfAlgebra.antipode k (x : H) * y)
            rw [augmentationGradedMul_mk]
            change DirectSum.of _ ((i : ℕ) + (n - i))
                (Submodule.Quotient.mk ⟨HopfAlgebra.antipode k (x : H) * y, _⟩) =
              augmentationGradedHopfLeading (k := k) (H := H) n
                (HopfAlgebra.antipode k (x : H) * y)
            rw [augmentationGradedHopfLeading_apply (n := n) ⟨_, hprod⟩]
            apply DirectSum.of_eq_of_gradedMonoid_eq
            apply Sigma.ext hi
            exact augmentationGradedHopf_mk_heq (k := k) (H := H) hi _ _ rfl
          exact LinearMap.congr_fun hinc q
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add u v hu hv hu' hv' =>
          change A (⟨u, hu⟩ + ⟨v, hv⟩) = B (⟨u, hu⟩ + ⟨v, hv⟩)
          rw [map_add, map_add, hu', hv']
    exact hmain t t.property
  exact LinearMap.congr_fun hAB ⟨z, hz⟩

set_option maxHeartbeats 4000000 in
-- The second induced antipode contraction is proved by the symmetric tensor argument.
private theorem gradedAntipode_lTensor_mul_on_regularTensorFiltration
    (n : ℕ) (z : H ⊗[k] H)
    (hz : z ∈ tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) n) :
    LinearMap.mul' k (AugmentationGradedHopf (k := k) (H := H))
        ((augmentationGradedAntipode (k := k) (H := H)).lTensor _
          (regularTensorSymbol (k := k) (H := H) n ⟨z, hz⟩)) =
      augmentationGradedHopfLeading (k := k) (H := H) n
        (LinearMap.mul' k H ((HopfAlgebra.antipode k).lTensor H z)) := by
  let W : ℕ → Submodule k H :=
    augmentationModuleFiltration (k := k) (H := H) (M := H)
  let A : tensorFiltration (k := k) W n →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) :=
    (LinearMap.mul' k _).comp
      ((augmentationGradedAntipode (k := k) (H := H)).lTensor _ |>.comp
        (regularTensorSymbol (k := k) (H := H) n))
  let B : tensorFiltration (k := k) W n →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) :=
    (augmentationGradedHopfLeading (k := k) (H := H) n).comp
      ((LinearMap.mul' k H).comp
        (((HopfAlgebra.antipode k).lTensor H).comp
          (tensorFiltration (k := k) W n).subtype))
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : H ⊗[k] H) (hv : v ∈ tensorFiltration (k := k) W n),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem i v hvi =>
          rcases hvi with ⟨q, rfl⟩
          let inc : W i ⊗[k] W (n - i) →ₗ[k] tensorFiltration (k := k) W n :=
            (TensorProduct.mapIncl (W i) (W (n - i))).codRestrict _
              (fun q => Submodule.mem_iSup_of_mem i ⟨q, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro x y
            have hi : (i : ℕ) + (n - i) = n :=
              Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.isLt)
            have hx : (x : H) ∈ augmentationFiltration (k := k) (H := H) i := by
              have hx' := x.property
              change (x : H) ∈ augmentationModuleFiltration
                (k := k) (H := H) (M := H) i at hx'
              rwa [regular_augmentationModuleFiltration_eq] at hx'
            have hyS : HopfAlgebra.antipode k (y : H) ∈
                augmentationFiltration (k := k) (H := H) (n - i) := by
              apply augmentationFiltration_antipode (k := k) (H := H) (n - i)
              have hy := y.property
              change (y : H) ∈ augmentationModuleFiltration
                (k := k) (H := H) (M := H) (n - i) at hy
              rwa [regular_augmentationModuleFiltration_eq] at hy
            have hprod : (x : H) * HopfAlgebra.antipode k (y : H) ∈
                augmentationFiltration (k := k) (H := H) n := by
              have hp := augmentationFiltration_mul_le (k := k) (H := H) i (n - i)
                (Submodule.mul_mem_mul hx hyS)
              simpa only [hi] using hp
            change LinearMap.mul' k _
                ((augmentationGradedAntipode (k := k) (H := H)).lTensor _
                  (regularTensorSymbol (k := k) (H := H) n
                    ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩)) = _
            rw [regularTensorSymbol_mapIncl_tmul, LinearMap.lTensor_tmul,
              augmentationGradedAntipode_of_mk, LinearMap.mul'_apply,
              DirectSum.of_mul_of]
            change DirectSum.of _ ((i : ℕ) + (n - i))
                (augmentationGradedMul (k := k) (H := H) i (n - i)
                  (Submodule.Quotient.mk ⟨x, hx⟩)
                  (Submodule.Quotient.mk
                    ⟨HopfAlgebra.antipode k (y : H), hyS⟩)) =
              augmentationGradedHopfLeading (k := k) (H := H) n
                ((x : H) * HopfAlgebra.antipode k (y : H))
            rw [augmentationGradedMul_mk]
            change DirectSum.of _ ((i : ℕ) + (n - i))
                (Submodule.Quotient.mk
                  ⟨(x : H) * HopfAlgebra.antipode k (y : H), _⟩) =
              augmentationGradedHopfLeading (k := k) (H := H) n
                ((x : H) * HopfAlgebra.antipode k (y : H))
            rw [augmentationGradedHopfLeading_apply (n := n) ⟨_, hprod⟩]
            apply DirectSum.of_eq_of_gradedMonoid_eq
            apply Sigma.ext hi
            exact augmentationGradedHopf_mk_heq (k := k) (H := H) hi _ _ rfl
          exact LinearMap.congr_fun hinc q
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add u v hu hv hu' hv' =>
          change A (⟨u, hu⟩ + ⟨v, hv⟩) = B (⟨u, hu⟩ + ⟨v, hv⟩)
          rw [map_add, map_add, hu', hv']
    exact hmain t t.property
  exact LinearMap.congr_fun hAB ⟨z, hz⟩

private theorem augmentationGradedHopfLeading_algebraMap_zero (r : k) :
    augmentationGradedHopfLeading (k := k) (H := H) 0 (algebraMap k H r) =
      algebraMap k (AugmentationGradedHopf (k := k) (H := H)) r := by
  rw [show algebraMap k H r = r • (1 : H) by
      rw [Algebra.smul_def, mul_one], map_smul]
  rw [show algebraMap k (AugmentationGradedHopf (k := k) (H := H)) r =
      r • (1 : AugmentationGradedHopf (k := k) (H := H)) by
        rw [Algebra.smul_def, mul_one]]
  congr 1
  let oneF : augmentationFiltration (k := k) (H := H) 0 :=
    ⟨1, by rw [augmentationFiltration_zero]; exact Submodule.mem_top⟩
  change augmentationGradedHopfLeading (k := k) (H := H) 0 oneF = 1
  rw [augmentationGradedHopfLeading_apply]
  rw [DirectSum.one_def]
  rfl

private theorem augmentationFiltration_counit_of_succ (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) (n + 1)) :
    Coalgebra.counit (R := k) (A := H) x = 0 := by
  change (x : H) ∈ augmentationIdeal (k := k) (H := H)
  exact Ideal.pow_le_self (Nat.succ_ne_zero n) x.property

private theorem gradedAntipode_right_of_mk (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) n) :
    LinearMap.mul' k (AugmentationGradedHopf (k := k) (H := H))
        ((augmentationGradedAntipode (k := k) (H := H)).rTensor _
          (Coalgebra.comul (R := k)
            (A := AugmentationGradedHopf (k := k) (H := H))
            (DirectSum.of _ n (Submodule.Quotient.mk x)))) =
      algebraMap k (AugmentationGradedHopf (k := k) (H := H))
        (Coalgebra.counit (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H))
          (DirectSum.of _ n (Submodule.Quotient.mk x))) := by
  rw [augmentationGradedHopf_comul_of_mk]
  change LinearMap.mul' k _
      ((augmentationGradedAntipode (k := k) (H := H)).rTensor _
        (regularTensorSymbol (k := k) (H := H) n ⟨Coalgebra.comul x, _⟩)) = _
  rw [gradedAntipode_rTensor_mul_on_regularTensorFiltration]
  rw [HopfAlgebra.mul_antipode_rTensor_comul_apply]
  cases n with
  | zero =>
      rw [augmentationGradedHopf_counit_of_zero]
      exact augmentationGradedHopfLeading_algebraMap_zero
        (Coalgebra.counit (R := k) (A := H) x)
  | succ n =>
      rw [augmentationFiltration_counit_of_succ n x, map_zero,
        augmentationGradedHopf_counit_of_succ, map_zero]
      simp

private theorem gradedAntipode_left_of_mk (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) n) :
    LinearMap.mul' k (AugmentationGradedHopf (k := k) (H := H))
        ((augmentationGradedAntipode (k := k) (H := H)).lTensor _
          (Coalgebra.comul (R := k)
            (A := AugmentationGradedHopf (k := k) (H := H))
            (DirectSum.of _ n (Submodule.Quotient.mk x)))) =
      algebraMap k (AugmentationGradedHopf (k := k) (H := H))
        (Coalgebra.counit (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H))
          (DirectSum.of _ n (Submodule.Quotient.mk x))) := by
  rw [augmentationGradedHopf_comul_of_mk]
  change LinearMap.mul' k _
      ((augmentationGradedAntipode (k := k) (H := H)).lTensor _
        (regularTensorSymbol (k := k) (H := H) n ⟨Coalgebra.comul x, _⟩)) = _
  rw [gradedAntipode_lTensor_mul_on_regularTensorFiltration]
  rw [HopfAlgebra.mul_antipode_lTensor_comul_apply]
  cases n with
  | zero =>
      rw [augmentationGradedHopf_counit_of_zero]
      exact augmentationGradedHopfLeading_algebraMap_zero
        (Coalgebra.counit (R := k) (A := H) x)
  | succ n =>
      rw [augmentationFiltration_counit_of_succ n x, map_zero,
        augmentationGradedHopf_counit_of_succ, map_zero]
      simp

private theorem gradedAntipode_right
    (a : AugmentationGradedHopf (k := k) (H := H)) :
    LinearMap.mul' k (AugmentationGradedHopf (k := k) (H := H))
        ((augmentationGradedAntipode (k := k) (H := H)).rTensor _
          (Coalgebra.comul (R := k) a)) =
      algebraMap k (AugmentationGradedHopf (k := k) (H := H))
        (Coalgebra.counit (R := k) a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
      simpa only [map_add] using congrArg₂ (fun x y => x + y) ha hb
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ x => exact gradedAntipode_right_of_mk (k := k) (H := H) n x

private theorem gradedAntipode_left
    (a : AugmentationGradedHopf (k := k) (H := H)) :
    LinearMap.mul' k (AugmentationGradedHopf (k := k) (H := H))
        ((augmentationGradedAntipode (k := k) (H := H)).lTensor _
          (Coalgebra.comul (R := k) a)) =
      algebraMap k (AugmentationGradedHopf (k := k) (H := H))
        (Coalgebra.counit (R := k) a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
      simpa only [map_add] using congrArg₂ (fun x y => x + y) ha hb
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ x => exact gradedAntipode_left_of_mk (k := k) (H := H) n x

noncomputable instance augmentationGradedHopfHopfAlgebra :
    HopfAlgebra k (AugmentationGradedHopf (k := k) (H := H)) where
  antipode := augmentationGradedAntipode (k := k) (H := H)
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro a
    exact gradedAntipode_right (k := k) (H := H) a
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro a
    exact gradedAntipode_left (k := k) (H := H) a

private def filteredRegularTensorComm (n : ℕ) :
    tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) n →ₗ[k]
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) n :=
  ((TensorProduct.comm k H H).toLinearMap.comp
      (tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := H)) n).subtype).codRestrict _
    (by
      intro z
      let W : ℕ → Submodule k H :=
        augmentationModuleFiltration (k := k) (H := H) (M := H)
      change TensorProduct.comm k H H z ∈ tensorFiltration (k := k) W n
      have hmain : ∀ (v : H ⊗[k] H)
          (hv : v ∈ tensorFiltration (k := k) W n),
          TensorProduct.comm k H H v ∈ tensorFiltration (k := k) W n := by
        intro v hv
        induction hv using Submodule.iSup_induction' with
        | mem i v hvi =>
            rcases hvi with ⟨q, rfl⟩
            induction q with
            | zero => exact Submodule.zero_mem _
            | add a b ha hb => simpa using Submodule.add_mem _ ha hb
            | tmul x y =>
                let j : Fin (n + 1) := ⟨n - (i : ℕ), Nat.sub_lt_succ n i⟩
                have hji : n - (j : ℕ) = (i : ℕ) := by
                  dsimp [j]
                  exact Nat.sub_sub_self (Nat.lt_succ_iff.mp i.isLt)
                simp only [TensorProduct.mapIncl, TensorProduct.map_tmul,
                  Submodule.coe_subtype, TensorProduct.comm_tmul]
                apply Submodule.mem_iSup_of_mem j
                refine ⟨(⟨y, ?_⟩ : W j) ⊗ₜ[k] (⟨x, ?_⟩ : W (n - j)), ?_⟩
                · exact y.property
                · simpa only [hji] using x.property
                · simp [TensorProduct.mapIncl]
        | zero => simp
        | add a b ha hb ha' hb' => simpa using Submodule.add_mem _ ha' hb'
      exact hmain z z.property)

set_option maxHeartbeats 4000000 in
-- Total leading symbols intertwine the tensor flip.
private theorem regularTensorSymbol_comm (n : ℕ)
    (z : tensorFiltration (k := k)
      (augmentationModuleFiltration (k := k) (H := H) (M := H)) n) :
    TensorProduct.comm k _ _ (regularTensorSymbol (k := k) (H := H) n z) =
      regularTensorSymbol (k := k) (H := H) n
        (filteredRegularTensorComm (k := k) (H := H) n z) := by
  let W : ℕ → Submodule k H :=
    augmentationModuleFiltration (k := k) (H := H) (M := H)
  let A : tensorFiltration (k := k) W n →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) ⊗[k]
        AugmentationGradedHopf (k := k) (H := H) :=
    (TensorProduct.comm k _ _).toLinearMap.comp
      (regularTensorSymbol (k := k) (H := H) n)
  let B : tensorFiltration (k := k) W n →ₗ[k]
      AugmentationGradedHopf (k := k) (H := H) ⊗[k]
        AugmentationGradedHopf (k := k) (H := H) :=
    (regularTensorSymbol (k := k) (H := H) n).comp
      (filteredRegularTensorComm (k := k) (H := H) n)
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : H ⊗[k] H) (hv : v ∈ tensorFiltration (k := k) W n),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem i v hvi =>
          rcases hvi with ⟨q, rfl⟩
          let inc : W i ⊗[k] W (n - i) →ₗ[k] tensorFiltration (k := k) W n :=
            (TensorProduct.mapIncl (W i) (W (n - i))).codRestrict _
              (fun q => Submodule.mem_iSup_of_mem i ⟨q, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro x y
            let j : Fin (n + 1) := ⟨n - (i : ℕ), Nat.sub_lt_succ n i⟩
            have hji : n - (j : ℕ) = (i : ℕ) := by
              dsimp [j]
              exact Nat.sub_sub_self (Nat.lt_succ_iff.mp i.isLt)
            change TensorProduct.comm k _ _
                (regularTensorSymbol (k := k) (H := H) n
                  ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩) = _
            rw [regularTensorSymbol_mapIncl_tmul, TensorProduct.comm_tmul]
            change _ = regularTensorSymbol (k := k) (H := H) n
              ⟨TensorProduct.comm k H H
                (TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y)), _⟩
            have hcommmem : TensorProduct.comm k H H
                (TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y)) ∈
                  tensorFiltration (k := k) W n :=
              (filteredRegularTensorComm (k := k) (H := H) n
                (inc (x ⊗ₜ[k] y))).property
            have hflip : (⟨TensorProduct.comm k H H
                  (TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y)), hcommmem⟩ :
                    tensorFiltration (k := k) W n) =
                ⟨TensorProduct.mapIncl (W j) (W (n - j))
                  ((⟨y, y.property⟩ : W j) ⊗ₜ[k]
                    (⟨x, by simpa only [hji] using x.property⟩ : W (n - j))),
                  Submodule.mem_iSup_of_mem j ⟨_, rfl⟩⟩ := by
              apply Subtype.ext
              simp [TensorProduct.mapIncl]
            rw [hflip, regularTensorSymbol_mapIncl_tmul]
            apply congrArg₂ (fun u v => u ⊗ₜ[k] v)
            · rfl
            · apply DirectSum.of_eq_of_gradedMonoid_eq
              apply Sigma.ext hji.symm
              exact augmentationGradedHopf_mk_heq (k := k) (H := H) hji.symm _ _ rfl
          exact LinearMap.congr_fun hinc q
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add u v hu hv hu' hv' =>
          change A (⟨u, hu⟩ + ⟨v, hv⟩) = B (⟨u, hu⟩ + ⟨v, hv⟩)
          rw [map_add, map_add, hu', hv']
    exact hmain t t.property
  exact LinearMap.congr_fun hAB z

private theorem augmentationGradedHopf_comm_comul_of_mk
    [Coalgebra.IsCocomm k H] (n : ℕ)
    (x : augmentationFiltration (k := k) (H := H) n) :
    TensorProduct.comm k _ _
        (Coalgebra.comul (R := k)
          (A := AugmentationGradedHopf (k := k) (H := H))
          (DirectSum.of _ n (Submodule.Quotient.mk x))) =
      Coalgebra.comul (R := k)
        (A := AugmentationGradedHopf (k := k) (H := H))
        (DirectSum.of _ n (Submodule.Quotient.mk x)) := by
  rw [augmentationGradedHopf_comul_of_mk]
  change TensorProduct.comm k _ _
      (regularTensorSymbol (k := k) (H := H) n
        ⟨Coalgebra.comul (R := k) (A := H) x, _⟩) =
    regularTensorSymbol (k := k) (H := H) n
      ⟨Coalgebra.comul (R := k) (A := H) x, _⟩
  rw [regularTensorSymbol_comm]
  apply congrArg (regularTensorSymbol (k := k) (H := H) n)
  apply Subtype.ext
  exact Coalgebra.comm_comul k (x : H)

private theorem augmentationGradedHopf_comm_comul
    [Coalgebra.IsCocomm k H]
    (a : AugmentationGradedHopf (k := k) (H := H)) :
    TensorProduct.comm k _ _ (Coalgebra.comul (R := k) a) =
      Coalgebra.comul (R := k) a := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (fun x y => x + y) ha hb
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ x =>
          exact augmentationGradedHopf_comm_comul_of_mk
            (k := k) (H := H) n x

noncomputable instance augmentationGradedHopfIsCocomm
    [Coalgebra.IsCocomm k H] :
    Coalgebra.IsCocomm k (AugmentationGradedHopf (k := k) (H := H)) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro a
    exact augmentationGradedHopf_comm_comul (k := k) (H := H) a

end

end HopfAmenability
