/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.AssociatedGradedModuleCoalgebra
import Amenability.TensorFiltrationGraded
import Amenability.TripleFiltrationGraded

/-! # Coalgebra maps on augmentation associated graded objects -/

open Coalgebra TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

private abbrev moduleFiltration (n : ℕ) : Submodule k M :=
  augmentationModuleFiltration (k := k) (H := H) (M := M) n

/-- Include a finite direct sum of total-degree tensor pieces into the
tensor square of the full associated graded. -/
def gradedTensorInclusion (n : ℕ) :
    (DirectSum (Fin (n + 1)) fun i =>
      AugmentationGradedModulePiece (k := k) (H := H) (M := M) i ⊗[k]
        AugmentationGradedModulePiece (k := k) (H := H) (M := M) (n - i)) →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M) :=
  DirectSum.toModule k _ _ fun i =>
    TensorProduct.map
      (DirectSum.lof k ℕ
        (fun r => AugmentationGradedModulePiece (k := k) (H := H) (M := M) r) i)
      (DirectSum.lof k ℕ
        (fun r => AugmentationGradedModulePiece (k := k) (H := H) (M := M) r) (n - i))

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
@[simp]
theorem gradedTensorInclusion_of_tmul (n : ℕ) (i : Fin (n + 1))
    (x : AugmentationGradedModulePiece (k := k) (H := H) (M := M) i)
    (y : AugmentationGradedModulePiece (k := k) (H := H) (M := M) (n - i)) :
    gradedTensorInclusion (k := k) (H := H) (M := M) n
        (DirectSum.of _ i (x ⊗ₜ[k] y)) =
      DirectSum.of
          (fun r : ℕ => AugmentationGradedModulePiece
            (k := k) (H := H) (M := M) r) (i : ℕ) x ⊗ₜ[k]
        DirectSum.of
          (fun r : ℕ => AugmentationGradedModulePiece
            (k := k) (H := H) (M := M) r) (n - i) y := by
  rw [← DirectSum.lof_eq_of k, gradedTensorInclusion, DirectSum.toModule_lof]
  simp [DirectSum.lof_eq_of]

private def filteredComul (n : ℕ) :
    moduleFiltration (k := k) (H := H) (M := M) n →ₗ[k]
      tensorFiltration (k := k) (moduleFiltration (k := k) (H := H) (M := M)) n :=
  (Coalgebra.comul (R := k) (A := M)).domRestrict
      (moduleFiltration (k := k) (H := H) (M := M) n) |>.codRestrict
    (tensorFiltration (k := k) (moduleFiltration (k := k) (H := H) (M := M)) n)
    (fun x => augmentationModuleFiltration_comul (k := k) (H := H) (M := M)
      n x x.property)

private def filteredComulToTensorQuotient (n : ℕ) :
    moduleFiltration (k := k) (H := H) (M := M) n →ₗ[k]
      (tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) n ⧸
        (tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) (n + 1)).comap
            (tensorFiltration (k := k)
              (moduleFiltration (k := k) (H := H) (M := M)) n).subtype) :=
  ((tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) (n + 1)).comap
        (tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) n).subtype).mkQ.comp
    (filteredComul (k := k) (H := H) (M := M) n)

private theorem filteredComulToTensorQuotient_vanishes (n : ℕ) :
    (moduleFiltration (k := k) (H := H) (M := M) (n + 1)).comap
        (moduleFiltration (k := k) (H := H) (M := M) n).subtype ≤
      LinearMap.ker
        (filteredComulToTensorQuotient (k := k) (H := H) (M := M) n) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply (Submodule.Quotient.mk_eq_zero _).2
  change Coalgebra.comul (R := k) (A := M) (x : M) ∈
    tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) (n + 1)
  exact augmentationModuleFiltration_comul (k := k) (H := H) (M := M)
    (n + 1) x hx

private def filtrationComulQuotient (n : ℕ) :
    AugmentationGradedModulePiece (k := k) (H := H) (M := M) n →ₗ[k]
      (tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) n ⧸
        (tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) (n + 1)).comap
            (tensorFiltration (k := k)
              (moduleFiltration (k := k) (H := H) (M := M)) n).subtype) :=
  ((moduleFiltration (k := k) (H := H) (M := M) (n + 1)).comap
      (moduleFiltration (k := k) (H := H) (M := M) n).subtype).liftQ
    (filteredComulToTensorQuotient (k := k) (H := H) (M := M) n)
    (filteredComulToTensorQuotient_vanishes (k := k) (H := H) (M := M) n)

/-- Comultiplication on one homogeneous associated-graded piece. -/
def augmentationGradedComulPiece (n : ℕ) :
    AugmentationGradedModulePiece (k := k) (H := H) (M := M) n →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M) :=
  (gradedTensorInclusion (k := k) (H := H) (M := M) n).comp
    ((tensorFiltrationGradedPieceEquiv (k := k)
      (moduleFiltration (k := k) (H := H) (M := M))
      (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M)) n).toLinearMap.comp
        (filtrationComulQuotient (k := k) (H := H) (M := M) n))

/-- The coproduct induced on the concrete augmentation associated graded
module. -/
def augmentationGradedComul :
    AugmentationGradedModule (k := k) (H := H) (M := M) →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        AugmentationGradedModule (k := k) (H := H) (M := M) :=
  DirectSum.toModule k _ _ fun n =>
    augmentationGradedComulPiece (k := k) (H := H) (M := M) n

/-- The concrete comultiplication and counit on the augmentation associated
graded module, before verification of the coalgebra laws. -/
noncomputable instance augmentationGradedCoalgebraStruct :
    CoalgebraStruct k
      (AugmentationGradedModule (k := k) (H := H) (M := M)) where
  comul := augmentationGradedComul (k := k) (H := H) (M := M)
  counit := augmentationGradedCounit (k := k) (H := H) (M := M)

/-- Extend the degree-`n` leading-symbol map to the ambient module and
include it in the full associated graded. Its values away from `M_n` are
irrelevant to filtered identities. -/
def gradedLeadingExtension (n : ℕ) :
    M →ₗ[k] AugmentationGradedModule (k := k) (H := H) (M := M) :=
  filtrationGradedLeading (k := k)
    (moduleFiltration (k := k) (H := H) (M := M)) n

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
@[simp]
theorem gradedLeadingExtension_apply (n : ℕ)
    (x : moduleFiltration (k := k) (H := H) (M := M) n) :
    gradedLeadingExtension (k := k) (H := H) (M := M) n x =
      DirectSum.of _ n (Submodule.Quotient.mk x) := by
  exact filtrationGradedLeading_apply
    (k := k) (moduleFiltration (k := k) (H := H) (M := M)) n x

omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
theorem gradedLeadingExtension_apply_of_eq {i n : ℕ} (hin : i = n)
    (x : moduleFiltration (k := k) (H := H) (M := M) i) :
    gradedLeadingExtension (k := k) (H := H) (M := M) n x =
      DirectSum.of _ i (Submodule.Quotient.mk x) := by
  subst n
  exact gradedLeadingExtension_apply (k := k) (H := H) (M := M) i x

@[simp]
theorem augmentationGradedComul_of_mk (n : ℕ)
    (x : moduleFiltration (k := k) (H := H) (M := M) n) :
    augmentationGradedComul (k := k) (H := H) (M := M)
        (DirectSum.of _ n (Submodule.Quotient.mk x)) =
      gradedTensorInclusion (k := k) (H := H) (M := M) n
        (tensorFiltrationCoordinates (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) n
          ⟨Coalgebra.comul (R := k) (A := M) x,
            augmentationModuleFiltration_comul (k := k) (H := H) (M := M)
              n x x.property⟩) := by
  rw [augmentationGradedComul, ← DirectSum.lof_eq_of k,
    DirectSum.toModule_lof]
  rfl

set_option maxHeartbeats 4000000 in
-- Nested filtration and tensor inductions normalize the total-degree coordinates.
private theorem graded_rTensor_counit_on_tensorFiltration
    (n : ℕ) (z : M ⊗[k] M)
    (hz : z ∈ tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n) :
    (augmentationGradedCounit (k := k) (H := H) (M := M)).rTensor
        (AugmentationGradedModule (k := k) (H := H) (M := M))
        (gradedTensorInclusion (k := k) (H := H) (M := M) n
          (tensorFiltrationCoordinates (k := k)
            (moduleFiltration (k := k) (H := H) (M := M)) n ⟨z, hz⟩)) =
      TensorProduct.map LinearMap.id
        (gradedLeadingExtension (k := k) (H := H) (M := M) n)
        ((Coalgebra.counit (R := k) (A := M)).rTensor M z) := by
  let L : tensorFiltration (k := k) moduleFiltration n →ₗ[k]
      k ⊗[k] AugmentationGradedModule (k := k) (H := H) (M := M) :=
    ((augmentationGradedCounit (k := k) (H := H) (M := M)).rTensor
      (AugmentationGradedModule (k := k) (H := H) (M := M))).comp
        ((gradedTensorInclusion (k := k) (H := H) (M := M) n).comp
          (tensorFiltrationCoordinates (k := k) moduleFiltration n))
  have hmem (i : Fin (n + 1))
      (a : moduleFiltration (k := k) (H := H) (M := M) i ⊗[k]
        moduleFiltration (k := k) (H := H) (M := M) (n - i)) :
      TensorProduct.mapIncl
          (moduleFiltration (k := k) (H := H) (M := M) i)
          (moduleFiltration (k := k) (H := H) (M := M) (n - i)) a ∈
        tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) n := by
    change _ ∈ ⨆ j : Fin (n + 1), LinearMap.range
      (TensorProduct.mapIncl (moduleFiltration j) (moduleFiltration (n - j)))
    exact Submodule.mem_iSup_of_mem i ⟨a, rfl⟩
  have hmain : ∀ (v : M ⊗[k] M)
      (hv : v ∈ tensorFiltration (k := k) moduleFiltration n),
      L ⟨v, hv⟩ =
        TensorProduct.map LinearMap.id
          (gradedLeadingExtension (k := k) (H := H) (M := M) n)
          ((Coalgebra.counit (R := k) (A := M)).rTensor M v) := by
    intro v hv
    induction hv using Submodule.iSup_induction' with
    | mem i z hzi =>
        rcases hzi with ⟨a, rfl⟩
        induction a with
        | zero => exact L.map_zero
        | add a b ha hb =>
            calc
              L ⟨TensorProduct.mapIncl
                    (moduleFiltration (k := k) (H := H) (M := M) i)
                    (moduleFiltration (k := k) (H := H) (M := M) (n - i))
                    (a + b), hmem i (a + b)⟩ =
                  L (⟨_, hmem i a⟩ + ⟨_, hmem i b⟩) := by
                    apply congrArg L
                    apply Subtype.ext
                    exact (TensorProduct.mapIncl
                      (moduleFiltration (k := k) (H := H) (M := M) i)
                      (moduleFiltration (k := k) (H := H) (M := M) (n - i))).map_add a b
              _ = _ + _ := by rw [map_add, ha, hb]
              _ = _ := by
                rw [(TensorProduct.mapIncl
                    (moduleFiltration (k := k) (H := H) (M := M) i)
                    (moduleFiltration (k := k) (H := H) (M := M) (n - i))).map_add,
                  ((Coalgebra.counit (R := k) (A := M)).rTensor M).map_add,
                  (TensorProduct.map LinearMap.id
                    (gradedLeadingExtension (k := k) (H := H) (M := M) n)).map_add]
        | tmul x y =>
            change (augmentationGradedCounit (k := k) (H := H) (M := M)).rTensor
              (AugmentationGradedModule (k := k) (H := H) (M := M))
              (gradedTensorInclusion (k := k) (H := H) (M := M) n
                (tensorFiltrationCoordinates (k := k)
                  (moduleFiltration (k := k) (H := H) (M := M)) n
                  ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩)) = _
            rw [tensorFiltrationCoordinates_mapIncl_tmul
              (moduleFiltration (k := k) (H := H) (M := M))
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)),
              gradedTensorInclusion_of_tmul]
            rcases i with ⟨_ | i, hi⟩
            · simp
            · have hx1 : (x : M) ∈
                moduleFiltration (k := k) (H := H) (M := M) 1 :=
                augmentationModuleFiltration_antitone
                  (k := k) (H := H) (M := M)
                  (Nat.succ_le_succ (Nat.zero_le i)) x.property
              have heps : Coalgebra.counit (R := k) (A := M) (x : M) = 0 :=
                augmentationModuleFiltration_counit_one
                  (k := k) (H := H) (M := M) x hx1
              simp [heps]
    | zero => exact L.map_zero
    | add a b hxa hxb ha hb =>
        change L (⟨a, hxa⟩ + ⟨b, hxb⟩) = _
        rw [map_add, ha, hb, map_add, map_add]
  change L ⟨z, hz⟩ = _
  exact hmain z hz

set_option maxHeartbeats 4000000 in
-- This is the left-handed companion to the preceding filtered tensor induction.
private theorem graded_lTensor_counit_on_tensorFiltration
    (n : ℕ) (z : M ⊗[k] M)
    (hz : z ∈ tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n) :
    (augmentationGradedCounit (k := k) (H := H) (M := M)).lTensor
        (AugmentationGradedModule (k := k) (H := H) (M := M))
        (gradedTensorInclusion (k := k) (H := H) (M := M) n
          (tensorFiltrationCoordinates (k := k)
            (moduleFiltration (k := k) (H := H) (M := M)) n ⟨z, hz⟩)) =
      TensorProduct.map
        (gradedLeadingExtension (k := k) (H := H) (M := M) n) LinearMap.id
        ((Coalgebra.counit (R := k) (A := M)).lTensor M z) := by
  let L : tensorFiltration (k := k) moduleFiltration n →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k] k :=
    ((augmentationGradedCounit (k := k) (H := H) (M := M)).lTensor
      (AugmentationGradedModule (k := k) (H := H) (M := M))).comp
        ((gradedTensorInclusion (k := k) (H := H) (M := M) n).comp
          (tensorFiltrationCoordinates (k := k) moduleFiltration n))
  have hmem (i : Fin (n + 1))
      (a : moduleFiltration (k := k) (H := H) (M := M) i ⊗[k]
        moduleFiltration (k := k) (H := H) (M := M) (n - i)) :
      TensorProduct.mapIncl
          (moduleFiltration (k := k) (H := H) (M := M) i)
          (moduleFiltration (k := k) (H := H) (M := M) (n - i)) a ∈
        tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) n := by
    change _ ∈ ⨆ j : Fin (n + 1), LinearMap.range
      (TensorProduct.mapIncl (moduleFiltration j) (moduleFiltration (n - j)))
    exact Submodule.mem_iSup_of_mem i ⟨a, rfl⟩
  have hmain : ∀ (v : M ⊗[k] M)
      (hv : v ∈ tensorFiltration (k := k) moduleFiltration n),
      L ⟨v, hv⟩ =
        TensorProduct.map
          (gradedLeadingExtension (k := k) (H := H) (M := M) n) LinearMap.id
          ((Coalgebra.counit (R := k) (A := M)).lTensor M v) := by
    intro v hv
    induction hv using Submodule.iSup_induction' with
    | mem i z hzi =>
        rcases hzi with ⟨a, rfl⟩
        induction a with
        | zero => exact L.map_zero
        | add a b ha hb =>
            calc
              L ⟨TensorProduct.mapIncl
                    (moduleFiltration (k := k) (H := H) (M := M) i)
                    (moduleFiltration (k := k) (H := H) (M := M) (n - i))
                    (a + b), hmem i (a + b)⟩ =
                  L (⟨_, hmem i a⟩ + ⟨_, hmem i b⟩) := by
                    apply congrArg L
                    apply Subtype.ext
                    exact (TensorProduct.mapIncl
                      (moduleFiltration (k := k) (H := H) (M := M) i)
                      (moduleFiltration (k := k) (H := H) (M := M) (n - i))).map_add a b
              _ = _ + _ := by rw [map_add, ha, hb]
              _ = _ := by
                rw [(TensorProduct.mapIncl
                    (moduleFiltration (k := k) (H := H) (M := M) i)
                    (moduleFiltration (k := k) (H := H) (M := M) (n - i))).map_add,
                  ((Coalgebra.counit (R := k) (A := M)).lTensor M).map_add,
                  (TensorProduct.map
                    (gradedLeadingExtension (k := k) (H := H) (M := M) n)
                    LinearMap.id).map_add]
        | tmul x y =>
            change (augmentationGradedCounit (k := k) (H := H) (M := M)).lTensor
              (AugmentationGradedModule (k := k) (H := H) (M := M))
              (gradedTensorInclusion (k := k) (H := H) (M := M) n
                (tensorFiltrationCoordinates (k := k) moduleFiltration n
                  ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩)) = _
            rw [tensorFiltrationCoordinates_mapIncl_tmul moduleFiltration
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)),
              gradedTensorInclusion_of_tmul]
            by_cases hdeg : n - (i : ℕ) = 0
            · have hi : (i : ℕ) = n := by omega
              have hc0 := augmentationGradedCounit_of_eq_zero
                (k := k) (H := H) (M := M) hdeg y
              have hlead := gradedLeadingExtension_apply_of_eq
                (k := k) (H := H) (M := M) hi x
              have hlead' : gradedLeadingExtension (k := k) (H := H) (M := M) n
                    ((moduleFiltration (k := k) (H := H) (M := M) i).subtype x) =
                  DirectSum.of _ (i : ℕ) (Submodule.Quotient.mk x) := hlead
              have hcounit' : Coalgebra.counit (R := k) (A := M)
                    ((moduleFiltration (k := k) (H := H) (M := M) (n - i)).subtype y) =
                  Coalgebra.counit (R := k) (A := M) (y : M) := rfl
              simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul,
                LinearMap.id_apply]
              rw [hc0, hlead', hcounit']
            · have hy1 : (y : M) ∈ moduleFiltration 1 :=
                augmentationModuleFiltration_antitone
                  (k := k) (H := H) (M := M)
                  (Nat.one_le_iff_ne_zero.2 hdeg) y.property
              have heps : Coalgebra.counit (R := k) (A := M) (y : M) = 0 :=
                augmentationModuleFiltration_counit_one
                  (k := k) (H := H) (M := M) y hy1
              have hc := augmentationGradedCounit_of_ne_zero
                (k := k) (H := H) (M := M) (n - (i : ℕ)) hdeg
                (Submodule.Quotient.mk y)
              simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul]
              rw [hc, LinearMap.id_apply]
              change Coalgebra.counit (R := k) (A := M) (y : M) = 0 at heps
              have heps' : Coalgebra.counit (R := k) (A := M)
                  ((moduleFiltration (k := k) (H := H) (M := M) (n - i)).subtype y) = 0 :=
                heps
              rw [heps']
              simp
    | zero => exact L.map_zero
    | add a b hxa hxb ha hb =>
        change L (⟨a, hxa⟩ + ⟨b, hxb⟩) = _
        rw [map_add, ha, hb, map_add, map_add]
  change L ⟨z, hz⟩ = _
  exact hmain z hz

@[simp]
theorem augmentationGraded_rTensor_counit_comul_of_mk (n : ℕ)
    (x : moduleFiltration (k := k) (H := H) (M := M) n) :
    (augmentationGradedCounit (k := k) (H := H) (M := M)).rTensor
        (AugmentationGradedModule (k := k) (H := H) (M := M))
        (augmentationGradedComul (k := k) (H := H) (M := M)
          (DirectSum.of _ n (Submodule.Quotient.mk x))) =
      TensorProduct.mk k k
        (AugmentationGradedModule (k := k) (H := H) (M := M)) 1
        (DirectSum.of _ n (Submodule.Quotient.mk x)) := by
  rw [augmentationGradedComul_of_mk,
    graded_rTensor_counit_on_tensorFiltration]
  rw [Coalgebra.rTensor_counit_comul]
  simp

@[simp]
theorem augmentationGraded_lTensor_counit_comul_of_mk (n : ℕ)
    (x : moduleFiltration (k := k) (H := H) (M := M) n) :
    (augmentationGradedCounit (k := k) (H := H) (M := M)).lTensor
        (AugmentationGradedModule (k := k) (H := H) (M := M))
        (augmentationGradedComul (k := k) (H := H) (M := M)
          (DirectSum.of _ n (Submodule.Quotient.mk x))) =
      (TensorProduct.mk k
        (AugmentationGradedModule (k := k) (H := H) (M := M)) k).flip 1
        (DirectSum.of _ n (Submodule.Quotient.mk x)) := by
  rw [augmentationGradedComul_of_mk,
    graded_lTensor_counit_on_tensorFiltration]
  rw [Coalgebra.lTensor_counit_comul]
  simp

theorem augmentationGraded_rTensor_counit_comp_comul :
    (Coalgebra.counit (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))).rTensor
          (AugmentationGradedModule (k := k) (H := H) (M := M)) ∘ₗ
        Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M)) =
      TensorProduct.mk k k
        (AugmentationGradedModule (k := k) (H := H) (M := M)) 1 := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ m =>
          exact augmentationGraded_rTensor_counit_comul_of_mk
            (k := k) (H := H) (M := M) n m

theorem augmentationGraded_lTensor_counit_comp_comul :
    (Coalgebra.counit (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))).lTensor
          (AugmentationGradedModule (k := k) (H := H) (M := M)) ∘ₗ
        Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M)) =
      (TensorProduct.mk k
        (AugmentationGradedModule (k := k) (H := H) (M := M)) k).flip 1 := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ m =>
          exact augmentationGraded_lTensor_counit_comul_of_mk
            (k := k) (H := H) (M := M) n m

set_option maxHeartbeats 4000000 in
-- Two nested tensor-filtration inductions identify the left-associated symbols.
omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
private theorem gradedComul_left_tensor
    (i j n : ℕ) (hdeg : i + j = n)
    (w : M ⊗[k] M)
    (hw : w ∈ tensorFiltration (k := k) moduleFiltration i)
    (y : moduleFiltration (k := k) (H := H) (M := M) j) :
    TensorProduct.assoc k _ _ _
        (gradedTensorInclusion (k := k) (H := H) (M := M) i
            (tensorFiltrationCoordinates (k := k) moduleFiltration i ⟨w, hw⟩) ⊗ₜ[k]
          DirectSum.of _ j (Submodule.Quotient.mk y)) =
      tripleGradedLeading (k := k) moduleFiltration n
        (TensorProduct.assoc k M M M (w ⊗ₜ[k] (y : M))) := by
  let A : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) i →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    (TensorProduct.assoc k _ _ _).toLinearMap.comp
      (((TensorProduct.mk k
          (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
            AugmentationGradedModule (k := k) (H := H) (M := M))
          (AugmentationGradedModule (k := k) (H := H) (M := M))).flip
          (DirectSum.of
            (fun r => AugmentationGradedModulePiece (k := k) (H := H) (M := M) r)
            j (Submodule.Quotient.mk y))).comp
        ((gradedTensorInclusion (k := k) (H := H) (M := M) i).comp
          (tensorFiltrationCoordinates (k := k) moduleFiltration i)))
  let B : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) i →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    (tripleGradedLeading (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n).comp
      ((TensorProduct.assoc k M M M).toLinearMap.comp
        (((TensorProduct.mk k (M ⊗[k] M) M).flip (y : M)).comp
          (tensorFiltration (k := k)
            (moduleFiltration (k := k) (H := H) (M := M)) i).subtype))
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : M ⊗[k] M)
        (hv : v ∈ tensorFiltration (k := k) moduleFiltration i),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem r v hvr =>
          rcases hvr with ⟨a, rfl⟩
          let inc : moduleFiltration (k := k) (H := H) (M := M) r ⊗[k]
                moduleFiltration (k := k) (H := H) (M := M) (i - r) →ₗ[k]
              tensorFiltration (k := k) moduleFiltration i :=
            (TensorProduct.mapIncl (moduleFiltration r) (moduleFiltration (i - r))).codRestrict _
              (fun a => Submodule.mem_iSup_of_mem r ⟨a, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro x z
            change TensorProduct.assoc k _ _ _
                (gradedTensorInclusion (k := k) (H := H) (M := M) i
                  (tensorFiltrationCoordinates (k := k) moduleFiltration i
                    ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] z), _⟩) ⊗ₜ[k]
                  DirectSum.of
                    (fun q => AugmentationGradedModulePiece
                      (k := k) (H := H) (M := M) q)
                    j (Submodule.Quotient.mk y)) = _
            rw [tensorFiltrationCoordinates_mapIncl_tmul moduleFiltration
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)),
              gradedTensorInclusion_of_tmul]
            simp only [TensorProduct.assoc_tmul,
              LinearMap.coe_comp, Function.comp_apply]
            change _ = tripleGradedLeading (k := k)
              (moduleFiltration (k := k) (H := H) (M := M)) n
                ((x : M) ⊗ₜ[k] ((z : M) ⊗ₜ[k] (y : M)))
            rw [tripleGradedLeading_tmul moduleFiltration
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)) n r (i - r) j (by omega),
              filtrationGradedLeading_apply,
              filtrationGradedLeading_apply,
              filtrationGradedLeading_apply]
          exact LinearMap.congr_fun hinc a
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add a b hxa hxb ha hb =>
          change A (⟨a, hxa⟩ + ⟨b, hxb⟩) = B (⟨a, hxa⟩ + ⟨b, hxb⟩)
          rw [map_add, map_add, ha, hb]
    exact hmain t t.property
  change A ⟨w, hw⟩ = B ⟨w, hw⟩
  exact LinearMap.congr_fun hAB ⟨w, hw⟩

set_option maxHeartbeats 4000000 in
-- The right-associated counterpart of `gradedComul_left_tensor`.
omit [Coalgebra k M] [IsHopfModuleCoalgebra k H M] in
private theorem gradedComul_right_tensor
    (i j n : ℕ) (hdeg : i + j = n)
    (x : moduleFiltration (k := k) (H := H) (M := M) i)
    (w : M ⊗[k] M)
    (hw : w ∈ tensorFiltration (k := k) moduleFiltration j) :
    DirectSum.of _ i (Submodule.Quotient.mk x) ⊗ₜ[k]
        gradedTensorInclusion (k := k) (H := H) (M := M) j
          (tensorFiltrationCoordinates (k := k) moduleFiltration j ⟨w, hw⟩) =
      tripleGradedLeading (k := k) moduleFiltration n
        ((x : M) ⊗ₜ[k] w) := by
  let A : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) j →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    ((TensorProduct.mk k _ _
      (DirectSum.of
        (fun r => AugmentationGradedModulePiece (k := k) (H := H) (M := M) r)
        i (Submodule.Quotient.mk x))).comp
      ((gradedTensorInclusion (k := k) (H := H) (M := M) j).comp
        (tensorFiltrationCoordinates (k := k) moduleFiltration j)))
  let B : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) j →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    (tripleGradedLeading (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n).comp
      ((TensorProduct.mk k M (M ⊗[k] M) (x : M)).comp
        (tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) j).subtype)
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : M ⊗[k] M)
        (hv : v ∈ tensorFiltration (k := k) moduleFiltration j),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem r v hvr =>
          rcases hvr with ⟨a, rfl⟩
          let inc : moduleFiltration (k := k) (H := H) (M := M) r ⊗[k]
                moduleFiltration (k := k) (H := H) (M := M) (j - r) →ₗ[k]
              tensorFiltration (k := k) moduleFiltration j :=
            (TensorProduct.mapIncl (moduleFiltration r) (moduleFiltration (j - r))).codRestrict _
              (fun a => Submodule.mem_iSup_of_mem r ⟨a, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro y z
            change DirectSum.of
                (fun q => AugmentationGradedModulePiece
                  (k := k) (H := H) (M := M) q)
                i (Submodule.Quotient.mk x) ⊗ₜ[k]
                gradedTensorInclusion (k := k) (H := H) (M := M) j
                  (tensorFiltrationCoordinates (k := k) moduleFiltration j
                    ⟨TensorProduct.mapIncl _ _ (y ⊗ₜ[k] z), _⟩) = _
            rw [tensorFiltrationCoordinates_mapIncl_tmul moduleFiltration
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)),
              gradedTensorInclusion_of_tmul]
            change _ = tripleGradedLeading (k := k) moduleFiltration n
              ((x : M) ⊗ₜ[k] ((y : M) ⊗ₜ[k] (z : M)))
            rw [tripleGradedLeading_tmul moduleFiltration
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)) n i r (j - r) (by omega),
              filtrationGradedLeading_apply,
              filtrationGradedLeading_apply,
              filtrationGradedLeading_apply]
          exact LinearMap.congr_fun hinc a
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add a b hxa hxb ha hb =>
          change A (⟨a, hxa⟩ + ⟨b, hxb⟩) = B (⟨a, hxa⟩ + ⟨b, hxb⟩)
          rw [map_add, map_add, ha, hb]
    exact hmain t t.property
  change A ⟨w, hw⟩ = B ⟨w, hw⟩
  exact LinearMap.congr_fun hAB ⟨w, hw⟩

set_option maxHeartbeats 4000000 in
-- Naturality of left iterated comultiplication with total leading symbols.
private theorem gradedComul_rTensor_on_tensorFiltration
    (n : ℕ) (z : M ⊗[k] M)
    (hz : z ∈ tensorFiltration (k := k) moduleFiltration n) :
    TensorProduct.assoc k _ _ _
        ((Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M))).rTensor
            (AugmentationGradedModule (k := k) (H := H) (M := M))
          (gradedTensorInclusion (k := k) (H := H) (M := M) n
            (tensorFiltrationCoordinates (k := k) moduleFiltration n ⟨z, hz⟩))) =
      tripleGradedLeading (k := k) moduleFiltration n
        (TensorProduct.assoc k M M M
          ((Coalgebra.comul (R := k) (A := M)).rTensor M z)) := by
  let A : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    (TensorProduct.assoc k _ _ _).toLinearMap.comp
      (((Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))).rTensor
          (AugmentationGradedModule (k := k) (H := H) (M := M))).comp
        ((gradedTensorInclusion (k := k) (H := H) (M := M) n).comp
          (tensorFiltrationCoordinates (k := k) moduleFiltration n)))
  let B : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    (tripleGradedLeading (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n).comp
      ((TensorProduct.assoc k M M M).toLinearMap.comp
        (((Coalgebra.comul (R := k) (A := M)).rTensor M).comp
          (tensorFiltration (k := k)
            (moduleFiltration (k := k) (H := H) (M := M)) n).subtype))
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : M ⊗[k] M)
        (hv : v ∈ tensorFiltration (k := k) moduleFiltration n),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem i v hvi =>
          rcases hvi with ⟨a, rfl⟩
          let inc : moduleFiltration (k := k) (H := H) (M := M) i ⊗[k]
                moduleFiltration (k := k) (H := H) (M := M) (n - i) →ₗ[k]
              tensorFiltration (k := k) moduleFiltration n :=
            (TensorProduct.mapIncl (moduleFiltration i) (moduleFiltration (n - i))).codRestrict _
              (fun a => Submodule.mem_iSup_of_mem i ⟨a, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro x y
            change TensorProduct.assoc k _ _ _
                ((Coalgebra.comul (R := k)
                  (A := AugmentationGradedModule (k := k) (H := H) (M := M))).rTensor _
                  (gradedTensorInclusion (k := k) (H := H) (M := M) n
                    (tensorFiltrationCoordinates (k := k) moduleFiltration n
                      ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩))) = _
            rw [tensorFiltrationCoordinates_mapIncl_tmul moduleFiltration
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)),
              gradedTensorInclusion_of_tmul, LinearMap.rTensor_tmul]
            change TensorProduct.assoc k _ _ _
                (augmentationGradedComul (k := k) (H := H) (M := M)
                    (DirectSum.of
                      (fun q => AugmentationGradedModulePiece
                        (k := k) (H := H) (M := M) q)
                      (i : ℕ) (Submodule.Quotient.mk x)) ⊗ₜ[k]
                  DirectSum.of
                    (fun q => AugmentationGradedModulePiece
                      (k := k) (H := H) (M := M) q)
                    (n - (i : ℕ)) (Submodule.Quotient.mk y)) = _
            rw [augmentationGradedComul_of_mk]
            exact gradedComul_left_tensor (k := k) (H := H) (M := M)
              i (n - i) n (by omega) _
              (augmentationModuleFiltration_comul
                (k := k) (H := H) (M := M) i x x.property) y
          exact LinearMap.congr_fun hinc a
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add a b hxa hxb ha hb =>
          change A (⟨a, hxa⟩ + ⟨b, hxb⟩) = B (⟨a, hxa⟩ + ⟨b, hxb⟩)
          rw [map_add, map_add, ha, hb]
    exact hmain t t.property
  change A ⟨z, hz⟩ = B ⟨z, hz⟩
  exact LinearMap.congr_fun hAB ⟨z, hz⟩

set_option maxHeartbeats 4000000 in
-- Naturality of right iterated comultiplication with total leading symbols.
private theorem gradedComul_lTensor_on_tensorFiltration
    (n : ℕ) (z : M ⊗[k] M)
    (hz : z ∈ tensorFiltration (k := k) moduleFiltration n) :
    (Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))).lTensor
          (AugmentationGradedModule (k := k) (H := H) (M := M))
        (gradedTensorInclusion (k := k) (H := H) (M := M) n
          (tensorFiltrationCoordinates (k := k) moduleFiltration n ⟨z, hz⟩)) =
      tripleGradedLeading (k := k) moduleFiltration n
        ((Coalgebra.comul (R := k) (A := M)).lTensor M z) := by
  let A : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    ((Coalgebra.comul (R := k)
      (A := AugmentationGradedModule (k := k) (H := H) (M := M))).lTensor
        (AugmentationGradedModule (k := k) (H := H) (M := M))).comp
      ((gradedTensorInclusion (k := k) (H := H) (M := M) n).comp
        (tensorFiltrationCoordinates (k := k) moduleFiltration n))
  let B : tensorFiltration (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n →ₗ[k]
      AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
        (AugmentationGradedModule (k := k) (H := H) (M := M) ⊗[k]
          AugmentationGradedModule (k := k) (H := H) (M := M)) :=
    (tripleGradedLeading (k := k)
      (moduleFiltration (k := k) (H := H) (M := M)) n).comp
      (((Coalgebra.comul (R := k) (A := M)).lTensor M).comp
        (tensorFiltration (k := k)
          (moduleFiltration (k := k) (H := H) (M := M)) n).subtype)
  have hAB : A = B := by
    apply LinearMap.ext
    intro t
    have hmain : ∀ (v : M ⊗[k] M)
        (hv : v ∈ tensorFiltration (k := k) moduleFiltration n),
        A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem i v hvi =>
          rcases hvi with ⟨a, rfl⟩
          let inc : moduleFiltration (k := k) (H := H) (M := M) i ⊗[k]
                moduleFiltration (k := k) (H := H) (M := M) (n - i) →ₗ[k]
              tensorFiltration (k := k) moduleFiltration n :=
            (TensorProduct.mapIncl (moduleFiltration i) (moduleFiltration (n - i))).codRestrict _
              (fun a => Submodule.mem_iSup_of_mem i ⟨a, rfl⟩)
          have hinc : A.comp inc = B.comp inc := by
            apply TensorProduct.ext'
            intro x y
            change (Coalgebra.comul (R := k)
                (A := AugmentationGradedModule (k := k) (H := H) (M := M))).lTensor _
                (gradedTensorInclusion (k := k) (H := H) (M := M) n
                  (tensorFiltrationCoordinates (k := k) moduleFiltration n
                    ⟨TensorProduct.mapIncl _ _ (x ⊗ₜ[k] y), _⟩)) = _
            rw [tensorFiltrationCoordinates_mapIncl_tmul moduleFiltration
              (augmentationModuleFiltration_antitone
                (k := k) (H := H) (M := M)),
              gradedTensorInclusion_of_tmul, LinearMap.lTensor_tmul]
            change DirectSum.of
                  (fun q => AugmentationGradedModulePiece
                    (k := k) (H := H) (M := M) q)
                  (i : ℕ) (Submodule.Quotient.mk x) ⊗ₜ[k]
                augmentationGradedComul (k := k) (H := H) (M := M)
                  (DirectSum.of
                    (fun q => AugmentationGradedModulePiece
                      (k := k) (H := H) (M := M) q)
                    (n - (i : ℕ)) (Submodule.Quotient.mk y)) = _
            rw [augmentationGradedComul_of_mk]
            exact gradedComul_right_tensor (k := k) (H := H) (M := M)
              i (n - i) n (by omega) x _
              (augmentationModuleFiltration_comul
                (k := k) (H := H) (M := M) (n - i) y y.property)
          exact LinearMap.congr_fun hinc a
      | zero => exact A.map_zero.trans B.map_zero.symm
      | add a b hxa hxb ha hb =>
          change A (⟨a, hxa⟩ + ⟨b, hxb⟩) = B (⟨a, hxa⟩ + ⟨b, hxb⟩)
          rw [map_add, map_add, ha, hb]
    exact hmain t t.property
  change A ⟨z, hz⟩ = B ⟨z, hz⟩
  exact LinearMap.congr_fun hAB ⟨z, hz⟩

@[simp]
theorem augmentationGraded_coassoc_of_mk (n : ℕ)
    (x : moduleFiltration (k := k) (H := H) (M := M) n) :
    TensorProduct.assoc k _ _ _
        ((Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M))).rTensor _
          (Coalgebra.comul (R := k)
            (A := AugmentationGradedModule (k := k) (H := H) (M := M))
            (DirectSum.of _ n (Submodule.Quotient.mk x)))) =
      (Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))).lTensor _
        (Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M))
          (DirectSum.of _ n (Submodule.Quotient.mk x))) := by
  change TensorProduct.assoc k _ _ _
      ((augmentationGradedComul (k := k) (H := H) (M := M)).rTensor _
        (augmentationGradedComul (k := k) (H := H) (M := M)
          (DirectSum.of _ n (Submodule.Quotient.mk x)))) =
    (augmentationGradedComul (k := k) (H := H) (M := M)).lTensor _
      (augmentationGradedComul (k := k) (H := H) (M := M)
        (DirectSum.of _ n (Submodule.Quotient.mk x)))
  rw [augmentationGradedComul_of_mk]
  change TensorProduct.assoc k _ _ _
      ((Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))).rTensor _
        (gradedTensorInclusion (k := k) (H := H) (M := M) n
          (tensorFiltrationCoordinates (k := k) moduleFiltration n
            ⟨Coalgebra.comul (R := k) (A := M) x, _⟩))) =
    (Coalgebra.comul (R := k)
      (A := AugmentationGradedModule (k := k) (H := H) (M := M))).lTensor _
      (gradedTensorInclusion (k := k) (H := H) (M := M) n
        (tensorFiltrationCoordinates (k := k) moduleFiltration n
          ⟨Coalgebra.comul (R := k) (A := M) x, _⟩))
  rw [gradedComul_rTensor_on_tensorFiltration,
    gradedComul_lTensor_on_tensorFiltration]
  rw [Coalgebra.coassoc_apply]

theorem augmentationGraded_coassoc :
    (TensorProduct.assoc k _ _ _).toLinearMap ∘ₗ
        (Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M))).rTensor _ ∘ₗ
        Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M)) =
      (Coalgebra.comul (R := k)
        (A := AugmentationGradedModule (k := k) (H := H) (M := M))).lTensor _ ∘ₗ
        Coalgebra.comul (R := k)
          (A := AugmentationGradedModule (k := k) (H := H) (M := M)) := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ m =>
          exact augmentationGraded_coassoc_of_mk
            (k := k) (H := H) (M := M) n m

/-- The coalgebra structure induced on the concrete augmentation associated
graded module. -/
noncomputable instance augmentationGradedCoalgebra :
    Coalgebra k (AugmentationGradedModule (k := k) (H := H) (M := M)) where
  coassoc := augmentationGraded_coassoc (k := k) (H := H) (M := M)
  rTensor_counit_comp_comul :=
    augmentationGraded_rTensor_counit_comp_comul (k := k) (H := H) (M := M)
  lTensor_counit_comp_comul :=
    augmentationGraded_lTensor_counit_comp_comul (k := k) (H := H) (M := M)

end

end HopfAmenability
