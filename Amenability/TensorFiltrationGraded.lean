/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TensorFiltrationIntersection
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Graded pieces of a tensor-product filtration -/

open TensorProduct

namespace HopfAmenability

noncomputable section

universe u v v'

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- A homogeneous quotient of a descending filtration. -/
abbrev FiltrationPiece (W : ℕ → Submodule k V) (n : ℕ) :=
  W n ⧸ (W (n + 1)).comap (W n).subtype

/-- The associated graded vector space of a descending filtration. -/
abbrev FiltrationGraded (W : ℕ → Submodule k V) :=
  DirectSum ℕ fun n => FiltrationPiece W n

/-- The map on homogeneous quotients induced by a filtration-preserving
linear map. -/
def filtrationPieceMap {V' : Type*} [AddCommGroup V'] [Module k V']
    (W : ℕ → Submodule k V) (W' : ℕ → Submodule k V')
    (f : V →ₗ[k] V') (hf : ∀ n, Submodule.map f (W n) ≤ W' n) (n : ℕ) :
    FiltrationPiece W n →ₗ[k] FiltrationPiece W' n :=
  Submodule.mapQ
    ((W (n + 1)).comap (W n).subtype)
    ((W' (n + 1)).comap (W' n).subtype)
    { toFun := fun x => ⟨f x, hf n ⟨x, x.property, rfl⟩⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    (by
      intro x hx
      change f (x : V) ∈ W' (n + 1)
      exact hf (n + 1) ⟨x, hx, rfl⟩)

@[simp]
theorem filtrationPieceMap_mk {V' : Type*} [AddCommGroup V'] [Module k V']
    (W : ℕ → Submodule k V) (W' : ℕ → Submodule k V')
    (f : V →ₗ[k] V') (hf : ∀ n, Submodule.map f (W n) ≤ W' n)
    (n : ℕ) (x : W n) :
    filtrationPieceMap (k := k) W W' f hf n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f x, hf n ⟨x, x.property, rfl⟩⟩ :=
  rfl

/-- A filtration-preserving linear map induces a map on each total-degree
tensor filtration. -/
def tensorFiltrationMap {V' : Type v'} [AddCommGroup V'] [Module k V']
    (W : ℕ → Submodule k V) (W' : ℕ → Submodule k V')
    (f : V →ₗ[k] V') (hf : ∀ n, Submodule.map f (W n) ≤ W' n) (n : ℕ) :
    tensorFiltration (k := k) W n →ₗ[k] tensorFiltration (k := k) W' n :=
  ((TensorProduct.map f f).domRestrict (tensorFiltration (k := k) W n)).codRestrict
    (tensorFiltration (k := k) W' n) (by
      intro z
      have hmain : ∀ v, v ∈ tensorFiltration (k := k) W n →
          TensorProduct.map f f v ∈ tensorFiltration (k := k) W' n := by
        intro v hv
        induction hv using Submodule.iSup_induction' with
        | mem i z hzi =>
            rcases hzi with ⟨t, rfl⟩
            induction t with
            | zero => simp
            | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
            | tmul x y =>
                apply Submodule.mem_iSup_of_mem i
                refine ⟨⟨f x, hf i ⟨x, x.property, rfl⟩⟩ ⊗ₜ[k]
                  ⟨f y, hf (n - i) ⟨y, y.property, rfl⟩⟩, ?_⟩
                simp [TensorProduct.mapIncl]
        | zero => simp
        | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
      exact hmain z z.property)

/-- A noncomputably chosen extension to the ambient vector space of the
degree-`n` symbol map. Its restriction to `W n` is canonical. -/
def filtrationSymbolExtension (W : ℕ → Submodule k V) (n : ℕ) :
    V →ₗ[k] FiltrationPiece W n :=
  (LinearMap.exists_extend
    ((W (n + 1)).comap (W n).subtype).mkQ).choose

theorem filtrationSymbolExtension_comp_subtype
    (W : ℕ → Submodule k V) (n : ℕ) :
    (filtrationSymbolExtension (k := k) W n).comp (W n).subtype =
      ((W (n + 1)).comap (W n).subtype).mkQ :=
  (LinearMap.exists_extend
    ((W (n + 1)).comap (W n).subtype).mkQ).choose_spec

@[simp]
theorem filtrationSymbolExtension_apply
    (W : ℕ → Submodule k V) (n : ℕ) (x : W n) :
    filtrationSymbolExtension (k := k) W n x = Submodule.Quotient.mk x := by
  exact LinearMap.congr_fun
    (filtrationSymbolExtension_comp_subtype (k := k) W n) x

theorem filtrationSymbolExtension_eq_zero_of_mem_succ
    (W : ℕ → Submodule k V) (hW : Antitone W) (n : ℕ)
    (x : V) (hx : x ∈ W (n + 1)) :
    filtrationSymbolExtension (k := k) W n x = 0 := by
  let xn : W n := ⟨x, hW (Nat.le_succ n) hx⟩
  rw [show x = (xn : V) from rfl, filtrationSymbolExtension_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2 hx

/-- The degree-`n` leading-symbol map, extended to the ambient vector space
and included in the full associated graded. -/
def filtrationGradedLeading (W : ℕ → Submodule k V) (n : ℕ) :
    V →ₗ[k] FiltrationGraded W :=
  (DirectSum.lof k ℕ (fun r => FiltrationPiece W r) n).comp
    (filtrationSymbolExtension (k := k) W n)

@[simp]
theorem filtrationGradedLeading_apply (W : ℕ → Submodule k V) (n : ℕ)
    (x : W n) :
    filtrationGradedLeading (k := k) W n x =
      DirectSum.of _ n (Submodule.Quotient.mk x) := by
  rw [filtrationGradedLeading, LinearMap.comp_apply,
    filtrationSymbolExtension_apply, DirectSum.lof_eq_of]

theorem filtrationGradedLeading_eq_zero_of_lt
    (W : ℕ → Submodule k V) (hW : Antitone W)
    {r i : ℕ} (hri : r < i) (x : V) (hx : x ∈ W i) :
    filtrationGradedLeading (k := k) W r x = 0 := by
  rw [filtrationGradedLeading, LinearMap.comp_apply,
    filtrationSymbolExtension_eq_zero_of_mem_succ W hW r x
      (hW (Nat.succ_le_of_lt hri) hx), map_zero]

/-- The `(i,n-i)` symbol coordinate on `V ⊗ V`. -/
def tensorFiltrationCoordinate (W : ℕ → Submodule k V)
    (n : ℕ) (i : Fin (n + 1)) :
    V ⊗[k] V →ₗ[k]
      FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i) :=
  TensorProduct.map
    (filtrationSymbolExtension (k := k) W i)
    (filtrationSymbolExtension (k := k) W (n - i))

/-- All total-degree-`n` symbol coordinates on the `n`th tensor-filtration
term. -/
def tensorFiltrationCoordinates (W : ℕ → Submodule k V) (n : ℕ) :
    tensorFiltration (k := k) W n →ₗ[k]
      DirectSum (Fin (n + 1)) fun i =>
        FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i) :=
  (DirectSum.linearEquivFunOnFintype k _ _).symm.toLinearMap.comp
    (LinearMap.pi fun i =>
      (tensorFiltrationCoordinate (k := k) W n i).comp
        (tensorFiltration (k := k) W n).subtype)

private abbrev tensorFiltrationNextIn (W : ℕ → Submodule k V) (n : ℕ) :
    Submodule k (tensorFiltration (k := k) W n) :=
  (tensorFiltration (k := k) W (n + 1)).comap
    (tensorFiltration (k := k) W n).subtype

/-- The map induced on the degree-`n` quotient of tensor filtrations. -/
def tensorFiltrationQuotientMap {V' : Type v'} [AddCommGroup V'] [Module k V']
    (W : ℕ → Submodule k V) (W' : ℕ → Submodule k V')
    (f : V →ₗ[k] V') (hf : ∀ n, Submodule.map f (W n) ≤ W' n) (n : ℕ) :
    (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n) →ₗ[k]
      (tensorFiltration (k := k) W' n ⧸ tensorFiltrationNextIn (k := k) W' n) :=
  Submodule.mapQ _ _ (tensorFiltrationMap (k := k) W W' f hf n) (by
    intro x hx
    change TensorProduct.map f f (x : V ⊗[k] V) ∈ tensorFiltration (k := k) W' (n + 1)
    exact (tensorFiltrationMap (k := k) W W' f hf (n + 1) ⟨x, hx⟩).property)

@[simp]
theorem tensorFiltrationQuotientMap_mk {V' : Type v'}
    [AddCommGroup V'] [Module k V']
    (W : ℕ → Submodule k V) (W' : ℕ → Submodule k V')
    (f : V →ₗ[k] V') (hf : ∀ n, Submodule.map f (W n) ≤ W' n) (n : ℕ)
    (z : tensorFiltration (k := k) W n) :
    tensorFiltrationQuotientMap (k := k) W W' f hf n
        (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (tensorFiltrationMap (k := k) W W' f hf n z) :=
  rfl

private theorem mapIncl_tmul_mem_tensorFiltration
    (W : ℕ → Submodule k V) (n : ℕ) (i : Fin (n + 1))
    (x : W i) (y : W (n - i)) :
    TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y) ∈
      tensorFiltration (k := k) W n :=
  Submodule.mem_iSup_of_mem i ⟨x ⊗ₜ[k] y, rfl⟩

private def pairTensorLinear (W : ℕ → Submodule k V)
    (n : ℕ) (i : Fin (n + 1)) (x : W i) :
    W (n - i) →ₗ[k]
      (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n) where
  toFun y := Submodule.Quotient.mk
    ⟨TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y),
      mapIncl_tmul_mem_tensorFiltration W n i x y⟩
  map_add' y z := by
    rw [← Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact tmul_add _ _ _
  map_smul' r y := by
    rw [← Submodule.Quotient.mk_smul]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    simp

private theorem pairTensorLinear_vanishes_right
    (W : ℕ → Submodule k V) (n : ℕ) (i : Fin (n + 1)) (x : W i) :
    (W (n - i + 1)).comap (W (n - i)).subtype ≤
      LinearMap.ker (pairTensorLinear (k := k) W n i x) := by
  intro y hy
  rw [LinearMap.mem_ker]
  apply (Submodule.Quotient.mk_eq_zero _).2
  change TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y) ∈
    tensorFiltration (k := k) W (n + 1)
  let i' : Fin (n + 2) := ⟨i, Nat.lt_succ_of_lt i.isLt⟩
  apply Submodule.mem_iSup_of_mem i'
  have heq : n + 1 - (i' : ℕ) = n - (i : ℕ) + 1 := by
    dsimp [i']
    omega
  let y' : W (n + 1 - (i' : ℕ)) := ⟨y, heq.symm ▸ hy⟩
  exact ⟨x ⊗ₜ[k] y', rfl⟩

private def pairTensorLeft (W : ℕ → Submodule k V)
    (n : ℕ) (i : Fin (n + 1)) (x : W i) :
    FiltrationPiece W (n - i) →ₗ[k]
      (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n) :=
  ((W (n - i + 1)).comap (W (n - i)).subtype).liftQ
    (pairTensorLinear (k := k) W n i x)
    (pairTensorLinear_vanishes_right (k := k) W n i x)

private def pairTensorLeftLinear (W : ℕ → Submodule k V)
    (n : ℕ) (i : Fin (n + 1)) :
    W i →ₗ[k] (FiltrationPiece W (n - i) →ₗ[k]
      (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n)) where
  toFun := pairTensorLeft (k := k) W n i
  map_add' x y := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ z =>
      simp only [pairTensorLeft, Submodule.liftQ_apply, LinearMap.add_apply,
        pairTensorLinear]
      change Submodule.Quotient.mk
          (⟨_, _⟩ : tensorFiltration (k := k) W n) =
        Submodule.Quotient.mk (⟨_, _⟩ : tensorFiltration (k := k) W n) +
          Submodule.Quotient.mk (⟨_, _⟩ : tensorFiltration (k := k) W n)
      rw [← Submodule.Quotient.mk_add]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact add_tmul _ _ _
  map_smul' r x := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ y =>
      simp only [pairTensorLeft, Submodule.liftQ_apply, LinearMap.smul_apply,
        RingHom.id_apply, pairTensorLinear]
      change Submodule.Quotient.mk
          (⟨_, _⟩ : tensorFiltration (k := k) W n) =
        r • Submodule.Quotient.mk (⟨_, _⟩ : tensorFiltration (k := k) W n)
      rw [← Submodule.Quotient.mk_smul]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact smul_tmul' _ _ _

private theorem pairTensorLeftLinear_vanishes
    (W : ℕ → Submodule k V) (n : ℕ) (i : Fin (n + 1)) :
    (W (i + 1)).comap (W i).subtype ≤
      LinearMap.ker (pairTensorLeftLinear (k := k) W n i) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    apply (Submodule.Quotient.mk_eq_zero _).2
    change TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y) ∈
      tensorFiltration (k := k) W (n + 1)
    let i' : Fin (n + 2) := ⟨i + 1, by omega⟩
    apply Submodule.mem_iSup_of_mem i'
    have heq : n + 1 - (i' : ℕ) = n - (i : ℕ) := by
      dsimp [i']
      omega
    let x' : W i' := ⟨x, hx⟩
    let y' : W (n + 1 - (i' : ℕ)) := ⟨y, heq.symm ▸ y.property⟩
    exact ⟨x' ⊗ₜ[k] y', rfl⟩

/-- A pair of homogeneous symbols maps to the class of the corresponding
tensor in the tensor-filtration quotient. -/
def pairSymbolsToTensorFiltrationQuotient
    (W : ℕ → Submodule k V) (n : ℕ) (i : Fin (n + 1)) :
    FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i) →ₗ[k]
      (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n) :=
  TensorProduct.lift
    (((W (i + 1)).comap (W i).subtype).liftQ
      (pairTensorLeftLinear (k := k) W n i)
      (pairTensorLeftLinear_vanishes (k := k) W n i))

/-- Reassemble total-degree symbol pairs in the tensor-filtration
quotient. -/
def tensorFiltrationSymbolsToQuotient (W : ℕ → Submodule k V) (n : ℕ) :
    (DirectSum (Fin (n + 1)) fun i =>
        FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i)) →ₗ[k]
      (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n) :=
  DirectSum.toModule k _ _ fun i =>
    pairSymbolsToTensorFiltrationQuotient (k := k) W n i

@[simp]
theorem pairSymbolsToTensorFiltrationQuotient_mk_tmul_mk
    (W : ℕ → Submodule k V) (n : ℕ) (i : Fin (n + 1))
    (x : W i) (y : W (n - i)) :
    pairSymbolsToTensorFiltrationQuotient (k := k) W n i
        (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y),
          mapIncl_tmul_mem_tensorFiltration W n i x y⟩ :=
  rfl

set_option maxHeartbeats 4000000 in
-- The proof performs nested induction over a finite supremum and tensors.
private theorem tensorFiltrationCoordinates_vanishes_next
    (W : ℕ → Submodule k V) (hW : Antitone W) (n : ℕ) :
    tensorFiltrationNextIn (k := k) W n ≤
      LinearMap.ker (tensorFiltrationCoordinates (k := k) W n) := by
  intro z hz
  rw [LinearMap.mem_ker]
  apply (DirectSum.linearEquivFunOnFintype k _ _).injective
  change (fun i => tensorFiltrationCoordinate (k := k) W n i (z : V ⊗[k] V)) = 0
  funext i
  have hz' : (z : V ⊗[k] V) ∈ tensorFiltration (k := k) W (n + 1) := hz
  have hkill : ∀ v : V ⊗[k] V,
      v ∈ tensorFiltration (k := k) W (n + 1) →
        tensorFiltrationCoordinate (k := k) W n i v = 0 := by
    intro v hv
    induction hv using Submodule.iSup_induction' with
    | mem r v hvrange =>
        rcases hvrange with ⟨t, rfl⟩
        induction t with
        | zero => simp
        | add a b ha hb => simpa using congrArg₂ (fun x y => x + y) ha hb
        | tmul x y =>
            by_cases hir : (i : ℕ) < r
            · have hx : (x : V) ∈ W ((i : ℕ) + 1) :=
                hW (Nat.succ_le_of_lt hir) x.property
              simp [tensorFiltrationCoordinate, TensorProduct.mapIncl,
                filtrationSymbolExtension_eq_zero_of_mem_succ W hW i x hx]
            · have hdeg : n - (i : ℕ) + 1 ≤ n + 1 - (r : ℕ) := by omega
              have hy : (y : V) ∈ W (n - (i : ℕ) + 1) := hW hdeg y.property
              simp [tensorFiltrationCoordinate, TensorProduct.mapIncl,
                filtrationSymbolExtension_eq_zero_of_mem_succ W hW (n - i) y hy]
    | zero => simp
    | add a b _ _ ha hb => simpa using congrArg₂ (fun x y => x + y) ha hb
  exact hkill z hz'

set_option maxHeartbeats 4000000 in
-- Elaborating the dependent finite direct-sum codomain needs extra reduction.
/-- Symbol coordinates descend from `T_n` to `T_n/T_(n+1)`. -/
def tensorFiltrationQuotientCoordinates
    (W : ℕ → Submodule k V) (hW : Antitone W) (n : ℕ) :
    (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n) →ₗ[k]
      DirectSum (Fin (n + 1)) fun i =>
        FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i) := by
  let f : tensorFiltration (k := k) W n →ₗ[k]
      DirectSum (Fin (n + 1)) fun i =>
        FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i) :=
    tensorFiltrationCoordinates (k := k) W n
  have hf : tensorFiltrationNextIn (k := k) W n ≤ LinearMap.ker f := by
    simpa only [f] using
      (tensorFiltrationCoordinates_vanishes_next (k := k) W hW n)
  exact
    { QuotientAddGroup.lift
        (tensorFiltrationNextIn (k := k) W n).toAddSubgroup
        f.toAddMonoidHom hf with
      map_smul' := by
        rintro r ⟨x⟩
        exact f.map_smul r x }

@[simp]
theorem tensorFiltrationCoordinate_mapIncl_tmul_self
    (W : ℕ → Submodule k V)
    (n : ℕ) (i : Fin (n + 1))
    (x : W i) (y : W (n - i)) :
    tensorFiltrationCoordinate (k := k) W n i
        (TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y)) =
      (Submodule.Quotient.mk x : FiltrationPiece W i) ⊗ₜ[k]
        (Submodule.Quotient.mk y : FiltrationPiece W (n - i)) := by
  simp [tensorFiltrationCoordinate, TensorProduct.mapIncl]

theorem tensorFiltrationCoordinate_mapIncl_tmul_of_ne
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (n : ℕ) (i r : Fin (n + 1)) (hir : i ≠ r)
    (x : W r) (y : W (n - r)) :
    tensorFiltrationCoordinate (k := k) W n i
        (TensorProduct.mapIncl (W r) (W (n - r)) (x ⊗ₜ[k] y)) = 0 := by
  have hine : (i : ℕ) ≠ (r : ℕ) := fun h => hir (Fin.ext h)
  have hor : (i : ℕ) < r ∨ (r : ℕ) < i := lt_or_gt_of_ne hine
  rcases hor with hir' | hri
  · have hx : (x : V) ∈ W ((i : ℕ) + 1) :=
      hW (Nat.succ_le_of_lt hir') x.property
    simp [tensorFiltrationCoordinate, TensorProduct.mapIncl,
      filtrationSymbolExtension_eq_zero_of_mem_succ W hW i x hx]
  · have hdeg : n - (i : ℕ) + 1 ≤ n - (r : ℕ) := by omega
    have hy : (y : V) ∈ W (n - (i : ℕ) + 1) := hW hdeg y.property
    simp [tensorFiltrationCoordinate, TensorProduct.mapIncl,
      filtrationSymbolExtension_eq_zero_of_mem_succ W hW (n - i) y hy]

@[simp]
theorem tensorFiltrationQuotientCoordinates_mk_mapIncl_tmul
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (n : ℕ) (i : Fin (n + 1)) (x : W i) (y : W (n - i)) :
    tensorFiltrationQuotientCoordinates (k := k) W hW n
        (Submodule.Quotient.mk
          ⟨TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y),
            mapIncl_tmul_mem_tensorFiltration W n i x y⟩) =
      DirectSum.of
        (fun r : Fin (n + 1) =>
          FiltrationPiece W r ⊗[k] FiltrationPiece W (n - r)) i
        (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y) := by
  apply (DirectSum.linearEquivFunOnFintype k _ _).injective
  change (fun r => tensorFiltrationCoordinate (k := k) W n r
      (TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y))) = _
  rw [← DirectSum.lof_eq_of k, DirectSum.linearEquivFunOnFintype_lof]
  funext r
  by_cases hri : r = i
  · subst r
    simpa [TensorProduct.mapIncl] using
      (tensorFiltrationCoordinate_mapIncl_tmul_self
        (k := k) W n i x y)
  · simpa [TensorProduct.mapIncl] using
      (tensorFiltrationCoordinate_mapIncl_tmul_of_ne
        (k := k) W hW n r i hri x y)
      |>.trans (by simp [hri])

@[simp]
theorem tensorFiltrationCoordinates_mapIncl_tmul
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (n : ℕ) (i : Fin (n + 1)) (x : W i) (y : W (n - i)) :
    tensorFiltrationCoordinates (k := k) W n
        ⟨TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y),
          mapIncl_tmul_mem_tensorFiltration W n i x y⟩ =
      DirectSum.of
        (fun r : Fin (n + 1) =>
          FiltrationPiece W r ⊗[k] FiltrationPiece W (n - r)) i
        (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y) := by
  change tensorFiltrationQuotientCoordinates (k := k) W hW n
      (Submodule.Quotient.mk
        ⟨TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y),
          mapIncl_tmul_mem_tensorFiltration W n i x y⟩) = _
  exact tensorFiltrationQuotientCoordinates_mk_mapIncl_tmul
    (k := k) W hW n i x y

@[simp]
theorem tensorFiltrationSymbolsToQuotient_of
    (W : ℕ → Submodule k V) (n : ℕ) (i : Fin (n + 1))
    (t : FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i)) :
    tensorFiltrationSymbolsToQuotient (k := k) W n
        (DirectSum.of _ i t) =
      pairSymbolsToTensorFiltrationQuotient (k := k) W n i t := by
  rw [← DirectSum.lof_eq_of k, tensorFiltrationSymbolsToQuotient,
    DirectSum.toModule_lof]

set_option maxHeartbeats 1000000 in
-- The proof uses extensionality on a dependent direct sum and two quotient inductions.
private theorem quotientCoordinates_comp_symbolsToQuotient
    (W : ℕ → Submodule k V) (hW : Antitone W) (n : ℕ) :
    (tensorFiltrationQuotientCoordinates (k := k) W hW n).comp
        (tensorFiltrationSymbolsToQuotient (k := k) W n) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro t
  induction t with
  | zero => simp
  | add a b ha hb => simpa using congrArg₂ (fun x y => x + y) ha hb
  | tmul a b =>
      induction a using Submodule.Quotient.induction_on with
      | _ x =>
        induction b using Submodule.Quotient.induction_on with
        | _ y =>
          change tensorFiltrationQuotientCoordinates (k := k) W hW n
              (tensorFiltrationSymbolsToQuotient (k := k) W n
                (DirectSum.lof k _ _ i
                  (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y))) =
            DirectSum.lof k _ _ i
              (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y)
          rw [DirectSum.lof_eq_of]
          simpa [TensorProduct.mapIncl] using
            (tensorFiltrationQuotientCoordinates_mk_mapIncl_tmul
              (k := k) W hW n i x y)

set_option maxHeartbeats 4000000 in
-- The proof expands membership in the finite supremum defining `T_n`.
private theorem symbolsToQuotient_comp_quotientCoordinates
    (W : ℕ → Submodule k V) (hW : Antitone W) (n : ℕ) :
    (tensorFiltrationSymbolsToQuotient (k := k) W n).comp
        (tensorFiltrationQuotientCoordinates (k := k) W hW n) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
    have hmain : ∀ (v : V ⊗[k] V)
        (hv : v ∈ tensorFiltration (k := k) W n),
          ((tensorFiltrationSymbolsToQuotient (k := k) W n).comp
            (tensorFiltrationQuotientCoordinates (k := k) W hW n))
              (Submodule.Quotient.mk ⟨v, hv⟩) =
            Submodule.Quotient.mk ⟨v, hv⟩ := by
      intro v hv
      induction hv using Submodule.iSup_induction' with
      | mem i v hvi =>
          rcases hvi with ⟨t, rfl⟩
          induction t with
          | zero =>
              have hzero : (Submodule.Quotient.mk
                  (⟨TensorProduct.mapIncl (W i) (W (n - i)) 0,
                    Submodule.mem_iSup_of_mem i ⟨0, rfl⟩⟩ :
                    tensorFiltration (k := k) W n) :
                    tensorFiltration (k := k) W n ⧸
                      tensorFiltrationNextIn (k := k) W n) = 0 := by
                apply (Submodule.Quotient.mk_eq_zero _).2
                simp
              rw [hzero, map_zero]
          | add a b ha hb =>
              have hab : Submodule.Quotient.mk
                    (⟨TensorProduct.mapIncl (W i) (W (n - i)) (a + b),
                      Submodule.mem_iSup_of_mem i ⟨a + b, rfl⟩⟩ :
                      tensorFiltration (k := k) W n) =
                  (Submodule.Quotient.mk
                      (⟨TensorProduct.mapIncl (W i) (W (n - i)) a,
                        Submodule.mem_iSup_of_mem i ⟨a, rfl⟩⟩ :
                        tensorFiltration (k := k) W n) :
                      tensorFiltration (k := k) W n ⧸
                        tensorFiltrationNextIn (k := k) W n) +
                    (Submodule.Quotient.mk
                      (⟨TensorProduct.mapIncl (W i) (W (n - i)) b,
                        Submodule.mem_iSup_of_mem i ⟨b, rfl⟩⟩ :
                        tensorFiltration (k := k) W n) :
                      tensorFiltration (k := k) W n ⧸
                        tensorFiltrationNextIn (k := k) W n) := by
                apply (Submodule.Quotient.eq _).2
                change TensorProduct.mapIncl (W i) (W (n - i)) (a + b) -
                    (TensorProduct.mapIncl (W i) (W (n - i)) a +
                      TensorProduct.mapIncl (W i) (W (n - i)) b) ∈
                    tensorFiltration (k := k) W (n + 1)
                rw [map_add, sub_self]
                exact Submodule.zero_mem _
              rw [hab, map_add, ha, hb]
          | tmul x y =>
              change tensorFiltrationSymbolsToQuotient (k := k) W n
                  (tensorFiltrationQuotientCoordinates (k := k) W hW n
                    (Submodule.Quotient.mk
                      ⟨TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y), _⟩)) = _
              rw [tensorFiltrationQuotientCoordinates_mk_mapIncl_tmul,
                tensorFiltrationSymbolsToQuotient_of,
                pairSymbolsToTensorFiltrationQuotient_mk_tmul_mk]
      | zero =>
          have hzero : (Submodule.Quotient.mk
              (⟨0, Submodule.zero_mem _⟩ : tensorFiltration (k := k) W n) :
                tensorFiltration (k := k) W n ⧸
                  tensorFiltrationNextIn (k := k) W n) = 0 := by
            apply (Submodule.Quotient.mk_eq_zero _).2
            exact Submodule.zero_mem _
          rw [hzero, map_zero]
      | add a b hxa hxb ha hb =>
          have hab : Submodule.Quotient.mk
                (⟨a + b, Submodule.add_mem _ hxa hxb⟩ :
                  tensorFiltration (k := k) W n) =
              (Submodule.Quotient.mk
                (⟨a, hxa⟩ : tensorFiltration (k := k) W n) :
                  tensorFiltration (k := k) W n ⧸
                    tensorFiltrationNextIn (k := k) W n) +
                (Submodule.Quotient.mk
                  (⟨b, hxb⟩ : tensorFiltration (k := k) W n) :
                    tensorFiltration (k := k) W n ⧸
                      tensorFiltrationNextIn (k := k) W n) := by
            rw [← Submodule.Quotient.mk_add]
            rfl
          rw [hab, map_add, ha, hb]
    exact hmain z z.property

/-- The associated graded of a tensor filtration is the direct sum of the
tensor products of its homogeneous pieces. -/
noncomputable def tensorFiltrationGradedPieceEquiv
    (W : ℕ → Submodule k V) (hW : Antitone W) (n : ℕ) :
    (tensorFiltration (k := k) W n ⧸ tensorFiltrationNextIn (k := k) W n) ≃ₗ[k]
      DirectSum (Fin (n + 1)) fun i =>
        FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i) :=
  LinearEquiv.ofLinearMap
    (tensorFiltrationQuotientCoordinates (k := k) W hW n)
    (tensorFiltrationSymbolsToQuotient (k := k) W n)
    (quotientCoordinates_comp_symbolsToQuotient (k := k) W hW n)
    (symbolsToQuotient_comp_quotientCoordinates (k := k) W hW n)

/-- The direct sum of the tensor products of the maps induced on homogeneous
filtration quotients. -/
def tensorFiltrationGradedMap {V' : Type v'} [AddCommGroup V'] [Module k V']
    (W : ℕ → Submodule k V) (W' : ℕ → Submodule k V')
    (f : V →ₗ[k] V') (hf : ∀ n, Submodule.map f (W n) ≤ W' n) (n : ℕ) :
    (DirectSum (Fin (n + 1)) fun i =>
      FiltrationPiece W i ⊗[k] FiltrationPiece W (n - i)) →ₗ[k]
    DirectSum (Fin (n + 1)) fun i =>
      FiltrationPiece W' i ⊗[k] FiltrationPiece W' (n - i) :=
  DirectSum.lmap fun i => TensorProduct.map
    (filtrationPieceMap (k := k) W W' f hf i)
    (filtrationPieceMap (k := k) W W' f hf (n - i))

set_option maxHeartbeats 4000000 in
-- Quotient, direct-sum, and tensor extensionality all occur in this proof.
/-- Naturality of the tensor-filtration graded-piece equivalence. -/
theorem tensorFiltrationGradedPieceEquiv_naturality
    {V' : Type v'} [AddCommGroup V'] [Module k V']
    (W : ℕ → Submodule k V) (W' : ℕ → Submodule k V')
    (hW : Antitone W) (hW' : Antitone W')
    (f : V →ₗ[k] V') (hf : ∀ n, Submodule.map f (W n) ≤ W' n) (n : ℕ) :
    (tensorFiltrationGradedPieceEquiv (k := k) W' hW' n).toLinearMap.comp
        (tensorFiltrationQuotientMap (k := k) W W' f hf n) =
      (tensorFiltrationGradedMap (k := k) W W' f hf n).comp
        (tensorFiltrationGradedPieceEquiv (k := k) W hW n).toLinearMap := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      let A := (tensorFiltrationCoordinates (k := k) W' n).comp
        (tensorFiltrationMap (k := k) W W' f hf n)
      let B := (tensorFiltrationGradedMap (k := k) W W' f hf n).comp
        (tensorFiltrationCoordinates (k := k) W n)
      change A z = B z
      have hmain : ∀ (v : V ⊗[k] V)
          (hv : v ∈ tensorFiltration (k := k) W n),
          A ⟨v, hv⟩ = B ⟨v, hv⟩ := by
        intro v hv
        induction hv using Submodule.iSup_induction' with
        | mem i v hvi =>
            rcases hvi with ⟨t, rfl⟩
            let inc : W i ⊗[k] W (n - i) →ₗ[k] tensorFiltration (k := k) W n :=
              (TensorProduct.mapIncl (W i) (W (n - i))).codRestrict _
                (fun t => Submodule.mem_iSup_of_mem i ⟨t, rfl⟩)
            have hi : A.comp inc = B.comp inc := by
              apply TensorProduct.ext'
              intro x y
              have hx' : f (x : V) ∈ W' i :=
                hf i (Submodule.mem_map_of_mem x.property)
              have hy' : f (y : V) ∈ W' (n - i) :=
                hf (n - i) (Submodule.mem_map_of_mem y.property)
              have hxy' : TensorProduct.mapIncl (W' i) (W' (n - i))
                    (⟨f x, hx'⟩ ⊗ₜ[k] ⟨f y, hy'⟩) ∈
                  tensorFiltration (k := k) W' n :=
                Submodule.mem_iSup_of_mem i ⟨_, rfl⟩
              change tensorFiltrationCoordinates (k := k) W' n
                  (tensorFiltrationMap (k := k) W W' f hf n (inc (x ⊗ₜ[k] y))) = _
              rw [show tensorFiltrationMap (k := k) W W' f hf n
                    (inc (x ⊗ₜ[k] y)) =
                  ⟨TensorProduct.mapIncl (W' i) (W' (n - i))
                    (⟨f x, hx'⟩ ⊗ₜ[k] ⟨f y, hy'⟩), hxy'⟩ by
                  apply Subtype.ext
                  change TensorProduct.map f f
                    (TensorProduct.map (W i).subtype (W (n - i)).subtype
                      (x ⊗ₜ[k] y)) = f x ⊗ₜ[k] f y
                  simp]
              rw [tensorFiltrationCoordinates_mapIncl_tmul W' hW']
              change _ = tensorFiltrationGradedMap (k := k) W W' f hf n
                (tensorFiltrationCoordinates (k := k) W n
                  ⟨TensorProduct.mapIncl (W i) (W (n - i)) (x ⊗ₜ[k] y), _⟩)
              rw [tensorFiltrationCoordinates_mapIncl_tmul W hW,
                tensorFiltrationGradedMap, DirectSum.lmap_of]
              simp
            exact LinearMap.congr_fun hi t
        | zero => exact A.map_zero.trans B.map_zero.symm
        | add a b hxa hxb ha hb =>
            change A (⟨a, hxa⟩ + ⟨b, hxb⟩) = B (⟨a, hxa⟩ + ⟨b, hxb⟩)
            rw [map_add, map_add, ha, hb]
      exact hmain z z.property

end

end HopfAmenability
