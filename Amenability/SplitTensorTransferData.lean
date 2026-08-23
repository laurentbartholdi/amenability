/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.SplitTensorFiltration
import Amenability.TransferData
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Filtered transfer data on a tensor product

Let `S` be a split filtration of a finite-dimensional commutative
`k`-algebra `R`, and let `A` be a commutative `k`-algebra.

The filtration `S_i ⊗ A` constructed in `SplitTensorFiltration` carries
the filtered transfer structure needed in the transfer argument.  The
algebra map on the `i`-th layer is
```
rho_i : R ⊗ A → A,
rho_i (r ⊗ a) = S.character i r * a.
```
-/

open TensorProduct

namespace UnifiedRounding

universe u v w

variable {k : Type u} {R : Type v} {A : Type w}
variable [Field k]
variable [CommRing R] [Algebra k R]
variable [CommRing A] [Algebra k A]

namespace SplitDualFiltration

variable (S : SplitDualFiltration k R)

/--
The algebra map describing the action on the `i`-th tensor layer.
-/
noncomputable def tensorRho
    (i : Fin S.n) :
    R ⊗[k] A →ₐ[k] A :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId k A).comp (S.character i))
    (AlgHom.id k A)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorRho_tmul
    (i : Fin S.n)
    (r : R) (a : A) :
    S.tensorRho (A := A) i (r ⊗ₜ[k] a) =
      S.character i r • a := by
  rw [tensorRho, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.smul_def]

/--
The maps `tensorRho i` are surjective: `a` is the image of `1 ⊗ a`.
-/
theorem tensorRho_surjective
    (i : Fin S.n) :
    Function.Surjective (S.tensorRho (A := A) i) := by
  intro a
  refine ⟨(1 : R) ⊗ₜ[k] a, ?_⟩
  simp

/--
Each tensor-filtration step is an ideal subspace of `R ⊗ A`.
-/
theorem tensorFiltration_isIdealSubspace
    (j : Fin (S.n + 1)) :
    IsIdealSubspace (S.tensorFiltration (A := A) j) := by
  intro q y hy
  rcases hy with ⟨z, rfl⟩
  induction q using TensorProduct.induction_on with
  | zero =>
      simp
  | add q₁ q₂ hq₁ hq₂ =>
      rw [add_mul]
      exact add_mem hq₁ hq₂
  | tmul r a =>
      induction z using TensorProduct.induction_on with
      | zero =>
          simp
      | add z₁ z₂ hz₁ hz₂ =>
          rw [map_add, mul_add]
          exact add_mem hz₁ hz₂
      | tmul x b =>
          refine ⟨
            (⟨r * (x : R), S.ideal j r x.2⟩ :
                S.filtration j) ⊗ₜ[k] (a * b), ?_⟩
          simp

/--
The tensor-layer coefficient intertwines multiplication with `tensorRho`.
-/
theorem tensorLayerCoeff_mul
    (i : Fin S.n)
    (q : R ⊗[k] A)
    (x : S.tensorFiltration (A := A) i.succ) :
    S.tensorLayerCoeff (A := A) i
        ⟨q * (x : R ⊗[k] A),
          S.tensorFiltration_isIdealSubspace (A := A) i.succ q x.2⟩ =
      S.tensorRho (A := A) i q *
        S.tensorLayerCoeff (A := A) i x := by
  obtain ⟨z, rfl⟩ :=
    (S.tensorFiltrationEquiv (A := A) i.succ).surjective x
  induction q using TensorProduct.induction_on with
  | zero =>
      have hzero :
          (⟨0 * ((S.tensorFiltrationEquiv (A := A) i.succ z :
              S.tensorFiltration (A := A) i.succ) : R ⊗[k] A), by simp⟩ :
            S.tensorFiltration (A := A) i.succ) = 0 := by
        apply Subtype.ext
        simp
      rw [hzero, map_zero, map_zero, zero_mul]
  | add q₁ q₂ hq₁ hq₂ =>
      have hadd :
          (⟨(q₁ + q₂) *
              ((S.tensorFiltrationEquiv (A := A) i.succ z :
                S.tensorFiltration (A := A) i.succ) : R ⊗[k] A),
              S.tensorFiltration_isIdealSubspace (A := A) i.succ
                (q₁ + q₂) (S.tensorFiltrationEquiv (A := A) i.succ z).2⟩ :
            S.tensorFiltration (A := A) i.succ) =
            ⟨q₁ * (S.tensorFiltrationEquiv (A := A) i.succ z : R ⊗[k] A),
              S.tensorFiltration_isIdealSubspace (A := A) i.succ q₁
                (S.tensorFiltrationEquiv (A := A) i.succ z).2⟩ +
              ⟨q₂ * (S.tensorFiltrationEquiv (A := A) i.succ z : R ⊗[k] A),
                S.tensorFiltration_isIdealSubspace (A := A) i.succ q₂
                  (S.tensorFiltrationEquiv (A := A) i.succ z).2⟩ := by
        apply Subtype.ext
        exact add_mul q₁ q₂ _
      rw [hadd, map_add, map_add, add_mul, hq₁, hq₂]
  | tmul r a =>
      induction z using TensorProduct.induction_on with
      | zero =>
          have hzero :
              (⟨(r ⊗ₜ[k] a) *
                  ((S.tensorFiltrationEquiv (A := A) i.succ 0 :
                    S.tensorFiltration (A := A) i.succ) : R ⊗[k] A),
                  S.tensorFiltration_isIdealSubspace (A := A) i.succ (r ⊗ₜ[k] a)
                    (S.tensorFiltrationEquiv (A := A) i.succ 0).2⟩ :
                S.tensorFiltration (A := A) i.succ) = 0 := by
            apply Subtype.ext
            simp
          rw [hzero]
          simp only [map_zero, mul_zero]
      | add z₁ z₂ hz₁ hz₂ =>
          have hadd :
              (⟨(r ⊗ₜ[k] a) *
                  ((S.tensorFiltrationEquiv (A := A) i.succ (z₁ + z₂) :
                    S.tensorFiltration (A := A) i.succ) : R ⊗[k] A),
                  S.tensorFiltration_isIdealSubspace (A := A) i.succ (r ⊗ₜ[k] a)
                    (S.tensorFiltrationEquiv (A := A) i.succ (z₁ + z₂)).2⟩ :
                S.tensorFiltration (A := A) i.succ) =
                ⟨(r ⊗ₜ[k] a) *
                  (S.tensorFiltrationEquiv (A := A) i.succ z₁ : R ⊗[k] A),
                  S.tensorFiltration_isIdealSubspace (A := A) i.succ (r ⊗ₜ[k] a)
                    (S.tensorFiltrationEquiv (A := A) i.succ z₁).2⟩ +
                ⟨(r ⊗ₜ[k] a) *
                  (S.tensorFiltrationEquiv (A := A) i.succ z₂ : R ⊗[k] A),
                  S.tensorFiltration_isIdealSubspace (A := A) i.succ (r ⊗ₜ[k] a)
                    (S.tensorFiltrationEquiv (A := A) i.succ z₂).2⟩ := by
            apply Subtype.ext
            simp [mul_add]
          rw [hadd]
          simp only [map_add, hz₁, hz₂, mul_add]
      | tmul y b =>
          have hmul :
              (⟨(r ⊗ₜ[k] a) *
                  ((S.tensorFiltrationEquiv (A := A) i.succ (y ⊗ₜ[k] b) :
                    S.tensorFiltration (A := A) i.succ) : R ⊗[k] A),
                  S.tensorFiltration_isIdealSubspace (A := A) i.succ (r ⊗ₜ[k] a)
                    (S.tensorFiltrationEquiv (A := A) i.succ (y ⊗ₜ[k] b)).2⟩ :
                S.tensorFiltration (A := A) i.succ) =
                S.tensorFiltrationEquiv (A := A) i.succ
                  (⟨r * (y : R), S.ideal i.succ r y.2⟩ ⊗ₜ[k] (a * b)) := by
            apply Subtype.ext
            simp
          rw [hmul, S.tensorLayerCoeff_equiv, S.tensorRho_tmul,
            S.tensorLayerCoeff_equiv]
          simp only [tensorCoeff_tmul]
          rw [S.coeff_mul i r y]
          simp [smul_smul, mul_comm]

/--
The split filtration tensored with `A` gives filtered transfer data.
-/
noncomputable def tensorTransferData :
    FilteredTransferData k (R ⊗[k] A) A where
  n := S.n
  filtration := S.tensorFiltration (A := A)
  bot := S.tensorFiltration_zero (A := A)
  top := S.tensorFiltration_last (A := A)
  monotone := S.tensorFiltration_mono (A := A)
  ideal := S.tensorFiltration_isIdealSubspace (A := A)
  coeff := S.tensorLayerCoeff (A := A)
  coeff_ker := S.tensorLayerCoeff_ker (A := A)
  rho := S.tensorRho
  rho_surjective := S.tensorRho_surjective
  coeff_mul := S.tensorLayerCoeff_mul (A := A)

end SplitDualFiltration

end UnifiedRounding
