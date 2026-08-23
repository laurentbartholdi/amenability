/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CoalgHomDual
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The dual of a tensor product of finite coalgebras

For finite-dimensional coalgebras `C,D`, the canonical vector-space
equivalence
`C* ⊗ D* ≃ (C ⊗ D)*`
is an algebra equivalence for convolution.

The `WithConv` wrappers are inserted only to select convolution rather than
composition as the multiplication on dual linear maps.
-/

open Coalgebra TensorProduct WithConv
open scoped TensorProduct

namespace UnifiedRounding

universe u v w

variable {k : Type u} {C : Type v} {D : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup D] [Module k D] [Coalgebra k D]
variable [FiniteDimensional k C] [FiniteDimensional k D]

/--
The canonical linear equivalence
`C* ⊗ D* ≃ (C ⊗ D)*`, with convolution wrappers.
-/
noncomputable def convDualDistribLinearEquiv :
    WithConv (Module.Dual k C) ⊗[k]
        WithConv (Module.Dual k D) ≃ₗ[k]
      WithConv (Module.Dual k (C ⊗[k] D)) :=
  TensorProduct.congr
      (WithConv.linearEquiv k (Module.Dual k C))
      (WithConv.linearEquiv k (Module.Dual k D)) ≪≫ₗ
    TensorProduct.dualDistribEquiv k C D ≪≫ₗ
      (WithConv.linearEquiv k
        (Module.Dual k (C ⊗[k] D))).symm

omit [Coalgebra k C] [Coalgebra k D] in
@[simp]
theorem convDualDistribLinearEquiv_tmul_apply
    (φ : WithConv (Module.Dual k C))
    (ψ : WithConv (Module.Dual k D))
    (c : C) (d : D) :
    convDualDistribLinearEquiv (k := k) (C := C) (D := D)
        (φ ⊗ₜ[k] ψ) (c ⊗ₜ[k] d) =
      φ c * ψ d := by
  rfl

/--
The canonical dual-distribution equivalence preserves the convolution unit.
-/
theorem convDualDistribLinearEquiv_one :
    convDualDistribLinearEquiv (k := k) (C := C) (D := D) 1 = 1 := by
  apply WithConv.ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul c d =>
      rw [Algebra.TensorProduct.one_def]
      rw [convDualDistribLinearEquiv_tmul_apply]
      simp [mul_comm]
  | add x y hx hy =>
      simp [hx, hy]

omit [Coalgebra k C] [Coalgebra k D] in
/-
On a pure tensor of functionals, the dual-distribution equivalence is
exactly the tensor product of the two underlying linear functionals.
-/
@[simp]
theorem convDualDistribLinearEquiv_tmul
    (φ : WithConv (Module.Dual k C))
    (ψ : WithConv (Module.Dual k D)) :
    convDualDistribLinearEquiv (k := k) (C := C) (D := D)
        (φ ⊗ₜ[k] ψ) =
      WithConv.toConv
        ((TensorProduct.lid k k).toLinearMap.comp
          (TensorProduct.map φ.ofConv ψ.ofConv)) := by
  apply WithConv.ext
  apply TensorProduct.ext'
  intro c d
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
  exact convDualDistribLinearEquiv_tmul_apply
    (k := k) (C := C) (D := D) φ ψ c d

/--
The canonical dual-distribution equivalence preserves multiplication.
-/
theorem convDualDistribLinearEquiv_mul
    (x y :
      WithConv (Module.Dual k C) ⊗[k]
        WithConv (Module.Dual k D)) :
    convDualDistribLinearEquiv (k := k) (C := C) (D := D) (x * y) =
      convDualDistribLinearEquiv (k := k) (C := C) (D := D) x *
        convDualDistribLinearEquiv (k := k) (C := C) (D := D) y := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      simp [add_mul, hx₁, hx₂]
  | tmul φ ψ =>
      induction y using TensorProduct.induction_on with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          simp [mul_add, hy₁, hy₂]
      | tmul φ' ψ' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          rw [convDualDistribLinearEquiv_tmul]
          rw [convDualDistribLinearEquiv_tmul]
          rw [convDualDistribLinearEquiv_tmul]
          apply WithConv.ext
          let h : k ⊗[k] k →ₐ[k] k :=
            (Algebra.TensorProduct.lid k k).toAlgHom
          have hm :=
            LinearMap.algHom_comp_convMul_distrib
              h
              (WithConv.toConv
                (TensorProduct.map φ.ofConv ψ.ofConv))
              (WithConv.toConv
                (TensorProduct.map φ'.ofConv ψ'.ofConv))
          rw [TensorProduct.map_convMul_map] at hm
          change
            h.toLinearMap.comp
                (TensorProduct.map
                  (φ * φ').ofConv (ψ * ψ').ofConv) =
              (WithConv.toConv
                    (h.toLinearMap.comp
                      (TensorProduct.map φ.ofConv ψ.ofConv)) *
                WithConv.toConv
                    (h.toLinearMap.comp
                      (TensorProduct.map φ'.ofConv ψ'.ofConv))).ofConv
          simpa [h, Algebra.TensorProduct.lid_toLinearEquiv] using hm

/--
For finite-dimensional coalgebras, dualizing tensor product is an algebra
equivalence.
-/
noncomputable def convDualDistribAlgEquiv :
    WithConv (Module.Dual k C) ⊗[k]
        WithConv (Module.Dual k D) ≃ₐ[k]
      WithConv (Module.Dual k (C ⊗[k] D)) :=
  AlgEquiv.ofLinearEquiv
    (convDualDistribLinearEquiv (k := k) (C := C) (D := D))
    convDualDistribLinearEquiv_one
    convDualDistribLinearEquiv_mul

@[simp]
theorem convDualDistribAlgEquiv_tmul_apply
    (φ : WithConv (Module.Dual k C))
    (ψ : WithConv (Module.Dual k D))
    (c : C) (d : D) :
    convDualDistribAlgEquiv (k := k) (C := C) (D := D)
        (φ ⊗ₜ[k] ψ) (c ⊗ₜ[k] d) =
      φ c * ψ d :=
  rfl

end UnifiedRounding
