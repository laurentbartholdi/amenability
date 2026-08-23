/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.SplitDual
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensoring a split filtration

Let `S` be a split filtration of a finite-dimensional commutative
`k`-algebra `R`, and let `A` be another commutative `k`-algebra.

This file constructs the tensor filtration
```
S_i ⊗ A ⊆ R ⊗ A
```
as the range of the natural inclusion, and transports the layer
coefficient
```
S_i → k
```
to a coefficient
```
S_i ⊗ A → A.
```

The main result is the tensor-layer kernel identity:
the kernel of the coefficient on the `i`-th tensor layer is precisely
the preceding tensor-filtration step. The proof uses right exactness of
tensor product.
-/

open TensorProduct

namespace HopfAmenability

universe u v w

variable {k : Type u} {R : Type v} {A : Type w}
variable [Field k]
variable [CommRing R] [Algebra k R]
variable [CommRing A] [Algebra k A]

namespace SplitDualFiltration

variable (S : SplitDualFiltration k R)

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/--
The natural inclusion of one step of the split filtration into the next.
-/
def layerInclusion
    (i : Fin S.n) :
    S.filtration i.castSucc →ₗ[k] S.filtration i.succ where
  toFun x := ⟨(x : R), S.monotone i x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_layerInclusion
    (i : Fin S.n)
    (x : S.filtration i.castSucc) :
    ((S.layerInclusion i x : S.filtration i.succ) : R) = (x : R) :=
  rfl

/--
The range of the layer inclusion is the kernel of the layer coefficient.
-/
theorem range_layerInclusion_eq_ker_coeff
    (i : Fin S.n) :
    LinearMap.range (S.layerInclusion i) =
      LinearMap.ker (S.coeff i) := by
  rw [S.coeff_ker i]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨(x : R), hx⟩, rfl⟩

/--
The successive layer inclusion and coefficient form an exact pair.
-/
theorem exact_layerInclusion_coeff
    (i : Fin S.n) :
    Function.Exact (S.layerInclusion i) (S.coeff i) := by
  rw [LinearMap.exact_iff]
  exact (S.range_layerInclusion_eq_ker_coeff i).symm

/--
The `j`-th tensor-filtration step `S_j ⊗ A`, viewed inside `R ⊗ A`.
-/
def tensorFiltration
    (j : Fin (S.n + 1)) :
    Submodule k (R ⊗[k] A) :=
  LinearMap.range ((S.filtration j).subtype.rTensor A)

/--
The inclusion `S_j ⊗ A → R ⊗ A` is injective over the field `k`.
-/
theorem tensorFiltrationMap_injective
    (j : Fin (S.n + 1)) :
    Function.Injective ((S.filtration j).subtype.rTensor A) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap
    (S.filtration j).subtype Subtype.val_injective

/--
Identification of `S_j ⊗ A` with its image in `R ⊗ A`.
-/
noncomputable def tensorFiltrationEquiv
    (j : Fin (S.n + 1)) :
    S.filtration j ⊗[k] A ≃ₗ[k] S.tensorFiltration (A := A) j :=
  LinearEquiv.ofInjective
    ((S.filtration j).subtype.rTensor A)
    (S.tensorFiltrationMap_injective (A := A) j)

@[simp]
theorem coe_tensorFiltrationEquiv
    (j : Fin (S.n + 1))
    (z : S.filtration j ⊗[k] A) :
    ((S.tensorFiltrationEquiv (A := A) j z :
        S.tensorFiltration (A := A) j) : R ⊗[k] A) =
      ((S.filtration j).subtype.rTensor A) z :=
  rfl

/--
The raw coefficient on `S_{i+1} ⊗ A`.
-/
def tensorCoeff
    (i : Fin S.n) :
    S.filtration i.succ ⊗[k] A →ₗ[k] A :=
  (TensorProduct.lid k A).toLinearMap.comp
    ((S.coeff i).rTensor A)

@[simp]
theorem tensorCoeff_tmul
    (i : Fin S.n)
    (x : S.filtration i.succ)
    (a : A) :
    S.tensorCoeff (A := A) i (x ⊗ₜ[k] a) = S.coeff i x • a :=
  rfl

/--
After tensoring with `A`, the preceding layer remains exactly the kernel
of the layer coefficient.
-/
theorem ker_tensorCoeff
    (i : Fin S.n) :
    LinearMap.ker (S.tensorCoeff (A := A) i) =
      LinearMap.range ((S.layerInclusion i).rTensor A) := by
  have hexact :
      Function.Exact
        ((S.layerInclusion i).rTensor A)
        ((S.coeff i).rTensor A) := rTensor_exact
      A
      (S.exact_layerInclusion_coeff i)
      (S.coeff_surjective i)
  have hker :
      LinearMap.ker ((S.coeff i).rTensor A) =
        LinearMap.range ((S.layerInclusion i).rTensor A) := by
    exact LinearMap.exact_iff.mp hexact
  apply le_antisymm
  · intro z hz
    have hz0 :
        ((S.coeff i).rTensor A) z = 0 := by
      rw [LinearMap.mem_ker] at hz
      apply (TensorProduct.lid k A).injective
      simpa [tensorCoeff] using hz
    have :
        z ∈ LinearMap.ker ((S.coeff i).rTensor A) := by
      simpa [LinearMap.mem_ker] using hz0
    rw [hker] at this
    exact this
  · intro z hz
    have hzker :
        z ∈ LinearMap.ker ((S.coeff i).rTensor A) := by
      rw [hker]
      exact hz
    rw [LinearMap.mem_ker] at hzker ⊢
    change
      (TensorProduct.lid k A)
          (((S.coeff i).rTensor A) z) = 0
    rw [hzker]
    simp

/--
The tensor filtration is monotone.
-/
theorem tensorFiltration_mono
    (i : Fin S.n) :
    S.tensorFiltration (A := A) i.castSucc ≤
      S.tensorFiltration (A := A) i.succ := by
  rintro y ⟨z, rfl⟩
  refine ⟨((S.layerInclusion i).rTensor A) z, ?_⟩
  change
    ((S.filtration i.succ).subtype.rTensor A)
        (((S.layerInclusion i).rTensor A) z) =
      ((S.filtration i.castSucc).subtype.rTensor A) z
  rw [← LinearMap.rTensor_comp_apply]
  rfl

/--
The tensor filtration starts at zero.
-/
theorem tensorFiltration_zero :
    S.tensorFiltration (A := A) 0 = ⊥ := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    rw [Submodule.mem_bot]
    induction z using TensorProduct.induction_on with
    | zero =>
        simp
    | add z₁ z₂ hz₁ hz₂ =>
        simp [hz₁, hz₂]
    | tmul x a =>
        have hx : (x : R) = 0 := by
          have hxmem : (x : R) ∈ (⊥ : Submodule k R) := by
            simpa [S.bot] using x.2
          simpa [Submodule.mem_bot] using hxmem
        simp [hx]
  · exact bot_le

/--
The tensor filtration ends at the whole tensor product.
-/
theorem tensorFiltration_last :
    S.tensorFiltration (A := A) (Fin.last S.n) = ⊤ := by
  rw [tensorFiltration]
  apply LinearMap.range_eq_top.mpr
  apply LinearMap.rTensor_surjective A
  intro r
  refine ⟨⟨r, ?_⟩, rfl⟩
  rw [S.top]
  exact Submodule.mem_top

/--
The coefficient on the actual tensor-filtration subspace, obtained by
transporting `tensorCoeff` through the identification with the range.
-/
noncomputable def tensorLayerCoeff
    (i : Fin S.n) :
    S.tensorFiltration (A := A) i.succ →ₗ[k] A :=
  (S.tensorCoeff (A := A) i).comp
    (S.tensorFiltrationEquiv (A := A) i.succ).symm.toLinearMap

@[simp]
theorem tensorLayerCoeff_equiv
    (i : Fin S.n)
    (z : S.filtration i.succ ⊗[k] A) :
    S.tensorLayerCoeff (A := A) i
        (S.tensorFiltrationEquiv (A := A) i.succ z) =
      S.tensorCoeff (A := A) i z := by
  simp [tensorLayerCoeff]

/--
The kernel of the coefficient on the tensor-filtration subtype is exactly
the preceding tensor-filtration step, viewed inside the current one.
-/
theorem tensorLayerCoeff_ker
    (i : Fin S.n) :
    LinearMap.ker (S.tensorLayerCoeff (A := A) i) =
      (S.tensorFiltration (A := A) i.castSucc).comap
        (S.tensorFiltration (A := A) i.succ).subtype := by
  ext x
  let z : S.filtration i.succ ⊗[k] A :=
    (S.tensorFiltrationEquiv (A := A) i.succ).symm x
  have hxz :
      S.tensorFiltrationEquiv (A := A) i.succ z = x := by
    exact (S.tensorFiltrationEquiv (A := A) i.succ).apply_symm_apply x
  have hxzAmbient :
      ((x : S.tensorFiltration (A := A) i.succ) : R ⊗[k] A) =
        ((S.filtration i.succ).subtype.rTensor A) z := by
    have h := congrArg
      (fun y : S.tensorFiltration (A := A) i.succ =>
        ((y : S.tensorFiltration (A := A) i.succ) : R ⊗[k] A))
      hxz
    simpa only [coe_tensorFiltrationEquiv] using h.symm
  constructor
  · intro hx
    have hzker :
        z ∈ LinearMap.ker (S.tensorCoeff (A := A) i) := by
      rw [LinearMap.mem_ker]
      have hx0 :
          S.tensorLayerCoeff (A := A) i x = 0 := by
        simpa [LinearMap.mem_ker] using hx
      rw [← hxz] at hx0
      have hz0 :
          S.tensorLayerCoeff (A := A) i
              (S.tensorFiltrationEquiv (A := A) i.succ z) = 0 := by
        rw [hxz]
        simpa only [hxz] using hx0
      simpa only [tensorLayerCoeff_equiv] using hz0
    rw [S.ker_tensorCoeff (A := A) i] at hzker
    rcases hzker with ⟨y, hy⟩
    change
      ((x : S.tensorFiltration (A := A) i.succ) : R ⊗[k] A) ∈
        S.tensorFiltration (A := A) i.castSucc
    refine ⟨y, ?_⟩
    rw [hxzAmbient, ← hy]
    change
      ((S.filtration i.castSucc).subtype.rTensor A) y =
        ((S.filtration i.succ).subtype.rTensor A)
          (((S.layerInclusion i).rTensor A) y)
    rw [← LinearMap.rTensor_comp_apply]
    rfl
  · intro hx
    change
      ((x : S.tensorFiltration (A := A) i.succ) : R ⊗[k] A) ∈
        S.tensorFiltration (A := A) i.castSucc at hx
    rcases hx with ⟨y, hy⟩
    have hpre :
        z = ((S.layerInclusion i).rTensor A) y := by
      apply S.tensorFiltrationMap_injective (A := A) i.succ
      calc
        ((S.filtration i.succ).subtype.rTensor A) z =
            ((x : S.tensorFiltration (A := A) i.succ) : R ⊗[k] A) :=
          hxzAmbient.symm
        _ = ((S.filtration i.castSucc).subtype.rTensor A) y :=
          hy.symm
        _ = ((S.filtration i.succ).subtype.rTensor A)
              (((S.layerInclusion i).rTensor A) y) := by
            rw [← LinearMap.rTensor_comp_apply]
            rfl
    rw [LinearMap.mem_ker]
    rw [← hxz]
    simp only [tensorLayerCoeff_equiv]
    rw [hpre]
    have hyker :
        ((S.layerInclusion i).rTensor A) y ∈
          LinearMap.ker (S.tensorCoeff (A := A) i) := by
      rw [S.ker_tensorCoeff (A := A) i]
      exact ⟨y, rfl⟩
    simpa [LinearMap.mem_ker] using hyker

end SplitDualFiltration

end HopfAmenability
