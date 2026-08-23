/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubcoalgebraIntersectionReduction
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic

/-!
# Intersections of tensor squares over a field

This file proves the linear-algebra identity needed for intersections of
subcoalgebras:
```
((C ∩ D) ⊗ (C ∩ D)) = (C ⊗ C) ∩ (D ⊗ D)
```
inside `H ⊗ H`.

The proof does not choose bases.  It uses that every vector space over a field
is free, hence flat, so tensoring preserves the exact sequence
`C → H → H/C`.
-/

open scoped TensorProduct

namespace HopfAmenability

universe u v w

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/--
Postcomposing a linear map with a linear equivalence does not change its
kernel.
-/
private theorem ker_equiv_comp
    {A : Type v} {B : Type w} {C : Type*}
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C]
    (e : B ≃ₗ[k] C) (f : A →ₗ[k] B) :
    LinearMap.ker (e.toLinearMap.comp f) = LinearMap.ker f := by
  ext x
  simp

/--
Tensoring the exact sequence `C → H → H/C` on the right gives
`C ⊗ M = ker(H ⊗ M → (H/C) ⊗ M)`.
-/
private theorem range_subtype_rTensor_eq_ker_mkQ_rTensor
    {M : Type w} [AddCommGroup M] [Module k M]
    (C : Submodule k H) :
    LinearMap.range (C.subtype.rTensor M) =
      LinearMap.ker (C.mkQ.rTensor M) := by
  have h :=
    Module.Flat.rTensor_exact M
      (LinearMap.exact_subtype_ker_map C.mkQ)
  have hC : C.mkQ.ker = C := by ext x; simp
  have hex := (LinearMap.exact_iff.mp h).symm
  rw [hC] at hex
  exact hex

/--
Tensoring the exact sequence `C → H → H/C` on the left gives
`M ⊗ C = ker(M ⊗ H → M ⊗ (H/C))`.
-/
private theorem range_subtype_lTensor_eq_ker_mkQ_lTensor
    {M : Type w} [AddCommGroup M] [Module k M]
    (C : Submodule k H) :
    LinearMap.range (C.subtype.lTensor M) =
      LinearMap.ker (C.mkQ.lTensor M) := by
  have h :=
    Module.Flat.lTensor_exact M
      (LinearMap.exact_subtype_ker_map C.mkQ)
  have hC : C.mkQ.ker = C := by ext x; simp
  have hex := (LinearMap.exact_iff.mp h).symm
  rw [hC] at hex
  exact hex

/--
Tensoring on the right preserves intersections of subspaces.
-/
theorem range_rTensor_inf
    (C D : Submodule k H) :
    LinearMap.range ((C ⊓ D : Submodule k H).subtype.rTensor H) =
      LinearMap.range (C.subtype.rTensor H) ⊓
        LinearMap.range (D.subtype.rTensor H) := by
  let q : H →ₗ[k] (H ⧸ C) × (H ⧸ D) := C.mkQ.prod D.mkQ
  let e :
      ((H ⧸ C) × (H ⧸ D)) ⊗[k] H ≃ₗ[k]
        ((H ⧸ C) ⊗[k] H) × ((H ⧸ D) ⊗[k] H) :=
    TensorProduct.prodLeft k k (H ⧸ C) (H ⧸ D) H
  have hkerq : LinearMap.ker q = (C ⊓ D : Submodule k H) := by
    simp [q]
  have hq :
      LinearMap.range ((LinearMap.ker q).subtype.rTensor H) =
        LinearMap.ker (q.rTensor H) := by
    have h :=
      Module.Flat.rTensor_exact H
        (LinearMap.exact_subtype_ker_map q)
    exact (LinearMap.exact_iff.mp h).symm
  have hcomp :
      e.toLinearMap.comp (q.rTensor H) =
        (C.mkQ.rTensor H).prod (D.mkQ.rTensor H) := by
    ext x y
    · simp [q, e, TensorProduct.prodLeft, LinearMap.prod_apply]
    · simp [q, e, TensorProduct.prodLeft, LinearMap.prod_apply]
  have hker :
      LinearMap.ker (q.rTensor H) =
        LinearMap.ker (C.mkQ.rTensor H) ⊓
          LinearMap.ker (D.mkQ.rTensor H) := by
    calc
      LinearMap.ker (q.rTensor H)
          = LinearMap.ker (e.toLinearMap.comp (q.rTensor H)) :=
              (ker_equiv_comp e (q.rTensor H)).symm
      _ = LinearMap.ker
          ((C.mkQ.rTensor H).prod (D.mkQ.rTensor H)) := by rw [hcomp]
      _ = LinearMap.ker (C.mkQ.rTensor H) ⊓
          LinearMap.ker (D.mkQ.rTensor H) := LinearMap.ker_prod _ _
  rw [hkerq] at hq
  calc
    LinearMap.range ((C ⊓ D : Submodule k H).subtype.rTensor H)
        = LinearMap.ker (q.rTensor H) := hq
    _ = LinearMap.ker (C.mkQ.rTensor H) ⊓
        LinearMap.ker (D.mkQ.rTensor H) := hker
    _ = LinearMap.range (C.subtype.rTensor H) ⊓
        LinearMap.range (D.subtype.rTensor H) := by
          rw [range_subtype_rTensor_eq_ker_mkQ_rTensor C,
            range_subtype_rTensor_eq_ker_mkQ_rTensor D]

/--
Tensoring on the left preserves intersections of subspaces.
-/
theorem range_lTensor_inf
    (C D : Submodule k H) :
    LinearMap.range ((C ⊓ D : Submodule k H).subtype.lTensor H) =
      LinearMap.range (C.subtype.lTensor H) ⊓
        LinearMap.range (D.subtype.lTensor H) := by
  let q : H →ₗ[k] (H ⧸ C) × (H ⧸ D) := C.mkQ.prod D.mkQ
  let e :
      H ⊗[k] ((H ⧸ C) × (H ⧸ D)) ≃ₗ[k]
        (H ⊗[k] (H ⧸ C)) × (H ⊗[k] (H ⧸ D)) :=
    TensorProduct.prodRight k k H (H ⧸ C) (H ⧸ D)
  have hkerq : LinearMap.ker q = (C ⊓ D : Submodule k H) := by
    simp [q]
  have hq :
      LinearMap.range ((LinearMap.ker q).subtype.lTensor H) =
        LinearMap.ker (q.lTensor H) := by
    have h :=
      Module.Flat.lTensor_exact H
        (LinearMap.exact_subtype_ker_map q)
    exact (LinearMap.exact_iff.mp h).symm
  have hcomp :
      e.toLinearMap.comp (q.lTensor H) =
        (C.mkQ.lTensor H).prod (D.mkQ.lTensor H) := by
    ext x y
    · simp [q, e, TensorProduct.prodRight]
    · simp [q, e, TensorProduct.prodRight]
  have hker :
      LinearMap.ker (q.lTensor H) =
        LinearMap.ker (C.mkQ.lTensor H) ⊓
          LinearMap.ker (D.mkQ.lTensor H) := by
    calc
      LinearMap.ker (q.lTensor H)
          = LinearMap.ker (e.toLinearMap.comp (q.lTensor H)) :=
              (ker_equiv_comp e (q.lTensor H)).symm
      _ = LinearMap.ker
          ((C.mkQ.lTensor H).prod (D.mkQ.lTensor H)) := by rw [hcomp]
      _ = LinearMap.ker (C.mkQ.lTensor H) ⊓
          LinearMap.ker (D.mkQ.lTensor H) := LinearMap.ker_prod _ _
  rw [hkerq] at hq
  calc
    LinearMap.range ((C ⊓ D : Submodule k H).subtype.lTensor H)
        = LinearMap.ker (q.lTensor H) := hq
    _ = LinearMap.ker (C.mkQ.lTensor H) ⊓
        LinearMap.ker (D.mkQ.lTensor H) := hker
    _ = LinearMap.range (C.subtype.lTensor H) ⊓
        LinearMap.range (D.subtype.lTensor H) := by
          rw [range_subtype_lTensor_eq_ker_mkQ_lTensor C,
            range_subtype_lTensor_eq_ker_mkQ_lTensor D]

/--
The image of `C ⊗ C` in `H ⊗ H` is the intersection of the two one-sided
tensor subspaces `C ⊗ H` and `H ⊗ C`.
-/
theorem range_mapIncl_self_eq_inf
    (C : Submodule k H) :
    LinearMap.range (TensorProduct.mapIncl C C) =
      LinearMap.range (C.subtype.rTensor H) ⊓
        LinearMap.range (C.subtype.lTensor H) := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    constructor
    · refine ⟨C.subtype.lTensor C z, ?_⟩
      change
        (C.subtype.rTensor H) (C.subtype.lTensor C z) =
          TensorProduct.map C.subtype C.subtype z
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
    · refine ⟨C.subtype.rTensor C z, ?_⟩
      change
        (C.subtype.lTensor H) (C.subtype.rTensor C z) =
          TensorProduct.map C.subtype C.subtype z
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]
  · rintro x ⟨hxL, hxR⟩
    rcases hxL with ⟨y, hy⟩
    have hxq : (C.mkQ.lTensor H) x = 0 := by
      rcases hxR with ⟨z, rfl⟩
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have hcomp : C.mkQ.comp C.subtype = 0 := by ext y; simp
      rw [hcomp]
      simp
    have hyq :
        (C.mkQ.lTensor H) ((C.subtype.rTensor H) y) = 0 := by
      rw [hy]
      exact hxq
    have hinj :
        Function.Injective (C.subtype.rTensor (H ⧸ C)) :=
      Module.Flat.rTensor_preserves_injective_linearMap
        C.subtype C.injective_subtype
    have hyker : (C.mkQ.lTensor C) y = 0 := by
      apply hinj
      simpa [← LinearMap.comp_apply] using hyq
    have hymem :
        y ∈ LinearMap.range (C.subtype.lTensor C) := by
      rw [range_subtype_lTensor_eq_ker_mkQ_lTensor C]
      exact hyker
    rcases hymem with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    simpa [TensorProduct.mapIncl, ← LinearMap.comp_apply] using hy

/--
Tensor squares preserve intersections over a field.
-/
theorem tensorSquareIntersectionProperty :
    TensorSquareIntersectionProperty (k := k) (H := H) := by
  intro C D
  rw [range_mapIncl_self_eq_inf (C ⊓ D : Submodule k H)]
  rw [range_rTensor_inf C D, range_lTensor_inf C D]
  rw [range_mapIncl_self_eq_inf C, range_mapIncl_self_eq_inf D]
  ac_rfl

/--
Consequently, subcoalgebras are closed under intersections.
-/
theorem IsSubcoalgebra.inf
    [Coalgebra k H]
    {C D : Submodule k H}
    (hC : IsSubcoalgebra (k := k) C)
    (hD : IsSubcoalgebra (k := k) D) :
    IsSubcoalgebra (k := k) (C ⊓ D : Submodule k H) :=
  hC.inf_of_tensorSquareIntersection
    (tensorSquareIntersectionProperty (k := k) (H := H)) hD

/--
The temporary intersection-closure hypothesis from `CoalgebraDensity.lean` is
automatic over a field.
-/
theorem subcoalgebraInfClosed
    [Coalgebra k H] (G : Submodule k H) :
    SubcoalgebraInfClosed (k := k) G :=
  subcoalgebraInfClosed_of_tensorSquareIntersection
    (tensorSquareIntersectionProperty (k := k) (H := H)) G

end HopfAmenability
