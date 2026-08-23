/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Comodule
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Linear maps of right comodules
-/

open TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w x

variable {k : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [RightComodule k C M]
variable [AddCommGroup N] [Module k N] [RightComodule k C N]

/-- A linear map intertwines the right coactions. -/
def IsRightComoduleMap (f : M →ₗ[k] N) : Prop :=
  RightComodule.coaction (k := k) (C := C) (M := N) ∘ₗ f =
    f.rTensor C ∘ₗ RightComodule.coaction (k := k) (C := C) (M := M)

namespace IsRightComoduleMap

theorem id : IsRightComoduleMap (C := C) (LinearMap.id (R := k) (M := M)) := by
  ext m
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.rTensor_id_apply]

theorem comp {P : Type*} [AddCommGroup P] [Module k P] [RightComodule k C P]
    {g : N →ₗ[k] P} {f : M →ₗ[k] N}
    (hg : IsRightComoduleMap (C := C) g)
    (hf : IsRightComoduleMap (C := C) f) :
    IsRightComoduleMap (C := C) (g.comp f) := by
  ext m
  have hgm := LinearMap.congr_fun hg (f m)
  have hfm := LinearMap.congr_fun hf m
  simp only [LinearMap.comp_apply] at hgm hfm ⊢
  rw [hgm, hfm, LinearMap.rTensor_comp_apply]

end IsRightComoduleMap

namespace IsRightSubcomodule

/-- The inverse image of a right subcomodule under a comodule map is a
right subcomodule. -/
theorem comap (P : Submodule k N) (f : M →ₗ[k] N)
    (hP : IsRightSubcomodule (C := C) P)
    (hf : IsRightComoduleMap (C := C) f) :
    IsRightSubcomodule (C := C) (P.comap f) := by
  intro m hm
  let q : M →ₗ[k] N ⧸ P := P.mkQ.comp f
  let qRange : M →ₗ[k] LinearMap.range q := q.rangeRestrict
  have hker : LinearMap.ker qRange = P.comap f := by
    ext x
    simp [qRange, q]
  have hqzero : q.rTensor C
      (RightComodule.coaction (k := k) (C := C) (M := M) m) = 0 := by
    have hfm : f m ∈ P := hm
    rcases hP (f m) hfm with ⟨z, hz⟩
    have hinter := LinearMap.congr_fun hf m
    simp only [LinearMap.comp_apply] at hinter
    calc
      q.rTensor C
          (RightComodule.coaction (k := k) (C := C) (M := M) m) =
          P.mkQ.rTensor C
            (f.rTensor C
              (RightComodule.coaction (k := k) (C := C) (M := M) m)) := by
            simp only [q, LinearMap.rTensor_comp_apply]
      _ = P.mkQ.rTensor C
          (RightComodule.coaction (k := k) (C := C) (M := N) (f m)) := by
            rw [← hinter]
      _ = P.mkQ.rTensor C (P.subtype.rTensor C z) := by rw [hz]
      _ = 0 := by
        rw [← LinearMap.rTensor_comp_apply]
        have hcomp : P.mkQ.comp P.subtype = 0 := by ext; simp
        rw [hcomp]
        simp
  have hqRangeZero : qRange.rTensor C
      (RightComodule.coaction (k := k) (C := C) (M := M) m) = 0 := by
    let : Module.Free k C := Module.Free.of_divisionRing k C
    have hinj : Function.Injective ((LinearMap.range q).subtype.rTensor C) :=
      Module.Flat.rTensor_preserves_injective_linearMap
        (LinearMap.range q).subtype (LinearMap.range q).subtype_injective
    refine @hinj
      (qRange.rTensor C
        (RightComodule.coaction (k := k) (C := C) (M := M) m)) 0 ?_
    rw [map_zero, ← LinearMap.rTensor_comp_apply]
    exact hqzero
  have hexact : Function.Exact
      ((LinearMap.ker qRange).subtype.rTensor C) (qRange.rTensor C) :=
    rTensor_exact C qRange.exact_subtype_ker_map (by
      exact q.surjective_rangeRestrict)
  rw [← hker]
  rw [← hexact.linearMap_ker_eq]
  exact hqRangeZero

/-- The image of a right subcomodule under a comodule map is a right
subcomodule. -/
theorem map (P : Submodule k M) (f : M →ₗ[k] N)
    (hP : IsRightSubcomodule (C := C) P)
    (hf : IsRightComoduleMap (C := C) f) :
    IsRightSubcomodule (C := C) (P.map f) := by
  rintro _ ⟨m, hm, rfl⟩
  rcases hP m hm with ⟨z, hz⟩
  let fP : P →ₗ[k] P.map f :=
    (f.domRestrict P).codRestrict (P.map f) fun p => ⟨p, p.2, rfl⟩
  refine ⟨fP.rTensor C z, ?_⟩
  have hinter := LinearMap.congr_fun hf m
  simp only [LinearMap.comp_apply] at hinter
  have hcomp : (P.map f).subtype.comp fP = f.comp P.subtype := by
    ext p
    rfl
  calc
    (P.map f).subtype.rTensor C (fP.rTensor C z) =
        ((P.map f).subtype.comp fP).rTensor C z := by
          rw [LinearMap.rTensor_comp_apply]
    _ = (f.comp P.subtype).rTensor C z := by rw [hcomp]
    _ = f.rTensor C (P.subtype.rTensor C z) := by
      rw [LinearMap.rTensor_comp_apply]
    _ = f.rTensor C
        (RightComodule.coaction (k := k) (C := C) (M := M) m) := by rw [hz]
    _ = RightComodule.coaction (k := k) (C := C) (M := N) (f m) := hinter.symm

end IsRightSubcomodule

end

end HopfAmenability
