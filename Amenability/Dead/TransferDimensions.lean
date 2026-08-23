/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.TransferData
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Dimension of the layers in filtered transfer data

For an ideal subspace `J ≤ Q`, the coefficient map identifies
`J_i / J_{i-1}` with its image `M_i ≤ A`.  This file records the
rank-nullity form
`dim J_i = dim J_{i-1} + dim M_i`.
-/

namespace HopfAmenability

universe u v w

variable {k : Type u} {Q : Type v} {A : Type w}
variable [Field k]
variable [CommRing Q] [Algebra k Q]
variable [CommRing A] [Algebra k A]
variable [FiniteDimensional k Q]

namespace FilteredTransferData

variable (T : FilteredTransferData k Q A)

open Module

/--
The natural inclusion from the previous `J`-step into the next one.
-/
def stepInclusion
    (J : Submodule k Q)
    (i : Fin T.n) :
    T.step J i.castSucc →ₗ[k] T.step J i.succ where
  toFun x :=
    ⟨⟨(x.1 : Q), T.monotone i x.1.2⟩, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional k Q] in
@[simp]
theorem coe_stepInclusion
    (J : Submodule k Q)
    (i : Fin T.n)
    (x : T.step J i.castSucc) :
    (((T.stepInclusion J i x).1 : T.filtration i.succ) : Q) =
      (x.1 : Q) :=
  rfl

omit [FiniteDimensional k Q] in
/--
The step inclusion is injective.
-/
theorem stepInclusion_injective
    (J : Submodule k Q)
    (i : Fin T.n) :
    Function.Injective (T.stepInclusion J i) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congr_arg (fun z : T.step J i.succ => ((z.1 : T.filtration i.succ) : Q)) h

omit [FiniteDimensional k Q] in
/--
The range of the previous-step inclusion is exactly the kernel of the
layer coefficient map.
-/
theorem range_stepInclusion_eq_ker_layerMap
    (J : Submodule k Q)
    (i : Fin T.n) :
    LinearMap.range (T.stepInclusion J i) =
      LinearMap.ker (T.layerMap J i) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [T.mem_ker_layerMap_iff J i]
    exact y.1.2
  · intro hx
    rw [T.mem_ker_layerMap_iff J i] at hx
    refine ⟨⟨⟨(x.1 : Q), hx⟩, x.2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [FiniteDimensional k Q] in
/--
The kernel of the layer map has the same dimension as the preceding
filtered piece.
-/
theorem finrank_ker_layerMap
    (J : Submodule k Q)
    (i : Fin T.n) :
    finrank k (LinearMap.ker (T.layerMap J i)) =
      finrank k (T.step J i.castSucc) := by
  rw [← T.range_stepInclusion_eq_ker_layerMap J i]
  symm
  exact
    (LinearEquiv.ofInjective
      (T.stepInclusion J i)
      (T.stepInclusion_injective J i)).finrank_eq

/--
Rank-nullity on a filtered layer:
`dim J_i = dim J_{i-1} + dim M_i`.
-/
theorem finrank_step_succ
    (J : Submodule k Q)
    (i : Fin T.n) :
    finrank k (T.step J i.succ) =
      finrank k (T.step J i.castSucc) +
        finrank k (T.layerImage J i) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (T.layerMap J i)
  rw [T.finrank_ker_layerMap J i] at h
  change
    finrank k (T.layerImage J i) +
        finrank k (T.step J i.castSucc) =
      finrank k (T.step J i.succ) at h
  omega

end FilteredTransferData

end HopfAmenability
