/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.SplitDual

/-!
# Abstract filtered transfer data

This file isolates the exact algebraic structure used by the filtered
transfer argument.

A `FilteredTransferData k Q A` consists of a finite filtration of `Q` by
ideal subspaces, coefficient maps from successive layers to `A`, and
surjective algebra maps `rho_i : Q → A` describing the action on each
layer.

The principal result here is that the image in `A` of the `i`-th layer of
an ideal of `Q` is again an ideal subspace of `A`.
-/

namespace HopfAmenability

universe u v w

variable {k : Type u} {Q : Type v} {A : Type w}
variable [Field k]
variable [CommRing Q] [Algebra k Q]
variable [CommRing A] [Algebra k A]

/--
The filtered algebra data needed for the transfer lemma.
-/
structure FilteredTransferData (k : Type u) (Q : Type v) (A : Type w)
    [Field k] [CommRing Q] [Algebra k Q]
    [CommRing A] [Algebra k A] where
  n : ℕ
  filtration : Fin (n + 1) → Submodule k Q
  bot : filtration 0 = ⊥
  top : filtration (Fin.last n) = ⊤
  monotone :
    ∀ i : Fin n, filtration i.castSucc ≤ filtration i.succ
  ideal :
    ∀ j : Fin (n + 1), IsIdealSubspace (filtration j)
  coeff :
    ∀ i : Fin n, filtration i.succ →ₗ[k] A
  coeff_ker :
    ∀ i : Fin n,
      LinearMap.ker (coeff i) =
        (filtration i.castSucc).comap
          (filtration i.succ).subtype
  rho :
    Fin n → Q →ₐ[k] A
  rho_surjective :
    ∀ i : Fin n, Function.Surjective (rho i)
  coeff_mul :
    ∀ (i : Fin n) (q : Q) (x : filtration i.succ),
      coeff i
          ⟨q * (x : Q),
            ideal i.succ q x.2⟩ =
        rho i q * coeff i x

namespace FilteredTransferData

variable (T : FilteredTransferData k Q A)

/--
The part of a subspace `J ≤ Q` lying in a filtration step, regarded as a
subspace of that filtration step.
-/
def step
    (J : Submodule k Q)
    (j : Fin (T.n + 1)) :
    Submodule k (T.filtration j) :=
  J.comap (T.filtration j).subtype

/--
The coefficient map restricted to the part of `J` in the upper endpoint of
a layer.
-/
def layerMap
    (J : Submodule k Q)
    (i : Fin T.n) :
    T.step J i.succ →ₗ[k] A :=
  (T.coeff i).comp (T.step J i.succ).subtype

/--
The image `M_i` in `A` of the `i`-th layer of `J`.
-/
def layerImage
    (J : Submodule k Q)
    (i : Fin T.n) :
    Submodule k A :=
  LinearMap.range (T.layerMap J i)

/--
Elements of a filtration step may be multiplied by arbitrary elements of
`Q`.
-/
theorem filtration_mul_mem
    (j : Fin (T.n + 1))
    (q : Q)
    {x : Q}
    (hx : x ∈ T.filtration j) :
    q * x ∈ T.filtration j :=
  T.ideal j q hx

/--
If `J` is an ideal subspace, multiplying an element of `step J j` by an
arbitrary element of `Q` remains in `step J j`.
-/
def mulStep
    (J : Submodule k Q)
    (hJ : IsIdealSubspace J)
    (j : Fin (T.n + 1))
    (q : Q)
    (x : T.step J j) :
    T.step J j :=
  ⟨⟨q * (x.1 : Q), T.filtration_mul_mem j q x.1.2⟩,
    hJ q x.2⟩

@[simp]
theorem coe_mulStep
    (J : Submodule k Q)
    (hJ : IsIdealSubspace J)
    (j : Fin (T.n + 1))
    (q : Q)
    (x : T.step J j) :
    ((T.mulStep J hJ j q x : T.filtration j) : Q) =
      q * (x.1 : Q) :=
  rfl

/--
The layer map intertwines multiplication by `q` with multiplication by
`rho_i(q)`.
-/
theorem layerMap_mulStep
    (J : Submodule k Q)
    (hJ : IsIdealSubspace J)
    (i : Fin T.n)
    (q : Q)
    (x : T.step J i.succ) :
    T.layerMap J i (T.mulStep J hJ i.succ q x) =
      T.rho i q * T.layerMap J i x := by
  exact T.coeff_mul i q x.1

/--
The image of every layer of an ideal subspace of `Q` is an ideal subspace
of `A`.

This is the point where surjectivity of `rho_i : Q → A` is essential.
-/
theorem layerImage_isIdealSubspace
    (J : Submodule k Q)
    (hJ : IsIdealSubspace J)
    (i : Fin T.n) :
    IsIdealSubspace (T.layerImage J i) := by
  intro a y hy
  rcases hy with ⟨x, rfl⟩
  obtain ⟨q, hq⟩ := T.rho_surjective i a
  refine ⟨T.mulStep J hJ i.succ q x, ?_⟩
  rw [T.layerMap_mulStep J hJ i q x, hq]

/--
The kernel of the layer map consists exactly of those elements which lie in
the preceding filtration step.
-/
theorem mem_ker_layerMap_iff
    (J : Submodule k Q)
    (i : Fin T.n)
    (x : T.step J i.succ) :
    x ∈ LinearMap.ker (T.layerMap J i) ↔
      (x.1 : Q) ∈ T.filtration i.castSucc := by
  change T.coeff i x.1 = 0 ↔ _
  rw [← LinearMap.mem_ker]
  rw [T.coeff_ker i]
  rfl

end FilteredTransferData

end HopfAmenability
