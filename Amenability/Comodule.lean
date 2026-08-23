/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Right comodules over coalgebras

Reusable definitions and elementary constructions for right comodules.
-/

open TensorProduct

universe u v w

variable (k : Type u) (C : Type v) (M : Type w)
variable [CommSemiring k]
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid M] [Module k M]

/-- A right comodule over a coalgebra. -/
class RightComodule where
  coaction : M →ₗ[k] M ⊗[k] C
  coassoc :
    (TensorProduct.assoc k M C C).toLinearMap ∘ₗ
        coaction.rTensor C ∘ₗ coaction =
      (Coalgebra.comul (R := k) (A := C)).lTensor M ∘ₗ coaction
  counit :
    (TensorProduct.rid k M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := k) (A := C)).lTensor M ∘ₗ coaction =
      LinearMap.id

namespace RightComodule

variable {k C M}
variable [RightComodule k C M]

@[simp]
theorem coassoc_apply (m : M) :
    TensorProduct.assoc k M C C
        ((RightComodule.coaction (k := k) (C := C) (M := M)).rTensor C
          (RightComodule.coaction (k := k) (C := C) (M := M) m)) =
      (Coalgebra.comul (R := k) (A := C)).lTensor M
        (RightComodule.coaction (k := k) (C := C) (M := M) m) :=
  LinearMap.congr_fun RightComodule.coassoc m

@[simp]
theorem counit_apply (m : M) :
    TensorProduct.rid k M
        ((Coalgebra.counit (R := k) (A := C)).lTensor M
          (RightComodule.coaction (k := k) (C := C) (M := M) m)) = m :=
  LinearMap.congr_fun RightComodule.counit m

end RightComodule

/-- A coalgebra is a right comodule over itself via comultiplication. -/
instance coalgebraRightComodule : RightComodule k C C where
  coaction := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  counit := by
    apply LinearMap.ext
    intro c
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      Coalgebra.lTensor_counit_comul]
    simp

variable {k C M}
variable [RightComodule k C M]

/-- A submodule stable under the right coaction. -/
def IsRightSubcomodule (N : Submodule k M) : Prop :=
  ∀ m : M, m ∈ N →
    RightComodule.coaction (k := k) (C := C) (M := M) m ∈
      LinearMap.range (N.subtype.rTensor C)

namespace IsRightSubcomodule

theorem bot : IsRightSubcomodule (C := C) (⊥ : Submodule k M) := by
  intro m hm
  rw [Submodule.mem_bot] at hm
  subst m
  exact ⟨0, by simp⟩

theorem top : IsRightSubcomodule (C := C) (⊤ : Submodule k M) := by
  intro m hm
  exact (LinearMap.rTensor_surjective C
    (show Function.Surjective (⊤ : Submodule k M).subtype from
      fun x => ⟨⟨x, trivial⟩, rfl⟩))
    (RightComodule.coaction (k := k) (C := C) (M := M) m)

theorem mono {N P : Submodule k M}
    (hN : IsRightSubcomodule (C := C) N) (hNP : N ≤ P) :
    ∀ m ∈ N,
      RightComodule.coaction (k := k) (C := C) (M := M) m ∈
        LinearMap.range (P.subtype.rTensor C) := by
  intro m hm
  rcases hN m hm with ⟨z, hz⟩
  refine ⟨TensorProduct.map (Submodule.inclusion hNP) LinearMap.id z, ?_⟩
  have hmaps :
      (P.subtype.rTensor C) ∘ₗ
          TensorProduct.map (Submodule.inclusion hNP) LinearMap.id =
        N.subtype.rTensor C := by
    rw [LinearMap.rTensor_comp_map]
    rfl
  rw [← hz]
  exact LinearMap.congr_fun hmaps z

theorem sup {N P : Submodule k M}
    (hN : IsRightSubcomodule (C := C) N)
    (hP : IsRightSubcomodule (C := C) P) :
    IsRightSubcomodule (C := C) (N ⊔ P) := by
  intro m hm
  rcases Submodule.mem_sup.mp hm with ⟨n, hn, p, hp, rfl⟩
  rcases hN.mono le_sup_left n hn with ⟨zn, hzn⟩
  rcases hP.mono le_sup_right p hp with ⟨zp, hzp⟩
  exact ⟨zn + zp, by simp [hzn, hzp]⟩

theorem finset_sup {ι : Type*} (s : Finset ι) (N : ι → Submodule k M)
    (hN : ∀ i ∈ s, IsRightSubcomodule (C := C) (N i)) :
    IsRightSubcomodule (C := C) (s.sup N) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (bot (k := k) (C := C) (M := M))
  | @insert a s ha ih =>
      rw [Finset.sup_insert]
      exact sup (hN a (Finset.mem_insert_self a s))
        (ih fun i hi => hN i (Finset.mem_insert_of_mem hi))

end IsRightSubcomodule
