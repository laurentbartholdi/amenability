/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubmoduleFinrank
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Subcoalgebras as a predicate on submodules

Mathlib currently has no bundled `Subcoalgebra`.  For the rounding development
we only need the underlying subspace and the condition that comultiplication
lands in its tensor square, so we use the predicate `IsSubcoalgebra`.

The nontrivial theorem that intersections are subcoalgebras is deliberately
left for a separate file.  The zero subspace and sums are handled here.
-/

open scoped TensorProduct

namespace UnifiedRounding

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

/--
A subspace `C` of a coalgebra is a subcoalgebra if the comultiplication of
every element of `C` lies in the image of `C ⊗ C` inside `H ⊗ H`.

There is no separate counit condition: the counit already has codomain `k`.
-/
def IsSubcoalgebra (C : Submodule k H) : Prop :=
  ∀ ⦃x : H⦄, x ∈ C →
    Coalgebra.comul (R := k) x ∈
      LinearMap.range (TensorProduct.mapIncl C C)

/--
The zero subspace is a subcoalgebra.
-/
theorem isSubcoalgebra_bot :
    IsSubcoalgebra (k := k) (H := H) (⊥ : Submodule k H) := by
  intro x hx
  have hx0 : x = 0 := by
    simpa using hx
  subst x
  simp

/--
The sum of two subcoalgebras is a subcoalgebra.
-/
theorem IsSubcoalgebra.sup
    {C D : Submodule k H}
    (hC : IsSubcoalgebra (k := k) C)
    (hD : IsSubcoalgebra (k := k) D) :
    IsSubcoalgebra (k := k) (C ⊔ D : Submodule k H) := by
  intro x hx
  let T : Submodule k H :=
    Submodule.comap (Coalgebra.comul (R := k) (A := H))
      (LinearMap.range
        (TensorProduct.mapIncl
          (C ⊔ D : Submodule k H)
          (C ⊔ D : Submodule k H)))
  have hCT : C ≤ T := by
    intro y hy
    change Coalgebra.comul (R := k) y ∈
      LinearMap.range
        (TensorProduct.mapIncl
          (C ⊔ D : Submodule k H)
          (C ⊔ D : Submodule k H))
    exact TensorProduct.range_mapIncl_mono le_sup_left le_sup_left (hC hy)
  have hDT : D ≤ T := by
    intro y hy
    change Coalgebra.comul (R := k) y ∈
      LinearMap.range
        (TensorProduct.mapIncl
          (C ⊔ D : Submodule k H)
          (C ⊔ D : Submodule k H))
    exact TensorProduct.range_mapIncl_mono le_sup_right le_sup_right (hD hy)
  have hxT : x ∈ T := (sup_le hCT hDT) hx
  exact hxT

/--
Finite sums of subcoalgebras are subcoalgebras.
-/
theorem isSubcoalgebra_finset_sup
    {ι : Type*} (s : Finset ι) (C : ι → Submodule k H)
    (hC : ∀ i ∈ s, IsSubcoalgebra (k := k) (C i)) :
    IsSubcoalgebra (k := k) (s.sup C : Submodule k H) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isSubcoalgebra_bot (k := k) (H := H))
  | @insert i s hi ih =>
      rw [Finset.sup_insert]
      exact (hC i (Finset.mem_insert_self i s)).sup
        (ih fun j hj => hC j (Finset.mem_insert_of_mem hj))

/--
A linear image along an injective map preserves intersections.

This elementary helper will be useful when translating an intersection of
subspaces of an ambient finite subcoalgebra back to the original coalgebra.
-/
theorem Submodule.map_inf_of_injective
    {V W : Type*}
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (hf : Function.Injective f)
    (C D : Submodule k V) :
    (C ⊓ D : Submodule k V).map f =
      C.map f ⊓ D.map f := by
  apply le_antisymm
  · exact le_inf
      (Submodule.map_mono inf_le_left)
      (Submodule.map_mono inf_le_right)
  · rintro y ⟨⟨x, hxC, rfl⟩, ⟨x', hxD, hxx'⟩⟩
    have heq : x' = x := hf hxx'
    subst x'
    exact ⟨x, ⟨hxC, hxD⟩, rfl⟩

end UnifiedRounding
