/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CoalgebraDensity
import Amenability.FiniteSubcoalgebra

/-!
# Passing between internal and ambient subcoalgebras

This file records the linear equivalence between a subspace of a subtype
`G ≤ H` and its image in `H`, and transports dimensions and the
subcoalgebra predicate across that equivalence.
-/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H]

/-- A subspace of `G` is linearly equivalent to its image in `H`. -/
noncomputable def ambientImageEquiv
    (G : Submodule k H) (C : Submodule k G) :
    C ≃ₗ[k] ambientImage G C :=
  Submodule.equivMapOfInjective G.subtype G.injective_subtype C

@[simp]
theorem coe_ambientImageEquiv
    (G : Submodule k H) (C : Submodule k G) (x : C) :
    ((ambientImageEquiv G C x : ambientImage G C) : H) = (x : G) :=
  rfl

/-- Passing to the ambient image preserves dimension. -/
theorem finrank_ambientImage
    (G : Submodule k H) (C : Submodule k G) :
    finrank k (ambientImage G C) = finrank k C :=
  (ambientImageEquiv G C).finrank_eq.symm

/-- An ambient subspace contained in `G` is recovered from its comap to `G`. -/
theorem ambientImage_comap_eq_of_le
    (G D : Submodule k H) (hDG : D ≤ G) :
    ambientImage G (D.comap G.subtype) = D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hDG hx⟩, hx, rfl⟩

/--
For the induced coalgebra structure on a subcoalgebra `G`, a subspace of
`G` is a subcoalgebra exactly when its image in `H` is one.
-/
theorem isSubcoalgebra_ambientImage_iff
    [Coalgebra k H]
    (G : Submodule k H) (hG : IsSubcoalgebra (k := k) G)
    (C : Submodule k G) :
    letI := subcoalgebraCoalgebra G hG
    IsSubcoalgebra (k := k) (ambientImage G C) ↔
    IsSubcoalgebra (k := k) C := by
  let := subcoalgebraCoalgebra G hG
  let e := ambientImageEquiv G C
  have hnatural :
      ∀ z : C ⊗[k] C,
        TensorProduct.mapIncl (ambientImage G C) (ambientImage G C)
            (TensorProduct.map e.toLinearMap e.toLinearMap z) =
          TensorProduct.mapIncl G G (TensorProduct.mapIncl C C z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y => rfl
  constructor
  · intro hC x hx
    have hxAmbient : (x : H) ∈ ambientImage G C :=
      ⟨x, hx, rfl⟩
    rcases hC hxAmbient with ⟨z, hz⟩
    obtain ⟨z', hz'⟩ :=
      (TensorProduct.map_bijective e.bijective e.bijective).2 z
    refine ⟨z', ?_⟩
    apply tensorProduct_mapIncl_injective G G
    calc
      TensorProduct.mapIncl G G (TensorProduct.mapIncl C C z') =
          TensorProduct.mapIncl (ambientImage G C) (ambientImage G C)
            (TensorProduct.map e.toLinearMap e.toLinearMap z') :=
        (hnatural z').symm
      _ = TensorProduct.mapIncl (ambientImage G C) (ambientImage G C) z := by
        rw [hz']
      _ = Coalgebra.comul (R := k) (A := H) (x : H) := hz
      _ = TensorProduct.mapIncl G G
          (Coalgebra.comul (R := k) (A := G) x) :=
        (mapIncl_subcoalgebraComul G hG x).symm
  · intro hC x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hC hy with ⟨z, hz⟩
    refine ⟨TensorProduct.map e.toLinearMap e.toLinearMap z, ?_⟩
    calc
      TensorProduct.mapIncl (ambientImage G C) (ambientImage G C)
          (TensorProduct.map e.toLinearMap e.toLinearMap z) =
        TensorProduct.mapIncl G G (TensorProduct.mapIncl C C z) :=
          hnatural z
      _ = TensorProduct.mapIncl G G
          (Coalgebra.comul (R := k) (A := G) y) := by rw [hz]
      _ = Coalgebra.comul (R := k) (A := H) (y : H) :=
        mapIncl_subcoalgebraComul G hG y

/-- Package an internal subspace whose ambient image is a subcoalgebra. -/
noncomputable def finiteSubcoalgebraOfAmbientImage
    [Coalgebra k H]
    (G : Submodule k H) [FiniteDimensional k G]
    (C : Submodule k G)
    (hC : IsSubcoalgebra (k := k) (ambientImage G C)) :
    FiniteSubcoalgebra k H where
  carrier := ambientImage G C
  isSubcoalgebra := hC
  finiteDimensional := by
    let : FiniteDimensional k C :=
      FiniteDimensional.of_injective C.subtype C.injective_subtype
    exact Module.Finite.equiv (ambientImageEquiv G C)

end

end HopfAmenability
