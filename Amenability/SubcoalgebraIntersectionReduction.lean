/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.CoalgebraDensity

/-!
# Reducing intersections of subcoalgebras to a tensor-product identity

The only missing lattice fact for the density filtration is that intersections
of subcoalgebras are subcoalgebras.

Over a field this follows from the linear-algebra identity

`((C ⊓ D) ⊗ (C ⊓ D)) = (C ⊗ C) ⊓ (D ⊗ D)`

inside `H ⊗ H`.

This file isolates that identity as `TensorSquareIntersectionProperty` and
proves that it implies all the intersection-closure hypotheses used by
`CoalgebraDensity.lean`.
-/

namespace HopfAmenability

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

/--
The tensor-square intersection identity needed for intersections of
subcoalgebras.
-/
def TensorSquareIntersectionProperty : Prop :=
  ∀ C D : Submodule k H,
    LinearMap.range
        (TensorProduct.mapIncl
          (C ⊓ D : Submodule k H)
          (C ⊓ D : Submodule k H)) =
      LinearMap.range (TensorProduct.mapIncl C C) ⊓
        LinearMap.range (TensorProduct.mapIncl D D)

/--
The tensor-square intersection identity implies that the intersection of two
subcoalgebras is a subcoalgebra.
-/
theorem IsSubcoalgebra.inf_of_tensorSquareIntersection
    (hTensor : TensorSquareIntersectionProperty (k := k) (H := H))
    {C D : Submodule k H}
    (hC : IsSubcoalgebra (k := k) C)
    (hD : IsSubcoalgebra (k := k) D) :
    IsSubcoalgebra (k := k) (C ⊓ D : Submodule k H) := by
  intro x hx
  have hxC : x ∈ C := hx.1
  have hxD : x ∈ D := hx.2
  have hcomulC := hC hxC
  have hcomulD := hD hxD
  rw [hTensor C D]
  exact ⟨hcomulC, hcomulD⟩

/--
The tensor-square intersection identity discharges the `SubcoalgebraInfClosed`
hypothesis for every ambient subspace `G`.
-/
theorem subcoalgebraInfClosed_of_tensorSquareIntersection
    (hTensor : TensorSquareIntersectionProperty (k := k) (H := H))
    (G : Submodule k H) :
    SubcoalgebraInfClosed (k := k) G := by
  intro C D hC hD
  rw [ambientImage_inf]
  exact hC.inf_of_tensorSquareIntersection hTensor hD

end HopfAmenability
