/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfAlgebraAmenability
import Amenability.HopfAlgebraHom
import Amenability.HopfExactSequence
import Amenability.HopfSubalgebraProjectivity
import Amenability.TheoremB

/-!
# Hopf-algebra amenability compatibility aggregator

This module re-exports the descriptive Hopf amenability, morphism, exact
sequence, and projectivity modules.  Augmentation and associated-graded
constructions deliberately live outside this compatibility layer.
-/

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- The quotient theorem specialized to the regular Hopf module. -/
theorem IsAmenableHopfModuleCoalgebra.quotient
    {Q : Type*} [AddCommGroup Q] [Module k Q] [Module H Q]
    [IsScalarTower k H Q] [Coalgebra k Q] [IsHopfModuleCoalgebra k H Q]
    (q : H →ₗc[k] Q) (hq : IsHopfModuleMap (H := H) q.toLinearMap)
    (hqsurj : Function.Surjective q)
    (hH : IsAmenableHopfAlgebra (k := k) (H := H)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := Q) :=
  hH.of_surjective_coalgHom q hq hqsurj

end

end HopfAmenability
