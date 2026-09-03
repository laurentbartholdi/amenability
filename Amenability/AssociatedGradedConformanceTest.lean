/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremJ

/-! # Exact conformance test for Theorem J -/

namespace HopfAmenability

universe u v

variable {k : Type u} {H M : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]

example (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra
      (k := k) (H := AugmentationGradedHopf (k := k) (H := H))
      (M := AugmentationGradedModule (k := k) (H := H) (M := M)) :=
  isAmenable_associatedGraded hM

#check augmentationGradedHopfHopfAlgebra
#check augmentationGradedHopfIsCocomm
#check augmentationGradedIsHopfModuleCoalgebra
#check theoremJ_associatedGraded

end HopfAmenability
