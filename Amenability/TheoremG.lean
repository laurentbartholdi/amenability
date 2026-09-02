/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfAmenability

/-!
# Theorem G: amenability of the associated graded module coalgebra

This file exposes the final main theorem of the accompanying article.  An
augmentation-associated graded pair is represented by the project data class
`IsAugmentationAssociatedGraded`; the filtered-to-graded argument carried by
that interface sends amenability of the original Hopf-module coalgebra to
amenability of its associated graded object.
-/

namespace HopfAmenability

universe u v w x

variable {k : Type u} {H M : Type v}
variable {grH : Type w} {grM : Type x}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
variable [Ring grH] [HopfAlgebra k grH] [Coalgebra.IsCocomm k grH]
variable [AddCommGroup grM] [Module k grM] [Module grH grM]
variable [IsScalarTower k grH grM] [Coalgebra k grM]
variable [IsHopfModuleCoalgebra k grH grM]
variable [IsAugmentationAssociatedGraded (k := k) (H := H) M grH grM]

/-- **Theorem G.** Amenability passes from a Hopf-module coalgebra to its
augmentation-associated graded Hopf-module coalgebra. -/
theorem theoremG_associatedGraded
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := grH) (M := grM) :=
  hM.associatedGraded

end HopfAmenability
