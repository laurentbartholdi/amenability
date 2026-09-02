/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfAmenability

/-!
# Theorem J: amenability of the associated graded module coalgebra

This file exposes the final main theorem of the accompanying article.  The
structure `AugmentationAssociatedGradedData` records the separated quotient,
leading-symbol spaces, and their standard finite-dimensional properties.  It
does not contain an amenability hypothesis or conclusion.
-/

namespace HopfAmenability

universe u v w x y

variable {k : Type u} {H M : Type v}
variable {Msep : Type y}
variable {grH : Type w} {grM : Type x}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
variable [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
variable [AddCommGroup Msep] [Module k Msep] [Module H Msep]
variable [IsScalarTower k H Msep] [Coalgebra k Msep]
variable [IsHopfModuleCoalgebra k H Msep]
variable [Ring grH] [HopfAlgebra k grH] [Coalgebra.IsCocomm k grH]
variable [AddCommGroup grM] [Module k grM] [Module grH grM]
variable [IsScalarTower k grH grM] [Coalgebra k grM]
variable [IsHopfModuleCoalgebra k grH grM]

/-- **Theorem J.** Amenability passes from a Hopf-module coalgebra to its
augmentation-associated graded Hopf-module coalgebra. -/
theorem theoremJ_associatedGraded
    (gr : AugmentationAssociatedGradedData (k := k) (H := H)
      M Msep grH grM)
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := grH) (M := grM) :=
  hM.associatedGraded gr

/-- Public endpoint for Theorem J.  The realization data identifies `grH`
and `grM` with the direct sums of the concrete augmentation quotients and
records the induced filtered operations; it contains no amenability field. -/
theorem isAmenable_associatedGraded
    (gr : AugmentationAssociatedGradedData (k := k) (H := H)
      M Msep grH grM)
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra (k := k) (H := grH) (M := grM) :=
  theoremJ_associatedGraded gr hM

end HopfAmenability
