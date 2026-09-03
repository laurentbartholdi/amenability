/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremA

/-! # Amenability of cocommutative Hopf algebras -/

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

def IsAmenableHopfAlgebra : Prop :=
  IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := H)

def IsAlgebraicallyAmenableHopfAlgebra : Prop :=
  HasActionFolnerSubspaces (k := k) (H := H) (M := H)

theorem isAmenableHopfAlgebra_iff_algebraicallyAmenable :
    IsAmenableHopfAlgebra (k := k) (H := H) ↔
      IsAlgebraicallyAmenableHopfAlgebra (k := k) (H := H) :=
  isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces

end

end HopfAmenability
