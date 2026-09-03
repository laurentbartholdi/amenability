/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfModuleCoalgebra

/-! # Equivariant maps of Hopf modules -/

namespace HopfAmenability

universe u v w x

variable {k : Type u} {H : Type v} {M : Type w} {Q : Type x}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M]
variable [AddCommGroup Q] [Module k Q] [Module H Q]

/-- A linear map between `H`-modules intertwines their actions. -/
def IsHopfModuleMap (f : M →ₗ[k] Q) : Prop :=
  ∀ (h : H) (m : M), f (h • m) = h • f m

end HopfAmenability
