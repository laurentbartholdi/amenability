/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfActionSubspace
import Amenability.FiniteSubcoalgebra

/-! # Amenability predicates for Hopf-module coalgebras -/

open Coalgebra Module

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- Elek's ordinary finite-dimensional Følner-subspace condition. -/
def HasActionFolnerSubspaces : Prop :=
  ∀ (F : Submodule k H), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ E : Submodule k M, E ≠ ⊥ ∧ FiniteDimensional k E ∧
        (sfinrank k (actionExpansion F E) : ℚ) ≤ (1 + ε) * sfinrank k E

variable [Coalgebra k M]

/-- The Følner-subcoalgebra definition of amenability. -/
def IsAmenableHopfModuleCoalgebra : Prop :=
  ∀ (F : Submodule k H), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ C : FiniteSubcoalgebra k M, C.carrier ≠ ⊥ ∧
        (sfinrank k (actionExpansion F C.carrier) : ℚ) ≤
          (1 + ε) * finrank k C.carrier

end

end HopfAmenability
