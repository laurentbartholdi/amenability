/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.CoalgebraInjective

/-!
# The induced coalgebra on a subcoalgebra

This file completes the construction started in
`SubcoalgebraCoalgebraStruct.lean`: every `IsSubcoalgebra C` inherits a
genuine coalgebra structure from the ambient coalgebra.

The subtype inclusion is then a coalgebra homomorphism.
-/

open Coalgebra LinearMap TensorProduct

namespace HopfAmenability

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

/--
The subtype inclusion of a subcoalgebra, viewed as a coalgebra homomorphism
for the restricted `CoalgebraStruct`.
-/
noncomputable def subcoalgebraSubtypeCoalgHom
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    letI := subcoalgebraCoalgebraStruct C hC
    C →ₗc[k] H := by
  letI := subcoalgebraCoalgebraStruct C hC
  exact
    { C.subtype with
      counit_comp := counit_comp_subtype C hC
      map_comp_comul := subtype_map_comp_comul C hC }

/--
The genuine coalgebra structure induced on the subtype of a subcoalgebra.
-/
@[instance_reducible]
noncomputable def subcoalgebraCoalgebra
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    Coalgebra k C := by
  letI := subcoalgebraCoalgebraStruct C hC
  exact coalgebraOfInjectiveCoalgHom
    (subcoalgebraSubtypeCoalgHom C hC)
    C.injective_subtype

/--
With the induced coalgebra structure, the subtype inclusion is a coalgebra
homomorphism.
-/
noncomputable def subcoalgebraInclusion
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    letI := subcoalgebraCoalgebra C hC
    C →ₗc[k] H := by
  letI := subcoalgebraCoalgebra C hC
  exact
    { C.subtype with
      counit_comp := by
        rfl
      map_comp_comul := by
        exact mapIncl_comp_subcoalgebraComul C hC }

/--
The inclusion of a subcoalgebra is injective.
-/
theorem subcoalgebraInclusion_injective
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    letI := subcoalgebraCoalgebra C hC
    Function.Injective (subcoalgebraInclusion C hC) := by
  let := subcoalgebraCoalgebra C hC
  exact C.injective_subtype

end HopfAmenability
