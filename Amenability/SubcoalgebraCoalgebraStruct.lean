/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubcoalgebraBasic
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The induced coalgebra structure on a subcoalgebra: structure maps

For `C : Submodule k H` satisfying `IsSubcoalgebra C`, this file constructs
the restricted comultiplication
`C → C ⊗ C`
as the unique lift of the ambient comultiplication through
`C ⊗ C ↪ H ⊗ H`.

The coalgebra axioms are proved in `SubcoalgebraCoalgebra.lean`.
-/

open scoped TensorProduct

namespace UnifiedRounding

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/--
Over a field, the natural map `C ⊗ D → H ⊗ H` is injective.
-/
theorem tensorProduct_mapIncl_injective
    (C D : Submodule k H) :
    Function.Injective (TensorProduct.mapIncl C D) := by
  exact Module.Flat.tensorProduct_mapIncl_injective_of_right C D

/--
The comultiplication of a subcoalgebra, obtained by restricting the ambient
comultiplication to `C ⊗ C`.
-/
noncomputable def subcoalgebraComul [Coalgebra k H]
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    C →ₗ[k] C ⊗[k] C :=
  LinearMap.codRestrictOfInjective
    ((Coalgebra.comul (R := k) (A := H)).comp C.subtype)
    (TensorProduct.mapIncl C C)
    (tensorProduct_mapIncl_injective C C)
    (fun x => hC x.2)

/--
The restricted comultiplication becomes the ambient comultiplication after
the inclusion `C ⊗ C ↪ H ⊗ H`.
-/
@[simp]
theorem mapIncl_subcoalgebraComul [Coalgebra k H]
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C)
    (x : C) :
    TensorProduct.mapIncl C C (subcoalgebraComul C hC x) =
      Coalgebra.comul (R := k) (A := H) x.1 := by
  exact LinearMap.codRestrictOfInjective_comp_apply
    ((Coalgebra.comul (R := k) (A := H)).comp C.subtype)
    (TensorProduct.mapIncl C C)
    (tensorProduct_mapIncl_injective C C)
    (fun y => hC y.2) x

/--
Map-level form of `mapIncl_subcoalgebraComul`.
-/
theorem mapIncl_comp_subcoalgebraComul [Coalgebra k H]
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    TensorProduct.mapIncl C C ∘ₗ subcoalgebraComul C hC =
      (Coalgebra.comul (R := k) (A := H)).comp C.subtype := by
  ext x
  exact mapIncl_subcoalgebraComul C hC x

/--
The counit on a subcoalgebra is simply the restriction of the ambient
counit.
-/
def subcoalgebraCounit [Coalgebra k H]
    (C : Submodule k H) :
    C →ₗ[k] k :=
  (Coalgebra.counit (R := k) (A := H)).comp C.subtype

@[simp]
theorem subcoalgebraCounit_apply [Coalgebra k H]
    (C : Submodule k H) (x : C) :
    subcoalgebraCounit C x =
      Coalgebra.counit (R := k) (A := H) x.1 :=
  rfl

/--
The induced `CoalgebraStruct` on the subtype of a subcoalgebra.
-/
@[instance_reducible]
noncomputable def subcoalgebraCoalgebraStruct [Coalgebra k H]
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    CoalgebraStruct k C where
  comul := subcoalgebraComul C hC
  counit := subcoalgebraCounit C

/--
With the induced `CoalgebraStruct`, the subtype inclusion preserves
comultiplication.
-/
theorem subtype_map_comp_comul [Coalgebra k H]
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    letI := subcoalgebraCoalgebraStruct C hC
    TensorProduct.map C.subtype C.subtype ∘ₗ
        Coalgebra.comul (R := k) (A := C) =
      (Coalgebra.comul (R := k) (A := H)).comp C.subtype := by
  let := subcoalgebraCoalgebraStruct C hC
  exact mapIncl_comp_subcoalgebraComul C hC

/--
With the induced `CoalgebraStruct`, the subtype inclusion preserves the
counit.
-/
theorem counit_comp_subtype [Coalgebra k H]
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    letI := subcoalgebraCoalgebraStruct C hC
    (Coalgebra.counit (R := k) (A := H)).comp C.subtype =
      Coalgebra.counit (R := k) (A := C) := by
  let := subcoalgebraCoalgebraStruct C hC
  rfl

end UnifiedRounding
