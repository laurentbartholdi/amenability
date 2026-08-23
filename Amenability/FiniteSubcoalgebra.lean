/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.SubcoalgebraCoalgebra
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Cocommutativity and finite subcoalgebras

Cocommutativity descends along injective coalgebra homomorphisms. We apply
this to subcoalgebras and package finite-dimensional subcoalgebras for use
in the transfer argument.
-/

open Coalgebra LinearMap TensorProduct

namespace HopfAmenability

universe u v w

section InjectiveCocomm

variable {k : Type u} {C : Type v} {H : Type w}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup H] [Module k H] [Coalgebra k H]

/--
Cocommutativity descends along an injective coalgebra homomorphism.

The proof deliberately works pointwise after applying `f ⊗ f`, avoiding
rewrite matching through the coercion of `TensorProduct.comm`.
-/
theorem isCocommOfInjectiveCoalgHom
    [Coalgebra.IsCocomm k H]
    (f : C →ₗc[k] H)
    (hf : Function.Injective f) :
    Coalgebra.IsCocomm k C := by
  constructor
  ext x
  apply CoalgHom.tensorMapStruct_injective f f hf hf
  change
    TensorProduct.map f.toLinearMap f.toLinearMap
        (TensorProduct.comm k C C
          (Coalgebra.comul (R := k) (A := C) x)) =
      TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) (A := C) x)
  calc
    _ = TensorProduct.comm k H H
        (TensorProduct.map f.toLinearMap f.toLinearMap
          (Coalgebra.comul (R := k) (A := C) x)) := by
          exact TensorProduct.map_comm
            f.toLinearMap f.toLinearMap
            (Coalgebra.comul (R := k) (A := C) x)
    _ = TensorProduct.comm k H H
        (Coalgebra.comul (R := k) (A := H) (f x)) := by
          exact congrArg (TensorProduct.comm k H H)
            (CoalgHomClass.map_comp_comul_apply f x)
    _ = Coalgebra.comul (R := k) (A := H) (f x) := by
          exact Coalgebra.comm_comul k (f x)
    _ = TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := k) (A := C) x) := by
          exact (CoalgHomClass.map_comp_comul_apply f x).symm

end InjectiveCocomm

section SubcoalgebraCocomm

variable {k : Type u} {H : Type v}
variable [Field k] [AddCommGroup H] [Module k H]
variable [Coalgebra k H]

/--
The induced coalgebra on a subcoalgebra of a cocommutative coalgebra is
cocommutative.
-/
theorem subcoalgebraIsCocomm
    [Coalgebra.IsCocomm k H]
    (C : Submodule k H)
    (hC : IsSubcoalgebra (k := k) C) :
    letI := subcoalgebraCoalgebra C hC
    Coalgebra.IsCocomm k C := by
  let := subcoalgebraCoalgebra C hC
  exact isCocommOfInjectiveCoalgHom
    (subcoalgebraInclusion C hC)
    C.injective_subtype

end SubcoalgebraCocomm

section FiniteSubcoalgebra

variable (k : Type u) (H : Type v)
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H]

/--
A finite-dimensional subcoalgebra of `H`.

We retain the underlying object as a `Submodule`, since that is the form
used by the density filtration and by submodule multiplication.
-/
structure FiniteSubcoalgebra where
  carrier : Submodule k H
  isSubcoalgebra : IsSubcoalgebra (k := k) carrier
  finiteDimensional : FiniteDimensional k carrier

namespace FiniteSubcoalgebra

variable {k H}

instance (C : FiniteSubcoalgebra k H) :
    FiniteDimensional k C.carrier :=
  C.finiteDimensional

noncomputable instance (C : FiniteSubcoalgebra k H) :
    Coalgebra k C.carrier :=
  subcoalgebraCoalgebra C.carrier C.isSubcoalgebra

noncomputable instance
    [Coalgebra.IsCocomm k H]
    (C : FiniteSubcoalgebra k H) :
    Coalgebra.IsCocomm k C.carrier :=
  subcoalgebraIsCocomm C.carrier C.isSubcoalgebra

/--
The finite dual algebra of a finite subcoalgebra.
-/
abbrev Dual (C : FiniteSubcoalgebra k H) :=
  WithConv (Module.Dual k C.carrier)

/--
The finite dual is finite-dimensional as a vector space.
-/
instance dualFiniteDimensional (C : FiniteSubcoalgebra k H) :
    FiniteDimensional k C.Dual := by
  exact Module.Finite.equiv
    (WithConv.linearEquiv k (Module.Dual k C.carrier)).symm

/-
These are compile-time sanity checks rather than part of the API.
The convolution ring and algebra instances are noncomputable, hence the
`noncomputable` modifier.
-/
noncomputable example
    [Coalgebra.IsCocomm k H]
    (C : FiniteSubcoalgebra k H) :
    CommRing C.Dual :=
  inferInstance

noncomputable example
    [Coalgebra.IsCocomm k H]
    (C : FiniteSubcoalgebra k H) :
    Algebra k C.Dual :=
  inferInstance

end FiniteSubcoalgebra

end FiniteSubcoalgebra

end HopfAmenability
