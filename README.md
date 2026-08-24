# Amenability

This Lean 4 project proves coalgebraic rounding theorems for cocommutative
Hopf algebras, Hopf-module coalgebras, Lie-module coalgebras, and linearized
group actions.

## Generic Hopf-module-coalgebra rounding

Let a cocommutative Hopf algebra `H` over a field `k` act compatibly on a
coalgebra `M`. For a finite subcoalgebra `F ≤ H` and a nonzero
finite-dimensional subspace `E ≤ M`, the main generic theorem produces a
nonzero finite subcoalgebra with no larger action-expansion ratio:

```lean
theorem HopfAmenability.exists_finiteSubcoalgebra_action_ratio_le
    (F : FiniteSubcoalgebra k H)
    (E : Submodule k M)
    [FiniteDimensional k E]
    (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (actionSubspace F.carrier C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (actionSubspace F.carrier E) : ℚ) /
            (finrank k E : ℚ)
```

The assumptions are

```lean
[Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
[AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
[Coalgebra k M] [HopfAmenability.IsHopfModuleCoalgebra k H M]
```

No cocommutativity assumption is made on the target coalgebra `M`.

The regular action gives the product-growth corollary
`HopfAmenability.exists_finiteSubcoalgebra_ratio_le` in
`Amenability/CoalgebraRounding.lean`.

## Lie-module coalgebras

`Amenability/LieAmenability.lean` is an opt-in specialization. It constructs
the standard cocommutative Hopf structure on the universal enveloping algebra,
extends the Lie action, and derives

```lean
theorem HopfAmenability.exists_finiteSubcoalgebra_lie_ratio_le
    (F : Submodule k L) [FiniteDimensional k F]
    (E : Submodule k M) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (lieExpansion F E) : ℚ) /
            (finrank k E : ℚ)
```

Here `Coalgebra.IsLieModuleCoalgebra` assumes only the coderivation identity
for comultiplication; counit compatibility is derived as
`Coalgebra.counit_lie_apply`. The standard Hopf structure on universal
enveloping algebras is isolated in
`Amenability/UniversalEnvelopingCoalgebra.lean` under `namespace Coalgebra`,
with future Mathlib integration in mind.

The public amenability corollary is
`HopfAmenability.IsAmenableLieModule.exists_finiteSubcoalgebra_folner`.

## Group actions

`Amenability/GroupAmenability.lean` is another opt-in specialization. For a
group `G` acting on a type `X`, it linearizes the action on `k[X]`, proves
that finite subcoalgebras of the diagonal coalgebra are spans of finite subsets
of `X`, and derives

```lean
theorem HopfAmenability.exists_finset_group_ratio_le
    [DecidableEq G] [DecidableEq X]
    (S : Finset G) (E : Submodule k (MonoidAlgebra k X))
    [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ A : Finset X,
      A.Nonempty ∧
        ((groupSetExpansion S A).card : ℚ) / A.card ≤
          (sfinrank k
              (actionSubspace
                (groupActingSubcoalgebra (k := k) S).carrier E) : ℚ) /
            finrank k E
```

The theorems
`HasGroupFolnerSubspaces.isAmenableGroupAction` and
`IsAmenableGroupAction.hasFolnerSubspaces` identify the linearized and
finite-set Følner conditions.

## Reusable coalgebra infrastructure

The project includes the fundamental theorem of coalgebras via comodules:

```lean
theorem Coalgebra.exists_finiteSubcoalgebra_containing_submodule
    (E : Submodule k C) [FiniteDimensional k E] :
    ∃ D : FiniteSubcoalgebra k C, E ≤ D.carrier
```

Generic tensor contraction lives in `namespace TensorProduct`; generic
coalgebra and comodule theorems live in `namespace Coalgebra`; rounding and
amenability declarations live in `namespace HopfAmenability`.

The earlier dual-transfer proof is retained for reference under
`Amenability/Dead` and is not in the main dependency chain.

## Imports

The root module `Amenability.lean` imports the generic theorem, both
specializations, and checks the two public Følner equivalences. They may also
be imported separately:

```lean
import Amenability.LieAmenability
import Amenability.GroupAmenability
```

## Building

```bash
lake build
```
