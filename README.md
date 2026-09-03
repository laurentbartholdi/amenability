# Amenability

[![Lean CI](https://github.com/laurentbartholdi/amenability/actions/workflows/lean_action_ci.yml/badge.svg?branch=main&event=push)](https://github.com/laurentbartholdi/amenability/actions/workflows/lean_action_ci.yml)

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

## Main theorems of the article

The files `Amenability/TheoremA.lean` through
`Amenability/TheoremJ.lean` expose the article's principal results:

- `isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces` is the
  coalgebraic/algebraic amenability equivalence (Theorem A).
- `IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom` proves permanence
  under equivariant coalgebra quotients (Theorem B).
- `isAmenableHopfAlgebra_iff_all_nonzero_moduleCoalgebras` is the
  all-nonzero-module-coalgebras characterization (Theorem C).
- `isAmenableHopfAlgebra_of_hopfSubalgebra` proves Hopf-subalgebra
  permanence from the Takeuchi--Wigner projectivity input (Theorem D).
- `isAmenableHopfAlgebra_cleftExtension_of_components` and
  `isAmenableHopfAlgebra_cleftExtension_iff` prove cleft-extension permanence;
  the normal-basis coalgebra equivalence is derived in
  `CleftNormalBasis.lean` rather than assumed (Theorem E).
- `hasActionFolnerSubspaces_of_quotient_permutationModule` and
  `hasActionFolnerSubspaces_of_isAmenableGroup` give the permutation-module
  and amenable-group results (Theorem F).
- `isAmenableLieAlgebra_of_locallySubexponentialGrowth`,
  `isAmenableLieAlgebra_of_injective`, `isAmenableLieAlgebra_quotient`,
  `isAmenableLieAlgebra_extension_iff`, and
  `isAmenableLieAlgebra_directedUnion` are the Lie-algebra permanence
  statements (Theorem G).  The subexponential clause is proved internally:
  `AscendingFiltrationBasis.lean` constructs a basis adapted to Lie-growth
  balls, while `WeightedPBW.lean` and `WeightedPBWGrowth.lean` formalize
  weighted PBW straightening and Smith's generating-function estimate.
- `elementaryLieAlgebras_ne_subexponentiallyAmenableLieAlgebras_general`
  separates the elementary and subexponentially amenable classes (Theorem
  H).  The inclusions `EL ⊆ SL ⊆ AL` are theorems
  `IsElementaryLieObject.isSubexponentiallyAmenable` and
  `IsSubexponentiallyAmenableLieObject.isAmenable`.  Its
  positive-characteristic self-similar example is the single
  explicitly permitted incomplete proof,
  `exists_psz_subexponential_not_elementary`.
- `exists_amenable_exponentialGrowth_locallyFiniteByOne` packages
  the explicit profile-matrix exponential-growth example (Theorem I).
- `isAmenable_associatedGraded` proves filtered-to-graded amenability for
  the concrete augmentation-associated graded, with no realization-data
  assumption (Theorem J).  `TensorFiltrationIntersection.lean` contains the
  nonseparated tensor-intersection and coideal argument;
  `FilteredInitial.lean` and `AugmentationLeadingSymbols.lean` construct
  homogeneous lifts and dimension-preserving initial subspaces.

The supporting files `GroupPermanence.lean` and
`GroupCleftExactSequence.lean` derive subgroup and normal-extension
permanence from Theorems D and E and identify the quotient group algebra with
the quotient by the explicit augmentation ideal.

## Imports

The root module `Amenability.lean` imports and type-checks all ten public
theorem files. Individual specializations may also be imported separately:

```lean
import Amenability.LieAmenability
import Amenability.GroupAmenability
```

## Building

```bash
lake build
```
