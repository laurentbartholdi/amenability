# Amenability

This Lean 4 project formalizes finite-subcoalgebra rounding theorems for
cocommutative Hopf algebras and for coalgebras carrying compatible Lie-module
structures.

## Hopf-algebra rounding

Let `H` be a cocommutative Hopf algebra over a field `k`. For every finite
subcoalgebra `F` of `H` and every nonzero finite-dimensional subspace `E` of
`H`, there is a nonzero finite subcoalgebra `C` whose product-growth ratio is
no larger than that of `E`:

```lean
theorem HopfAmenability.exists_finiteSubcoalgebra_ratio_le
    (F : FiniteSubcoalgebra k H)
    (E : Submodule k H)
    [FiniteDimensional k E]
    (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k H,
      C.carrier ≠ ⊥ ∧
        (finrank k (F.carrier * C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (finrank k (F.carrier * E) : ℚ) /
            (finrank k E : ℚ)
```

The theorem is proved under the assumptions

```lean
[Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
```

The development includes the fundamental theorem of coalgebras via comodules
(in the `Coalgebra` namespace),
finite-dimensional density rounding, and a primal transfer argument based on
codimension-one coalgebra steps. The final result is in
`Amenability/CoalgebraRounding.lean`.

The earlier dual-transfer proof branch is retained for reference under
`Amenability/Dead` but is not part of the dependency chain of the main theorem.

## Lie-module coalgebra rounding

Let `L` be a Lie algebra over `k` and let `M` be an `L`-module coalgebra: every
element of `L` acts on `M` as a coderivation. For a finite-dimensional
subspace `F ≤ L`, the subspace `lieExpansion F E` is

```text
E + span { [x,e] | x ∈ F, e ∈ E }.
```

No cocommutativity assumption on `M` is needed. Every nonzero
finite-dimensional `E ≤ M` can be rounded to a nonzero finite subcoalgebra
without increasing its Lie-expansion ratio:

```lean
theorem HopfAmenability.exists_finiteSubcoalgebra_lie_ratio_le
    (F : Submodule k L)
    [FiniteDimensional k F]
    (E : Submodule k M)
    [FiniteDimensional k E]
    (hE : E ≠ ⊥) :
    ∃ C : FiniteSubcoalgebra k M,
      C.carrier ≠ ⊥ ∧
        (sfinrank k (lieExpansion F C.carrier) : ℚ) /
            (finrank k C.carrier : ℚ) ≤
          (sfinrank k (lieExpansion F E) : ℚ) /
            (finrank k E : ℚ)
```

The assumptions are

```lean
[Field k]
[LieRing L] [LieAlgebra k L]
[AddCommGroup M] [Module k M]
[LieRingModule L M] [LieModule k L M]
[Coalgebra k M] [Coalgebra.IsLieModuleCoalgebra k L M]
```

For applications that want selected data rather than an existential
proposition, the project also provides
`HopfAmenability.lieRounding : LieRoundingResult F E`, together with
`lieRounding_ne_bot` and `lieRounding_ratio_le`.

Finally,
`HopfAmenability.IsAmenableLieModule.exists_finiteSubcoalgebra_folner`
states explicitly that the Følner subspaces witnessing amenability of a
Lie-module coalgebra may be chosen to be finite subcoalgebras.

The Lie result is proved directly from the coderivation action. It does not
use a universal enveloping algebra, the old dual-transfer machinery, or the
Hopf-algebra multiplication theorem.

## Hopf-module coalgebra infrastructure

The current development also includes the foundational definitions
`IsHopfModuleCoalgebra`, `hopfModuleActionCoalgHom`, `actionSubspace`, and
`FiniteSubcoalgebra.act`. These prepare the generalization of the regular
Hopf-algebra theorem to arbitrary Hopf-module coalgebras; that generalized
rounding theorem is not yet claimed here.

## Building

```bash
lake build
```
