# Amenability

This Lean 4 project formalizes a finite-subcoalgebra rounding theorem for
cocommutative Hopf algebras.

## Main theorem

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

## Building

```bash
lake build
```
