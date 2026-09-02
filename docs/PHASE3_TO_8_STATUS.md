# Phases 3--8 status

## Phase 3: cleft extensions and groups

`CleftExactSequence` contains only intrinsic exact-sequence and coalgebra
section data. `CleftNormalBasis.lean` derives the normal-basis equivalence;
`CleftAmenability.lean` proves both amenability directions. The group files
construct the cleft sequence of a normal subgroup and prove the explicit
augmentation-ideal quotient description.

## Phase 4: Lie permanence

`TheoremG.lean` exposes the growth, subalgebra, quotient, extension, and
directed-union clauses. The subalgebra and extension paths use Theorems D and
E through universal-enveloping Hopf maps and PBW coalgebra sections.

## Phase 5: class separation

`TheoremH.lean` proves the characteristic-zero Witt branch and reduces the
positive-characteristic branch to the single permitted PSZ proof.

## Phase 6: exponential example

The locally-matrix profile, shift-profile algebra, and matrix-Lie encoding
are implemented in three descriptive files. `TheoremI.lean` constructs the
witness, including its ideal, quotient equivalence and splitting, growth,
local finite-dimensionality, finite generation, and amenability.

## Phase 7: associated graded

`HopfAmenability.lean` defines the concrete augmentation filtrations and
graded direct sums. `TensorFiltrationIntersection.lean` proves the full
tensor-intersection identity and the infinite-intersection coideal theorem.
The associated-graded realization data records induced operations and
finite-filtration facts but contains no amenability assumption or conclusion;
`isAmenable_associatedGraded` proves the conclusion.

## Phase 8: integration and assumptions

`Amenability.lean` checks A--J and the group applications.
`AxiomAudit.lean` audits every main endpoint and the directional extension
lemmas. Builds and scans are recorded in the final task report.
