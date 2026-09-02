# Phase 2 status: Theorems C and D

Public declarations validated in this phase:

- `HopfAmenability.isAmenableHopfAlgebra_iff_all_nonzero_moduleCoalgebras`
  is Theorem C.
- `HopfAmenability.algebraicallyAmenable_of_projective` is the generic
  projective-module Folner descent lemma.
- `HopfAmenability.isAmenableHopfAlgebra_of_hopfSubalgebra` is Theorem D.

Theorem C uses the external first-factor action on `H tensor M`. The action
is bundled as `firstFactorActionCoalgHom`; the original module action appears
only in the equivariant quotient map `H tensor M -> M`.

The former amenability-descent axiom has been deleted. Its replacement,
`HopfAmenability.takeuchiWigner_projective_left`, concludes only that `H` is
projective for the restricted left `K`-module structure. The Folner descent
from this projective module is proved in Lean.

Validation commands:

```text
lake env lean -DwarningAsError=true Amenability/TheoremC.lean
lake env lean -DwarningAsError=true Amenability/TheoremD.lean
lake env lean -DwarningAsError=true Amenability/AxiomAudit.lean
```

The C audit has no project-local assumptions. The D audit contains precisely
`HopfAmenability.takeuchiWigner_projective_left`, in addition to Lean's
standard foundational axioms.
