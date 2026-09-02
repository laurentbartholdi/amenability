# Phase 1 status: Theorems A, B, and F

Public declarations validated in this phase:

- `HopfAmenability.isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces`
  is the equivalence in Theorem A.
- `HopfAmenability.exists_finiteSubcoalgebra_expansion_ratio_le` is the sharp
  `C + F C` versus `E + F E` ratio statement from Theorem A.
- `HopfAmenability.IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom` is
  Theorem B.
- `HopfAmenability.theoremF_quotientPermutationModule` and
  `HopfAmenability.theoremF_moduleOverAmenableGroup` are Theorem F.

Validation commands:

```text
lake env lean -DwarningAsError=true Amenability/TheoremA.lean
lake env lean -DwarningAsError=true Amenability/TheoremB.lean
lake env lean -DwarningAsError=true Amenability/TheoremC.lean
lake env lean -DwarningAsError=true Amenability/TheoremF.lean
lake env lean -DwarningAsError=true Amenability/AxiomAudit.lean
```

The audit reports only `propext`, `Classical.choice`, and `Quot.sound` for
these endpoints. There are no project-local assumptions in A, B, or F.

The sharp A endpoint strengthens neither side of the manuscript statement:
it applies the existing rounding theorem to the exact finite subcoalgebra
`F + k 1`, whose action space is definitionally proved equal to `E + F E`.

The only remaining project-local assumptions at the end of this phase are
the pre-existing overstrong Hopf-subalgebra axiom, the cleft-extension proof
placeholder, and the positive-characteristic hierarchy axiom. Phases 2, 3,
and 5 replace these by exactly the two authorized exceptions.
