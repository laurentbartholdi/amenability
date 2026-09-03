# Amenability refactor report

This report records the refactor from the audited baseline
`c7cfb66432fa0fe64fd374cc91d65aafef25d7dc`.

## File moves

The augmentation-specific associated-graded files were renamed as follows:

- `AssociatedGradedAlgebra.lean` to `AugmentationGradedAlgebra.lean`;
- `AssociatedGradedModuleCoalgebra.lean` to `AugmentationGradedModule.lean`;
- `AssociatedGradedCoalgebra.lean` to `AugmentationGradedCoalgebra.lean`;
- `AssociatedGradedHopf.lean` to `AugmentationGradedHopf.lean`;
- `AssociatedGradedHopfModule.lean` to
  `AugmentationGradedHopfModuleCoalgebra.lean`;
- `AugmentationAssociatedGraded.lean` to
  `AugmentationLeadingSymbols.lean`.

The associated-graded and all-characteristic PBW conformance sources moved to
`Amenability/Tests/`. The phase-status documents moved to `docs/history/`.

## Extracted declarations

- Generic sequence growth and its ratio lemma moved to
  `SubexponentialGrowth.lean`.
- Associative growth balls and local algebra growth moved to
  `AlgebraGrowth.lean`.
- UEA finite-word generation moved to `UniversalEnvelopingGeneration.lean`.
- Weighted PBW growth and Smith's theorem moved to
  `UniversalEnvelopingGrowth.lean`.
- Lie extension PBW maps, coalgebra equivalences, finite-defect estimates, and
  `LieIdeal.ueaCleftExactSequence` moved to
  `UniversalEnvelopingExtension.lean`.
- Reusable Lie amenability helpers moved to
  `LieAmenabilityPermanence.lean`; the public Theorem G clauses remain in
  `TheoremG.lean`.
- Generic projective descent moved to `ProjectiveAmenability.lean`.
- Permutation-module and orbit infrastructure moved from `TheoremC.lean` to
  `PermutationModuleAmenability.lean`; the final action Folner theorems are in
  `TheoremF.lean`.
- Witt algebra construction, simplicity, finite generation, and growth moved
  to `WittAlgebra.lean`; the hierarchy and separation endpoints remain in
  `TheoremH.lean`.
- Hopf morphisms, exact sequences, the Takeuchi--Wigner projectivity input,
  Hopf algebra amenability, Hopf module maps, and Hopf-module-coalgebra
  amenability now live in their respective `Hopf*.lean` modules.
- Base augmentation filtration and separated-quotient constructions moved to
  `AugmentationFiltration.lean`. The amenability transfer and the sole concrete
  associated-graded amenability proof are in `TheoremJ.lean`.

The obsolete associated-graded realization-data proof package and its
data-parameter theorem were deleted.

## Smith's theorem

`UniversalEnvelopingGrowth.lean` proves the fixed-generator equivalence
`isSubexponential_lieGrowth_iff_ueaGrowth` and the finitely generated global
equivalence `hasSubexponentialLieGrowth_iff_uea`. The proof includes the
converse comparison from Lie balls to powers of the unital UEA generator
subspace. Both results are independent of project-local axioms.

## Assumption policy

The only project-local assumption is
`takeuchiWigner_projective_left`. The only incomplete proof is the explicitly
permitted positive-characteristic PSZ existence theorem
`exists_psz_subexponential_not_elementary`. No other `axiom`, `sorry`, or
`admit` occurs.

## Validation

The completed refactor is validated with:

```text
lake build
lake env lean -DwarningAsError=true Amenability/TheoremA.lean ... TheoremJ.lean
lake env lean Amenability/AxiomAudit.lean
lake env lean Amenability/Tests/ManuscriptConformance.lean
bash scripts/check_architecture.sh
```

The source scans confirm that only the permitted axiom and PSZ `sorry` remain,
that the obsolete proof-package name is absent, and that structural
augmentation, graded, and growth modules do not import theorem-letter files.
