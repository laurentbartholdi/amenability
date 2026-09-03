# Repository architecture

The main dependency direction is:

```text
general algebra, coalgebra, filtration, and PBW infrastructure
  -> Hopf-module-coalgebra amenability definitions
  -> rounding Theorems A and B
  -> Hopf-algebra permanence Theorems C through E
  -> group and Lie applications Theorems F through I
  -> augmentation-associated-graded amenability Theorem J
```

Support files contain definitions and reusable lemmas. Each `TheoremX.lean`
contains the final public declaration for that manuscript theorem. Compile-time
`#check` commands belong in `Amenability.lean`, `AxiomAudit.lean`, or `Tests`.

The only project-local assumptions are the projectivity axiom
`takeuchiWigner_projective_left` and the explicitly isolated PSZ result in
positive characteristic.

## Mathlib candidates

The coalgebra files, tensor-filtration files, `AscendingFiltrationBasis.lean`,
`WeightedPBW.lean`, `WeightedPBWGrowth.lean`,
`UniversalEnvelopingPBW.lean`, `SubexponentialGrowth.lean`, and the structural
universal-enveloping files are intended as possible upstream contributions.

