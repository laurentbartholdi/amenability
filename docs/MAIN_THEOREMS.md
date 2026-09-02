# Manuscript main theorems A--J

| Letter | Lean endpoint | Main implementation |
|---|---|---|
| A | `exists_finiteSubcoalgebra_expansion_ratio_le`, `isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces` | `TheoremA.lean` |
| B | `IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom` | `TheoremB.lean` |
| C | `isAmenableHopfAlgebra_iff_all_nonzero_moduleCoalgebras` | `TheoremC.lean` |
| D | `isAmenableHopfAlgebra_of_hopfSubalgebra` | `TheoremD.lean`, `HopfAmenability.lean` |
| E | `isAmenableHopfAlgebra_cleftExtension_of_components`, `isAmenableHopfAlgebra_cleftExtension_iff` | `CleftNormalBasis.lean`, `CleftAmenability.lean`, `TheoremE.lean` |
| F | `hasActionFolnerSubspaces_of_quotient_permutationModule`, `hasActionFolnerSubspaces_of_isAmenableGroup` | `TheoremF.lean` |
| G | `isAmenableLieAlgebra_of_locallySubexponentialGrowth`, `isAmenableLieAlgebra_of_injective`, `isAmenableLieAlgebra_quotient`, `isAmenableLieAlgebra_extension_iff`, `isAmenableLieAlgebra_directedUnion` | `UniversalEnvelopingPBW.lean`, `LieGrowth.lean`, `TheoremG.lean` |
| H | `elementaryLieAlgebras_ne_subexponentiallyAmenableLieAlgebras_general` | `TheoremH.lean` |
| I | `exists_amenable_exponentialGrowth_locallyFiniteByOne` | `LocallyMatrixProfile.lean`, `ShiftProfileAlgebra.lean`, `ProfileLieExample.lean`, `TheoremI.lean` |
| J | `isAmenable_associatedGraded` | `TensorFiltrationIntersection.lean`, `HopfAmenability.lean`, `TheoremJ.lean` |

`Amenability.lean` imports and checks all endpoints. `AxiomAudit.lean` prints
their assumptions. The sole project axiom is
`takeuchiWigner_projective_left`; the sole incomplete proof is the designated
positive-characteristic PSZ input in Theorem H.

The group-algebra application is in `GroupPermanence.lean` and
`GroupCleftExactSequence.lean`. It proves the group/group-algebra
equivalence, subgroup and normal-extension permanence, the coinvariant
identity, the quotient-kernel identity, and the resulting quotient ring
equivalence.
