/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremA
import Amenability.TheoremB
import Amenability.TheoremC
import Amenability.TheoremD
import Amenability.TheoremE
import Amenability.HopfAmenability

/-!
# Amenability

Top-level imports and compile-time checks for the main theorems of the
accompanying article.
-/

/- Theorem A claims that a Hopf-module coalgebra is amenable exactly when
its underlying associative-algebra module is algebraically amenable. -/
#check HopfAmenability.isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces

/- Theorem B claims that every surjective equivariant counital coalgebra
quotient of an amenable Hopf-module coalgebra is amenable. -/
#check HopfAmenability.IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom

/- Every Hopf subalgebra of an amenable cocommutative Hopf algebra is
amenable. -/
#check HopfAmenability.isAmenableHopfAlgebra_of_hopfSubalgebra

/- A cleft extension of cocommutative Hopf algebras is amenable exactly when
its kernel and quotient Hopf algebras are amenable. -/
#check HopfAmenability.isAmenableHopfAlgebra_cleftExtension_iff

/- Theorem C claims that a quotient of a permutation module is algebraically
amenable when a basis point has nonzero image and amenable orbit; consequently,
every nonzero module over the group algebra of an amenable group is
algebraically amenable. -/
#check HopfAmenability.hasActionFolnerSubspaces_of_quotient_permutationModule
#check HopfAmenability.hasActionFolnerSubspaces_of_isAmenableGroup
#check HopfAmenability.isAmenableGroupAction_iff_isAmenableHopfModuleCoalgebra

/- Theorem D claims that Lie algebras of locally subexponential growth are
amenable, and that subalgebras, quotient algebras, extensions, and directed
unions of amenable Lie algebras are amenable. -/
#check HopfAmenability.isAmenableLieAlgebra_of_locallySubexponentialGrowth
#check HopfAmenability.isAmenableLieAlgebra_of_injective
#check HopfAmenability.isAmenableLieAlgebra_quotient
#check HopfAmenability.isAmenableLieAlgebra_extension_iff
#check HopfAmenability.isAmenableLieAlgebra_directedUnion

/- Theorem E claims that, over every field, the elementary amenable and
subexponentially amenable classes of Lie algebras are distinct. -/
#check HopfAmenability.elementaryLieAlgebras_ne_subexponentiallyAmenableLieAlgebras_general

/- The exponential-growth example claims that there is an amenable Lie
algebra of exponential growth which is locally finite-dimensional-by-one-
dimensional.  Its formalization is intentionally deferred in this pass. -/

/- Amenability of a Hopf-module coalgebra passes to the Hopf-module
coalgebra associated graded for its augmentation filtration. -/
#check HopfAmenability.IsAmenableHopfModuleCoalgebra.associatedGraded
