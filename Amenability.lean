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
import Amenability.TheoremF
import Amenability.TheoremG
import Amenability.TheoremH
import Amenability.TheoremI
import Amenability.TheoremJ
import Amenability.GroupPermanence
import Amenability.GroupCleftExactSequence

/-!
# Amenability

Compile-time documentation and checks for the manuscript's main theorems.
-/

/- Theorem A: coalgebraic amenability is equivalent to algebraic amenability,
with the sharper non-increasing expansion-ratio rounding theorem. -/
#check HopfAmenability.exists_finiteSubcoalgebra_expansion_ratio_le
#check HopfAmenability.isAmenableHopfModuleCoalgebra_iff_hasActionFolnerSubspaces

/- Theorem B: amenability descends through surjective equivariant counital
coalgebra quotients. -/
#check HopfAmenability.IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom

/- Theorem C: a cocommutative Hopf algebra is amenable exactly when all its
nonzero module coalgebras are amenable. -/
#check HopfAmenability.isAmenableHopfAlgebra_iff_all_nonzero_moduleCoalgebras

/- Theorem D: Hopf subalgebras of amenable cocommutative Hopf algebras are
amenable. -/
#check HopfAmenability.isAmenableHopfAlgebra_of_hopfSubalgebra

/- Theorem E: the middle algebra of a cleft exact Hopf sequence is amenable
exactly when its kernel and quotient are amenable. -/
#check HopfAmenability.isAmenableHopfAlgebra_cleftExtension_of_components
#check HopfAmenability.isAmenableHopfAlgebra_cleftExtension_iff

/- Theorem F: quotients of permutation modules with a nonzero amenable orbit
are algebraically amenable; in particular every nonzero module over an
amenable group algebra is algebraically amenable. -/
#check HopfAmenability.hasActionFolnerSubspaces_of_quotient_permutationModule
#check HopfAmenability.hasActionFolnerSubspaces_of_isAmenableGroup

/- Theorem G: every locally subexponential-growth Lie algebra (in particular,
every Abelian Lie algebra) is amenable, and amenable Lie algebras are closed
under subalgebras, quotients, extensions, and directed unions. -/
#check HopfAmenability.isAmenableLieAlgebra_iff_algebraicallyAmenable
#check HopfAmenability.isAmenableLieAlgebra_iff_isAmenableHopfAlgebra
#check HopfAmenability.isAmenableLieAlgebra_of_locallySubexponentialGrowth
#check HopfAmenability.isAmenableLieAlgebra_of_isLieAbelian
#check HopfAmenability.isAmenableLieAlgebra_of_injective
#check HopfAmenability.isAmenableLieAlgebra_quotient
#check HopfAmenability.isAmenableLieAlgebra_extension_iff
#check HopfAmenability.isAmenableLieAlgebra_directedUnion

/- Theorem H: elementary and subexponentially amenable Lie algebras form
distinct classes in every characteristic. -/
#check HopfAmenability.IsElementaryLieObject.isSubexponentiallyAmenable
#check HopfAmenability.IsSubexponentiallyAmenableLieObject.isAmenable
#check HopfAmenability.elementaryLieAlgebras_ne_subexponentiallyAmenableLieAlgebras_general

/- Theorem I: an explicit finitely generated amenable Lie algebra has
exponential growth and a locally finite-dimensional kernel with
one-dimensional quotient. -/
#check HopfAmenability.exists_amenable_exponentialGrowth_locallyFiniteByOne

/- Theorem J: amenability passes unconditionally to the concrete
augmentation-associated graded Hopf-module coalgebra. -/
#check HopfAmenability.isAmenable_associatedGraded

/- Supporting group permanence: group amenability agrees with amenability of
the group Hopf algebra, descends to subgroups, and is preserved and reflected
by normal extensions.  The quotient group algebra is also identified with
the quotient by the explicit augmentation ideal. -/
#check HopfAmenability.isAmenableGroup_iff_groupAlgebra
#check HopfAmenability.isAmenableGroup_subgroup
#check HopfAmenability.isAmenableGroup_normalExtension_iff
#check HopfAmenability.groupAlgebra_projection_ker
#check HopfAmenability.groupAlgebraQuotientEquiv
