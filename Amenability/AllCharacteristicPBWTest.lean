/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.UniversalEnvelopingPBW

/-! # All-characteristic PBW conformance checks -/

section

variable (k : Type*) [Field k]
variable (L : Type*) [LieRing L] [LieAlgebra k L]

#check UniversalEnvelopingAlgebra.iota_injective_of_basis
#check UniversalEnvelopingAlgebra.iota_injective
#check UniversalEnvelopingAlgebra.orderedMonomialBasis
#check UniversalEnvelopingAlgebra.relativePBWBasis

end
