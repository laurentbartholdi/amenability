/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfModuleCoalgebraRounding
import Amenability.CoalgebraRounding
import Amenability.LieAmenability
import Amenability.GroupAmenability

/-!
# Amenability

Top-level imports and compile-time checks for the generic rounding theorem,
its regular-coalgebra specialization, and the Lie and group Følner
equivalences.
-/

#check HopfAmenability.exists_finiteSubcoalgebra_action_ratio_le
#check HopfAmenability.exists_finiteSubcoalgebra_ratio_le
#check HopfAmenability.isAmenableLieModule_iff_hasFolnerSubspaces
#check HopfAmenability.isAmenableGroupAction_iff_hasFolnerSubspaces
