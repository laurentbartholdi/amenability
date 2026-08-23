/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.BialgebraSubcoalgebra
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite-dimensional products of subcoalgebras

The product `F * C` is the range of `Submodule.mulMap F C`, so it is
finite-dimensional as soon as `F` and `C` are finite-dimensional.
-/

namespace UnifiedRounding

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [Bialgebra k H]

/--
The product of two finite-dimensional subspaces is finite-dimensional.
-/
theorem finiteDimensional_mul
    (F C : Submodule k H)
    [FiniteDimensional k F]
    [FiniteDimensional k C] :
    FiniteDimensional k (F * C : Submodule k H) := by
  rw [← Submodule.mulMap_range F C]
  infer_instance

/--
A convenient local instance form of `finiteDimensional_mul`.
-/
scoped instance finiteDimensional_mul_instance
    (F C : Submodule k H)
    [FiniteDimensional k F]
    [FiniteDimensional k C] :
    FiniteDimensional k (F * C : Submodule k H) :=
  finiteDimensional_mul F C

/--
The multiplication map from `F ⊗ C` onto `F * C`.
-/
theorem mulMap_surjective
    (F C : Submodule k H) :
    Function.Surjective (Submodule.mulMap' F C) :=
  Submodule.mulMap'_surjective F C

end UnifiedRounding
