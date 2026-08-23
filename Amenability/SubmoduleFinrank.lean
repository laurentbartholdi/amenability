/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Ergonomic finrank notation for submodules
-/

namespace UnifiedRounding

/-- The finrank of a submodule, with the scalar field explicit and the
ambient module inferred from the submodule argument. -/
noncomputable abbrev sfinrank
    (k : Type*) {V : Type*} [DivisionRing k]
    [AddCommGroup V] [Module k V]
    (P : Submodule k V) : ℕ :=
  Module.finrank k P

@[simp]
theorem sfinrank_eq
    (k : Type*) {V : Type*} [DivisionRing k]
    [AddCommGroup V] [Module k V]
    (P : Submodule k V) :
    sfinrank k P = Module.finrank k P :=
  rfl

end UnifiedRounding
