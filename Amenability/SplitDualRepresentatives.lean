/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.SplitDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Representatives of split-dual characters and layer coefficients

For a finite-dimensional coalgebra `F`, every linear functional on
`F*` is evaluation at a unique element of `F`.

Applied to a split filtration of `F*`, this produces two useful families:
* `characterRepresentative i`, representing `S.character i`;
* `coeffRepresentative i`, representing an extension of `S.coeff i`.

These are the elements denoted `g_i` and, implicitly, the coefficient
representatives in the paper proof.
-/

open Module WithConv

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {F : Type v}
variable [Field k]
variable [AddCommGroup F] [Module k F] [Coalgebra k F]
variable [FiniteDimensional k F]
variable [Coalgebra.IsCocomm k F]

namespace SplitDualFiltration

variable (S :
  SplitDualFiltration k
    (WithConv (Module.Dual k F)))

/--
The ordinary double-dual functional underlying the character of a layer.
-/
def characterFunctional
    (i : Fin S.n) :
    Module.Dual k (Module.Dual k F) :=
  (S.character i).toLinearMap.comp
    (WithConv.linearEquiv k (Module.Dual k F)).symm.toLinearMap

/--
The element `g_i ∈ F` represented by the character of the `i`-th layer.
-/
def characterRepresentative
    (i : Fin S.n) : F :=
  (Module.evalEquiv k F).symm (S.characterFunctional i)

/--
The character is evaluation at `characterRepresentative i`.
-/
theorem character_eq_eval
    (i : Fin S.n)
    (φ : WithConv (Module.Dual k F)) :
    S.character i φ =
      φ (S.characterRepresentative i) := by
  change
    S.character i φ =
      (WithConv.linearEquiv k (Module.Dual k F) φ)
        ((Module.evalEquiv k F).symm
          (S.characterFunctional i))
  rw [Module.apply_evalEquiv_symm_apply]
  simp [characterFunctional]

/--
An arbitrary extension to all of `F*` of the coefficient functional on
the upper filtration step.
-/
def coeffExtension
    (i : Fin S.n) :
    Module.Dual k
      (WithConv (Module.Dual k F)) :=
  Subspace.dualLift (S.filtration i.succ) (S.coeff i)

/--
The ordinary double-dual functional corresponding to the extended layer
coefficient.
-/
def coeffFunctional
    (i : Fin S.n) :
    Module.Dual k (Module.Dual k F) :=
  (S.coeffExtension i).comp
    (WithConv.linearEquiv k (Module.Dual k F)).symm.toLinearMap

/--
An element of `F` representing the `i`-th layer coefficient.
-/
def coeffRepresentative
    (i : Fin S.n) : F :=
  (Module.evalEquiv k F).symm (S.coeffFunctional i)

/--
On the filtration step, the chosen coefficient representative realizes
the original coefficient map.
-/
theorem coeff_eq_eval
    (i : Fin S.n)
    (x : S.filtration i.succ) :
    S.coeff i x =
      (x : WithConv (Module.Dual k F)).ofConv
        (S.coeffRepresentative i) := by
  change
    S.coeff i x =
      (WithConv.linearEquiv k (Module.Dual k F)
        (x : WithConv (Module.Dual k F)))
        ((Module.evalEquiv k F).symm
          (S.coeffFunctional i))
  rw [Module.apply_evalEquiv_symm_apply]
  simp [coeffFunctional, coeffExtension]

end SplitDualFiltration

end

end UnifiedRounding
