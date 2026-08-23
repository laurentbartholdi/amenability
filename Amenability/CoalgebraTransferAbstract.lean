/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.IdealCoannihilator
import Amenability.TransferInequality

/-!
# Abstract coalgebraic transfer theorem

This file turns `FilteredTransferData` into the dimension inequality used
by the density-filtration argument.

Let `V` play the role of `FC` and `C` the role of `C`.  For
`D ≤ V`, `W ≤ V`, and `U ≤ C`, put
```
J = D^⊥,
N = J ∩ W^⊥,
K = U^⊥.
```
If every layer image of `N` lies in `K`, and semistability on `C`
extends to every ideal of `C*`, the abstract filtered transfer theorem
gives
```
t (dim V - dim D) ≤ dim W - dim(W ∩ D).
```
-/

open Module WithConv

namespace UnifiedRounding

noncomputable section

universe u v w

variable {k : Type u} {V : Type v} {C : Type w}
variable [Field k]
variable [AddCommGroup V] [Module k V] [Coalgebra k V]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [Coalgebra.IsCocomm k V] [Coalgebra.IsCocomm k C]
variable [FiniteDimensional k V] [FiniteDimensional k C]

/--
Semistability against all subcoalgebras of `C` implies the dual
semistability inequality against all ideals of `C*`, provided the
coannihilator of every ideal is a subcoalgebra.
-/
theorem semistable_all_conv_ideals
    (U : Submodule k C)
    (t : ℚ)
    (hsem :
      ∀ B : Submodule k C,
        IsSubcoalgebra (k := k) B →
          t * ((finrank k C : ℚ) - (finrank k B : ℚ)) ≤
            (finrank k U : ℚ) -
              (finrank k (U ⊓ B : Submodule k C) : ℚ)) :
    ∀ M : Submodule k (WithConv (Module.Dual k C)),
      IsIdealSubspace M →
        t * (finrank k M : ℚ) ≤
          (finrank k M : ℚ) -
            (finrank k
              (M ⊓ convDualAnnihilator U :
                Submodule k (WithConv (Module.Dual k C))) : ℚ) := by
  intro M hM
  let B : Submodule k C := convDualCoannihilator M
  have hB : IsSubcoalgebra (k := k) B :=
    convDualCoannihilator_isSubcoalgebra M hM
  have h :=
    semistable_to_convDualAnnihilator
      U B t (hsem B hB)
  have hMB :
      convDualAnnihilator B = M := by
    exact convDualAnnihilator_convDualCoannihilator M
  rw [hMB] at h
  exact h

/--
The abstract coalgebraic transfer inequality.

The hypothesis `hbad` is the concrete statement that the successive
coefficients of
`D^⊥ ∩ W^⊥`
annihilate `U`.  In the application it follows from
`W = F U` and the realization of the tensor-layer coefficient by an
element of `F`.
-/
theorem coalgebra_transfer
    (T :
      FilteredTransferData k
        (WithConv (Module.Dual k V))
        (WithConv (Module.Dual k C)))
    (U : Submodule k C)
    (W D : Submodule k V)
    (t : ℚ)
    (hD : IsSubcoalgebra (k := k) D)
    (hsem :
      ∀ B : Submodule k C,
        IsSubcoalgebra (k := k) B →
          t * ((finrank k C : ℚ) - (finrank k B : ℚ)) ≤
            (finrank k U : ℚ) -
              (finrank k (U ⊓ B : Submodule k C) : ℚ))
    (hbad :
      ∀ i : Fin T.n,
        T.layerImage
            (convDualAnnihilator D ⊓ convDualAnnihilator W) i ≤
          convDualAnnihilator U) :
    t * ((finrank k V : ℚ) - (finrank k D : ℚ)) ≤
      (finrank k W : ℚ) -
        (finrank k (W ⊓ D : Submodule k V) : ℚ) := by
  letI : FiniteDimensional k (WithConv (Module.Dual k V)) :=
    FiniteDimensional.of_injective
      (WithConv.linearEquiv k (Module.Dual k V)).toLinearMap
      (WithConv.linearEquiv k (Module.Dual k V)).injective
  letI : FiniteDimensional k (WithConv (Module.Dual k C)) :=
    FiniteDimensional.of_injective
      (WithConv.linearEquiv k (Module.Dual k C)).toLinearMap
      (WithConv.linearEquiv k (Module.Dual k C)).injective
  let J : Submodule k (WithConv (Module.Dual k V)) :=
    convDualAnnihilator D
  let N : Submodule k (WithConv (Module.Dual k V)) :=
    J ⊓ convDualAnnihilator W
  let K : Submodule k (WithConv (Module.Dual k C)) :=
    convDualAnnihilator U
  have hJideal : IsIdealSubspace J := by
    dsimp [J]
    exact convDualAnnihilator_isIdealSubspace D hD
  have hNK : ∀ i : Fin T.n, T.layerImage N i ≤ K := by
    intro i
    simpa [N, J, K] using hbad i
  have hfiltered :=
    T.filtered_transfer_finrank
      J N K hJideal inf_le_left hNK t
      (semistable_all_conv_ideals U t hsem)
  have hright :
      (finrank k J : ℚ) - (finrank k N : ℚ) =
        (finrank k W : ℚ) -
          (finrank k (W ⊓ D : Submodule k V) : ℚ) := by
    simpa [J, N] using
      convDualAnnihilator_difference W D
  have hannNat :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq D
  have hann :
      (finrank k D : ℚ) +
          (finrank k D.dualAnnihilator : ℚ) =
        (finrank k V : ℚ) := by
    exact_mod_cast hannNat
  have hJann :
      (finrank k J : ℚ) =
        (finrank k D.dualAnnihilator : ℚ) := by
    exact_mod_cast finrank_convDualAnnihilator D
  have hleft :
      (finrank k J : ℚ) =
        (finrank k V : ℚ) - (finrank k D : ℚ) := by
    linarith
  rw [hright, hleft] at hfiltered
  exact hfiltered

end

end UnifiedRounding
