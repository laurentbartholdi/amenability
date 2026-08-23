/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.TransferDimensions
import Amenability.RoundingCore
import Amenability.SubmoduleFinrank
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Telescoping and the abstract filtered transfer inequality

This file completes the dimension bookkeeping for `FilteredTransferData`.

First, the rank-nullity identity on each successive layer is telescoped to
identify the dimension of an arbitrary subspace `J ≤ Q` with the sum of
the dimensions of its layer images.

Second, if `J` is an ideal subspace, `N ≤ J`, the layer images of `N`
land in a fixed subspace `K ≤ A`, and every ideal subspace `M ≤ A`
satisfies the semistability estimate
```
t * dim M ≤ dim M - dim (M ∩ K),
```
then
```
t * dim J ≤ dim J - dim N.
```
This is the abstract numerical heart of the transfer lemma.
-/

open scoped BigOperators
open Module

namespace HopfAmenability

/--
A finite telescoping lemma indexed by `Fin`.

If
`d(i+1) = d(i) + m(i)` for every adjacent pair, then the last value of
`d` is its first value plus the sum of the increments.
-/
theorem fin_last_eq_add_sum_of_succ_eq
    {n : ℕ}
    (d : Fin (n + 1) → ℕ)
    (m : Fin n → ℕ)
    (h : ∀ i : Fin n, d i.succ = d i.castSucc + m i) :
    d (Fin.last n) = d 0 + ∑ i, m i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hih :
          d (Fin.last n).castSucc =
            d 0 + ∑ i : Fin n, m i.castSucc := by
        have h' :=
          ih
            (d := fun j : Fin (n + 1) => d j.castSucc)
            (m := fun i : Fin n => m i.castSucc)
            (fun i => by
              simpa only [Fin.succ_castSucc] using h i.castSucc)
        simpa using h'
      have hlast :
          d (Fin.last (n + 1)) =
            d (Fin.last n).castSucc + m (Fin.last n) := by
        simpa using h (Fin.last n)
      calc
        d (Fin.last (n + 1))
            = d (Fin.last n).castSucc + m (Fin.last n) := hlast
        _ = (d 0 + ∑ i : Fin n, m i.castSucc) +
              m (Fin.last n) := by
              rw [hih]
        _ = d 0 +
              ((∑ i : Fin n, m i.castSucc) + m (Fin.last n)) := by
              rw [Nat.add_assoc]
        _ = d 0 + ∑ i : Fin (n + 1), m i := by
              rw [Fin.sum_univ_castSucc]

universe u v w

variable {k : Type u} {Q : Type v} {A : Type w}
variable [Field k]
variable [CommRing Q] [Algebra k Q]
variable [CommRing A] [Algebra k A]
variable [FiniteDimensional k Q]

namespace FilteredTransferData

variable (T : FilteredTransferData k Q A)

omit [FiniteDimensional k Q] in
/--
At the bottom of the filtration, every vector is zero, hence every
subspace has zero filtered step.
-/
theorem step_zero_eq_bot
    (J : Submodule k Q) :
    T.step J 0 = ⊥ := by
  apply le_antisymm
  · intro x _
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have hx : (x : Q) ∈ T.filtration 0 := x.2
    have hx' : (x : Q) ∈ (⊥ : Submodule k Q) := by
      simpa only [T.bot] using hx
    simpa using hx'
  · exact bot_le

omit [FiniteDimensional k Q] in
@[simp]
theorem finrank_step_zero
    (J : Submodule k Q) :
    finrank k (T.step J 0) = 0 := by
  rw [T.step_zero_eq_bot J]
  simp

/--
The last filtered step is linearly equivalent to the original subspace.
-/
noncomputable def stepLastEquiv
    (J : Submodule k Q) :
    T.step J (Fin.last T.n) ≃ₗ[k] J where
  toFun x :=
    ⟨(x.1 : Q), x.2⟩
  invFun x :=
    ⟨⟨(x : Q), by
      rw [T.top]
      exact Submodule.mem_top⟩, x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := rfl
  map_smul' r x := rfl

omit [FiniteDimensional k Q] in
theorem finrank_step_last
    (J : Submodule k Q) :
    finrank k (T.step J (Fin.last T.n)) =
      finrank k J :=
  (T.stepLastEquiv J).finrank_eq

/--
The dimension of a subspace is the sum of the dimensions of all its
successive layer images.
-/
theorem finrank_eq_sum_layerImage
    (J : Submodule k Q) :
    finrank k J =
      ∑ i : Fin T.n, finrank k (T.layerImage J i) := by
  have h :=
    fin_last_eq_add_sum_of_succ_eq
      (d := fun j : Fin (T.n + 1) =>
        finrank k (T.step J j))
      (m := fun i : Fin T.n =>
        finrank k (T.layerImage J i))
      (fun i => T.finrank_step_succ J i)
  rw [T.finrank_step_last J, T.finrank_step_zero J] at h
  simpa using h

omit [FiniteDimensional k Q] in
/--
Layer images are monotone in the original subspace.
-/
theorem layerImage_mono
    {N J : Submodule k Q}
    (hNJ : N ≤ J)
    (i : Fin T.n) :
    T.layerImage N i ≤ T.layerImage J i := by
  rintro y ⟨x, rfl⟩
  let xJ : T.step J i.succ :=
    ⟨x.1, hNJ x.2⟩
  refine ⟨xJ, ?_⟩
  rfl

omit [FiniteDimensional k Q] in
/--
If `N ≤ J` and the `i`-th layer image of `N` lies in `K`, then it lies
in the intersection of the `i`-th layer image of `J` with `K`.
-/
theorem layerImage_le_inf
    {N J : Submodule k Q}
    (K : Submodule k A)
    (hNJ : N ≤ J)
    (hNK : ∀ i : Fin T.n, T.layerImage N i ≤ K)
    (i : Fin T.n) :
    T.layerImage N i ≤ T.layerImage J i ⊓ K :=
  le_inf (T.layerImage_mono hNJ i) (hNK i)

variable [FiniteDimensional k A]

/--
Abstract filtered transfer inequality.

`J` is the ideal whose codimension we want to estimate and `N ≤ J` is
the part already lying in the bad subspace. The hypothesis `hNK` says
that each layer image of `N` lies in `K`. The semistability inequality
is required only for ideal subspaces of `A`; the layer images of `J`
are ideal by `layerImage_isIdealSubspace`.
-/
theorem filtered_transfer_finrank
    (J N : Submodule k Q)
    (K : Submodule k A)
    (hJ : IsIdealSubspace J)
    (hNJ : N ≤ J)
    (hNK : ∀ i : Fin T.n, T.layerImage N i ≤ K)
    (t : ℚ)
    (hsem :
      ∀ M : Submodule k A,
        IsIdealSubspace M →
          t * (finrank k M : ℚ) ≤
            (finrank k M : ℚ) -
              (sfinrank k (M ⊓ K) : ℚ)) :
    t * (finrank k J : ℚ) ≤
      (finrank k J : ℚ) - (finrank k N : ℚ) := by
  let cert : LayerCertificate (Fin T.n) :=
    { t := t
      dimJ := finrank k J
      dimN := finrank k N
      jLayer := fun i => finrank k (T.layerImage J i)
      nLayer := fun i => sfinrank k (T.layerImage J i ⊓ K)
      dimJ_eq := by
        exact_mod_cast T.finrank_eq_sum_layerImage J
      dimN_le := by
        have hnat :
            finrank k N ≤
              ∑ i : Fin T.n,
                sfinrank k (T.layerImage J i ⊓ K) := by
          rw [T.finrank_eq_sum_layerImage N]
          exact Finset.sum_le_sum fun i _ =>
            Submodule.finrank_mono
              (T.layerImage_le_inf K hNJ hNK i)
        exact_mod_cast hnat
      semistable := fun i =>
        hsem
          (T.layerImage J i)
          (T.layerImage_isIdealSubspace J hJ i) }
  exact cert.quotient_bound

end FilteredTransferData

end HopfAmenability
