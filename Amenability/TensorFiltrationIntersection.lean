/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Coalgebra.Quotient

/-! # Tensor products and separated descending filtrations -/

open Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- A finite-dimensional test space meets a separated descending filtration
trivially at some finite stage. -/
theorem exists_inf_eq_bot_of_finiteDimensional_of_iInf_eq_bot
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (hsep : ⨅ n, W n = ⊥) (P : Submodule k V)
    [FiniteDimensional k ↑P] : ∃ n, P ⊓ W n = ⊥ := by
  let d : ℕ → ℕ := fun n => Module.finrank k ↑(P ⊓ W n)
  have hd : Antitone d := by
    intro m n hmn
    dsimp [d]
    exact Submodule.finrank_mono (inf_le_inf_left P (hW hmn))
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition hd
  have hstable : ∀ m, n ≤ m → P ⊓ W n = P ⊓ W m := by
    intro m hnm
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · exact inf_le_inf_left P (hW hnm)
    · have heq := hn m hnm
      dsimp [d] at heq
      exact Nat.le_of_eq heq
  have hinter : P ⊓ W n = P ⊓ (⨅ m, W m) := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1, (Submodule.mem_iInf W).2 fun m => ?_⟩
      by_cases hnm : n ≤ m
      · exact (show x ∈ P ⊓ W m from (hstable m hnm) ▸ hx).2
      · exact hW (Nat.le_of_lt (Nat.lt_of_not_ge hnm)) hx.2
    · exact inf_le_inf_left P (iInf_le W n)
  refine ⟨n, ?_⟩
  rw [hinter, hsep, inf_bot_eq]

/-- The degree-`n` tensor filtration
`∑_{i+j=n} W i ⊗ W j`, represented inside `V ⊗ V`. -/
def tensorFiltration (W : ℕ → Submodule k V) (n : ℕ) :
    Submodule k (V ⊗[k] V) :=
  ⨆ i : Fin (n + 1), LinearMap.range
    (TensorProduct.mapIncl (W i) (W (n - i)))

/-- The `(r+s)`-th tensor-filtration term vanishes in
`(V/W r) ⊗ (V/W s)`. -/
theorem tensorFiltration_le_ker_quotientMap
    (W : ℕ → Submodule k V) (hW : Antitone W) (r s : ℕ) :
    tensorFiltration (k := k) W (r + s) ≤
      LinearMap.ker (TensorProduct.map (W r).mkQ (W s).mkQ) := by
  rw [tensorFiltration]
  apply iSup_le
  intro i
  rintro _ ⟨z, rfl⟩
  change TensorProduct.map (W r).mkQ (W s).mkQ
      (TensorProduct.mapIncl (W i) (W (r + s - i)) z) = 0
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      by_cases hir : r ≤ (i : ℕ)
      · have hx : (x : V) ∈ W r := hW hir x.property
        change (W r).mkQ (x : V) ⊗ₜ[k] (W s).mkQ (y : V) = 0
        rw [Submodule.mkQ_apply (W r)]
        rw [(Submodule.Quotient.mk_eq_zero (W r)).2 hx, zero_tmul]
      · have his : s ≤ r + s - (i : ℕ) := by omega
        have hy : (y : V) ∈ W s := hW his y.property
        change (W r).mkQ (x : V) ⊗ₜ[k] (W s).mkQ (y : V) = 0
        rw [Submodule.mkQ_apply (W s)]
        rw [(Submodule.Quotient.mk_eq_zero (W s)).2 hy, tmul_zero]

/-- For a separated filtration, the tensor filtration is separated.  This is
the finite-support argument in the manuscript. -/
theorem iInf_tensorFiltration_eq_bot_of_iInf_eq_bot
    (W : ℕ → Submodule k V) (hW : Antitone W)
    (hsep : ⨅ n, W n = ⊥) :
    ⨅ n, tensorFiltration (k := k) W n = ⊥ := by
  apply bot_unique
  intro z hz
  by_contra hz0
  obtain ⟨d, left, right, hrepr⟩ := TensorProduct.exists_sum_tmul_eq z
  let P : Submodule k V := Submodule.span k (Set.range left)
  let Q : Submodule k V := Submodule.span k (Set.range right)
  let _ : FiniteDimensional k ↑P := by
    exact FiniteDimensional.span_of_finite k (Set.finite_range left)
  let _ : FiniteDimensional k ↑Q := by
    exact FiniteDimensional.span_of_finite k (Set.finite_range right)
  obtain ⟨r, hr⟩ := exists_inf_eq_bot_of_finiteDimensional_of_iInf_eq_bot
    W hW hsep P
  obtain ⟨s, hs⟩ := exists_inf_eq_bot_of_finiteDimensional_of_iInf_eq_bot
    W hW hsep Q
  let leftP : Fin d → P := fun j =>
    ⟨left j, Submodule.subset_span ⟨j, rfl⟩⟩
  let rightQ : Fin d → Q := fun j =>
    ⟨right j, Submodule.subset_span ⟨j, rfl⟩⟩
  let zp : P ⊗[k] Q := ∑ j, leftP j ⊗ₜ[k] rightQ j
  have hmap : TensorProduct.mapIncl P Q zp = z := by
    rw [hrepr]
    simp [zp, leftP, rightQ, TensorProduct.mapIncl]
  have hzp : zp ≠ 0 := by
    intro hzero
    apply hz0
    rw [← hmap, hzero, map_zero]
    exact Submodule.zero_mem _
  let qr : P →ₗ[k] V ⧸ W r := (W r).mkQ.comp P.subtype
  let qs : Q →ₗ[k] V ⧸ W s := (W s).mkQ.comp Q.subtype
  have hqr : Function.Injective qr := by
    intro x y hxy
    apply Subtype.ext
    have hzero : (W r).mkQ ((x : V) - (y : V)) = 0 := by
      simpa [qr] using sub_eq_zero.mpr hxy
    have hxyW : (x : V) - (y : V) ∈ W r :=
      (Submodule.Quotient.mk_eq_zero (W r)).1 hzero
    have hxyP : (x : V) - (y : V) ∈ P := P.sub_mem x.property y.property
    have : (x : V) - (y : V) ∈ P ⊓ W r := ⟨hxyP, hxyW⟩
    rw [hr] at this
    exact sub_eq_zero.mp this
  have hqs : Function.Injective qs := by
    intro x y hxy
    apply Subtype.ext
    have hzero : (W s).mkQ ((x : V) - (y : V)) = 0 := by
      simpa [qs] using sub_eq_zero.mpr hxy
    have hxyW : (x : V) - (y : V) ∈ W s :=
      (Submodule.Quotient.mk_eq_zero (W s)).1 hzero
    have hxyQ : (x : V) - (y : V) ∈ Q := Q.sub_mem x.property y.property
    have : (x : V) - (y : V) ∈ Q ⊓ W s := ⟨hxyQ, hxyW⟩
    rw [hs] at this
    exact sub_eq_zero.mp this
  have htensor : Function.Injective (TensorProduct.map qr qs) :=
    TensorProduct.map_injective_of_flat_flat qr qs hqr hqs
  have hzker : TensorProduct.map (W r).mkQ (W s).mkQ z = 0 :=
    tensorFiltration_le_ker_quotientMap W hW r s
      ((Submodule.mem_iInf (tensorFiltration (k := k) W)).1 hz (r + s))
  have hcomm : TensorProduct.map qr qs zp =
      TensorProduct.map (W r).mkQ (W s).mkQ
        (TensorProduct.mapIncl P Q zp) := by
    induction zp with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y => rfl
  apply hzp
  apply htensor
  rw [hcomm, hmap, hzker, map_zero]

/-- The quotient filtration by the infinite intersection. -/
def separatedQuotientFiltration (W : ℕ → Submodule k V) (n : ℕ) :
    Submodule k (V ⧸ (⨅ m, W m)) :=
  (W n).map (⨅ m, W m).mkQ

theorem separatedQuotientFiltration_antitone
    (W : ℕ → Submodule k V) (hW : Antitone W) :
    Antitone (separatedQuotientFiltration (k := k) W) := by
  intro m n hmn
  exact Submodule.map_mono (hW hmn)

theorem iInf_separatedQuotientFiltration_eq_bot
    (W : ℕ → Submodule k V) :
    ⨅ n, separatedQuotientFiltration (k := k) W n = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (⨅ n, W n) x
  have hv : v ∈ ⨅ n, W n := (Submodule.mem_iInf W).2 fun n => by
    have hn := (Submodule.mem_iInf
      (separatedQuotientFiltration (k := k) W)).1 hx n
    rcases hn with ⟨w, hw, heq⟩
    have hd : v - w ∈ ⨅ n, W n := by
      apply (Submodule.Quotient.mk_eq_zero (⨅ n, W n)).1
      simpa using sub_eq_zero.mpr heq.symm
    simpa using (W n).add_mem ((Submodule.mem_iInf W).1 hd n) hw
  exact (Submodule.Quotient.mk_eq_zero (⨅ n, W n)).2 hv

/-- Passing to the separated quotient maps every tensor-filtration term into
the corresponding quotient-filtration term. -/
theorem tensorFiltration_map_separatedQuotient
    (W : ℕ → Submodule k V) (n : ℕ) :
    tensorFiltration (k := k) W n ≤
      (tensorFiltration (k := k)
        (separatedQuotientFiltration (k := k) W) n).comap
          (TensorProduct.map (⨅ m, W m).mkQ (⨅ m, W m).mkQ) := by
  rw [tensorFiltration]
  apply iSup_le
  intro i
  rintro _ ⟨z, rfl⟩
  change TensorProduct.map (⨅ m, W m).mkQ (⨅ m, W m).mkQ
      (TensorProduct.mapIncl (W i) (W (n - i)) z) ∈
        tensorFiltration (k := k)
          (separatedQuotientFiltration (k := k) W) n
  induction z with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  | tmul x y =>
      change (⨅ m, W m).mkQ (x : V) ⊗ₜ[k]
        (⨅ m, W m).mkQ (y : V) ∈ _
      apply Submodule.mem_iSup_of_mem i
      refine ⟨(⟨(⨅ m, W m).mkQ (x : V), ⟨x, x.property, rfl⟩⟩ :
          separatedQuotientFiltration (k := k) W i) ⊗ₜ[k]
        (⟨(⨅ m, W m).mkQ (y : V), ⟨y, y.property, rfl⟩⟩ :
          separatedQuotientFiltration (k := k) W (n - i)), ?_⟩
      rfl

/-- **Tensor-intersection lemma.** For a descending filtration beginning at
`V`, the intersection of the tensor filtration is precisely the sum of the
two tensor factors involving the infinite intersection. -/
theorem iInf_tensorFiltration_eq
    (W : ℕ → Submodule k V) (hW : Antitone W) (hzero : W 0 = ⊤) :
    ⨅ n, tensorFiltration (k := k) W n =
      LinearMap.range (LinearMap.lTensor V (⨅ n, W n).subtype) ⊔
        LinearMap.range (LinearMap.rTensor V (⨅ n, W n).subtype) := by
  apply le_antisymm
  · intro z hz
    have hzq : TensorProduct.map (⨅ n, W n).mkQ (⨅ n, W n).mkQ z ∈
        ⨅ n, tensorFiltration (k := k)
          (separatedQuotientFiltration (k := k) W) n :=
      (Submodule.mem_iInf _).2 fun n =>
        tensorFiltration_map_separatedQuotient W n
          ((Submodule.mem_iInf _).1 hz n)
    have hzq0 : TensorProduct.map (⨅ n, W n).mkQ (⨅ n, W n).mkQ z = 0 := by
      rw [iInf_tensorFiltration_eq_bot_of_iInf_eq_bot
        (separatedQuotientFiltration (k := k) W)
        (separatedQuotientFiltration_antitone W hW)
        (iInf_separatedQuotientFiltration_eq_bot W)] at hzq
      exact hzq
    rw [← LinearMap.mem_ker] at hzq0
    rw [TensorProduct.map_ker
      (LinearMap.exact_subtype_mkQ (⨅ n, W n))
      (Submodule.mkQ_surjective (⨅ n, W n))
      (LinearMap.exact_subtype_mkQ (⨅ n, W n))
      (Submodule.mkQ_surjective (⨅ n, W n))] at hzq0
    exact hzq0
  · rw [sup_le_iff]
    constructor
    · rintro _ ⟨z, rfl⟩
      apply (Submodule.mem_iInf _).2
      intro n
      rw [tensorFiltration]
      apply Submodule.mem_iSup_of_mem ⟨0, Nat.zero_lt_succ n⟩
      rw [Nat.sub_zero, hzero]
      induction z with
      | zero => exact Submodule.zero_mem _
      | add x y hx hy => simpa using Submodule.add_mem _ hx hy
      | tmul x y => exact ⟨⟨x, Submodule.mem_top⟩ ⊗ₜ[k]
          ⟨y, (Submodule.mem_iInf _).1 y.property n⟩, rfl⟩
    · rintro _ ⟨z, rfl⟩
      apply (Submodule.mem_iInf _).2
      intro n
      rw [tensorFiltration]
      apply Submodule.mem_iSup_of_mem ⟨n, Nat.lt_succ_self n⟩
      induction z with
      | zero => exact Submodule.zero_mem _
      | add x y hx hy => simpa using Submodule.add_mem _ hx hy
      | tmul x y =>
          have hy0 : y ∈ W (n - n) := by
            rw [Nat.sub_self, hzero]
            exact Submodule.mem_top
          exact ⟨⟨x, (Submodule.mem_iInf _).1 x.property n⟩ ⊗ₜ[k]
            ⟨y, hy0⟩, rfl⟩

/-- The infinite intersection of a counital coalgebra filtration is a
coideal. -/
theorem iInf_isCoideal_of_coalgebraFiltration
    [Coalgebra k V]
    (W : ℕ → Submodule k V) (hW : Antitone W) (hzero : W 0 = ⊤)
    (hcounit : ∀ x ∈ W 1, Coalgebra.counit (R := k) x = 0)
    (hcomul : ∀ n x, x ∈ W n →
      Coalgebra.comul (R := k) x ∈ tensorFiltration (k := k) W n) :
    (⨅ n, W n).IsCoideal := by
  rw [Submodule.isCoideal_iff_comul_mem]
  constructor
  · intro x hx
    exact hcounit x ((Submodule.mem_iInf W).1 hx 1)
  · intro x hx
    have hdelta : Coalgebra.comul (R := k) x ∈
        ⨅ n, tensorFiltration (k := k) W n :=
      (Submodule.mem_iInf _).2 fun n => hcomul n x ((Submodule.mem_iInf W).1 hx n)
    rw [iInf_tensorFiltration_eq W hW hzero] at hdelta
    exact hdelta

end

end HopfAmenability
