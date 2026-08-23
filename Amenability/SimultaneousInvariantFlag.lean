/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CompleteSubcoalgebraFlag
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Simultaneous invariant flags
-/

open Module Polynomial

namespace UnifiedRounding

noncomputable section

universe u v w

variable {K : Type u} {V : Type v} {W : Type w} {ι : Type*}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A subspace invariant under every endomorphism in a family. -/
def IsInvariantUnder (f : ι → Module.End K V) (P : Submodule K V) : Prop :=
  ∀ i, P ∈ (f i).invtSubmodule

/-- A complete invariant flag, built in codimension-one steps. -/
inductive HasCompleteInvariantFlag (f : ι → Module.End K V) :
    Submodule K V → Prop
  | bot : HasCompleteInvariantFlag f ⊥
  | step {P Q : Submodule K V}
      (hP : HasCompleteInvariantFlag f P)
      (hPQ : P ≤ Q)
      (hdim : sfinrank K Q = sfinrank K P + 1)
      (hQinv : IsInvariantUnder f Q) :
      HasCompleteInvariantFlag f Q

@[simp]
theorem isInvariantUnder_bot (f : ι → Module.End K V) :
    IsInvariantUnder f ⊥ := by
  intro i
  exact Module.End.invtSubmodule.bot_mem (f i)

@[simp]
theorem isInvariantUnder_top (f : ι → Module.End K V) :
    IsInvariantUnder f ⊤ := by
  intro i x _
  trivial

/-- Lift a complete invariant flag in an invariant subspace to the ambient space. -/
theorem HasCompleteInvariantFlag.map_subtype
    (f : ι → Module.End K V) (P : Submodule K V)
    (hP : IsInvariantUnder f P)
    (hflag : HasCompleteInvariantFlag
      (fun i ↦ LinearMap.restrict (f i) (hP i)) ⊤) :
    HasCompleteInvariantFlag f P := by
  have lift {Q : Submodule K P}
      (hQ : HasCompleteInvariantFlag
        (fun i ↦ LinearMap.restrict (f i) (hP i)) Q) :
      HasCompleteInvariantFlag f (Q.map P.subtype) := by
    induction hQ with
    | bot => simpa using (HasCompleteInvariantFlag.bot (f := f))
    | @step Q' Q hflag hQQ hdim hQinv ih =>
        apply HasCompleteInvariantFlag.step ih
        · exact Submodule.map_mono hQQ
        · simpa only [Submodule.finrank_map_subtype_eq] using hdim
        · intro i
          exact Module.End.invtSubmodule.map_subtype_mem_of_mem_invtSubmodule
            (f i) (hP i) (hQinv i)
  simpa using lift hflag

/-- Polynomial evaluation commutes with restriction to an invariant subspace. -/
theorem aeval_restrict_intertwines
    (f : Module.End K V) (P : Submodule K V)
    (hP : P ∈ f.invtSubmodule) (p : K[X]) :
    P.subtype.comp (Polynomial.aeval (LinearMap.restrict f hP) p) =
      (Polynomial.aeval f p).comp P.subtype := by
  have hpow (n : ℕ) :
      P.subtype.comp ((LinearMap.restrict f hP) ^ n) =
        (f ^ n).comp P.subtype := by
    induction n with
    | zero => ext x; rfl
    | succ n hn =>
        apply LinearMap.ext
        intro x
        change P.subtype (((LinearMap.restrict f hP) ^ n)
          ((LinearMap.restrict f hP) x)) =
            (f ^ n) (f (P.subtype x))
        have hx := LinearMap.congr_fun hn ((LinearMap.restrict f hP) x)
        exact hx
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply LinearMap.ext
      intro x
      simpa only [map_add, LinearMap.add_apply, LinearMap.comp_apply] using
        congrArg₂ (fun a b ↦ a + b)
          (LinearMap.congr_fun hp x) (LinearMap.congr_fun hq x)
  | monomial n a =>
      apply LinearMap.ext
      intro x
      have hn := LinearMap.congr_fun (hpow n) x
      simp only [LinearMap.comp_apply, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.pow_apply,
        Module.algebraMap_end_apply]
      simpa only [map_smul, Module.End.pow_apply, LinearMap.comp_apply] using
        congrArg (fun y ↦ a • y) hn

/-- An annihilating polynomial still annihilates a restriction. -/
theorem aeval_restrict_eq_zero
    (f : Module.End K V) (P : Submodule K V)
    (hP : P ∈ f.invtSubmodule) (p : K[X])
    (hzero : Polynomial.aeval f p = 0) :
    Polynomial.aeval (LinearMap.restrict f hP) p = 0 := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (aeval_restrict_intertwines f P hP p) x
  apply P.injective_subtype
  simpa [hzero] using h

/-- A nonzero split annihilator forces an eigenvalue. -/
theorem exists_hasEigenvalue_of_splits_annihilator
    [FiniteDimensional K V] [Nontrivial V]
    (f : Module.End K V) (p : K[X])
    (hp0 : p ≠ 0) (hsplit : p.Splits)
    (hann : Polynomial.aeval f p = 0) :
    ∃ μ : K, f.HasEigenvalue μ := by
  have hdiv : minpoly K f ∣ p := minpoly.dvd K f hann
  have hqsplit : (minpoly K f).Splits := hsplit.of_dvd hp0 hdiv
  have hdeg : (minpoly K f).degree ≠ 0 :=
    ne_of_gt (minpoly.degree_pos
      (Algebra.IsIntegral.isIntegral f))
  obtain ⟨μ, hμ⟩ := hqsplit.exists_eval_eq_zero hdeg
  exact ⟨μ, Module.End.hasEigenvalue_of_isRoot hμ⟩

/-- A finite commuting family with split annihilators has a common eigenvector. -/
theorem exists_common_eigenvector_of_splits_annihilators
    [FiniteDimensional K V] [Nontrivial V]
    (s : Finset ι) (f : ι → Module.End K V) (p : ι → K[X])
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, Commute (f i) (f j))
    (hp0 : ∀ i ∈ s, p i ≠ 0)
    (hsplit : ∀ i ∈ s, (p i).Splits)
    (hann : ∀ i ∈ s, Polynomial.aeval (f i) (p i) = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ i ∈ s, ∃ μ : K, f i v = μ • v := by
  classical
  induction s using Finset.induction_on generalizing V with
  | empty =>
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨v, hv, by simp⟩
  | @insert i s his ih =>
      obtain ⟨μ, hμ⟩ := exists_hasEigenvalue_of_splits_annihilator
        (f i) (p i) (hp0 i (by simp)) (hsplit i (by simp)) (hann i (by simp))
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      let E := (f i).eigenspace μ
      have hvE : v ∈ E := Module.End.mem_eigenspace_iff.mpr hv.apply_eq_smul
      let : Nontrivial E :=
        ⟨⟨⟨v, hvE⟩, 0, fun h ↦ hv.2 (congrArg Subtype.val h)⟩⟩
      have hEinv (j : ι) (hj : j ∈ s) : E ∈ (f j).invtSubmodule := by
        intro x hx
        change f j x ∈ E
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        calc
          f i (f j x) = f j (f i x) := by
            exact LinearMap.congr_fun (hcomm i (by simp) j (by simp [hj])) x
          _ = μ • f j x := by rw [hx, map_smul]
      let fE : ι → Module.End K E := fun j ↦
        if hj : j ∈ s then
          LinearMap.restrict (p := E) (q := E) (f j)
            (fun x hx ↦ hEinv j hj hx) else 0
      have hfE (j : ι) (hj : j ∈ s) :
          fE j = LinearMap.restrict (p := E) (q := E) (f j)
            (fun x hx ↦ hEinv j hj hx) := by
        simp [fE, hj]
      obtain ⟨w, hw0, hw⟩ := ih fE
        (fun a ha b hb ↦ by
          rw [hfE a ha, hfE b hb]
          exact LinearMap.restrict_commute
            (hcomm a (by simp [ha]) b (by simp [hb]))
            (hEinv a ha) (hEinv b hb))
        (fun a ha ↦ hp0 a (by simp [ha]))
        (fun a ha ↦ hsplit a (by simp [ha]))
        (fun a ha ↦ by
          rw [hfE a ha]
          exact aeval_restrict_eq_zero (f a) E (hEinv a ha) (p a)
            (hann a (by simp [ha])))
      refine ⟨(w : E), ?_, ?_⟩
      · exact fun hw ↦ hw0 (Subtype.ext hw)
      · intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact ⟨μ, Module.End.mem_eigenspace_iff.mp w.2⟩
        · obtain ⟨μ', hμ'⟩ := hw j hj
          refine ⟨μ', ?_⟩
          have := congrArg Subtype.val hμ'
          simpa [hfE j hj] using this

/-- Polynomial evaluation is compatible with transposition. -/
theorem aeval_dualMap_apply
    (f : Module.End K V) (p : K[X])
    (ell : Module.Dual K V) (x : V) :
    Polynomial.aeval f.dualMap p ell x =
      ell (Polynomial.aeval f p x) := by
  have hpow (n : ℕ) : (f.dualMap ^ n) ell x = ell ((f ^ n) x) := by
    induction n generalizing ell x with
    | zero => rfl
    | succ n hn =>
        rw [pow_succ, pow_succ]
        change (f.dualMap ^ n) (f.dualMap ell) x = ell ((f ^ n) (f x))
        calc
          _ = f.dualMap ell ((f ^ n) x) := hn (f.dualMap ell) x
          _ = ell (f ((f ^ n) x)) := rfl
          _ = ell ((f ^ n) (f x)) := by
            exact congrArg ell
              (LinearMap.congr_fun (Commute.self_pow f n).eq x)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.End.pow_apply, Module.algebraMap_end_apply, LinearMap.smul_apply,
        map_smul]
      simpa only [Module.End.pow_apply] using
        congrArg (fun y ↦ a • y) (hpow n)

/-- An annihilator of an endomorphism also annihilates its transpose. -/
theorem aeval_dualMap_eq_zero
    (f : Module.End K V) (p : K[X])
    (h : Polynomial.aeval f p = 0) :
    Polynomial.aeval f.dualMap p = 0 := by
  apply LinearMap.ext
  intro ell
  apply LinearMap.ext
  intro x
  simpa [h] using aeval_dualMap_apply f p ell x

/-- Transposes of commuting endomorphisms commute. -/
theorem dualMap_commute {f g : Module.End K V} (h : Commute f g) :
    Commute f.dualMap g.dualMap := by
  apply LinearMap.ext
  intro ell
  apply LinearMap.ext
  intro x
  change ell (g (f x)) = ell (f (g x))
  exact congrArg ell (LinearMap.congr_fun h.eq.symm x)

/-- Commuting endomorphisms with split annihilators admit a complete invariant flag. -/
theorem completeInvariantFlag_of_commute_of_splits_annihilators
    [Finite ι] [FiniteDimensional K V]
    (f : ι → Module.End K V) (p : ι → K[X])
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hp0 : ∀ i, p i ≠ 0)
    (hsplit : ∀ i, (p i).Splits)
    (hann : ∀ i, Polynomial.aeval (f i) (p i) = 0) :
    HasCompleteInvariantFlag f ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  generalize hn : finrank K V = n
  induction n using Nat.strongRecOn generalizing V with
  | ind n ih =>
      by_cases hn0 : n = 0
      · have hsub : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
        have htop : (⊤ : Submodule K V) = ⊥ := by
          apply le_antisymm
          · intro x _
            change x = 0
            exact Subsingleton.elim x 0
          · exact bot_le
        rw [htop]
        exact HasCompleteInvariantFlag.bot
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let : Nontrivial V := Module.nontrivial_of_finrank_pos (hn ▸ hnpos)
        let fd : ι → Module.End K (Module.Dual K V) := fun i ↦ (f i).dualMap
        obtain ⟨ell, hell0, hell⟩ :=
          exists_common_eigenvector_of_splits_annihilators
            Finset.univ fd p
            (fun i _ j _ ↦ dualMap_commute (hcomm i j))
            (fun i _ ↦ hp0 i) (fun i _ ↦ hsplit i)
            (fun i _ ↦ aeval_dualMap_eq_zero (f i) (p i) (hann i))
        let P := LinearMap.ker ell
        have hPinv : IsInvariantUnder f P := by
          intro i x hx
          change ell (f i x) = 0
          obtain ⟨μ, hμ⟩ := hell i (Finset.mem_univ i)
          have hμx := LinearMap.congr_fun hμ x
          change ell (f i x) = μ * ell x at hμx
          rw [show ell x = 0 from hx] at hμx
          simpa using hμx
        let fP : ι → Module.End K P := fun i ↦
          LinearMap.restrict (p := P) (q := P) (f i)
            (fun x hx ↦ hPinv i hx)
        have hcommP : ∀ i j, Commute (fP i) (fP j) := by
          intro i j
          exact LinearMap.restrict_commute (hcomm i j)
            (hPinv i) (hPinv j)
        have hannP : ∀ i, Polynomial.aeval (fP i) (p i) = 0 := by
          intro i
          exact aeval_restrict_eq_zero (f i) P (hPinv i) (p i) (hann i)
        have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hell0
        change finrank K P + 1 = finrank K V at hdim
        have hPn : finrank K P < n := by omega
        have hflagP : HasCompleteInvariantFlag fP ⊤ :=
          ih (finrank K P) hPn fP hcommP hannP rfl
        have hlift : HasCompleteInvariantFlag f P :=
          HasCompleteInvariantFlag.map_subtype f P hPinv hflagP
        apply HasCompleteInvariantFlag.step hlift le_top
        · simpa [P, sfinrank, hn] using hdim.symm
        · exact isInvariantUnder_top f

/-- A commuting family with split characteristic polynomials has a complete invariant flag. -/
theorem completeInvariantFlag_of_commute_of_splits_charpoly
    [Finite ι] [FiniteDimensional K V]
    (f : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hsplit : ∀ i, (f i).charpoly.Splits) :
    HasCompleteInvariantFlag f ⊤ := by
  apply completeInvariantFlag_of_commute_of_splits_annihilators
    f (fun i ↦ (f i).charpoly) hcomm
  · intro i
    exact (LinearMap.charpoly_monic (f i)).ne_zero
  · exact hsplit
  · intro i
    exact LinearMap.aeval_self_charpoly (f i)

end

end UnifiedRounding
