/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.UniversalEnvelopingExtension
import Amenability.HopfSubalgebraProjectivity

/-! # Amenability descent along projective modules -/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]

local notation "U" => UniversalEnvelopingAlgebra k L

section AlgebraicAmenability

variable {A : Type*} {Q : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- The algebraic expansion `E + F E`, stated without any coalgebraic
assumptions on the acting algebra. -/
def algebraModuleExpansion (F : Submodule k A) (E : Submodule k Q) :
    Submodule k Q :=
  E ⊔ Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E

/-- Elek amenability for a module over an arbitrary associative algebra. -/
def IsAlgebraicallyAmenableModule : Prop :=
  ∀ (F : Submodule k A), FiniteDimensional k F →
    ∀ ε : ℚ, 0 < ε →
      ∃ E : Submodule k Q,
        E ≠ ⊥ ∧ FiniteDimensional k E ∧
          (sfinrank k (algebraModuleExpansion F E) : ℚ) ≤
            (1 + ε) * sfinrank k E

end AlgebraicAmenability

section FreeModuleSupport

variable {A : Type*} {Q : Type*} {ι : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- A finite-dimensional subspace of a free `A`-module uses only finitely
many coordinates of any chosen `A`-basis. -/
theorem Basis.exists_finset_support
    (b : Basis ι A Q) (E : Submodule k Q) [FiniteDimensional k E] :
    ∃ s : Finset ι, ∀ x ∈ E, (b.repr x).support ⊆ s := by
  classical
  let e := Module.finBasis k E
  let s : Finset ι := Finset.univ.biUnion fun i =>
    (b.repr (e i : Q)).support
  refine ⟨s, ?_⟩
  intro x hx
  let xE : E := ⟨x, hx⟩
  have hxsum : ∑ i, (e.repr xE i) • (e i : Q) = x := by
    have h := congrArg E.subtype (e.sum_repr xE)
    rw [map_sum] at h
    simp only [LinearMap.map_smul_of_tower] at h
    exact h
  rw [← hxsum, map_sum]
  refine Finsupp.support_finsetSum.trans ?_
  apply Finset.biUnion_subset.2
  intro i hi
  have heq := (b.repr : Q →ₗ[A] ι →₀ A).map_smul_of_tower
    (e.repr xE i) (e i : Q)
  change (((b.repr : Q →ₗ[A] ι →₀ A)
    ((e.repr xE i) • (e i : Q))).support) ⊆ s
  rw [heq]
  exact Finsupp.support_smul.trans
    (Finset.subset_biUnion_of_mem
      (fun j => (b.repr (e j : Q)).support) (Finset.mem_univ i))

end FreeModuleSupport

section FreeModuleLayers

variable {A : Type*} {Q : Type*} {ι : Type*} [Fintype ι]
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

omit [Module A Q] [IsScalarTower k A Q] in
/-- The finite weighted-average step in the standard proof that amenability
of a free `A`-module implies amenability of `A`.  The geometric construction
of the layers is kept separate from this numerical lemma. -/
theorem exists_layer_ratio_le
    (F : Submodule k A) [FiniteDimensional k F]
    (E Eplus : Submodule k Q) [FiniteDimensional k E]
    [FiniteDimensional k Eplus] (hE : E ≠ ⊥)
    (V Vplus : ι → Submodule k A)
    (hVfd : ∀ i, FiniteDimensional k (V i))
    (hVplusfd : ∀ i, FiniteDimensional k (Vplus i))
    (hsource : ∑ i, sfinrank k (V i) = sfinrank k E)
    (htarget : ∑ i, sfinrank k (Vplus i) = sfinrank k Eplus)
    (haction : ∀ i, algebraModuleExpansion F (V i) ≤ Vplus i) :
    ∃ i, V i ≠ ⊥ ∧
      (sfinrank k (algebraModuleExpansion F (V i)) : ℚ) /
          sfinrank k (V i) ≤
        (sfinrank k Eplus : ℚ) / sfinrank k E := by
  classical
  let _ (i : ι) : FiniteDimensional k (V i) := hVfd i
  let _ (i : ι) : FiniteDimensional k (Vplus i) := hVplusfd i
  have hplus (i : ι) : FiniteDimensional k
      (algebraModuleExpansion F (V i)) := by
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k A).toLinearMap F (V i)) := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k A).toLinearMap F (V i)) := hmap
    rw [algebraModuleExpansion]
    infer_instance
  let _ (i : ι) : FiniteDimensional k
      (algebraModuleExpansion F (V i)) := hplus i
  have hmono (i : ι) :
      sfinrank k (algebraModuleExpansion F (V i)) ≤
        sfinrank k (Vplus i) :=
    Submodule.finrank_mono (haction i)
  let cert : RoundingCertificate ι := {
    w := fun _ => 1
    cDim := fun i => sfinrank k (V i)
    fcDim := fun i => sfinrank k (algebraModuleExpansion F (V i))
    dimE := sfinrank k E
    dimFE := sfinrank k Eplus
    w_nonneg := fun _ => by norm_num
    cDim_nonneg := fun _ => by positivity
    fcDim_nonneg := fun _ => by positivity
    dimE_pos := by
      let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
      exact_mod_cast Module.finrank_pos (R := k) (M := E)
    mass := by
      simp only [one_mul]
      exact_mod_cast hsource
    plus_mass := by
      have hsum : ∑ i, sfinrank k (algebraModuleExpansion F (V i)) ≤
          ∑ i, sfinrank k (Vplus i) :=
        Finset.sum_le_sum fun i _ => hmono i
      simp only [one_mul]
      exact_mod_cast hsum.trans_eq htarget }
  obtain ⟨i, _, hi, hratio⟩ := cert.exists_ratio_le
  refine ⟨i, ?_, hratio⟩
  intro hbot
  change 0 < (sfinrank k (V i) : ℚ) at hi
  rw [hbot] at hi
  simp [sfinrank] at hi

end FreeModuleLayers

section PiFlag

variable {A : Type*} [Ring A] [Algebra k A]

/-- The first `j` coordinates in the finite free module `Fin n → A`. -/
def piPrefix (n j : ℕ) : Submodule k (Fin n → A) where
  carrier := {x | ∀ i : Fin n, j ≤ i.1 → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro r x hx i hi
    simp [hx i hi]

theorem piPrefix_mono {n i j : ℕ} (hij : i ≤ j) :
    piPrefix (k := k) (A := A) n i ≤ piPrefix n j := by
  intro x hx a ha
  exact hx a (hij.trans ha)

@[simp]
theorem piPrefix_zero (n : ℕ) :
    piPrefix (k := k) (A := A) n 0 = ⊥ := by
  ext x
  simp [piPrefix, funext_iff]

@[simp]
theorem piPrefix_top (n : ℕ) :
    piPrefix (k := k) (A := A) n n = ⊤ := by
  ext x
  simp [piPrefix]

/-- Projection onto one coordinate, as a `k`-linear map. -/
def piCoordinate (n : ℕ) (i : Fin n) : (Fin n → A) →ₗ[k] A :=
  LinearMap.proj i

@[simp]
theorem piCoordinate_apply (n : ℕ) (i : Fin n) (x : Fin n → A) :
    piCoordinate (k := k) n i x = x i :=
  rfl

/-- The `i`th successive coordinate layer of a subspace of a finite free
module. -/
def piLayer {n : ℕ} (E : Submodule k (Fin n → A)) (i : Fin n) :
    Submodule k A :=
  (E ⊓ piPrefix n (i.1 + 1)).map (piCoordinate n i)

theorem mem_piPrefix_succ_and_coordinate_zero_iff
    {n : ℕ} (i : Fin n) (x : Fin n → A) :
    x ∈ piPrefix (k := k) (A := A) n (i.1 + 1) ∧ x i = 0 ↔
      x ∈ piPrefix (k := k) (A := A) n i.1 := by
  constructor
  · rintro ⟨hx, hxi⟩ a ha
    rcases ha.eq_or_lt with heq | hlt
    · have hai : a = i := Fin.ext heq.symm
      simpa [hai] using hxi
    · exact hx a (Nat.succ_le_iff.2 hlt)
  · intro hx
    exact ⟨piPrefix_mono (k := k) (A := A) (Nat.le_succ i.1) hx,
      hx i le_rfl⟩

theorem piLayer_finrank_add {n : ℕ}
    (E : Submodule k (Fin n → A)) [FiniteDimensional k E] (i : Fin n) :
    sfinrank k (E ⊓ piPrefix n i.1) + sfinrank k (piLayer E i) =
      sfinrank k (E ⊓ piPrefix n (i.1 + 1)) := by
  let S : Submodule k (Fin n → A) := E ⊓ piPrefix n i.1
  let Ssucc : Submodule k (Fin n → A) :=
    E ⊓ piPrefix n (i.1 + 1)
  have hle : S ≤ Ssucc := inf_le_inf_left E
    (piPrefix_mono (k := k) (A := A) (Nat.le_succ i.1))
  let f : Ssucc →ₗ[k] A := (piCoordinate n i).domRestrict Ssucc
  have hker : LinearMap.ker f = S.comap Ssucc.subtype := by
    ext x
    change (x : Fin n → A) i = 0 ↔ (x : Fin n → A) ∈ S
    rw [show (x : Fin n → A) ∈ S ↔
        (x : Fin n → A) ∈ piPrefix n i.1 by
      simp only [S, Submodule.mem_inf]
      exact and_iff_right x.2.1]
    constructor
    · intro hxzero
      exact (mem_piPrefix_succ_and_coordinate_zero_iff
        (k := k) (A := A) i (x : Fin n → A)).mp ⟨x.2.2, hxzero⟩
    · intro hxprefix
      exact ((mem_piPrefix_succ_and_coordinate_zero_iff
        (k := k) (A := A) i (x : Fin n → A)).mpr hxprefix).2
  have hrange : LinearMap.range f = piLayer E i := by
    change LinearMap.range ((piCoordinate n i).domRestrict Ssucc) = _
    rw [LinearMap.range_domRestrict]
    rfl
  have hkerDim : finrank k (LinearMap.ker f) = finrank k S := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange, hkerDim] at hrank
  change finrank k S + finrank k (piLayer E i) = finrank k Ssucc
  simpa [add_comm] using hrank

theorem sum_piLayer_finrank {n : ℕ}
    (E : Submodule k (Fin n → A)) [FiniteDimensional k E] :
    ∑ i : Fin n, sfinrank k (piLayer E i) = sfinrank k E := by
  classical
  let d : ℕ → ℕ := fun j => sfinrank k (E ⊓ piPrefix n j)
  let layer : ℕ → ℕ := fun j =>
    if hj : j < n then sfinrank k (piLayer E ⟨j, hj⟩) else 0
  have hd : Monotone d := by
    intro i j hij
    exact Submodule.finrank_mono
      (inf_le_inf_left E (piPrefix_mono (k := k) (A := A) hij))
  have hlayer {j : ℕ} (hj : j < n) :
      d (j + 1) - d j = layer j := by
    have hrec := piLayer_finrank_add E ⟨j, hj⟩
    apply (Nat.sub_eq_iff_eq_add' (hd (Nat.le_succ j))).2
    dsimp only [d, layer]
    rw [dite_eq_left hj]
    exact hrec.symm
  calc
    ∑ i : Fin n, sfinrank k (piLayer E i) =
        ∑ j ∈ Finset.range n, layer j := by
      simpa [layer] using
        (Fin.sum_univ_eq_sum_range layer n)
    _ = ∑ j ∈ Finset.range n, (d (j + 1) - d j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hlayer (Finset.mem_range.1 hj)).symm
    _ = d n - d 0 := Finset.sum_range_tsub hd n
    _ = sfinrank k E := by
      dsimp only [d]
      rw [piPrefix_top (k := k) (A := A), inf_top_eq,
        piPrefix_zero (k := k) (A := A), inf_bot_eq]
      simp [sfinrank]

theorem algebraModuleExpansion_piLayer_le {n : ℕ}
    (F : Submodule k A) (E : Submodule k (Fin n → A)) (i : Fin n) :
    algebraModuleExpansion F (piLayer E i) ≤
      piLayer (algebraModuleExpansion F E) i := by
  rw [algebraModuleExpansion, sup_le_iff]
  constructor
  · rintro v ⟨x, hx, rfl⟩
    exact ⟨x, ⟨(le_sup_left : E ≤ algebraModuleExpansion F E) hx.1,
      hx.2⟩, rfl⟩
  · apply Submodule.map₂_le.2
    intro a ha v hv
    rcases hv with ⟨x, hx, rfl⟩
    let y : Fin n → A := a • (x : Fin n → A)
    have hyE : y ∈ algebraModuleExpansion F E := by
      rw [algebraModuleExpansion]
      apply (le_sup_right :
        Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E ≤ _)
      exact Submodule.mem_map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap
        F E ha hx.1
    have hyPrefix : y ∈ piPrefix (k := k) (A := A) n (i.1 + 1) := by
      intro j hj
      simp [y, hx.2 j hj]
    refine ⟨y, ⟨hyE, hyPrefix⟩, ?_⟩
    rfl

/-- Amenability descends from a nonzero finite free module to its coefficient
algebra.  This is the finite-support core of the free-module observation in
the proof of the subalgebra clause of Theorem D. -/
theorem IsAlgebraicallyAmenableModule.coefficient_of_pi (n : ℕ)
    (h : IsAlgebraicallyAmenableModule
      (k := k) (A := A) (Q := Fin n → A)) :
    IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := A) := by
  intro F hF ε hε
  let _ : FiniteDimensional k F := hF
  obtain ⟨E, hE, hEfd, hEplus⟩ := h F inferInstance ε hε
  let _ : FiniteDimensional k E := hEfd
  let Eplus : Submodule k (Fin n → A) := algebraModuleExpansion F E
  have hEplusfd : FiniteDimensional k Eplus := by
    dsimp [Eplus, algebraModuleExpansion]
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E) := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E) := hmap
    exact Submodule.finiteDimensional_sup E
      (Submodule.map₂ (Algebra.lsmul k k (Fin n → A)).toLinearMap F E)
  let _ : FiniteDimensional k Eplus := hEplusfd
  have hlayerfd (i : Fin n) : FiniteDimensional k (piLayer E i) := by
    rw [piLayer]
    infer_instance
  have hlayerplusfd (i : Fin n) : FiniteDimensional k (piLayer Eplus i) := by
    rw [piLayer]
    infer_instance
  obtain ⟨i, hVi, hratio⟩ := exists_layer_ratio_le
    F E Eplus hE (piLayer E) (piLayer Eplus)
    hlayerfd hlayerplusfd (sum_piLayer_finrank E)
    (sum_piLayer_finrank Eplus) (algebraModuleExpansion_piLayer_le F E)
  let _ : FiniteDimensional k (piLayer E i) := hlayerfd i
  let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let _ : Nontrivial (piLayer E i) :=
    Submodule.nontrivial_iff_ne_bot.mpr hVi
  have hEpos : (0 : ℚ) < sfinrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hVpos : (0 : ℚ) < sfinrank k (piLayer E i) := by
    exact_mod_cast Module.finrank_pos (R := k) (M := piLayer E i)
  have hsource : (sfinrank k Eplus : ℚ) / sfinrank k E ≤ 1 + ε :=
    (div_le_iff₀ hEpos).2 hEplus
  refine ⟨piLayer E i, hVi, hlayerfd i, ?_⟩
  exact (div_le_iff₀ hVpos).1 (hratio.trans hsource)

end PiFlag

section FiniteCoordinates

variable {A : Type*} {Q : Type*} {ι : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- Restrict the coordinates of an `A`-basis to a finite set and enumerate
that set by `Fin`. -/
noncomputable def Basis.finiteCoordinates
    (b : Basis ι A Q) (s : Finset ι) :
    Q →ₗ[k] (Fin s.card → A) where
  toFun x i := b.repr x (s.equivFin.symm i)
  map_add' x y := by
    ext i
    simp
  map_smul' r x := by
    ext i
    change b.repr (r • x) (s.equivFin.symm i) =
      r • b.repr x (s.equivFin.symm i)
    exact congrArg (fun z : ι →₀ A => z (s.equivFin.symm i))
      ((b.repr : Q →ₗ[A] ι →₀ A).map_smul_of_tower r x)

theorem Basis.finiteCoordinates_smul
    (b : Basis ι A Q) (s : Finset ι) (a : A) (x : Q) :
    Basis.finiteCoordinates (k := k) b s (a • x) =
      a • Basis.finiteCoordinates (k := k) b s x := by
  ext i
  exact congrArg (fun z : ι →₀ A => z (s.equivFin.symm i))
    (b.repr.map_smul a x)

theorem Basis.finiteCoordinates_injectiveOn
    (b : Basis ι A Q) (s : Finset ι) {x y : Q}
    (hx : (b.repr x).support ⊆ s) (hy : (b.repr y).support ⊆ s)
    (hxy : Basis.finiteCoordinates (k := k) b s x =
      Basis.finiteCoordinates (k := k) b s y) :
    x = y := by
  apply b.repr.injective
  ext j
  by_cases hj : j ∈ s
  · let js : s := ⟨j, hj⟩
    have h := congrFun hxy (s.equivFin js)
    simpa [Basis.finiteCoordinates, js] using h
  · have hxzero : b.repr x j = 0 := by
      rw [← Finsupp.notMem_support_iff]
      exact fun hmem => hj (hx hmem)
    have hyzero : b.repr y j = 0 := by
      rw [← Finsupp.notMem_support_iff]
      exact fun hmem => hj (hy hmem)
    rw [hxzero, hyzero]

end FiniteCoordinates

section FreeModuleDescent

variable {A : Type*} {Q : Type*} {ι : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- The one-shot free-module coefficient extraction used in the proof that
an amenable free module has an amenable coefficient algebra. -/
theorem exists_coefficient_ratio_le_of_basis
    (b : Basis ι A Q) (F : Submodule k A) [FiniteDimensional k F]
    (E : Submodule k Q) [FiniteDimensional k E] (hE : E ≠ ⊥) :
    ∃ V : Submodule k A, V ≠ ⊥ ∧ FiniteDimensional k V ∧
      (sfinrank k (algebraModuleExpansion F V) : ℚ) / sfinrank k V ≤
        (sfinrank k (algebraModuleExpansion F E) : ℚ) / sfinrank k E := by
  classical
  let Eplus : Submodule k Q := algebraModuleExpansion F E
  have hEplusfd : FiniteDimensional k Eplus := by
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E) := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E) := hmap
    dsimp [Eplus, algebraModuleExpansion]
    exact Submodule.finiteDimensional_sup E
      (Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E)
  let _ : FiniteDimensional k Eplus := hEplusfd
  obtain ⟨s, hs⟩ := Basis.exists_finset_support (k := k) b Eplus
  let T : Q →ₗ[k] (Fin s.card → A) :=
    Basis.finiteCoordinates (k := k) b s
  have hEle : E ≤ Eplus := le_sup_left
  have hTinjEplus : Function.Injective (T.domRestrict Eplus) := by
    intro x y hxy
    apply Subtype.ext
    exact Basis.finiteCoordinates_injectiveOn (k := k) b s
      (hs x x.2) (hs y y.2) hxy
  have hTinjE : Function.Injective (T.domRestrict E) := by
    intro x y hxy
    apply Subtype.ext
    exact Basis.finiteCoordinates_injectiveOn (k := k) b s
      (hs x (hEle x.2)) (hs y (hEle y.2)) hxy
  let E' : Submodule k (Fin s.card → A) := E.map T
  let Eplus' : Submodule k (Fin s.card → A) := Eplus.map T
  have hdimE : sfinrank k E' = sfinrank k E := by
    have h := (LinearEquiv.ofInjective (T.domRestrict E) hTinjE).finrank_eq
    change finrank k E = finrank k (LinearMap.range (T.domRestrict E)) at h
    rw [LinearMap.range_domRestrict] at h
    exact h.symm
  have hdimEplus : sfinrank k Eplus' = sfinrank k Eplus := by
    have h :=
      (LinearEquiv.ofInjective (T.domRestrict Eplus) hTinjEplus).finrank_eq
    change finrank k Eplus =
      finrank k (LinearMap.range (T.domRestrict Eplus)) at h
    rw [LinearMap.range_domRestrict] at h
    exact h.symm
  have hE'fd : FiniteDimensional k E' := by
    dsimp [E']
    infer_instance
  let _ : FiniteDimensional k E' := hE'fd
  have hE' : E' ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdimE
    have hzero : sfinrank k E = 0 := by simpa [sfinrank] using hdimE.symm
    let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    exact (Nat.ne_of_gt (Module.finrank_pos (R := k) (M := E))) hzero
  let Target : Submodule k (Fin s.card → A) :=
    algebraModuleExpansion F E'
  have hTargetfd : FiniteDimensional k Target := by
    dsimp [Target, algebraModuleExpansion]
    have hmap : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin s.card → A)).toLinearMap
          F E') := by
      rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
      infer_instance
    let _ : FiniteDimensional k
        (Submodule.map₂ (Algebra.lsmul k k (Fin s.card → A)).toLinearMap
          F E') := hmap
    exact Submodule.finiteDimensional_sup E' _
  let _ : FiniteDimensional k Target := hTargetfd
  have hTarget : Target ≤ Eplus' := by
    change algebraModuleExpansion F E' ≤ Eplus'
    rw [algebraModuleExpansion, sup_le_iff]
    constructor
    · exact Submodule.map_mono hEle
    · apply Submodule.map₂_le.2
      intro a ha y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hax : a • x ∈ Eplus := by
        change a • x ∈ algebraModuleExpansion F E
        rw [algebraModuleExpansion]
        apply (le_sup_right :
          Submodule.map₂ (Algebra.lsmul k k Q).toLinearMap F E ≤ _)
        exact Submodule.mem_map₂ (Algebra.lsmul k k Q).toLinearMap F E ha hx
      refine ⟨a • x, hax, ?_⟩
      exact Basis.finiteCoordinates_smul (k := k) b s a x
  have hlayerfd (i : Fin s.card) : FiniteDimensional k (piLayer E' i) := by
    rw [piLayer]
    infer_instance
  have hlayerTargetfd (i : Fin s.card) :
      FiniteDimensional k (piLayer Target i) := by
    rw [piLayer]
    infer_instance
  obtain ⟨i, hVi, hratio⟩ := exists_layer_ratio_le
    F E' Target hE' (piLayer E') (piLayer Target)
    hlayerfd hlayerTargetfd (sum_piLayer_finrank E')
    (sum_piLayer_finrank Target) (algebraModuleExpansion_piLayer_le F E')
  have htargetDim : sfinrank k Target ≤ sfinrank k Eplus' :=
    Submodule.finrank_mono hTarget
  have htargetRatio :
      (sfinrank k Target : ℚ) / sfinrank k E' ≤
        (sfinrank k Eplus : ℚ) / sfinrank k E := by
    rw [hdimE, ← hdimEplus]
    let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
    have hEpos : (0 : ℚ) < sfinrank k E := by
      exact_mod_cast Module.finrank_pos (R := k) (M := E)
    exact (div_le_div_iff_of_pos_right hEpos).2 (by exact_mod_cast htargetDim)
  exact ⟨piLayer E' i, hVi, hlayerfd i, hratio.trans htargetRatio⟩

/-- Standard free-module observation from the proof of Theorem D: if a
nonzero free left `A`-module is algebraically amenable, then `A` is
algebraically amenable. -/
theorem IsAlgebraicallyAmenableModule.coefficient_of_basis
    (b : Basis ι A Q)
    (hQ : IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := Q)) :
    IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := A) := by
  intro F hF ε hε
  let _ : FiniteDimensional k F := hF
  obtain ⟨E, hE, hEfd, hEfolner⟩ := hQ F inferInstance ε hε
  let _ : FiniteDimensional k E := hEfd
  obtain ⟨V, hV, hVfd, hratio⟩ :=
    exists_coefficient_ratio_le_of_basis b F E hE
  let _ : FiniteDimensional k V := hVfd
  let _ : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  let _ : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  have hEpos : (0 : ℚ) < sfinrank k E := by
    exact_mod_cast Module.finrank_pos (R := k) (M := E)
  have hVpos : (0 : ℚ) < sfinrank k V := by
    exact_mod_cast Module.finrank_pos (R := k) (M := V)
  have hsource :
      (sfinrank k (algebraModuleExpansion F E) : ℚ) / sfinrank k E ≤
        1 + ε :=
    (div_le_iff₀ hEpos).2 hEfolner
  exact ⟨V, hV, hVfd, (div_le_iff₀ hVpos).1 (hratio.trans hsource)⟩

end FreeModuleDescent

section ProjectiveModuleDescent

variable {A : Type*} {Q : Type*}
variable [Ring A] [Algebra k A]
variable [AddCommGroup Q] [Module k Q] [Module A Q]
variable [IsScalarTower k A Q]

/-- Algebraic amenability descends from an amenable projective module to its
coefficient algebra. This is the projective-module Følner argument, separate
from the Takeuchi--Wigner projectivity input. -/
theorem algebraicallyAmenable_of_projective
    [Module.Projective A Q]
    (hQ : IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := Q)) :
    IsAlgebraicallyAmenableModule (k := k) (A := A) (Q := A) := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A Q)
  have hsInjective : Function.Injective s := hs.injective
  let sk : Q →ₗ[k] Q →₀ A := s.restrictScalars k
  have hfree : IsAlgebraicallyAmenableModule
      (k := k) (A := A) (Q := Q →₀ A) := by
    intro F hF ε hε
    obtain ⟨E, hE, hEfd, hratio⟩ := hQ F hF ε hε
    let E' : Submodule k (Q →₀ A) := E.map sk
    have hE' : E' ≠ ⊥ := by
      intro hbot
      apply hE
      apply le_antisymm
      · intro x hx
        have hx' : sk x ∈ E' := Submodule.mem_map_of_mem hx
        rw [hbot, Submodule.mem_bot] at hx'
        exact hsInjective (by simpa [sk] using hx')
      · exact bot_le
    have hmap : (algebraModuleExpansion F E).map sk =
        algebraModuleExpansion F E' := by
      rw [algebraModuleExpansion, algebraModuleExpansion, Submodule.map_sup]
      congr 1
      apply le_antisymm
      · apply Submodule.map_le_iff_le_comap.mpr
        apply Submodule.map₂_le.2
        intro a ha e he
        change sk (a • e) ∈
          Submodule.map₂ (Algebra.lsmul k k (Q →₀ A)).toLinearMap F E'
        rw [show sk (a • e) = a • sk e by simp [sk]]
        exact Submodule.mem_map₂ _ _ _ ha (Submodule.mem_map_of_mem he)
      · apply Submodule.map₂_le.2
        intro a ha y hy
        rcases hy with ⟨e, he, rfl⟩
        refine ⟨a • e, Submodule.mem_map₂ _ _ _ ha he, ?_⟩
        simp [sk]
    let _ : FiniteDimensional k E' := by
      dsimp [E']
      infer_instance
    have hdimE : finrank k E' = finrank k E := by
      have h := (LinearEquiv.ofInjective (sk.domRestrict E)
        (fun x y hxy => Subtype.ext (hsInjective hxy))).finrank_eq.symm
      rw [LinearMap.range_domRestrict] at h
      exact h
    have hdimExpansion :
        finrank k ((algebraModuleExpansion F E).map sk) =
          finrank k (algebraModuleExpansion F E) := by
      have h := (LinearEquiv.ofInjective
        (sk.domRestrict (algebraModuleExpansion F E))
        (fun x y hxy => Subtype.ext (hsInjective hxy))).finrank_eq.symm
      rw [LinearMap.range_domRestrict] at h
      exact h
    refine ⟨E', hE', inferInstance, ?_⟩
    rw [← hmap, sfinrank, sfinrank, hdimE, hdimExpansion]
    exact hratio
  exact hfree.coefficient_of_basis (Finsupp.basisSingleOne (R := A))

end ProjectiveModuleDescent


end
end HopfAmenability

