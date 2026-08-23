/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.TensorSemistability
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.FieldTheory.Tower

/-!
# Base change of coalgebra semistability
-/

open Module TensorProduct

namespace UnifiedRounding

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {V : Type w}
variable [Field k] [Field K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

/-- Extension of a subspace along a field extension. -/
noncomputable def baseChangeSubspace (K : Type v)
    [Field K] [Algebra k K] (P : Submodule k V) :
    Submodule K (K ⊗[k] V) :=
  LinearMap.range (P.subtype.baseChange K)

theorem baseChangeSubspace_mono {P Q : Submodule k V} (hPQ : P ≤ Q) :
    baseChangeSubspace (k := k) K P ≤ baseChangeSubspace (k := k) K Q := by
  rintro _ ⟨z, rfl⟩
  refine ⟨(Submodule.inclusion hPQ).baseChange K z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

@[simp]
theorem baseChangeSubspace_bot :
    baseChangeSubspace (k := k) K (⊥ : Submodule k V) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, rfl⟩
  change (⊥ : Submodule k V).subtype.baseChange K z = 0
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      simpa only [map_add, zero_add] using congrArg₂ (· + ·) hz hz'
  | tmul a p =>
      rcases p with ⟨p, hp⟩
      simp only [Submodule.mem_bot] at hp
      subst p
      simp

@[simp]
theorem baseChangeSubspace_top :
    baseChangeSubspace (k := k) K (⊤ : Submodule k V) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  rw [baseChangeSubspace]
  exact LinearMap.lTensor_surjective K
    (fun x => ⟨⟨x, trivial⟩, rfl⟩) z

theorem baseChangeSubspace_sup (P Q : Submodule k V) :
    baseChangeSubspace (k := k) K (P ⊔ Q) =
      baseChangeSubspace (k := k) K P ⊔
        baseChangeSubspace (k := k) K Q := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        rw [map_add]
        exact (baseChangeSubspace K P ⊔
          baseChangeSubspace K Q).add_mem hz hz'
    | tmul a x =>
        rcases Submodule.mem_sup.mp x.2 with ⟨p, hp, q, hq, hpq⟩
        change a ⊗ₜ[k] (x : V) ∈ _
        rw [← hpq, tmul_add]
        apply Submodule.add_mem
        · exact Submodule.mem_sup_left
            ⟨a ⊗ₜ[k] (⟨p, hp⟩ : P), rfl⟩
        · exact Submodule.mem_sup_right
            ⟨a ⊗ₜ[k] (⟨q, hq⟩ : Q), rfl⟩
  · exact sup_le
      (baseChangeSubspace_mono (K := K) le_sup_left)
      (baseChangeSubspace_mono (K := K) le_sup_right)

theorem sfinrank_baseChangeSubspace
    (P : Submodule k V) [FiniteDimensional k P] :
    sfinrank K (baseChangeSubspace (k := k) K P) = sfinrank k P := by
  let : Module.Free k K := Module.Free.of_divisionRing k K
  have hinj : Function.Injective (P.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap
      P.subtype P.subtype_injective
  change finrank K (LinearMap.range (P.subtype.baseChange K)) = finrank k P
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

variable [FiniteDimensional k K]

omit [FiniteDimensional k K] in
theorem restrictScalars_baseChangeSubspace (U : Submodule k V) :
    (baseChangeSubspace (k := k) K U).restrictScalars k =
      tensorSubspace (k := k) K U := by
  ext z
  constructor <;> rintro ⟨x, hx⟩
  · exact ⟨x, by simpa [LinearMap.baseChange_eq_ltensor] using hx⟩
  · exact ⟨x, by simpa [LinearMap.baseChange_eq_ltensor] using hx⟩

theorem sfinrank_restrictScalars
    (Z : Submodule K (K ⊗[k] V)) :
    sfinrank k (Z.restrictScalars k) =
      finrank k K * sfinrank K Z := by
  let : Module.Free K (Z.restrictScalars k) :=
    Module.Free.of_divisionRing K (Z.restrictScalars k)
  have hmul := Module.finrank_mul_finrank k K (Z.restrictScalars k)
  have heq :
      finrank K (Z.restrictScalars k) = finrank K Z :=
    (Z.restrictScalarsEquiv k K).finrank_eq
  change finrank k (Z.restrictScalars k) =
    finrank k K * finrank K Z
  rw [← heq]
  exact hmul.symm

omit [FiniteDimensional k K] in
theorem restrictScalars_inf
    (Z Z' : Submodule K (K ⊗[k] V)) :
    (Z ⊓ Z').restrictScalars k =
      Z.restrictScalars k ⊓ Z'.restrictScalars k :=
  Submodule.restrictScalars_inf k Z Z'

variable {C : Type w}
variable [AddCommGroup C] [Module k C] [Coalgebra k C]

omit [FiniteDimensional k K] in
/-- The scalar-extension comultiplication corresponds to the standard
right-comodule coaction after cancelling the middle scalar extension. -/
theorem cancelBaseChange_comul_eq_coaction (z : K ⊗[k] C) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange
        k K K (K ⊗[k] C) C
        (Coalgebra.comul (R := K) (A := K ⊗[k] C) z) =
      RightComodule.coaction
        (k := k) (C := C) (M := K ⊗[k] C) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp [hz, hz']
  | tmul a c =>
      rw [tensorRightComodule_coaction_tmul]
      rw [TensorProduct.comul_tmul]
      generalize hq : Coalgebra.comul (R := k) (A := C) c = q
      clear hq c
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q q' hq hq' =>
          simpa only [map_add, tmul_add] using congrArg₂ (· + ·) hq hq'
      | tmul c₁ c₂ =>
          simp [CommSemiring.comul_apply, smul_tmul', smul_eq_mul]

omit [FiniteDimensional k K] in
/-- A subcoalgebra after scalar extension is a right subcomodule after
restricting scalars to the original field. -/
theorem restrictScalars_isRightSubcomodule_of_isSubcoalgebra
    (Z : Submodule K (K ⊗[k] C))
    (hZ : IsSubcoalgebra (k := K) Z) :
    IsRightSubcomodule (k := k) (C := C) (Z.restrictScalars k) := by
  intro z hz
  rcases hZ hz with ⟨q, hq⟩
  rw [← cancelBaseChange_comul_eq_coaction z, ← hq]
  have hpure : ∀ (z₁ : Z) (y : K ⊗[k] C),
      TensorProduct.AlgebraTensorModule.cancelBaseChange
          k K K (K ⊗[k] C) C
          ((z₁ : K ⊗[k] C) ⊗ₜ[K] y) ∈
        LinearMap.range ((Z.restrictScalars k).subtype.rTensor C) := by
    intro z₁ y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add y y' hy hy' =>
        rw [tmul_add, map_add]
        exact (LinearMap.range
          ((Z.restrictScalars k).subtype.rTensor C)).add_mem hy hy'
    | tmul a c =>
        refine ⟨(⟨a • z₁, Z.smul_mem a z₁.2⟩ :
            Z.restrictScalars k) ⊗ₜ[k] c, ?_⟩
        simp
  clear hq
  induction q using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add q q' hq hq' =>
      rw [map_add, map_add]
      exact (LinearMap.range
        ((Z.restrictScalars k).subtype.rTensor C)).add_mem hq hq'
  | tmul z₁ z₂ => exact hpure z₁ z₂

omit [FiniteDimensional k K] in
/-- Scalar extension carries subcoalgebras to subcoalgebras. -/
theorem isSubcoalgebra_baseChangeSubspace
    (P : Submodule k C) (hP : IsSubcoalgebra (k := k) P) :
    IsSubcoalgebra (k := K)
      (baseChangeSubspace (k := k) K P) := by
  let PK := baseChangeSubspace (k := k) K P
  let j : K ⊗[k] P →ₗ[K] PK :=
    (P.subtype.baseChange K).rangeRestrict
  intro z hz
  rcases hz with ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x x' hx hx' =>
      rw [map_add, map_add]
      exact (LinearMap.range (TensorProduct.mapIncl PK PK)).add_mem hx hx'
  | tmul a p =>
      rcases hP p.2 with ⟨q, hq⟩
      refine ⟨TensorProduct.map j j
        (TensorProduct.AlgebraTensorModule.distribBaseChange
          k K P P (a ⊗ₜ[k] q)), ?_⟩
      have hmap : ∀ q : P ⊗[k] P,
          TensorProduct.mapIncl PK PK
              (TensorProduct.map j j
                (TensorProduct.AlgebraTensorModule.distribBaseChange
                  k K P P (a ⊗ₜ[k] q))) =
            TensorProduct.AlgebraTensorModule.distribBaseChange
              k K C C
              (a ⊗ₜ[k] TensorProduct.mapIncl P P q) := by
        intro q
        induction q using TensorProduct.induction_on with
        | zero => simp
        | add q q' hq hq' =>
            simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hq hq'
        | tmul p₁ p₂ => rfl
      rw [hmap, hq]
      change _ = Coalgebra.comul (R := K) (A := K ⊗[k] C)
        (a ⊗ₜ[k] (p : C))
      rw [TensorProduct.comul_tmul]
      generalize hr : Coalgebra.comul (R := k) (A := C) (p : C) = r
      clear hr p q hq
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add r r' hr hr' =>
          simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hr hr'
      | tmul c₁ c₂ =>
          simp only [CommSemiring.comul_apply,
            TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
            AlgebraTensorModule.tensorTensorTensorComm_tmul]
          calc
            (a ⊗ₜ[k] c₁) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] c₂) =
                a • (((1 : K) ⊗ₜ[k] c₁) ⊗ₜ[K]
                  ((1 : K) ⊗ₜ[k] c₂)) := by
              rw [smul_tmul']
              congr 1
              simp [smul_tmul', smul_eq_mul]
            _ = ((1 : K) ⊗ₜ[k] c₁) ⊗ₜ[K]
                (a • ((1 : K) ⊗ₜ[k] c₂)) := by
              rw [tmul_smul]
            _ = ((1 : K) ⊗ₜ[k] c₁) ⊗ₜ[K] (a ⊗ₜ[k] c₂) := by
              congr 1
              simp [smul_tmul', smul_eq_mul]

/-- Semistability survives a finite extension of the base field. -/
theorem semistable_baseChange
    [Coalgebra.IsCocomm k C]
    [FiniteDimensional k C]
    (U : Submodule k C) (t : ℚ)
    (hsem : ∀ B : Submodule k C,
      IsSubcoalgebra (k := k) B →
      t * ((finrank k C : ℚ) - sfinrank k B) ≤
        (sfinrank k U : ℚ) - sfinrank k (U ⊓ B))
    (Z : Submodule K (K ⊗[k] C))
    (hZ : IsSubcoalgebra (k := K) Z) :
    t * ((finrank K (K ⊗[k] C) : ℚ) - sfinrank K Z) ≤
      (sfinrank K (baseChangeSubspace (k := k) K U) : ℚ) -
        sfinrank K (baseChangeSubspace (k := k) K U ⊓ Z) := by
  let UK := baseChangeSubspace (k := k) K U
  let Zk := Z.restrictScalars k
  have hZk : IsRightSubcomodule (k := k) (C := C) Zk :=
    restrictScalars_isRightSubcomodule_of_isSubcoalgebra Z hZ
  have htensor := tensor_semistable (W := K) U t hsem Zk hZk
  have hZdim :
      sfinrank k Zk = finrank k K * sfinrank K Z :=
    sfinrank_restrictScalars Z
  have hinter :
      (UK ⊓ Z).restrictScalars k =
        Zk ⊓ tensorSubspace (k := k) K U := by
    rw [restrictScalars_inf, restrictScalars_baseChangeSubspace]
    simpa [Zk] using
      (inf_comm (tensorSubspace (k := k) K U) (Z.restrictScalars k))
  have hinterDim :
      sfinrank k (Zk ⊓ tensorSubspace (k := k) K U) =
        finrank k K * sfinrank K (UK ⊓ Z) := by
    rw [← hinter]
    exact sfinrank_restrictScalars (UK ⊓ Z)
  have hCKdim : finrank K (K ⊗[k] C) = finrank k C :=
    Module.finrank_baseChange
  have hUKdim : sfinrank K UK = sfinrank k U :=
    sfinrank_baseChangeSubspace U
  rw [hZdim, hinterDim] at htensor
  simp only [Nat.cast_mul] at htensor
  let d := finrank k K
  have hdpos : (0 : ℚ) < d := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := K))
  have hfactor :
      (d : ℚ) *
          (t * ((finrank K (K ⊗[k] C) : ℚ) - sfinrank K Z)) ≤
        (d : ℚ) *
          ((sfinrank K UK : ℚ) - sfinrank K (UK ⊓ Z)) := by
    calc
      _ = t * ((d : ℚ) * finrank k C -
            (d : ℚ) * sfinrank K Z) := by rw [hCKdim]; ring
      _ ≤ (d : ℚ) * sfinrank k U -
            (d : ℚ) * sfinrank K (UK ⊓ Z) := htensor
      _ = _ := by rw [hUKdim]; ring
  change t * ((finrank K (K ⊗[k] C) : ℚ) - sfinrank K Z) ≤
    (sfinrank K UK : ℚ) - sfinrank K (UK ⊓ Z)
  exact le_of_mul_le_mul_left hfactor hdpos

end

end UnifiedRounding
