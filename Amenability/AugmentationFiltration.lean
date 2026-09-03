/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.HopfAmenability

/-! # Structural lemmas for the augmentation filtration -/

open Coalgebra Module TensorProduct

namespace HopfAmenability

noncomputable section

universe u v w

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]

/-- Multiplication respects powers of the augmentation ideal. -/
theorem augmentationFiltration_mul_le (i j : ℕ) :
    augmentationFiltration (k := k) (H := H) i *
        augmentationFiltration (k := k) (H := H) j ≤
      augmentationFiltration (k := k) (H := H) (i + j) := by
  let _ : (augmentationIdeal (k := k) (H := H)).IsTwoSided := by
    dsimp [augmentationIdeal]
    infer_instance
  apply Submodule.mul_le.2
  intro x hx y hy
  change x ∈ augmentationIdeal (k := k) (H := H) ^ i at hx
  change y ∈ augmentationIdeal (k := k) (H := H) ^ j at hy
  change x * y ∈ augmentationIdeal (k := k) (H := H) ^ (i + j)
  rw [Ideal.IsTwoSided.pow_add]
  exact Ideal.mul_mem_mul hx hy

/-- The zeroth augmentation-filtration term is the whole Hopf algebra. -/
theorem augmentationFiltration_zero :
    augmentationFiltration (k := k) (H := H) 0 = ⊤ := by
  apply top_unique
  intro x _hx
  change x ∈ augmentationIdeal (k := k) (H := H) ^ 0
  rw [Submodule.pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

/-- For the regular module, the module augmentation filtration is exactly
the augmentation-ideal filtration. -/
theorem regular_augmentationModuleFiltration_eq (n : ℕ) :
    augmentationModuleFiltration (k := k) (H := H) (M := H) n =
      augmentationFiltration (k := k) (H := H) n := by
  apply le_antisymm
  · rw [augmentationModuleFiltration, actionSubspace_eq_map₂]
    apply Submodule.map₂_le.2
    intro a ha b _hb
    let _ : (augmentationIdeal (k := k) (H := H)).IsTwoSided := by
      dsimp [augmentationIdeal]
      infer_instance
    change a * b ∈ augmentationIdeal (k := k) (H := H) ^ n
    exact Ideal.mul_mem_right b _ ha
  · intro a ha
    change a ∈ actionSubspace
      (augmentationFiltration (k := k) (H := H) n) (⊤ : Submodule k H)
    simpa using product_mem_actionSubspace ha (Submodule.mem_top : (1 : H) ∈ (⊤ : Submodule k H))

/-- The Hopf action respects the augmentation module filtration. -/
theorem augmentationFiltration_action_le
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] (i j : ℕ) :
    actionSubspace (augmentationFiltration (k := k) (H := H) i)
        (augmentationModuleFiltration (k := k) (H := H) (M := M) j) ≤
      augmentationModuleFiltration (k := k) (H := H) (M := M) (i + j) := by
  rw [actionSubspace_eq_map₂]
  apply Submodule.map₂_le.2
  intro h hh m hm
  rcases hm with ⟨z, rfl⟩
  induction z with
  | zero => simp
  | add x y hx hy => simpa [smul_add] using Submodule.add_mem _ hx hy
  | tmul a x =>
      change h • ((a : H) • (x : M)) ∈ _
      rw [← mul_smul]
      apply product_mem_actionSubspace
      · exact augmentationFiltration_mul_le i j
          (Submodule.mul_mem_mul hh a.property)
      · exact Submodule.mem_top

/-- The infinite intersection used in the separated augmentation quotient. -/
def augmentationInfinity
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] : Submodule k M :=
  ⨅ n, augmentationModuleFiltration (k := k) (H := H) (M := M) n

/-- The augmentation intersection is stable under the original Hopf
action. -/
theorem augmentationInfinity_stable
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M]
    (h : H) (x : M) (hx : x ∈ augmentationInfinity (k := k) (H := H)) :
    h • x ∈ augmentationInfinity (k := k) (H := H) :=
  augmentationModuleFiltration_iInf_stable h x hx

/-- The counit vanishes on the augmentation intersection. -/
theorem augmentationInfinity_counit
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    (x : M) (hx : x ∈ augmentationInfinity (k := k) (H := H)) :
    Coalgebra.counit (R := k) x = 0 :=
  augmentationModuleFiltration_iInf_counit x hx

/-- The coproduct of an augmentation-ideal element lies in the sum of the
two tensor kernels.  This is the degree-one input for the filtered
comultiplication proof. -/
theorem comul_mem_augmentationKernel_tensor_sum
    (x : H) (hx : x ∈ augmentationFiltration (k := k) (H := H) 1) :
    Coalgebra.comul (R := k) x ∈
      LinearMap.range
          ((LinearMap.ker (Coalgebra.counit (R := k) (A := H))).subtype.lTensor H) ⊔
        LinearMap.range
          ((LinearMap.ker (Coalgebra.counit (R := k) (A := H))).subtype.rTensor H) := by
  let ε := Coalgebra.counit (R := k) (A := H)
  have hsurj : Function.Surjective ε := by
    intro r
    refine ⟨r • (1 : H), ?_⟩
    simp [ε]
  have hexact : Function.Exact (LinearMap.ker ε).subtype ε :=
    LinearMap.exact_subtype_ker_map ε
  have hker := TensorProduct.map_ker hexact hsurj hexact hsurj
  rw [← hker]
  change TensorProduct.map ε ε (Coalgebra.comul (R := k) x) = 0
  have hxε : ε x = 0 := by
    change x ∈ LinearMap.ker ε
    rw [show LinearMap.ker ε = augmentationFiltration
        (k := k) (H := H) 1 by
      ext y
      simp [ε, augmentationFiltration, augmentationIdeal,
        Submodule.pow_one]]
    exact hx
  rw [← LinearMap.lTensor_comp_rTensor H ε ε]
  change (ε.lTensor k) (ε.rTensor H (Coalgebra.comul (R := k) x)) = 0
  rw [Coalgebra.rTensor_counit_comul]
  simp [hxε]

/-- The degree-one coproduct estimate for the augmentation filtration. -/
theorem augmentationFiltration_comul_one
    (x : H) (hx : x ∈ augmentationFiltration (k := k) (H := H) 1) :
    Coalgebra.comul (R := k) x ∈
      tensorFiltration (k := k)
        (augmentationFiltration (k := k) (H := H)) 1 := by
  let ε := Coalgebra.counit (R := k) (A := H)
  have hker : LinearMap.ker ε =
      augmentationFiltration (k := k) (H := H) 1 := by
    ext y
    simp [ε, augmentationFiltration, augmentationIdeal,
      Submodule.pow_one]
  have hsum := comul_mem_augmentationKernel_tensor_sum x hx
  apply (show
      LinearMap.range ((LinearMap.ker ε).subtype.lTensor H) ⊔
          LinearMap.range ((LinearMap.ker ε).subtype.rTensor H) ≤
        tensorFiltration (k := k)
          (augmentationFiltration (k := k) (H := H)) 1 by
    apply sup_le
    · rintro _ ⟨z, rfl⟩
      induction z with
      | zero => simp
      | add z z' hz hz' => simpa using Submodule.add_mem _ hz hz'
      | tmul h a =>
          apply (le_iSup (fun i : Fin 2 => LinearMap.range
            (TensorProduct.mapIncl
              (augmentationFiltration (k := k) (H := H) i)
              (augmentationFiltration (k := k) (H := H) (1 - i))))
              ⟨0, by omega⟩)
          refine ⟨⟨h, ?_⟩ ⊗ₜ[k] ⟨a, ?_⟩, rfl⟩
          · rw [augmentationFiltration_zero]
            exact Submodule.mem_top
          · change (a : H) ∈ augmentationFiltration (k := k) (H := H) 1
            rw [← hker]
            exact a.property
    · rintro _ ⟨z, rfl⟩
      induction z with
      | zero => simp
      | add z z' hz hz' => simpa using Submodule.add_mem _ hz hz'
      | tmul a h =>
          apply (le_iSup (fun i : Fin 2 => LinearMap.range
            (TensorProduct.mapIncl
              (augmentationFiltration (k := k) (H := H) i)
              (augmentationFiltration (k := k) (H := H) (1 - i))))
              ⟨1, by omega⟩)
          refine ⟨⟨a, ?_⟩ ⊗ₜ[k] ⟨h, ?_⟩, rfl⟩
          · rw [← hker]
            exact a.property
          · change h ∈ augmentationFiltration (k := k) (H := H) 0
            rw [augmentationFiltration_zero]
            exact Submodule.mem_top) hsum

/-- Multiplication respects the tensor filtration whenever it respects the
underlying descending filtration. -/
theorem tensorFiltration_mul_le
    (W : ℕ → Submodule k H)
    (hWmul : ∀ i j, W i * W j ≤ W (i + j)) (m n : ℕ) :
    tensorFiltration (k := k) W m * tensorFiltration (k := k) W n ≤
      tensorFiltration (k := k) W (m + n) := by
  rw [tensorFiltration, tensorFiltration, tensorFiltration,
    Submodule.iSup_mul]
  apply iSup_le
  intro i
  rw [Submodule.mul_iSup]
  apply iSup_le
  intro j
  apply Submodule.mul_le.2
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  induction x with
  | zero => simp
  | add x x' hx hx' => simpa [add_mul] using Submodule.add_mem _ hx hx'
  | tmul a b =>
      induction y with
      | zero => simp
      | add y y' hy hy' => simpa [mul_add] using Submodule.add_mem _ hy hy'
      | tmul c d =>
          let r : Fin (m + n + 1) :=
            ⟨(i : ℕ) + (j : ℕ), by omega⟩
          apply (le_iSup (fun s : Fin (m + n + 1) => LinearMap.range
            (TensorProduct.mapIncl (W s) (W (m + n - s)))) r)
          refine ⟨⟨(a : H) * (c : H), ?_⟩ ⊗ₜ[k]
              ⟨(b : H) * (d : H), ?_⟩, ?_⟩
          · exact hWmul i j (Submodule.mul_mem_mul a.property c.property)
          · have hdeg : (m - (i : ℕ)) + (n - (j : ℕ)) =
                m + n - ((i : ℕ) + (j : ℕ)) := by omega
            rw [← hdeg]
            exact hWmul _ _ (Submodule.mul_mem_mul b.property d.property)
          · simp [TensorProduct.mapIncl, Algebra.TensorProduct.tmul_mul_tmul]

/-- Comultiplication respects every term of the augmentation filtration. -/
theorem augmentationFiltration_comul
    (n : ℕ) (x : H)
    (hx : x ∈ augmentationFiltration (k := k) (H := H) n) :
    Coalgebra.comul (R := k) x ∈
      tensorFiltration (k := k)
        (augmentationFiltration (k := k) (H := H)) n := by
  induction n generalizing x with
  | zero =>
      rw [tensorFiltration]
      induction Coalgebra.comul (R := k) x with
      | zero => simp
      | add z z' hz hz' => simpa using Submodule.add_mem _ hz hz'
      | tmul a b =>
          apply (le_iSup (fun i : Fin 1 => LinearMap.range
            (TensorProduct.mapIncl
              (augmentationFiltration (k := k) (H := H) i)
              (augmentationFiltration (k := k) (H := H) (0 - i))))
              ⟨0, by omega⟩)
          refine ⟨⟨a, ?_⟩ ⊗ₜ[k] ⟨b, ?_⟩, rfl⟩
          · rw [augmentationFiltration_zero]
            exact Submodule.mem_top
          · change b ∈ augmentationFiltration (k := k) (H := H) 0
            rw [augmentationFiltration_zero]
            exact Submodule.mem_top
  | succ n ih =>
      let _ : (augmentationIdeal (k := k) (H := H)).IsTwoSided := by
        dsimp [augmentationIdeal]
        infer_instance
      have hx' : x ∈
          augmentationIdeal (k := k) (H := H) *
            augmentationIdeal (k := k) (H := H) ^ n := by
        change x ∈ augmentationIdeal (k := k) (H := H) ^ (n + 1) at hx
        rwa [Ideal.IsTwoSided.pow_succ] at hx
      refine Submodule.mul_induction_on
        (C := fun y => Coalgebra.comul (R := k) y ∈
          tensorFiltration (k := k)
            (augmentationFiltration (k := k) (H := H)) (n + 1))
        hx' ?_ ?_
      · intro a ha b hb
        rw [show Coalgebra.comul (R := k) (a * b) =
            Coalgebra.comul (R := k) a * Coalgebra.comul (R := k) b by
          exact map_mul (Bialgebra.comulAlgHom k H) a b]
        have haC : Coalgebra.comul (R := k) a ∈
            tensorFiltration (k := k)
              (augmentationFiltration (k := k) (H := H)) 1 := by
          apply augmentationFiltration_comul_one a
          simpa [augmentationFiltration, Submodule.pow_one] using ha
        have hbC := ih b hb
        have hprod := tensorFiltration_mul_le
          (augmentationFiltration (k := k) (H := H))
          augmentationFiltration_mul_le 1 n
          (Submodule.mul_mem_mul haC hbC)
        simpa [Nat.add_comm] using hprod
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb

/-- The antipode preserves every augmentation-filtration term. -/
theorem augmentationFiltration_antipode
    (n : ℕ) (x : H)
    (hx : x ∈ augmentationFiltration (k := k) (H := H) n) :
    HopfAlgebra.antipode k x ∈
      augmentationFiltration (k := k) (H := H) n := by
  induction n generalizing x with
  | zero =>
      rw [augmentationFiltration_zero]
      exact Submodule.mem_top
  | succ n ih =>
      let _ : (augmentationIdeal (k := k) (H := H)).IsTwoSided := by
        dsimp [augmentationIdeal]
        infer_instance
      have hx' : x ∈
          augmentationIdeal (k := k) (H := H) *
            augmentationIdeal (k := k) (H := H) ^ n := by
        change x ∈ augmentationIdeal (k := k) (H := H) ^ (n + 1) at hx
        rwa [Ideal.IsTwoSided.pow_succ] at hx
      refine Submodule.mul_induction_on
        (C := fun y => HopfAlgebra.antipode k y ∈
          augmentationFiltration (k := k) (H := H) (n + 1))
        hx' ?_ ?_
      · intro a ha b hb
        rw [HopfAlgebra.antipode_mul_antidistrib]
        have haS : HopfAlgebra.antipode k a ∈
            augmentationIdeal (k := k) (H := H) := by
          change Coalgebra.counit (R := k) (HopfAlgebra.antipode k a) = 0
          rw [HopfAlgebra.counit_antipode]
          exact ha
        have hbS : HopfAlgebra.antipode k b ∈
            augmentationIdeal (k := k) (H := H) ^ n := by
          exact ih b hb
        change HopfAlgebra.antipode k b * HopfAlgebra.antipode k a ∈
          augmentationIdeal (k := k) (H := H) ^ (n + 1)
        rw [show n + 1 = n + 1 by rfl,
          Ideal.IsTwoSided.pow_add]
        simpa [Submodule.pow_one] using Ideal.mul_mem_mul hbS haS
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb

/-- A filtered coproduct element acts diagonally into the corresponding
tensor filtration of the module. -/
theorem diagonalAction_mem_augmentationTensorFiltration
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M]
    (n : ℕ) (dh : H ⊗[k] H)
    (hdh : dh ∈ tensorFiltration (k := k)
      (augmentationFiltration (k := k) (H := H)) n)
    (dm : M ⊗[k] M) :
    TensorProduct.map
        (hopfModuleAction (k := k) (H := H) (M := M))
        (hopfModuleAction (k := k) (H := H) (M := M))
      (TensorProduct.tensorTensorTensorComm k H H M M (dh ⊗ₜ[k] dm)) ∈
        tensorFiltration (k := k)
          (augmentationModuleFiltration (k := k) (H := H) (M := M)) n := by
  let Φ : (H ⊗[k] H) →ₗ[k] (M ⊗[k] M) :=
    (TensorProduct.map
      (hopfModuleAction (k := k) (H := H) (M := M))
      (hopfModuleAction (k := k) (H := H) (M := M))).comp
    ((TensorProduct.tensorTensorTensorComm k H H M M).toLinearMap.comp
      ((TensorProduct.mk k (H ⊗[k] H) (M ⊗[k] M)).flip dm))
  change Φ dh ∈ _
  rw [tensorFiltration] at hdh ⊢
  refine Submodule.iSup_induction (fun i : Fin (n + 1) => LinearMap.range
    (TensorProduct.mapIncl
      (augmentationFiltration (k := k) (H := H) i)
      (augmentationFiltration (k := k) (H := H) (n - i))))
      (motive := fun dh => Φ dh ∈ ⨆ i : Fin (n + 1), LinearMap.range
        (TensorProduct.mapIncl
          (augmentationModuleFiltration (k := k) (H := H) (M := M) i)
          (augmentationModuleFiltration
            (k := k) (H := H) (M := M) (n - i)))) hdh ?_ ?_ ?_
  · intro i dh hdi
    rcases hdi with ⟨z, rfl⟩
    induction z with
    | zero => simp [Φ]
    | add z z' hz hz' => simpa using Submodule.add_mem _ hz hz'
    | tmul h₁ h₂ =>
        induction dm using TensorProduct.induction_on with
        | zero => simp [Φ]
        | add dm dm' hdm hdm' =>
            simpa [Φ, tmul_add, map_add] using Submodule.add_mem _ hdm hdm'
        | tmul m₁ m₂ =>
            apply (le_iSup (fun j : Fin (n + 1) => LinearMap.range
              (TensorProduct.mapIncl
                (augmentationModuleFiltration
                  (k := k) (H := H) (M := M) j)
                (augmentationModuleFiltration
                  (k := k) (H := H) (M := M) (n - j)))) i)
            refine ⟨⟨(h₁ : H) • m₁, ?_⟩ ⊗ₜ[k]
                ⟨(h₂ : H) • m₂, ?_⟩, ?_⟩
            · exact product_mem_actionSubspace h₁.property Submodule.mem_top
            · exact product_mem_actionSubspace h₂.property Submodule.mem_top
            · simp [Φ, TensorProduct.mapIncl,
                TensorProduct.tensorTensorTensorComm_tmul,
                hopfModuleAction_tmul]
  · simp
  · intro dh dh' hdh hdh'
    simpa [add_tmul, map_add] using Submodule.add_mem _ hdh hdh'

set_option maxHeartbeats 800000 in
-- The nested tensor-product inductions normalize four filtered factors.
/-- Comultiplication respects the augmentation filtration of every Hopf
module coalgebra. -/
theorem augmentationModuleFiltration_comul
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    (n : ℕ) (x : M)
    (hx : x ∈ augmentationModuleFiltration
      (k := k) (H := H) (M := M) n) :
    Coalgebra.comul (R := k) x ∈
      tensorFiltration (k := k)
        (augmentationModuleFiltration (k := k) (H := H) (M := M)) n := by
  rcases hx with ⟨z, rfl⟩
  induction z with
  | zero => simp
  | add z z' hz hz' => simpa [map_add] using Submodule.add_mem _ hz hz'
  | tmul h m =>
      change Coalgebra.comul (R := k) ((h : H) • (m : M)) ∈ _
      rw [comul_smul, TensorProduct.comul_tmul]
      have hh := augmentationFiltration_comul
        (k := k) (H := H) n (h : H) h.property
      exact diagonalAction_mem_augmentationTensorFiltration
        (k := k) (H := H) (M := M) n
        (Coalgebra.comul (R := k) (h : H))
        hh
        (Coalgebra.comul (R := k) (m : M))

/-- The augmentation intersection is canonically an `H`-stable coideal. -/
theorem augmentationInfinity_isCoideal
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M] :
    (augmentationInfinity (k := k) (H := H) (M := M)).IsCoideal := by
  exact iInf_isCoideal_of_coalgebraFiltration _
    (augmentationModuleFiltration_antitone (k := k) (H := H) (M := M))
    (augmentationModuleFiltration_zero (k := k) (H := H) (M := M))
    (augmentationModuleFiltration_counit_one (k := k) (H := H) (M := M))
    (augmentationModuleFiltration_comul (k := k) (H := H) (M := M))

/-- The augmentation intersection as an `H`-submodule. -/
def augmentationInfinityHSubmodule
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] : Submodule H M where
  carrier := augmentationInfinity (k := k) (H := H) (M := M)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' h _ hx := augmentationInfinity_stable h _ hx

/-- The canonical separated quotient by the infinite augmentation
intersection. -/
abbrev AugmentationSeparatedModule
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :=
  M ⧸ augmentationInfinity (k := k) (H := H) (M := M)

noncomputable instance augmentationSeparatedCoalgebra
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M] :
    Coalgebra k (AugmentationSeparatedModule (k := k) (H := H) (M := M)) := by
  let I := augmentationInfinity (k := k) (H := H) (M := M)
  let _ : I.IsCoideal := augmentationInfinity_isCoideal
  infer_instance

/-- The descended regular action on the separated quotient. -/
noncomputable def augmentationSeparatedRepresentation
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :
    H →+* Module.End k
      (AugmentationSeparatedModule (k := k) (H := H) (M := M)) where
  toFun h := Submodule.mapQ _ _
    ((Algebra.lsmul k k M).toLinearMap h) (by
      intro x hx
      exact augmentationInfinity_stable h x hx)
  map_one' := by ext; simp
  map_mul' h h' := by ext; simp
  map_zero' := by ext; simp
  map_add' h h' := by ext; simp

noncomputable instance augmentationSeparatedModule
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :
    Module H (AugmentationSeparatedModule (k := k) (H := H) (M := M)) :=
  Module.compHom _
    (augmentationSeparatedRepresentation (k := k) (H := H) (M := M))

noncomputable instance augmentationSeparatedIsScalarTower
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] :
    IsScalarTower k H
      (AugmentationSeparatedModule (k := k) (H := H) (M := M)) :=
  IsScalarTower.of_algebraMap_smul (fun r x => by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk
          ((algebraMap k H r) • x) = r • Submodule.Quotient.mk x
        rw [IsScalarTower.algebraMap_smul H r x]
        rfl)

noncomputable instance augmentationSeparatedIsHopfModuleCoalgebra
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M] :
    IsHopfModuleCoalgebra k H
      (AugmentationSeparatedModule (k := k) (H := H) (M := M)) where
  counit_action := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) hz hz'
    | tmul h q =>
        induction q using Submodule.Quotient.induction_on with
        | _ m =>
            change Coalgebra.counit (R := k)
                (Submodule.Quotient.mk (p := augmentationInfinity
                  (k := k) (H := H) (M := M)) (h • m)) = _
            rw [Coalgebra.Quotient.counit_mk, counit_smul]
            exact mul_comm _ _
  comul_action := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) hz hz'
    | tmul h q =>
        induction q using Submodule.Quotient.induction_on with
        | _ m =>
            change TensorProduct.map
                (augmentationInfinity (k := k) (H := H) (M := M)).mkQ
                (augmentationInfinity (k := k) (H := H) (M := M)).mkQ
                (Coalgebra.comul (R := k) (h • m)) =
              TensorProduct.map
                (hopfModuleAction (k := k) (H := H)
                  (M := AugmentationSeparatedModule
                    (k := k) (H := H) (M := M)))
                (hopfModuleAction (k := k) (H := H)
                  (M := AugmentationSeparatedModule
                    (k := k) (H := H) (M := M)))
                (TensorProduct.tensorTensorTensorComm k H H
                  (AugmentationSeparatedModule (k := k) (H := H) (M := M))
                  (AugmentationSeparatedModule (k := k) (H := H) (M := M))
                  (Coalgebra.comul (R := k) h ⊗ₜ[k]
                    TensorProduct.map
                      (augmentationInfinity (k := k) (H := H) (M := M)).mkQ
                      (augmentationInfinity (k := k) (H := H) (M := M)).mkQ
                      (Coalgebra.comul (R := k) m)))
            rw [comul_smul]
            rw [TensorProduct.comul_tmul]
            generalize hh : Coalgebra.comul (R := k) (A := H) h = dh
            generalize hm : Coalgebra.comul (R := k) (A := M) m = dm
            clear hh hm h m
            induction dh using TensorProduct.induction_on with
            | zero => simp
            | add dh dh' hdh hdh' =>
                simpa only [add_tmul, map_add] using
                  congrArg₂ (fun a b => a + b) hdh hdh'
            | tmul h₁ h₂ =>
                induction dm using TensorProduct.induction_on with
                | zero => simp
                | add dm dm' hdm hdm' =>
                    simpa only [tmul_add, map_add] using
                      congrArg₂ (fun a b => a + b) hdm hdm'
                | tmul m₁ m₂ =>
                    change Submodule.Quotient.mk (h₁ • m₁) ⊗ₜ[k]
                        Submodule.Quotient.mk (h₂ • m₂) =
                      (h₁ • Submodule.Quotient.mk m₁) ⊗ₜ[k]
                        (h₂ • Submodule.Quotient.mk m₂)
                    rfl

/-- The canonical equivariant coalgebra quotient onto the separated
module. -/
noncomputable def augmentationSeparatedQuotient
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M] :
    M →ₗc[k]
      AugmentationSeparatedModule (k := k) (H := H) (M := M) := by
  let I := augmentationInfinity (k := k) (H := H) (M := M)
  let _ : I.IsCoideal := augmentationInfinity_isCoideal
  exact Coalgebra.Quotient.mkQCoalgHom (R := k) I

theorem augmentationSeparatedQuotient_equivariant
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M] :
    IsHopfModuleMap (H := H)
      (augmentationSeparatedQuotient
        (k := k) (H := H) (M := M)).toLinearMap := by
  intro h m
  change Submodule.Quotient.mk (h • m) =
    h • Submodule.Quotient.mk m
  rfl

theorem augmentationSeparatedQuotient_surjective
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M] :
    Function.Surjective
      (augmentationSeparatedQuotient (k := k) (H := H) (M := M)) :=
  by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      (augmentationInfinity (k := k) (H := H) (M := M)) q
    exact ⟨x, rfl⟩

theorem augmentationSeparatedQuotient_ker
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M] :
    LinearMap.ker
        (augmentationSeparatedQuotient
          (k := k) (H := H) (M := M)).toLinearMap =
      augmentationInfinity (k := k) (H := H) (M := M) :=
  by
    ext x
    change (Submodule.Quotient.mk x = 0) ↔
      x ∈ augmentationInfinity (k := k) (H := H) (M := M)
    exact Submodule.Quotient.mk_eq_zero _

/-- Amenability descends canonically to the separated augmentation
quotient. -/
theorem IsAmenableHopfModuleCoalgebra.augmentationSeparated
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M]
    [IsScalarTower k H M] [Coalgebra k M] [IsHopfModuleCoalgebra k H M]
    [Coalgebra.IsCocomm k H]
    (hM : IsAmenableHopfModuleCoalgebra (k := k) (H := H) (M := M)) :
    IsAmenableHopfModuleCoalgebra
      (k := k) (H := H)
      (M := AugmentationSeparatedModule (k := k) (H := H) (M := M)) :=
  hM.of_surjective_coalgHom
    (augmentationSeparatedQuotient (k := k) (H := H) (M := M))
    (augmentationSeparatedQuotient_equivariant (k := k) (H := H) (M := M))
    (augmentationSeparatedQuotient_surjective (k := k) (H := H) (M := M))

end

end HopfAmenability
