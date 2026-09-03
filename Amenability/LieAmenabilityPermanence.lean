/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.TheoremD
import Amenability.TheoremB
import Amenability.UniversalEnvelopingExtension
import Amenability.UniversalEnvelopingGrowth
import Amenability.SubexponentialGrowth

/-! # Reusable permanence lemmas for amenable Lie algebras -/

open Coalgebra Module TensorProduct
namespace HopfAmenability
noncomputable section
universe u v w
variable {k : Type u} {L : Type v}
variable [Field k] [LieRing L] [LieAlgebra k L]
local notation "U" => UniversalEnvelopingAlgebra k L

section AssociativeLieInstance

attribute [local instance 100] LieRing.ofAssociativeRing

theorem algebraModuleExpansion_eq_actionExpansion
    (F E : Submodule k U) :
    algebraModuleExpansion F E = actionExpansion F E := by
  rw [algebraModuleExpansion, actionExpansion, actionSubspace_eq_map₂]

/-- The manuscript definition of Lie amenability is equivalent, by the
generator test, to Elek's associative-module condition on `U(L)`. -/
theorem isAmenableLieAlgebra_iff_algebraicallyAmenableModule :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAlgebraicallyAmenableModule (k := k) (A := U) (Q := U) := by
  constructor
  · intro h F hF ε hε
    have hregular := isAmenableLieAlgebra_iff_regularActionFolner.mp h
    obtain ⟨E, hE, hEfd, hratio⟩ := hregular F hF ε hε
    exact ⟨E, hE, hEfd, by
      rwa [algebraModuleExpansion_eq_actionExpansion]⟩
  · intro h
    apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
    intro F hF ε hε
    obtain ⟨E, hE, hEfd, hratio⟩ := h F hF ε hε
    exact ⟨E, hE, hEfd, by
      rwa [algebraModuleExpansion_eq_actionExpansion] at hratio⟩


/-- The subalgebra argument of Theorem D, with the exact relative-freeness
conclusion of PBW made explicit. -/
theorem isAmenableLieAlgebra_of_map_basis
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) {ι : Type*}
    (b : UniversalEnvelopingAlgebra.RelativePBWBasis f ι)
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let φ : UL →ₐ[k] UQ := ueaMap f
  let _ : Module UL UQ := ueaRestrictionModule f
  let _ : IsScalarTower k UL UQ :=
    IsScalarTower.of_algebraMap_smul (fun r x => by
      change φ (algebraMap k UL r) * x = r • x
      rw [φ.commutes, Algebra.smul_def])
  change Basis ι UL UQ at b
  have hQalg : IsAlgebraicallyAmenableModule
      (k := k) (A := UQ) (Q := UQ) :=
    isAmenableLieAlgebra_iff_algebraicallyAmenableModule.mp hQ
  have hrestricted : IsAlgebraicallyAmenableModule
      (k := k) (A := UL) (Q := UQ) := by
    intro F hF ε hε
    let _ : FiniteDimensional k F := hF
    let F' : Submodule k UQ := F.map φ.toLinearMap
    let _ : FiniteDimensional k F' := by
      dsimp [F']
      infer_instance
    obtain ⟨E, hE, hEfd, hratio⟩ := hQalg F' inferInstance ε hε
    have hexpansion :
        algebraModuleExpansion (k := k) F E =
          algebraModuleExpansion (k := k) F' E := by
      rw [algebraModuleExpansion, algebraModuleExpansion]
      congr 1
      apply le_antisymm
      · apply Submodule.map₂_le.2
        intro a ha x hx
        exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap F' E
          ⟨a, ha, rfl⟩ hx
      · apply Submodule.map₂_le.2
        intro a ha x hx
        rcases ha with ⟨a, ha, rfl⟩
        exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap F E ha hx
    exact ⟨E, hE, hEfd, by rwa [hexpansion]⟩
  have hULalg :=
    IsAlgebraicallyAmenableModule.coefficient_of_basis b hrestricted
  exact isAmenableLieAlgebra_iff_algebraicallyAmenableModule.mpr hULalg




/-- Amenability of a Lie algebra is equivalent to amenability of its
universal enveloping Hopf algebra. -/
theorem isAmenableLieAlgebra_iff_isAmenableHopfAlgebra :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAmenableHopfAlgebra
        (k := k) (H := UniversalEnvelopingAlgebra k L) := by
  exact isAmenableLieAlgebra_iff_regularActionFolner.trans
    (isAmenableHopfAlgebra_iff_algebraicallyAmenable
      (k := k) (H := UniversalEnvelopingAlgebra k L)).symm


/-- Amenability transfers through an injective enveloping-algebra map for
coefficient spaces contained in its range.  This is the local step used for
directed unions. -/
theorem exists_folner_of_le_ueaMap_range
 {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (hL : IsAmenableLieAlgebra (k := k) (L := L))
    (P : Submodule k (UniversalEnvelopingAlgebra k Q))
    (hP : P ≤ LinearMap.range (ueaMap f).toLinearMap)
    (hPfd : FiniteDimensional k P) (ε : ℚ) (hε : 0 < ε) :
    ∃ E : Submodule k (UniversalEnvelopingAlgebra k Q),
      E ≠ ⊥ ∧ FiniteDimensional k E ∧
        (sfinrank k (actionExpansion P E) : ℚ) ≤
      (1 + ε) * sfinrank k E := by
  have hL := isAmenableLieAlgebra_iff_regularActionFolner.mp hL
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let φ : UL →ₗ[k] UQ := (ueaMap f).toLinearMap
  have hφ : Function.Injective φ := ueaMap_injective f hf
  let F : Submodule k UL := P.comap φ
  have hmap : F.map φ = P := by
    apply le_antisymm
    · exact Submodule.map_comap_le φ P
    · intro x hx
      obtain ⟨y, hy⟩ := hP hx
      refine ⟨y, ?_, hy⟩
      change φ y ∈ P
      rw [hy]
      exact hx
  let eFP : F ≃ₗ[k] P := LinearEquiv.ofBijective
    ((φ.domRestrict F).codRestrict P fun x => by
      rw [← hmap]
      exact Submodule.mem_map_of_mem x.2)
    ⟨fun x y hxy => Subtype.ext (hφ (congrArg Subtype.val hxy)), by
      intro x
      obtain ⟨y, hy, hxy⟩ := hmap.ge x.2
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩⟩
  let _ : FiniteDimensional k F :=
    FiniteDimensional.of_injective eFP.toLinearMap eFP.injective
  obtain ⟨E, hE, hEfd, hratio⟩ := hL F inferInstance ε hε
  let E' : Submodule k UQ := E.map φ
  have hE' : E' ≠ ⊥ := by
    intro hbot
    apply hE
    apply le_antisymm
    · intro x hx
      have : φ x ∈ E' := Submodule.mem_map_of_mem hx
      rw [hbot, Submodule.mem_bot] at this
      apply hφ
      simpa using this
    · exact bot_le
  let _ : FiniteDimensional k E' := by dsimp [E']; infer_instance
  have hexp : (actionExpansion F E).map φ = actionExpansion P E' := by
    rw [actionExpansion, actionExpansion, Submodule.map_sup]
    change E.map φ ⊔ (actionSubspace F E).map φ =
      E.map φ ⊔ actionSubspace P (E.map φ)
    congr 1
    rw [actionSubspace_eq_map₂, actionSubspace_eq_map₂]
    rw [← hmap]
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.map₂_le.2
      intro a ha x hx
      change φ (a * x) ∈ Submodule.map₂
        (Algebra.lsmul k k UQ).toLinearMap (F.map φ) (E.map φ)
      rw [show φ (a * x) = φ a * φ x from map_mul (ueaMap f) a x]
      exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap
        (F.map φ) (E.map φ) (Submodule.mem_map_of_mem ha)
        (Submodule.mem_map_of_mem hx)
    · apply Submodule.map₂_le.2
      intro a ha x hx
      rcases ha with ⟨a, ha, rfl⟩
      rcases hx with ⟨x, hx, rfl⟩
      exact ⟨a * x, Submodule.mem_map₂
        (Algebra.lsmul k k UL).toLinearMap F E ha hx, map_mul (ueaMap f) a x⟩
  refine ⟨E', hE', inferInstance, ?_⟩
  rw [← hexp]
  have hdimE := (LinearEquiv.ofInjective (φ.domRestrict E)
    (fun x y hxy => Subtype.ext (hφ hxy))).finrank_eq
  have hdimExp := (LinearEquiv.ofInjective
    (φ.domRestrict (actionExpansion F E))
    (fun x y hxy => Subtype.ext (hφ hxy))).finrank_eq
  rw [LinearMap.range_domRestrict] at hdimE hdimExp
  change (sfinrank k ((actionExpansion F E).map φ) : ℚ) ≤
    (1 + ε) * sfinrank k (E.map φ)
  simp only [sfinrank]
  rw [show Module.finrank k ((actionExpansion F E).map φ) =
      Module.finrank k (actionExpansion F E) by
        exact hdimExp.symm]
  rw [show Module.finrank k (E.map φ) = Module.finrank k E by
        exact hdimE.symm]
  exact hratio


/-- Restricting scalars along `U(f)` makes `U(Q)` a module coalgebra over
`U(L)`. -/
theorem ueaRestrictionIsHopfModuleCoalgebra {Q : Type w}
    [LieRing Q] [LieAlgebra k Q] (f : L →ₗ⁅k⁆ Q) : by
    letI : Module (UniversalEnvelopingAlgebra k L)
        (UniversalEnvelopingAlgebra k Q) := ueaRestrictionModule f
    letI : IsScalarTower k (UniversalEnvelopingAlgebra k L)
        (UniversalEnvelopingAlgebra k Q) :=
      IsScalarTower.of_algebraMap_smul (fun r q => by
        change ueaMap f (algebraMap k (UniversalEnvelopingAlgebra k L) r) * q =
          r • q
        rw [(ueaMap f).commutes, Algebra.smul_def])
    exact IsHopfModuleCoalgebra k (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) := by
  let : Module (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) := ueaRestrictionModule f
  let : IsScalarTower k (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k Q) :=
    IsScalarTower.of_algebraMap_smul (fun r q => by
      change ueaMap f (algebraMap k (UniversalEnvelopingAlgebra k L) r) * q =
        r • q
      rw [(ueaMap f).commutes, Algebra.smul_def])
  let act :
      ((UniversalEnvelopingAlgebra k L) ⊗[k]
          (UniversalEnvelopingAlgebra k Q)) →ₗc[k]
        (UniversalEnvelopingAlgebra k Q) :=
    (Bialgebra.mulCoalgHom k (UniversalEnvelopingAlgebra k Q)).comp
      (CoalgHom.tensorMapStruct (ueaMapCoalgHom f) (CoalgHom.id k _))
  have hact : hopfModuleAction (k := k)
      (H := UniversalEnvelopingAlgebra k L)
      (M := UniversalEnvelopingAlgebra k Q) = act.toLinearMap := by
    ext a q
    change ueaMap f a * q = act (a ⊗ₜ[k] q)
    simp [act]
  refine {
    counit_action := ?_
    comul_action := ?_ }
  · rw [hact]
    exact act.counit_comp
  · rw [hact]
    exact act.map_comp_comul.symm

/-- Quotient closure in Theorem D. -/
theorem IsAmenableLieAlgebra.of_surjective
    {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Surjective f)
    (hL : IsAmenableLieAlgebra (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := Q) := by
  let UL := UniversalEnvelopingAlgebra k L
  let UQ := UniversalEnvelopingAlgebra k Q
  let φ : UL →ₐ[k] UQ := ueaMap f
  let q : UL →ₗc[k] UQ := ueaMapCoalgHom f
  let : Module UL UQ := ueaRestrictionModule f
  let : IsScalarTower k UL UQ :=
    IsScalarTower.of_algebraMap_smul (fun r x => by
      change φ (algebraMap k UL r) * x = r • x
      rw [φ.commutes, Algebra.smul_def])
  let : IsHopfModuleCoalgebra k UL UQ :=
    ueaRestrictionIsHopfModuleCoalgebra f
  have hq : IsHopfModuleMap (H := UL) q.toLinearMap := by
    intro a b
    change φ (a * b) = φ a * φ b
    exact map_mul φ a b
  have hULcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := UL) (M := UL) :=
    HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra
      (isAmenableLieAlgebra_iff_regularActionFolner.mp hL)
  have hUQcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := UL) (M := UQ) :=
    IsAmenableHopfModuleCoalgebra.of_surjective_coalgHom q hq
      (by
        intro y
        obtain ⟨x, hx⟩ := ueaMap_surjective f hf y
        exact ⟨x, hx⟩) hULcoal
  have hrestricted : HasActionFolnerSubspaces
      (k := k) (H := UL) (M := UQ) :=
    hUQcoal.hasActionFolnerSubspaces
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro P hP ε hε
  let : FiniteDimensional k P := hP
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
    φ.toLinearMap (LinearMap.range_eq_top.2 (ueaMap_surjective f hf))
  let F : Submodule k UL := P.map s
  let : FiniteDimensional k F := by
    dsimp [F]
    infer_instance
  obtain ⟨E, hE, hEfd, hEfolner⟩ :=
    hrestricted F inferInstance ε hε
  have hs_apply (p : UQ) : φ (s p) = p := by
    have h := LinearMap.congr_fun hs p
    exact h
  have haction : actionSubspace F E = actionSubspace P E := by
    rw [actionSubspace_eq_map₂, actionSubspace_eq_map₂]
    apply le_antisymm
    · apply Submodule.map₂_le.2
      rintro _ ⟨p, hp, rfl⟩ e he
      change φ (s p) * e ∈ _
      rw [hs_apply]
      exact Submodule.mem_map₂ (Algebra.lsmul k k UQ).toLinearMap P E hp he
    · apply Submodule.map₂_le.2
      intro p hp e he
      have hsp : s p ∈ F := ⟨p, hp, rfl⟩
      have hmem := Submodule.mem_map₂
        (Algebra.lsmul k k UQ).toLinearMap F E hsp he
      change φ (s p) * e ∈ _ at hmem
      rwa [hs_apply] at hmem
  refine ⟨E, hE, hEfd, ?_⟩
  change (sfinrank k (E ⊔ actionSubspace P E) : ℚ) ≤
    (1 + ε) * sfinrank k E
  change (sfinrank k (E ⊔ actionSubspace F E) : ℚ) ≤
    (1 + ε) * sfinrank k E at hEfolner
  rw [haction] at hEfolner
  exact hEfolner


/-- Subalgebra closure in Theorem D, obtained from Hopf-subalgebra
permanence through the injective map of universal enveloping algebras. -/
theorem isAmenableLieAlgebra_of_injective_aux
 {Q : Type w} [LieRing Q] [LieAlgebra k Q]
    (f : L →ₗ⁅k⁆ Q) (hf : Function.Injective f)
    (hQ : IsAmenableLieAlgebra (k := k) (L := Q)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  let i : HopfSubalgebraEmbedding
      (k := k) (H := UniversalEnvelopingAlgebra k Q)
      (UniversalEnvelopingAlgebra k L) :=
    { toAlgHom := ueaMap f
      map_counit := (ueaMapCoalgHom f).counit_comp
      map_comul := (ueaMapCoalgHom f).map_comp_comul
      injective := ueaMap_injective f hf }
  apply isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mpr
  exact isAmenableHopfAlgebra_of_hopfSubalgebra i
    (isAmenableLieAlgebra_iff_isAmenableHopfAlgebra.mp hQ)


/-- The easy implication in the extension clause: amenability passes from
the middle algebra to its ideal and quotient. -/
theorem IsAmenableLieAlgebra.extension_components
 (I : LieIdeal k L)
    (hL : IsAmenableLieAlgebra (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := I) ∧
      IsAmenableLieAlgebra (k := k) (L := L ⧸ I) := by
  constructor
  · exact isAmenableLieAlgebra_of_injective_aux
      (LieSubalgebra.incl (I : LieSubalgebra k L))
      (fun x y hxy => Subtype.ext hxy) hL
  · exact hL.of_surjective (LieIdeal.quotientMkLieHom I)
      (LieIdeal.quotientMkLieHom_surjective I)

/-- Extension closure in Theorem D. -/
theorem isAmenableLieAlgebra_extension_direct
    (I : LieIdeal k L)
    (hI : IsAmenableLieAlgebra (k := k) (L := I))
    (hQ : IsAmenableLieAlgebra (k := k) (L := L ⧸ I)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  classical
  have hI := isAmenableLieAlgebra_iff_regularActionFolner.mp hI
  have hQ := isAmenableLieAlgebra_iff_regularActionFolner.mp hQ
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro F hF ε hε
  let δ : ℚ := min (ε / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδeps : 3 * δ ≤ ε := by
    have := min_le_left (ε / 3) (1 : ℚ)
    dsimp [δ]
    linarith
  have hsq : (1 + δ) ^ 2 ≤ 1 + ε := by
    nlinarith [sq_nonneg δ]
  let _ : FiniteDimensional k F := hF
  let F1 : Submodule k (UniversalEnvelopingAlgebra k L) :=
    F ⊔ Submodule.span k {1}
  let _ : FiniteDimensional k F1 := by dsimp [F1]; infer_instance
  obtain ⟨A, hF1A⟩ :=
    Coalgebra.exists_finiteSubcoalgebra_containing_submodule F1
  have hFA : F ≤ A.carrier := le_sup_left.trans hF1A
  have h1A : (1 : UniversalEnvelopingAlgebra k L) ∈ A.carrier := by
    apply hF1A
    exact (le_sup_right : Submodule.span k {1} ≤ F1)
      (Submodule.subset_span (Set.mem_singleton 1))
  let π := UniversalEnvelopingAlgebra.pbwMap
    (LieIdeal.quotientMkLieHom I)
  let G : Submodule k (UniversalEnvelopingAlgebra k (L ⧸ I)) :=
    A.carrier.map π.toLinearMap
  let _ : FiniteDimensional k G := by dsimp [G]; infer_instance
  have h1G : (1 : UniversalEnvelopingAlgebra k (L ⧸ I)) ∈ G := by
    exact ⟨1, h1A, map_one π⟩
  have hQcoal : IsAmenableHopfModuleCoalgebra
      (k := k) (H := UniversalEnvelopingAlgebra k (L ⧸ I))
      (M := UniversalEnvelopingAlgebra k (L ⧸ I)) :=
    HasActionFolnerSubspaces.isAmenableHopfModuleCoalgebra hQ
  obtain ⟨C, hC, hCratio0⟩ := hQcoal G inferInstance δ hδ
  have hCratio :
      (sfinrank k (actionSubspace G C.carrier) : ℚ) ≤
        (1 + δ) * sfinrank k C.carrier := by
    rw [actionExpansion_eq_actionSubspace_of_one_mem h1G] at hCratio0
    exact hCratio0
  let α := Module.Basis.ofVectorSpaceIndex k I
  let β := Module.Basis.ofVectorSpaceIndex k (L ⧸ I)
  let bI : Basis α k I := Module.Basis.ofVectorSpace k I
  let bQ : Basis β k (L ⧸ I) := Module.Basis.ofVectorSpace k (L ⧸ I)
  let _ : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  let _ : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨D, hDfd, hdefect⟩ :=
    LieIdeal.exists_finite_extension_defect I bQ bI A C
  let _ : FiniteDimensional k D := hDfd
  obtain ⟨K, hK, hKfd, hKratio⟩ := hI D inferInstance δ hδ
  let _ : FiniteDimensional k K := hKfd
  let CP : Submodule k (UniversalEnvelopingAlgebra k (L ⧸ I)) :=
    actionSubspace G C.carrier
  let KP : Submodule k (UniversalEnvelopingAlgebra k I) :=
    actionExpansion D K
  let _ : FiniteDimensional k CP := by
    dsimp [CP]
    exact finiteDimensional_actionSubspace _ _
  let _ : FiniteDimensional k KP := by
    dsimp [KP]
    exact finiteDimensional_actionExpansion _ _
  let E0 := tensorProductSubspace C.carrier K
  let θ := (LieIdeal.extensionPBWCoalgEquiv I bQ bI).toLinearEquiv
  let E : Submodule k (UniversalEnvelopingAlgebra k L) := E0.map θ.toLinearMap
  let Target0 := tensorProductSubspace CP KP
  let Target : Submodule k (UniversalEnvelopingAlgebra k L) :=
    Target0.map θ.toLinearMap
  let _ : FiniteDimensional k E0 := by
    dsimp [E0]
    exact finiteDimensional_tensorProductSubspace C.carrier K
  let _ : FiniteDimensional k E := by dsimp [E]; infer_instance
  let _ : FiniteDimensional k Target0 := by
    dsimp [Target0]
    exact finiteDimensional_tensorProductSubspace CP KP
  let _ : FiniteDimensional k Target := by
    dsimp [Target]
    infer_instance
  have hC_CP : C.carrier ≤ CP := by
    intro c hc
    change c ∈ actionSubspace G C.carrier
    rw [actionSubspace_eq_map₂]
    simpa using Submodule.mem_map₂
      (Algebra.lsmul k k (UniversalEnvelopingAlgebra k (L ⧸ I))).toLinearMap
      G C.carrier h1G hc
  have hK_KP : K ≤ KP := by
    exact le_sup_left
  have hETarget : E ≤ Target := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    apply (show E0 ≤ Target0 by
      exact tensorProductSubspace_mono hC_CP hK_KP)
    exact hz
  have haction : actionSubspace F E ≤ Target := by
    rw [actionSubspace_eq_map₂]
    apply Submodule.map₂_le.2
    intro f hf x hx
    rcases hx with ⟨z, hz, rfl⟩
    change z ∈ tensorProductSubspace C.carrier K at hz
    rw [tensorProductSubspace_eq_range_mapIncl] at hz
    obtain ⟨zCK, rfl⟩ := hz
    induction zCK using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
        simp only [map_add]
        exact Target.add_mem hz hz'
    | tmul c e =>
        have hprod : f * LieIdeal.ueaLinearSection I bQ bI c ∈
            actionSubspace A.carrier
              (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI)) := by
          rw [actionSubspace_eq_map₂]
          exact Submodule.mem_map₂
            (Algebra.lsmul k k (UniversalEnvelopingAlgebra k L)).toLinearMap
            A.carrier
            (C.carrier.map (LieIdeal.ueaLinearSection I bQ bI))
            (hFA hf) ⟨c, c.2, rfl⟩
        have hzD := hdefect
          (Submodule.mem_map_of_mem hprod)
        have hmul := LieIdeal.extensionPBWEquiv_symm_mul_ideal_mem
          I bQ bI CP D K
          ((LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
            (f * LieIdeal.ueaLinearSection I bQ bI c)) hzD e e.2
        have hmul0 : (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
            ((f * LieIdeal.ueaLinearSection I bQ bI c) *
              UniversalEnvelopingAlgebra.pbwMap
                (LieIdeal.inclusionLieHom I) e) ∈
            tensorProductSubspace CP (actionSubspace D K) := by
          simpa using hmul
        have hmul' : (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
            (f * LieIdeal.extensionPBWCoalgEquiv I bQ bI
              (c ⊗ₜ[k] e)) ∈ Target0 := by
          change (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
              (f * LieIdeal.extensionPBWMap I bQ bI (c ⊗ₜ[k] e)) ∈ Target0
          rw [LieIdeal.extensionPBWMap_tmul]
          rw [← mul_assoc]
          change (LieIdeal.extensionPBWCoalgEquiv I bQ bI).symm
              ((f * LieIdeal.ueaLinearSection I bQ bI c) *
                UniversalEnvelopingAlgebra.pbwMap
                  (LieIdeal.inclusionLieHom I) e) ∈
            tensorProductSubspace CP KP
          exact tensorProductSubspace_mono le_rfl
            (le_sup_right : actionSubspace D K ≤ KP) hmul0
        exact ⟨_, hmul', (LieIdeal.extensionPBWCoalgEquiv I bQ bI).apply_symm_apply _⟩
  have hexpansion : actionExpansion F E ≤ Target := by
    exact sup_le hETarget haction
  have hdimE : sfinrank k E = sfinrank k C.carrier * sfinrank k K := by
    rw [show sfinrank k E = sfinrank k E0 by
      exact θ.finrank_map_eq E0]
    exact sfinrank_tensorProductSubspace C.carrier K
  have hdimTarget : sfinrank k Target = sfinrank k CP * sfinrank k KP := by
    rw [show sfinrank k Target = sfinrank k Target0 by
      exact θ.finrank_map_eq Target0]
    exact sfinrank_tensorProductSubspace CP KP
  have hdimExpansion : sfinrank k (actionExpansion F E) ≤
      sfinrank k Target := Submodule.finrank_mono hexpansion
  have hnonzero : E ≠ ⊥ := by
    intro hbot
    have hzero : sfinrank k E = 0 := by simp [hbot, sfinrank]
    rw [hdimE] at hzero
    have hCpos : 0 < sfinrank k C.carrier := by
      let _ : Nontrivial C.carrier := Submodule.nontrivial_iff_ne_bot.mpr hC
      exact Module.finrank_pos
    have hKpos : 0 < sfinrank k K := by
      let _ : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK
      exact Module.finrank_pos
    have hprod : sfinrank k C.carrier * sfinrank k K ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt hCpos) (Nat.ne_of_gt hKpos)
    exact hprod (hdimE ▸ hzero)
  refine ⟨E, hnonzero, inferInstance, ?_⟩
  calc
    (sfinrank k (actionExpansion F E) : ℚ) ≤ sfinrank k Target := by
      exact_mod_cast hdimExpansion
    _ = (sfinrank k CP : ℚ) * sfinrank k KP := by rw [hdimTarget]; norm_num
    _ ≤ ((1 + δ) * sfinrank k C.carrier) *
        ((1 + δ) * sfinrank k K) := by
      apply mul_le_mul hCratio hKratio
      · positivity
      · positivity
    _ = (1 + δ) ^ 2 *
        ((sfinrank k C.carrier : ℚ) * sfinrank k K) := by ring
    _ ≤ (1 + ε) *
        ((sfinrank k C.carrier : ℚ) * sfinrank k K) := by
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (1 + ε) * sfinrank k E := by rw [hdimE]; norm_num

/-- The extension clause of Theorem D in iff form. -/
theorem isAmenableLieAlgebra_extension_direct_iff
    (I : LieIdeal k L) :
    IsAmenableLieAlgebra (k := k) (L := L) ↔
      IsAmenableLieAlgebra (k := k) (L := I) ∧
        IsAmenableLieAlgebra (k := k) (L := L ⧸ I) := by
  constructor
  · exact IsAmenableLieAlgebra.extension_components I
  · rintro ⟨hI, hQ⟩
    exact isAmenableLieAlgebra_extension_direct I hI hQ

end AssociativeLieInstance

/-- The ball generated by a finite-dimensional subspace of an associative
algebra.  The zeroth ball consists of the scalars and each successor is
obtained by one further multiplication by the generating subspace. -/
noncomputable def algebraBall (P : Submodule k U) : ℕ → Submodule k U
  | 0 => k ∙ (1 : U)
  | n + 1 => actionExpansion P (algebraBall P n)

theorem algebraBall_zero (P : Submodule k U) :
    algebraBall P 0 = k ∙ (1 : U) :=
  rfl

theorem algebraBall_succ (P : Submodule k U) (n : ℕ) :
    algebraBall P (n + 1) = actionExpansion P (algebraBall P n) :=
  rfl

theorem finiteDimensional_algebraBall
    (P : Submodule k U) [FiniteDimensional k P] (n : ℕ) :
    FiniteDimensional k (algebraBall P n) := by
  induction n with
  | zero =>
      rw [algebraBall_zero]
      infer_instance
  | succ n ih =>
      rw [algebraBall_succ]
      exact finiteDimensional_actionExpansion P (algebraBall P n)

theorem algebraBall_ne_bot (P : Submodule k U) (n : ℕ) :
    algebraBall P n ≠ ⊥ := by
  have hmono : algebraBall P 0 ≤ algebraBall P n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        exact ih.trans (le_sup_left : algebraBall P n ≤
          actionExpansion P (algebraBall P n))
  intro hbot
  have hOne : (1 : U) ∈ (⊥ : Submodule k U) := by
    rw [← hbot]
    apply hmono
    rw [algebraBall_zero]
    exact Submodule.mem_span_singleton_self 1
  have hone : (1 : U) ≠ 0 := by
    intro h
    have := congrArg (Coalgebra.eps (L := L)) h
    simp at this
  simp only [Submodule.mem_bot] at hOne
  exact hone hOne

set_option linter.unusedVariables false in
/-- The legacy unit-coefficient bound on UEA balls.  This auxiliary
condition is retained only for the ratio lemma below; it is deliberately not
called subexponential growth. -/
def HasUnitCoefficientUEAGrowth : Prop :=
  ∀ (P : Submodule k U), FiniteDimensional k P →
    ∀ ε : ℚ, 0 < ε →
      ∃ C : ℚ, ∀ n : ℕ,
        (sfinrank k (algebraBall P n) : ℚ) ≤ (1 + ε) ^ n

/-- The locally-subexponential-growth clause of Theorem D. -/
theorem HasUnitCoefficientUEAGrowth.isAmenableLieAlgebra
    (hL : HasUnitCoefficientUEAGrowth (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := L) := by
  apply isAmenableLieAlgebra_iff_regularActionFolner.mpr
  intro P hP ε hε
  let : FiniteDimensional k P := hP
  obtain ⟨_, hbound⟩ := hL P inferInstance (ε / 2) (by linarith)
  obtain ⟨n, hn⟩ := exists_succ_le_mul_of_exponential_bound
    (fun m => (sfinrank k (algebraBall P m) : ℚ))
    (by
      rw [algebraBall_zero]
      have hone : (1 : U) ≠ 0 := by
        intro h
        have := congrArg (Coalgebra.eps (L := L)) h
        simp at this
      rw [sfinrank, finrank_span_singleton hone]
      norm_num) ε hε 1 (by
        intro m
        simpa [div_div] using hbound m)
  let E : Submodule k U := algebraBall P n
  let : FiniteDimensional k E := finiteDimensional_algebraBall P n
  have hE : E ≠ ⊥ := algebraBall_ne_bot P n
  refine ⟨E, hE, inferInstance, ?_⟩
  change (sfinrank k (algebraBall P (n + 1)) : ℚ) ≤
    (1 + ε) * sfinrank k (algebraBall P n)
  exact hn

/-- Public statement of the locally-subexponential-growth clause of
Theorem D. -/
theorem isAmenableLieAlgebra_of_unitCoefficientUEAGrowth
    (hL : HasUnitCoefficientUEAGrowth (k := k) (L := L)) :
    IsAmenableLieAlgebra (k := k) (L := L) :=
  hL.isAmenableLieAlgebra


theorem associativeGrowthBall_eq_algebraBall
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (P : Submodule k (UniversalEnvelopingAlgebra k L)) (n : ℕ) :
    associativeGrowthBall k P n = algebraBall P n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [associativeGrowthBall, algebraBall_succ, ih, actionExpansion,
        actionSubspace_regular_eq_mul]








end
end HopfAmenability

