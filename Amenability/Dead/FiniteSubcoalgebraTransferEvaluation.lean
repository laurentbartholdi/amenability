/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.FiniteSubcoalgebraDualEmbedding
import Amenability.Dead.SplitTensorTransferData
import Amenability.Dead.PullbackTransferData
import Amenability.Dead.CharacterRepresentativeGroupLike
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Evaluation of the concrete transfer filtration

For finite subcoalgebras `F,C` of a Hopf algebra, this file evaluates the
tensor filtration maps after pulling them back along
```
(FC)* ↪ F* ⊗ C*.
```

The character map is evaluation along multiplication by the group-like
representative `g_i`, while the layer coefficient is evaluation along
multiplication by the coefficient representative `f_i`.
-/

open Coalgebra Module TensorProduct WithConv

namespace HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

namespace SplitDualFiltration

variable
    (F C : FiniteSubcoalgebra k H)
    (S : SplitDualFiltration k F.Dual)

/--
Evaluation of the tensor-layer character map on `C*`.
-/
theorem tensorRho_evaluation
    (i : Fin S.n)
    (z : F.Dual ⊗[k] C.Dual)
    (c : C.carrier) :
    S.tensorRho (A := C.Dual) i z c =
      convDualDistribAlgEquiv
        (k := k) (C := F.carrier) (D := C.carrier)
        z (S.characterRepresentative i ⊗ₜ[k] c) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | add x y hx hy =>
      simp [hx, hy]
  | tmul φ ψ =>
      rw [S.tensorRho_tmul]
      rw [convDualDistribAlgEquiv_tmul_apply]
      rw [S.character_eq_eval i φ]
      rfl

/--
After the dual multiplication embedding, `rho_i(q)` is the functional
`c ↦ q(g_i c)`.
-/
theorem tensorRho_mulDualEmbedding_evaluation
    (i : Fin S.n)
    (q : (FiniteSubcoalgebra.mul F C).Dual)
    (c : C.carrier) :
    S.tensorRho (A := C.Dual) i
        (FiniteSubcoalgebra.mulDualEmbedding F C q) c =
      q
        ⟨(S.characterRepresentative i : H) * (c : H),
          Submodule.mul_mem_mul
            (S.characterRepresentative i).2 c.2⟩ := by
  rw [S.tensorRho_evaluation F C i
    (FiniteSubcoalgebra.mulDualEmbedding F C q) c]
  exact
    FiniteSubcoalgebra.mulDualEmbedding_evaluation_ambient
      F C q (S.characterRepresentative i) c

/--
Evaluation of the tensor-layer coefficient on `C*`.
-/
theorem tensorLayerCoeff_evaluation
    (i : Fin S.n)
    (x : S.tensorFiltration (A := C.Dual) i.succ)
    (c : C.carrier) :
    S.tensorLayerCoeff (A := C.Dual) i x c =
      convDualDistribAlgEquiv
        (k := k) (C := F.carrier) (D := C.carrier)
        (x : F.Dual ⊗[k] C.Dual)
        (S.coeffRepresentative i ⊗ₜ[k] c) := by
  let z : S.filtration i.succ ⊗[k] C.Dual :=
    (S.tensorFiltrationEquiv (A := C.Dual) i.succ).symm x
  have hx :
      S.tensorFiltrationEquiv (A := C.Dual) i.succ z = x :=
    (S.tensorFiltrationEquiv (A := C.Dual) i.succ).apply_symm_apply x
  rw [← hx]
  rw [S.tensorLayerCoeff_equiv]
  change
    S.tensorCoeff (A := C.Dual) i z c =
      convDualDistribAlgEquiv
        (k := k) (C := F.carrier) (D := C.carrier)
        (((S.filtration i.succ).subtype.rTensor C.Dual) z)
        (S.coeffRepresentative i ⊗ₜ[k] c)
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | add z₁ z₂ hz₁ hz₂ =>
      simp [hz₁, hz₂]
  | tmul y ψ =>
      rw [S.tensorCoeff_tmul]
      change
        (S.coeff i y • ψ).ofConv c =
          convDualDistribAlgEquiv
            (k := k) (C := F.carrier) (D := C.carrier)
            ((y : F.Dual) ⊗ₜ[k] ψ)
            (S.coeffRepresentative i ⊗ₜ[k] c)
      rw [convDualDistribAlgEquiv_tmul_apply]
      rw [S.coeff_eq_eval i y]
      rfl

/--
The coefficient of the pulled-back tensor filtration is
`c ↦ q(f_i c)`.
-/
theorem pullbackCoeff_evaluation
    (i : Fin S.n)
    (q :
      (S.tensorTransferData (A := C.Dual)).pullbackFiltration
        (FiniteSubcoalgebra.mulDualEmbedding F C) i.succ)
    (c : C.carrier) :
    (S.tensorTransferData (A := C.Dual)).pullbackCoeff
        (FiniteSubcoalgebra.mulDualEmbedding F C) i q c =
      q.1
        ⟨(S.coeffRepresentative i : H) * (c : H),
          Submodule.mul_mem_mul
            (S.coeffRepresentative i).2 c.2⟩ := by
  change
    S.tensorLayerCoeff (A := C.Dual) i
        ⟨FiniteSubcoalgebra.mulDualEmbedding F C q.1, q.2⟩ c =
      _
  rw [S.tensorLayerCoeff_evaluation F C i]
  exact
    FiniteSubcoalgebra.mulDualEmbedding_evaluation_ambient
      F C q.1 (S.coeffRepresentative i) c

/--
Multiplication by the group-like character representative,
`C → FC`.
-/
def characterMulMap
    (i : Fin S.n) :
    C.carrier →ₗ[k] (FiniteSubcoalgebra.mul F C).carrier where
  toFun c :=
    ⟨(S.characterRepresentative i : H) * (c : H),
      Submodule.mul_mem_mul
        (S.characterRepresentative i).2 c.2⟩
  map_add' c d := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' r c := by
    apply Subtype.ext
    simp

@[simp]
theorem characterMulMap_apply
    (i : Fin S.n)
    (c : C.carrier) :
    S.characterMulMap F C i c =
      ⟨(S.characterRepresentative i : H) * (c : H),
        Submodule.mul_mem_mul
          (S.characterRepresentative i).2 c.2⟩ :=
  rfl

/--
The character representative remains group-like in the ambient Hopf
algebra.
-/
theorem characterRepresentative_isGroupLike_ambient
    (i : Fin S.n) :
    IsGroupLikeElem k
      ((S.characterRepresentative i : F.carrier) : H) := by
  exact
    (S.characterRepresentative_isGroupLike i).map
      (subcoalgebraInclusion F.carrier F.isSubcoalgebra)

/--
Multiplication by the character representative is injective.
-/
theorem characterMulMap_injective
    (i : Fin S.n) :
    Function.Injective (S.characterMulMap F C i) := by
  intro c d h
  apply Subtype.ext
  have hcd :
      (S.characterRepresentative i : H) * (c : H) =
        (S.characterRepresentative i : H) * (d : H) :=
    congrArg Subtype.val h
  have hg :=
    S.characterRepresentative_isGroupLike_ambient F i
  calc
    (c : H) = 1 * (c : H) := by simp
    _ =
        (HopfAlgebra.antipode k
            (S.characterRepresentative i : H) *
          (S.characterRepresentative i : H)) * (c : H) := by
          rw [hg.antipode_mul_cancel]
    _ =
        HopfAlgebra.antipode k
            (S.characterRepresentative i : H) *
          ((S.characterRepresentative i : H) * (c : H)) := by
          rw [mul_assoc]
    _ =
        HopfAlgebra.antipode k
            (S.characterRepresentative i : H) *
          ((S.characterRepresentative i : H) * (d : H)) := by
          rw [hcd]
    _ =
        (HopfAlgebra.antipode k
            (S.characterRepresentative i : H) *
          (S.characterRepresentative i : H)) * (d : H) := by
          rw [mul_assoc]
    _ = 1 * (d : H) := by
          rw [hg.antipode_mul_cancel]
    _ = (d : H) := by simp

/--
The restricted `rho_i : (FC)* → C*` is surjective.
-/
theorem mulDualRho_surjective
    (i : Fin S.n) :
    Function.Surjective
      ((S.tensorRho (A := C.Dual) i).comp
        (FiniteSubcoalgebra.mulDualEmbedding F C)) := by
  intro ψ
  obtain ⟨q₀, hq₀⟩ :=
    LinearMap.dualMap_surjective_of_injective
      (S.characterMulMap_injective F C i) ψ.ofConv
  let q : (FiniteSubcoalgebra.mul F C).Dual :=
    WithConv.toConv q₀
  refine ⟨q, ?_⟩
  apply WithConv.ext
  apply LinearMap.ext
  intro c
  change
    S.tensorRho (A := C.Dual) i
        (FiniteSubcoalgebra.mulDualEmbedding F C q) c =
      ψ c
  rw [S.tensorRho_mulDualEmbedding_evaluation F C i q c]
  have h :=
    LinearMap.congr_fun hq₀ c
  simpa [q, characterMulMap] using h

/--
The concrete filtered transfer data on `(FC)*`.
-/
noncomputable def mulTransferData :
    FilteredTransferData k
      (FiniteSubcoalgebra.mul F C).Dual C.Dual :=
  (S.tensorTransferData (A := C.Dual)).pullback
    (FiniteSubcoalgebra.mulDualEmbedding F C)
    (FiniteSubcoalgebra.mulDualEmbedding_injective F C)
    (S.mulDualRho_surjective F C)

end SplitDualFiltration

end

end HopfAmenability
