/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.FiniteSubcoalgebraTransferEvaluation
import Amenability.CoalgebraTransferAbstract

/-!
# The transfer inequality for finite subcoalgebras

This file instantiates the abstract transfer theorem for finite
subcoalgebras `F,C` of a cocommutative Hopf algebra.

For `U ≤ C`, let `FU ≤ FC` be the image of
```
F ⊗ U → F ⊗ C → FC.
```
The layer coefficient of a functional annihilating `FU` annihilates
`U`, because it is evaluation on `f_i u` for a representative
`f_i ∈ F`.
-/

open Coalgebra Module TensorProduct WithConv

namespace UnifiedRounding

noncomputable section

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocomm k H]

namespace FiniteSubcoalgebra

/--
Multiplication restricted to `F ⊗ U`.
-/
def leftProductMap
    (F C : FiniteSubcoalgebra k H)
    (U : Submodule k C.carrier) :
    F.carrier ⊗[k] U →ₗ[k] (mul F C).carrier :=
  (mulCoalgHom F C).toLinearMap.comp
    (U.subtype.lTensor F.carrier)

omit [IsCocomm k H] in
@[simp]
theorem leftProductMap_tmul
    (F C : FiniteSubcoalgebra k H)
    (U : Submodule k C.carrier)
    (f : F.carrier) (u : U) :
    leftProductMap F C U (f ⊗ₜ[k] u) =
      ⟨(f : H) * (u : H),
        Submodule.mul_mem_mul f.2 u.1.2⟩ :=
  rfl

/--
The subspace `FU ≤ FC`.
-/
def leftProductSubspace
    (F C : FiniteSubcoalgebra k H)
    (U : Submodule k C.carrier) :
    Submodule k (mul F C).carrier :=
  LinearMap.range (leftProductMap F C U)

omit [IsCocomm k H] in
theorem product_mem_leftProductSubspace
    (F C : FiniteSubcoalgebra k H)
    (U : Submodule k C.carrier)
    (f : F.carrier) {u : C.carrier}
    (hu : u ∈ U) :
    (⟨(f : H) * (u : H),
      Submodule.mul_mem_mul f.2 u.2⟩ :
      (mul F C).carrier) ∈
        leftProductSubspace F C U := by
  exact
    ⟨f ⊗ₜ[k] (⟨u, hu⟩ : U), rfl⟩

end FiniteSubcoalgebra

namespace SplitDualFiltration

variable
    (F C : FiniteSubcoalgebra k H)
    (S : SplitDualFiltration k F.Dual)

/--
Every layer image of the annihilator of `FU` lies in the annihilator of
`U`.
-/
theorem layerImage_leftProductAnnihilator_le
    (U : Submodule k C.carrier)
    (i : Fin S.n) :
    (S.mulTransferData F C).layerImage
        (convDualAnnihilator
          (FiniteSubcoalgebra.leftProductSubspace F C U)) i ≤
      convDualAnnihilator U := by
  rintro y ⟨x, rfl⟩
  rw [mem_convDualAnnihilator]
  intro u hu
  change
    (S.tensorTransferData (A := C.Dual)).pullbackCoeff
        (FiniteSubcoalgebra.mulDualEmbedding F C) i x.1 u = 0
  rw [S.pullbackCoeff_evaluation F C i x.1 u]
  have hxann :
      x.1.1 ∈
        convDualAnnihilator
          (FiniteSubcoalgebra.leftProductSubspace F C U) :=
    x.2
  rw [mem_convDualAnnihilator] at hxann
  exact
    hxann _
      (FiniteSubcoalgebra.product_mem_leftProductSubspace
        F C U (S.coeffRepresentative i) hu)

include S in
/--
The transfer inequality
```
t (dim FC - dim D) ≤ dim FU - dim(FU ∩ D)
```
for every subcoalgebra `D ≤ FC`.
-/
theorem finiteSubcoalgebra_transfer
    (U : Submodule k C.carrier)
    (D : Submodule k (FiniteSubcoalgebra.mul F C).carrier)
    (t : ℚ)
    (hD : IsSubcoalgebra (k := k) D)
    (hsem :
      ∀ B : Submodule k C.carrier,
        IsSubcoalgebra (k := k) B →
          t *
              ((finrank k C.carrier : ℚ) -
                (finrank k B : ℚ)) ≤
            (finrank k U : ℚ) -
              (finrank k
                (U ⊓ B : Submodule k C.carrier) : ℚ)) :
    t *
        ((finrank k (FiniteSubcoalgebra.mul F C).carrier : ℚ) -
          (finrank k D : ℚ)) ≤
      (finrank k
        (FiniteSubcoalgebra.leftProductSubspace F C U) : ℚ) -
        (finrank k
          (FiniteSubcoalgebra.leftProductSubspace F C U ⊓ D :
            Submodule k (FiniteSubcoalgebra.mul F C).carrier) : ℚ) := by
  let T := S.mulTransferData F C
  apply
    coalgebra_transfer
      T U
      (FiniteSubcoalgebra.leftProductSubspace F C U)
      D t hD hsem
  intro i
  exact le_trans
    (T.layerImage_mono inf_le_right i)
    (S.layerImage_leftProductAnnihilator_le F C U i)

end SplitDualFiltration

end

end UnifiedRounding
