/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.FiniteSubcoalgebraMul
import Amenability.Dead.CoalgHomDual
import Amenability.Dead.DualTensorAlgebra

/-!
# The dual embedding `(FC)* ↪ F* ⊗ C*`

For finite subcoalgebras `F,C` of a bialgebra, multiplication gives a
surjective coalgebra map
`F ⊗ C → FC`.
Dualizing, and then using the canonical dual-tensor equivalence, gives the
algebra embedding
`(FC)* ↪ F* ⊗ C*`
used in the transfer lemma.
-/

open Coalgebra TensorProduct WithConv

namespace HopfAmenability

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [Bialgebra k H]

namespace FiniteSubcoalgebra

/--
The algebra embedding
`(FC)* →ₐ[k] F* ⊗ C*`
obtained by dualizing multiplication.
-/
noncomputable def mulDualEmbedding
    (F C : FiniteSubcoalgebra k H) :
    (mul F C).Dual →ₐ[k] F.Dual ⊗[k] C.Dual :=
  (convDualDistribAlgEquiv
      (k := k) (C := F.carrier) (D := C.carrier)).symm.toAlgHom.comp
    (CoalgHom.dualAlgHom (mulCoalgHom F C))

/--
The dual multiplication embedding is injective.
-/
theorem mulDualEmbedding_injective
    (F C : FiniteSubcoalgebra k H) :
    Function.Injective (mulDualEmbedding F C) := by
  exact
    (convDualDistribAlgEquiv
      (k := k) (C := F.carrier) (D := C.carrier)).symm.injective.comp
      (CoalgHom.dualAlgHom_injective_of_surjective
        (mulCoalgHom F C) (mulCoalgHom_surjective F C))

/--
Characterization of the embedding: after identifying
`F* ⊗ C*` with `(F ⊗ C)*`, an element `q ∈ (FC)*` evaluates on
`f ⊗ c` as `q(fc)`.
-/
theorem mulDualEmbedding_evaluation
    (F C : FiniteSubcoalgebra k H)
    (q : (mul F C).Dual)
    (f : F.carrier) (c : C.carrier) :
    convDualDistribAlgEquiv
        (k := k) (C := F.carrier) (D := C.carrier)
        (mulDualEmbedding F C q)
        (f ⊗ₜ[k] c) =
      q (mulCoalgHom F C (f ⊗ₜ[k] c)) := by
  simp [mulDualEmbedding, CoalgHom.dualAlgHom_apply]

/--
Ambient form of the evaluation formula:
the right-hand side is the functional `q` evaluated on the product `fc`
regarded as an element of `FC`.
-/
theorem mulDualEmbedding_evaluation_ambient
    (F C : FiniteSubcoalgebra k H)
    (q : (mul F C).Dual)
    (f : F.carrier) (c : C.carrier) :
    convDualDistribAlgEquiv
        (k := k) (C := F.carrier) (D := C.carrier)
        (mulDualEmbedding F C q)
        (f ⊗ₜ[k] c) =
      q ⟨(f : H) * (c : H), Submodule.mul_mem_mul f.2 c.2⟩ := by
  rw [mulDualEmbedding_evaluation]
  congr 1

end FiniteSubcoalgebra

end HopfAmenability
