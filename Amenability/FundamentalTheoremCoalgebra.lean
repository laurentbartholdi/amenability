/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.CoefficientCoalgebra

/-!
# The fundamental theorem of coalgebras
-/

open Coalgebra Module TensorProduct

namespace Coalgebra

open HopfAmenability

noncomputable section

universe u v

variable {k : Type u} {C : Type v}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A finite-dimensional right subcomodule of the regular comodule is
contained in a finite-dimensional subcoalgebra. -/
theorem exists_finiteSubcoalgebra_containing_rightSubcomodule
    (N : Submodule k C)
    [FiniteDimensional k N]
    (hN : IsRightSubcomodule (C := C) N) :
    ∃ D : FiniteSubcoalgebra k C, N ≤ D.carrier := by
  obtain ⟨D, hD⟩ :=
    exists_finiteSubcoalgebra_coaction_of_rightSubcomodule N hN
  refine ⟨D, ?_⟩
  intro x hx
  have hcomul := hD x hx
  change Coalgebra.comul (R := k) (A := C) x ∈
    LinearMap.range (D.carrier.subtype.lTensor C) at hcomul
  rcases hcomul with ⟨z, hz⟩
  have hnatural : ∀ q : C ⊗[k] D.carrier,
      ((TensorProduct.lid k D.carrier
        ((Coalgebra.counit (R := k) (A := C)).rTensor D.carrier q) :
          D.carrier) : C) =
        TensorProduct.lid k C
          ((Coalgebra.counit (R := k) (A := C)).rTensor C
            ((D.carrier.subtype.lTensor C) q)) := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add q r hq hr => simp [hq, hr]
    | tmul c d' => rfl
  let d : D.carrier := TensorProduct.lid k D.carrier
    ((Coalgebra.counit (R := k) (A := C)).rTensor D.carrier z)
  have hcontract := congrArg
    (fun y : C ⊗[k] C => TensorProduct.lid k C
      ((Coalgebra.counit (R := k) (A := C)).rTensor C y)) hz
  have hleft : (d : C) = TensorProduct.lid k C
      ((Coalgebra.counit (R := k) (A := C)).rTensor C
        ((D.carrier.subtype.lTensor C) z)) := hnatural z
  rw [← hleft] at hcontract
  rw [Coalgebra.rTensor_counit_comul] at hcontract
  have hdx : (d : C) = x := by simpa using hcontract
  rw [← hdx]
  exact d.2

/-- Every finite-dimensional subspace of a coalgebra is contained in a
finite-dimensional subcoalgebra. -/
theorem exists_finiteSubcoalgebra_containing_submodule
    (E : Submodule k C)
    [FiniteDimensional k E] :
    ∃ D : FiniteSubcoalgebra k C, E ≤ D.carrier := by
  obtain ⟨N, hN, hNfin, hEN⟩ :=
    RightComodule.exists_finiteDimensional_rightSubcomodule_of_submodule
      (C := C) E
  let _ : FiniteDimensional k N := hNfin
  obtain ⟨D, hND⟩ :=
    exists_finiteSubcoalgebra_containing_rightSubcomodule N hN
  exact ⟨D, hEN.trans hND⟩

/-- Every coalgebra element belongs to a finite-dimensional subcoalgebra. -/
theorem exists_finiteSubcoalgebra_containing (c : C) :
    ∃ D : FiniteSubcoalgebra k C, c ∈ D.carrier := by
  let E : Submodule k C := k ∙ c
  obtain ⟨D, hED⟩ := exists_finiteSubcoalgebra_containing_submodule E
  exact ⟨D, hED (Submodule.mem_span_singleton_self c)⟩

/-- Every finite set of coalgebra elements belongs to one finite-dimensional
subcoalgebra. -/
theorem exists_finiteSubcoalgebra_containing_finite
    (s : Set C) (hs : s.Finite) :
    ∃ D : FiniteSubcoalgebra k C, s ⊆ D.carrier := by
  let E : Submodule k C := Submodule.span k s
  let _ : FiniteDimensional k E := Module.Finite.span_of_finite k hs
  obtain ⟨D, hED⟩ := exists_finiteSubcoalgebra_containing_submodule E
  exact ⟨D, fun x hx => hED (Submodule.subset_span hx)⟩

end

end Coalgebra
