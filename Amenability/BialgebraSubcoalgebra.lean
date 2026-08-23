/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Amenability.CoalgebraDensityClosed
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Submodule

/-!
# Products of subcoalgebras in a bialgebra

Mathlib already equips `Submodule k H` with multiplication:
`F * C` is the span of products `f * c`.

This file proves that the product of two subcoalgebras is again a
subcoalgebra.
-/

open scoped TensorProduct

namespace UnifiedRounding

universe u v

variable {k : Type u} {H : Type v}
variable [Field k] [Ring H] [Bialgebra k H]

/--
If
`x ∈ A ⊗ B` and `y ∈ C ⊗ D`
inside `H ⊗ H`, then
`x * y ∈ (A * C) ⊗ (B * D)`.

Here tensor-product subspaces are represented as ranges of `mapIncl`.
-/
theorem range_mapIncl_mul_mem
    (A B C D : Submodule k H)
    {x y : H ⊗[k] H}
    (hx : x ∈ LinearMap.range (TensorProduct.mapIncl A B))
    (hy : y ∈ LinearMap.range (TensorProduct.mapIncl C D)) :
    x * y ∈
      LinearMap.range
        (TensorProduct.mapIncl
          (A * C : Submodule k H)
          (B * D : Submodule k H)) := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  induction u using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a b =>
      induction v using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul c d =>
          refine
            ⟨⟨a.1 * c.1, Submodule.mul_mem_mul a.2 c.2⟩ ⊗ₜ[k]
                ⟨b.1 * d.1, Submodule.mul_mem_mul b.2 d.2⟩, ?_⟩
          simp [TensorProduct.mapIncl, Algebra.TensorProduct.tmul_mul_tmul]
      | add v w hv hw =>
          rw [map_add, mul_add]
          exact add_mem hv hw
  | add u v hu hv =>
      rw [map_add, add_mul]
      exact add_mem hu hv

/--
The product of two subcoalgebras of a bialgebra is a subcoalgebra.
-/
theorem IsSubcoalgebra.mul
    {F C : Submodule k H}
    (hF : IsSubcoalgebra (k := k) F)
    (hC : IsSubcoalgebra (k := k) C) :
    IsSubcoalgebra (k := k) (F * C : Submodule k H) := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro f hf c hc
    rw [Bialgebra.comul_mul]
    exact range_mapIncl_mul_mem F F C C (hF hf) (hC hc)
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

/--
Multiplication of subcoalgebras is monotone in both variables.
-/
theorem subcoalgebra_mul_mono
    {F F' C C' : Submodule k H}
    (hFF' : F ≤ F') (hCC' : C ≤ C') :
    F * C ≤ F' * C' :=
  Submodule.smul_mono hFF' hCC'

end UnifiedRounding
