/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.FiniteSubcoalgebraDualEmbedding

/-!
# Split finite-dimensional algebras: transfer data

The transfer proof does not need a particular implementation of a
Jordan--Hölder series.  It needs a finite filtration of the algebra by
`k`-subspaces which are ideals, together with a one-dimensional character
description of each successive layer.

We package exactly that data here.  A later specialization will construct
such a certificate from the hypothesis that every simple module is
one-dimensional.
-/

namespace HopfAmenability

universe u v

variable {k : Type u} {R : Type v}
variable [Field k] [CommRing R] [Algebra k R]

/--
A `k`-subspace of a `k`-algebra which is stable under multiplication by
arbitrary elements of the algebra.

For a commutative algebra this is exactly an ideal, expressed as a
`Submodule k R`; this representation is more convenient for dimension
arguments.
-/
def IsIdealSubspace (I : Submodule k R) : Prop :=
  ∀ r : R, ∀ ⦃x : R⦄, x ∈ I → r * x ∈ I

@[simp]
theorem isIdealSubspace_bot :
    IsIdealSubspace (k := k) (R := R) (⊥ : Submodule k R) := by
  intro r x hx
  simpa [Submodule.mem_bot] using congrArg (fun y => r * y) hx

@[simp]
theorem isIdealSubspace_top :
    IsIdealSubspace (k := k) (R := R) (⊤ : Submodule k R) := by
  intro r x hx
  exact Submodule.mem_top

/--
A finite split filtration of a finite-dimensional commutative `k`-algebra.

For `i : Fin n`, the successive layer is
`filtration i.succ / filtration i.castSucc`.
The map `coeff i` identifies that layer with `k`, while `character i`
describes the action of `R` on the layer.
-/
structure SplitDualFiltration (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R] where
  n : ℕ
  filtration : Fin (n + 1) → Submodule k R
  bot : filtration 0 = ⊥
  top : filtration (Fin.last n) = ⊤
  monotone :
    ∀ i : Fin n, filtration i.castSucc ≤ filtration i.succ
  ideal :
    ∀ j : Fin (n + 1), IsIdealSubspace (filtration j)
  character : Fin n → R →ₐ[k] k
  coeff :
    ∀ i : Fin n, filtration i.succ →ₗ[k] k
  coeff_surjective :
    ∀ i : Fin n, Function.Surjective (coeff i)
  coeff_ker :
    ∀ i : Fin n,
      LinearMap.ker (coeff i) =
        (filtration i.castSucc).comap
          (filtration i.succ).subtype
  coeff_mul :
    ∀ (i : Fin n) (r : R) (x : filtration i.succ),
      coeff i
          ⟨r * (x : R),
            ideal i.succ r x.2⟩ =
        character i r * coeff i x

namespace SplitDualFiltration

variable (S : SplitDualFiltration k R)

/--
Multiplication by an algebra element preserves every filtration step.
-/
theorem mul_mem
    (j : Fin (S.n + 1)) (r : R)
    {x : R} (hx : x ∈ S.filtration j) :
    r * x ∈ S.filtration j :=
  S.ideal j r hx

/--
The lower filtration step embeds in the kernel of the coefficient map.
-/
theorem coeff_eq_zero_of_mem_lower
    (i : Fin S.n)
    (x : S.filtration i.succ)
    (hx :
      (x : R) ∈ S.filtration i.castSucc) :
    S.coeff i x = 0 := by
  rw [← LinearMap.mem_ker]
  rw [S.coeff_ker i]
  exact hx

/--
Conversely, vanishing of the layer coefficient means membership in the
previous filtration step.
-/
theorem mem_lower_of_coeff_eq_zero
    (i : Fin S.n)
    (x : S.filtration i.succ)
    (hx : S.coeff i x = 0) :
    (x : R) ∈ S.filtration i.castSucc := by
  have hxker : x ∈ LinearMap.ker (S.coeff i) := by
    simpa [LinearMap.mem_ker] using hx
  rw [S.coeff_ker i] at hxker
  exact hxker

/--
The coefficient of a product is the character value times the coefficient.
-/
theorem coeff_mul_apply
    (i : Fin S.n) (r : R)
    (x : S.filtration i.succ) :
    S.coeff i
        ⟨r * (x : R), S.mul_mem i.succ r x.2⟩ =
      S.character i r * S.coeff i x :=
  S.coeff_mul i r x

end SplitDualFiltration

end HopfAmenability
