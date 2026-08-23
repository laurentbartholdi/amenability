/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.DualSemistability
import Amenability.CoalgHomDual
import Amenability.SplitDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Annihilators in convolution duals

The finite-dimensional transfer argument naturally uses annihilators in
`Module.Dual`, while the dual algebra is the type synonym `WithConv`.
This file supplies the bridge between the two descriptions.

It also proves the easy half of the finite-dimensional
subcoalgebra/ideal correspondence: the annihilator of a subcoalgebra is
an ideal subspace of the convolution dual.
-/

open Module WithConv

namespace UnifiedRounding

universe u v

variable {k : Type u} {C : Type v}
variable [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]

/--
The annihilator of `B ≤ C`, regarded as a subspace of the convolution
dual of `C`.
-/
def convDualAnnihilator
    (B : Submodule k C) :
    Submodule k (WithConv (Module.Dual k C)) :=
  B.dualAnnihilator.comap
    (WithConv.linearEquiv k (Module.Dual k C)).toLinearMap

omit [Coalgebra k C] in
@[simp]
theorem mem_convDualAnnihilator
    (B : Submodule k C)
    (φ : WithConv (Module.Dual k C)) :
    φ ∈ convDualAnnihilator B ↔
      ∀ b : C, b ∈ B → φ b = 0 := by
  change
    (WithConv.linearEquiv k (Module.Dual k C)) φ ∈
        B.dualAnnihilator ↔ _
  simp only [Submodule.mem_dualAnnihilator, WithConv.linearEquiv_apply]

omit [Coalgebra k C] in
/--
The `WithConv` type synonym does not change the dimension of an
annihilator.
-/
theorem finrank_convDualAnnihilator
    [FiniteDimensional k C]
    (B : Submodule k C) :
    finrank k (convDualAnnihilator B) =
      finrank k B.dualAnnihilator := by
  let e :=
    (WithConv.linearEquiv k (Module.Dual k C)).ofSubmodule'
      B.dualAnnihilator
  exact e.finrank_eq

omit [Coalgebra k C] in
/--
Likewise for intersections of two convolution annihilators.
-/
theorem finrank_inf_convDualAnnihilator
    [FiniteDimensional k C]
    (B U : Submodule k C) :
    finrank k
        (convDualAnnihilator B ⊓ convDualAnnihilator U :
          Submodule k (WithConv (Module.Dual k C))) =
      finrank k
        (B.dualAnnihilator ⊓ U.dualAnnihilator :
          Submodule k (Module.Dual k C)) := by
  let E := WithConv.linearEquiv k (Module.Dual k C)
  let W :=
    (B.dualAnnihilator ⊓ U.dualAnnihilator :
      Submodule k (Module.Dual k C))
  let e := E.ofSubmodule' W
  have heq :
      W.comap E.toLinearMap =
        (convDualAnnihilator B ⊓ convDualAnnihilator U :
          Submodule k (WithConv (Module.Dual k C))) := by
    ext φ
    simp [W, E, convDualAnnihilator, Submodule.mem_comap]
  rw [← heq]
  exact e.finrank_eq

omit [Coalgebra k C] in
/--
The annihilator dimension identity in convolution-dual notation.
-/
theorem convDualAnnihilator_difference
    [FiniteDimensional k C]
    (U B : Submodule k C) :
    (finrank k (convDualAnnihilator B) : ℚ) -
        (finrank k
          (convDualAnnihilator B ⊓ convDualAnnihilator U :
            Submodule k (WithConv (Module.Dual k C))) : ℚ) =
      (finrank k U : ℚ) -
        (sfinrank k (U ⊓ B) : ℚ) := by
  rw [finrank_convDualAnnihilator B,
    finrank_inf_convDualAnnihilator B U]
  exact dualAnnihilator_difference U B

omit [Coalgebra k C] in
/--
Semistability transported to convolution-dual notation.
-/
theorem semistable_to_convDualAnnihilator
    [FiniteDimensional k C]
    (U B : Submodule k C) (t : ℚ)
    (hsem :
      t * ((finrank k C : ℚ) - (finrank k B : ℚ)) ≤
        (finrank k U : ℚ) -
          (sfinrank k (U ⊓ B) : ℚ)) :
    t * (finrank k (convDualAnnihilator B) : ℚ) ≤
      (finrank k (convDualAnnihilator B) : ℚ) -
        (finrank k
          (convDualAnnihilator B ⊓ convDualAnnihilator U :
            Submodule k (WithConv (Module.Dual k C))) : ℚ) := by
  have h :=
    semistable_to_dualAnnihilator U B t hsem
  rw [← finrank_convDualAnnihilator B,
    ← finrank_inf_convDualAnnihilator B U] at h
  exact h

omit [Coalgebra k C] in
/--
For finite-dimensional `C`, taking the coannihilator and then the
annihilator recovers a subspace of `C*`.
-/
theorem dualCoannihilator_dualAnnihilator_eq
    [FiniteDimensional k C]
    (M : Submodule k (Module.Dual k C)) :
    M.dualCoannihilator.dualAnnihilator = M := by
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

/--
The underlying ordinary-dual subspace of a convolution-dual subspace.
-/
def convUnderlying
    (M : Submodule k (WithConv (Module.Dual k C))) :
    Submodule k (Module.Dual k C) :=
  M.map (WithConv.linearEquiv k (Module.Dual k C)).toLinearMap

/--
The coannihilator in `C` of a convolution-dual subspace.
-/
def convDualCoannihilator
    (M : Submodule k (WithConv (Module.Dual k C))) :
    Submodule k C :=
  (convUnderlying M).dualCoannihilator

omit [Coalgebra k C] in
/--
In finite dimension, every convolution-dual subspace is the annihilator
of its coannihilator, as a statement of vector spaces.
-/
theorem convDualAnnihilator_convDualCoannihilator
    [FiniteDimensional k C]
    (M : Submodule k (WithConv (Module.Dual k C))) :
    convDualAnnihilator (convDualCoannihilator M) = M := by
  let E := WithConv.linearEquiv k (Module.Dual k C)
  have hdouble :
      (convUnderlying M).dualCoannihilator.dualAnnihilator =
        convUnderlying M :=
    dualCoannihilator_dualAnnihilator_eq (convUnderlying M)
  rw [convDualAnnihilator, convDualCoannihilator, hdouble]
  ext φ
  constructor
  · intro hφ
    change E φ ∈ M.map E.toLinearMap at hφ
    rcases hφ with ⟨ψ, hψ, hψφ⟩
    have : ψ = φ := E.injective hψφ
    simpa [this] using hψ
  · intro hφ
    change E φ ∈ M.map E.toLinearMap
    exact ⟨φ, hφ, rfl⟩

/--
The annihilator of a subcoalgebra is an ideal subspace of the
convolution dual.
-/
theorem convDualAnnihilator_isIdealSubspace
    [Coalgebra.IsCocomm k C]
    (B : Submodule k C)
    (hB : IsSubcoalgebra (k := k) B) :
    IsIdealSubspace (convDualAnnihilator B) := by
  let : Coalgebra k B := subcoalgebraCoalgebra B hB
  let f :
      WithConv (Module.Dual k C) →ₐ[k]
        WithConv (Module.Dual k B) :=
    CoalgHom.dualAlgHom (subcoalgebraInclusion B hB)
  have hker :
      convDualAnnihilator B =
        LinearMap.ker f.toLinearMap := by
    ext φ
    constructor
    · intro hφ
      rw [LinearMap.mem_ker]
      apply WithConv.ext
      ext b
      have hb :=
        (mem_convDualAnnihilator B φ).1 hφ (b : C) b.2
      change φ.ofConv (b : C) = 0
      exact hb
    · intro hφ
      rw [LinearMap.mem_ker] at hφ
      rw [mem_convDualAnnihilator]
      intro b hb
      have h :=
        congrArg
          (fun η : WithConv (Module.Dual k B) =>
            η ⟨b, hb⟩) hφ
      change φ.ofConv b = 0
      exact h
  rw [hker]
  intro r x hx
  rw [LinearMap.mem_ker] at hx ⊢
  change f x = 0 at hx
  change f (r * x) = 0
  rw [map_mul, hx, mul_zero]

end UnifiedRounding
