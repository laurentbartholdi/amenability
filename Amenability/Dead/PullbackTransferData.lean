/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/
import Amenability.Dead.TransferData

/-!
# Pulling filtered transfer data back along an algebra embedding

If `T` is filtered transfer data on an algebra `B` and
`e : Q →ₐ[k] B` is injective, then the filtration can be pulled back
to `Q`.

The only additional hypothesis needed is that the restricted maps
```
T.rho i ∘ e : Q →ₐ[k] A
```
are surjective. This is exactly the point which, in the concrete
coalgebra application, is proved by extending functionals from `g_i C`
to `FC`.
-/

namespace HopfAmenability

universe u v w x

variable {k : Type u} {Q : Type v} {B : Type w} {A : Type x}
variable [Field k]
variable [CommRing Q] [Algebra k Q]
variable [CommRing B] [Algebra k B]
variable [CommRing A] [Algebra k A]

namespace FilteredTransferData

variable (T : FilteredTransferData k B A)

/--
The pullback of one filtration step along an algebra map.
-/
def pullbackFiltration
    (e : Q →ₐ[k] B)
    (j : Fin (T.n + 1)) :
    Submodule k Q :=
  (T.filtration j).comap e.toLinearMap

/--
The natural map from a pulled-back filtration step to the corresponding
ambient step.
-/
def pullbackStepMap
    (e : Q →ₐ[k] B)
    (j : Fin (T.n + 1)) :
    T.pullbackFiltration e j →ₗ[k] T.filtration j where
  toFun x := ⟨e x.1, x.2⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_pullbackStepMap
    (e : Q →ₐ[k] B)
    (j : Fin (T.n + 1))
    (x : T.pullbackFiltration e j) :
    ((T.pullbackStepMap e j x : T.filtration j) : B) = e x.1 :=
  rfl

/--
The coefficient on the pullback filtration.
-/
def pullbackCoeff
    (e : Q →ₐ[k] B)
    (i : Fin T.n) :
    T.pullbackFiltration e i.succ →ₗ[k] A :=
  (T.coeff i).comp (T.pullbackStepMap e i.succ)

/--
Pullback of filtered transfer data along an injective algebra map.
-/
noncomputable def pullback
    (e : Q →ₐ[k] B)
    (he : Function.Injective e)
    (hrho :
      ∀ i : Fin T.n,
        Function.Surjective ((T.rho i).comp e)) :
    FilteredTransferData k Q A where
  n := T.n
  filtration := T.pullbackFiltration e
  bot := by
    ext q
    constructor
    · intro hq
      change e q ∈ T.filtration 0 at hq
      rw [T.bot] at hq
      have heq : e q = 0 := by
        simpa [Submodule.mem_bot] using hq
      have : q = 0 := he (by simpa using heq)
      simp [this]
    · intro hq
      have : q = 0 := by
        simpa [Submodule.mem_bot] using hq
      subst q
      simp [pullbackFiltration, T.bot]
  top := by
    ext q
    simp [pullbackFiltration, T.top]
  monotone := by
    intro i
    exact Submodule.comap_mono (T.monotone i)
  ideal := by
    intro j q x hx
    change e (q * x) ∈ T.filtration j
    rw [map_mul]
    exact T.ideal j (e q) hx
  coeff := T.pullbackCoeff e
  coeff_ker := by
    intro i
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      change T.coeff i (T.pullbackStepMap e i.succ x) = 0 at hx
      have hxker :
          T.pullbackStepMap e i.succ x ∈
            LinearMap.ker (T.coeff i) := by
        simpa [LinearMap.mem_ker] using hx
      rw [T.coeff_ker i] at hxker
      exact hxker
    · intro hx
      rw [LinearMap.mem_ker]
      change T.coeff i (T.pullbackStepMap e i.succ x) = 0
      have hxker :
          T.pullbackStepMap e i.succ x ∈
            LinearMap.ker (T.coeff i) := by
        rw [T.coeff_ker i]
        exact hx
      simpa [LinearMap.mem_ker] using hxker
  rho := fun i => (T.rho i).comp e
  rho_surjective := hrho
  coeff_mul := by
    intro i q x
    change
      T.coeff i
          ⟨e (q * (x : Q)), ?_⟩ =
        T.rho i (e q) *
          T.coeff i ⟨e (x : Q), x.2⟩
    · convert T.coeff_mul i (e q) ⟨e (x : Q), x.2⟩ using 1
      simp only [map_mul]

end FilteredTransferData

end HopfAmenability
