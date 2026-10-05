import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap ComplexInnerProductSpace FourierTransform Laplacian Real

namespace Brockian.FreeLaplacianPlancherel

noncomputable section

/-! ## An abstract criterion for essential self-adjointness

We work with a symmetric, densely defined operator `T` with domain a submodule `D` of a complex
Hilbert space `H`.  Mathlib does not (yet) have a theory of unbounded operators, so we spell out
the relevant notions.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `IsAdjointPair D T y z` says that `y` belongs to the domain of the adjoint of the operator
`T` (with domain `D`) and that `z` is a corresponding adjoint value, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain.  If `D` is dense then `z` is uniquely determined
by `y`, and `z = T* y`. -/

theorem isEssentiallySelfAdjoint_of_dense_range
    (hdense : Dense (D : Set H))
    (hsym : ∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫)
    (hplus : Dense (Set.range fun x : D => T x + Complex.I • (x : H)))
    (hminus : Dense (Set.range fun x : D => T x - Complex.I • (x : H))) :
    IsEssentiallySelfAdjoint D T := by
  refine ⟨hdense, hsym, ?_⟩
  have hplus' : DenseRange (fun x : D => T x + Complex.I • (x : H)) := hplus
  have hminus' : DenseRange (fun x : D => T x - Complex.I • (x : H)) := hminus
  intro y₁ z₁ y₂ z₂ h1 h2
  have hsq : ∀ x : D, ‖T x + Complex.I • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : H)‖ ^ 2 :=
    norm_add_I_sq hsym
  set Sp : D →ₗ[ℂ] H := T + Complex.I • D.subtype with hSp
  have hSpapp : ∀ x : D, Sp x = T x + Complex.I • (x : H) := by intro x; simp [hSp]
  have hb1 : ∀ x : D, ‖(D.subtype) x‖ ≤ 1 * ‖Sp x‖ := by
    intro x
    have h := hsq x
    rw [hSpapp]
    show ‖(x : H)‖ ≤ 1 * ‖T x + Complex.I • (x : H)‖
    nlinarith [norm_nonneg (T x + Complex.I • (x : H)), norm_nonneg (T x), norm_nonneg ((x : H))]
  have hb2 : ∀ x : D, ‖T x‖ ≤ 1 * ‖Sp x‖ := by
    intro x
    have h := hsq x
    rw [hSpapp]
    nlinarith [norm_nonneg (T x + Complex.I • (x : H)), norm_nonneg (T x), norm_nonneg ((x : H))]
  have hdr : DenseRange (Sp : D → H) := by
    have : (Sp : D → H) = fun x : D => T x + Complex.I • (x : H) := by funext x; exact hSpapp x
    rw [this]; exact hplus'
  set A : H →L[ℂ] H := (D.subtype).extendOfNorm Sp with hA
  set B : H →L[ℂ] H := T.extendOfNorm Sp with hB
  have hAeq : ∀ x : D, A (Sp x) = (x : H) := fun x => LinearMap.extendOfNorm_eq hdr ⟨1, hb1⟩ x
  have hBeq : ∀ x : D, B (Sp x) = T x := fun x => LinearMap.extendOfNorm_eq hdr ⟨1, hb2⟩ x
  have key1 : ∀ v : H, B v + Complex.I • A v = v := by
    have : (fun v => B v + Complex.I • A v) = (id : H → H) := by
      refine hdr.equalizer (by fun_prop) continuous_id ?_
      funext x
      show B (Sp x) + Complex.I • A (Sp x) = id (Sp x)
      rw [hAeq, hBeq, hSpapp]
      rfl
    exact fun v => congrFun this v
  have key2 : ∀ y z : H, (∀ x : D, ⟪T x, y⟫ = ⟪(x : H), z⟫) → ∀ v : H, ⟪B v, y⟫ = ⟪A v, z⟫ := by
    intro y z hyz
    have : (fun v => ⟪B v, y⟫) = (fun v => ⟪A v, z⟫) := by
      refine hdr.equalizer (by fun_prop) (by fun_prop) ?_
      funext x
      show ⟪B (Sp x), y⟫ = ⟪A (Sp x), z⟫
      rw [hAeq, hBeq]
      exact hyz x
    exact fun v => congrFun this v
  have key3 : ∀ (x : D) (v : H), ⟪T x, A v⟫ = ⟪(x : H), B v⟫ := by
    intro x
    have : (fun v => ⟪T x, A v⟫) = (fun v => ⟪(x : H), B v⟫) := by
      refine hdr.equalizer (by fun_prop) (by fun_prop) ?_
      funext y
      show ⟪T x, A (Sp y)⟫ = ⟪(x : H), B (Sp y)⟫
      rw [hAeq, hBeq]
      exact hsym x y
    exact fun v => congrFun this v
  set v : H := z₁ + Complex.I • y₁ with hv
  set g : H := A v with hg
  set w : H := B v with hw
  have hvg : w + Complex.I • g = z₁ + Complex.I • y₁ := key1 v
  have hu : y₁ - g = 0 := by
    have horth : ∀ x : D, ⟪T x - Complex.I • (x : H), y₁ - g⟫ = 0 := by
      intro x
      have e1 : ⟪T x, y₁ - g⟫ = ⟪(x : H), z₁ - w⟫ := by
        rw [inner_sub_right, inner_sub_right, h1 x, key3 x v]
      have e2 : z₁ - w = -(Complex.I • (y₁ - g)) := by
        rw [smul_sub]
        linear_combination (norm := module) -hvg
      rw [inner_sub_left, e1, e2, inner_neg_right, inner_smul_right, inner_smul_left]
      simp
    have hzero : (fun x : H => ⟪x, y₁ - g⟫) = (fun _ : H => (0 : ℂ)) := by
      refine hminus'.equalizer (by fun_prop) (by fun_prop) ?_
      funext x
      exact horth x
    exact inner_self_eq_zero.mp (congrFun hzero (y₁ - g))
  have hy1 : y₁ = g := by linear_combination (norm := module) hu
  have hz1 : z₁ = w := by
    rw [← hy1] at hvg
    linear_combination (norm := module) -hvg
  rw [hz1, hy1, hw, hg]
  exact key2 y₂ z₂ h2 v

end Abstract

/-! ## The free Laplacian on `L²(V)`

`V` is a finite-dimensional real inner product space (e.g. `EuclideanSpace ℝ (Fin d)`), equipped
with its Haar measure `volume`, and `H = L²(V, ℂ)`.
-/

section Concrete

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The multiplier `4π²‖ξ‖²` of the free Laplacian on the Fourier side. -/
