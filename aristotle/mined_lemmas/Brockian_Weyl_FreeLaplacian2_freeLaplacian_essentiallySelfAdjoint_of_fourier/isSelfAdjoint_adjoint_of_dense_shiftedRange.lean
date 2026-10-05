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
# A basic criterion for essential self-adjointness

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/

theorem isSelfAdjoint_adjoint_of_dense_shiftedRange {T : H →ₗ.[ℂ] H}
    (hdense : Dense (T.domain : Set H)) (hsymm : T.IsFormalAdjoint T)
    (hplus : Dense (shiftedRange T Complex.I))
    (hminus : Dense (shiftedRange T (-Complex.I))) : IsSelfAdjoint (T†) := by
  classical
  have hTT : T ≤ T† := LinearPMap.IsFormalAdjoint.le_adjoint hdense hsymm
  have hdense' : Dense ((T†).domain : Set H) := Dense.mono (fun _ hx => hTT.1 hx) hdense
  -- `A := T††`
  set A : H →ₗ.[ℂ] H := (T†)† with hA
  have hAle : A ≤ T† := adjoint_le_adjoint hdense hTT
  have hTA : T ≤ A :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense' (LinearPMap.adjoint_isFormalAdjoint hdense)
  have hAdense : Dense ((A.domain : Set H)) := Dense.mono (fun _ hx => hTA.1 hx) hdense
  have hAclosed : A.IsClosed := LinearPMap.adjoint_isClosed hdense'
  have hAsymm : A.IsFormalAdjoint A := by
    intro x y
    have hy : (y : H) ∈ (T†).domain := hAle.1 y.2
    have hTy : A y = T† ⟨(y : H), hy⟩ := hAle.2 rfl
    have := LinearPMap.adjoint_isFormalAdjoint (T := T†) hdense' x ⟨(y : H), hy⟩
    rw [hTy]
    exact this
  -- the range of `A + i` is dense, since it contains the range of `T + i`
  have hAplus : Dense (shiftedRange A Complex.I) := by
    refine Dense.mono ?_ hplus
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨(x : H), hTA.1 x.2⟩, ?_⟩
    show A ⟨(x : H), hTA.1 x.2⟩ + Complex.I • (x : H) = T x + Complex.I • (x : H)
    rw [hTA.2 (x := x) (y := ⟨(x : H), hTA.1 x.2⟩) rfl]
  -- hence `A + i` is surjective
  have hsurj := surjective_add_I_of_isClosed hAclosed hAsymm hAplus
  -- now show `T† ≤ A`
  have hle : T† ≤ A := by
    have hdom : (T†).domain ≤ A.domain := by
      intro y hy
      obtain ⟨w, hw⟩ := hsurj (T† ⟨y, hy⟩ + Complex.I • y)
      set y' : H := y - (w : H) with hy'
      have hwT : (w : H) ∈ (T†).domain := hAle.1 w.2
      have hy'mem : y' ∈ (T†).domain := Submodule.sub_mem _ hy hwT
      have hTw : T† ⟨(w : H), hwT⟩ = A w := (hAle.2 rfl).symm
      have hTy' : T† ⟨y', hy'mem⟩ = -(Complex.I • y') := by
        have hsub : (⟨y', hy'mem⟩ : (T†).domain)
            = (⟨y, hy⟩ : (T†).domain) - ⟨(w : H), hwT⟩ := by
          apply Subtype.ext; simp [hy']
        rw [hsub, (T†).map_sub, hTw]
        have : A w = T† ⟨y, hy⟩ + Complex.I • y - Complex.I • (w : H) := by
          rw [← hw]; abel
        rw [this, hy']
        simp only [smul_sub]
        abel
      -- `y'` is orthogonal to the range of `T - i`
      have horth : ∀ v ∈ shiftedRange T (-Complex.I), ⟪y', v⟫ = 0 := by
        rintro _ ⟨x, rfl⟩
        have hfa := LinearPMap.adjoint_isFormalAdjoint (T := T) hdense ⟨y', hy'mem⟩ x
        have h1 : (⟪y', T x⟫ : ℂ) = ⟪-(Complex.I • y'), (x : H)⟫ := by
          rw [← hTy']
          exact hfa.symm
        rw [inner_add_right, h1]
        rw [inner_smul_right, inner_neg_left, inner_smul_left]
        simp [Complex.conj_I]
      have hy'zero : y' = 0 := eq_zero_of_dense_inner_eq_zero hminus horth
      have : y = (w : H) := by
        have := sub_eq_zero.mp hy'zero
        exact this
      rw [this]
      exact w.2
    refine ⟨hdom, ?_⟩
    rintro ⟨y, hy⟩ ⟨y2, hy2⟩ (hyy : y = y2)
    subst hyy
    -- values agree
    obtain ⟨w, hw⟩ := hsurj (T† ⟨y, hy⟩ + Complex.I • y)
    have hwT : (w : H) ∈ (T†).domain := hAle.1 w.2
    have hTw : T† ⟨(w : H), hwT⟩ = A w := (hAle.2 rfl).symm
    have hy'mem : y - (w : H) ∈ (T†).domain := Submodule.sub_mem _ hy hwT
    have hTy' : T† ⟨y - (w : H), hy'mem⟩ = -(Complex.I • (y - (w : H))) := by
      have hsub : (⟨y - (w : H), hy'mem⟩ : (T†).domain)
          = (⟨y, hy⟩ : (T†).domain) - ⟨(w : H), hwT⟩ := by
        apply Subtype.ext; simp
      rw [hsub, (T†).map_sub, hTw]
      have : A w = T† ⟨y, hy⟩ + Complex.I • y - Complex.I • (w : H) := by
        rw [← hw]; abel
      rw [this]
      simp only [smul_sub]
      abel
    have horth : ∀ v ∈ shiftedRange T (-Complex.I), ⟪y - (w : H), v⟫ = 0 := by
      rintro _ ⟨x, rfl⟩
      have hfa := LinearPMap.adjoint_isFormalAdjoint (T := T) hdense ⟨y - (w : H), hy'mem⟩ x
      have h1 : (⟪y - (w : H), T x⟫ : ℂ) = ⟪-(Complex.I • (y - (w : H))), (x : H)⟫ := by
        rw [← hTy']
        exact hfa.symm
      rw [inner_add_right, h1, inner_smul_right, inner_neg_left, inner_smul_left]
      simp [Complex.conj_I]
    have hyw : y = (w : H) := sub_eq_zero.mp (eq_zero_of_dense_inner_eq_zero hminus horth)
    have : T† ⟨y, hy⟩ = A w := by
      have : (⟨y, hy⟩ : (T†).domain) = ⟨(w : H), hwT⟩ := Subtype.ext hyw
      rw [this, hTw]
    rw [this]
    have : (⟨y, hy2⟩ : A.domain) = w := Subtype.ext hyw
    rw [this]
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAle hle

end Brockian.Weyl

import Mathlib

/-!
# Resolvents of the one-dimensional Laplacian on Schwartz space

For every Schwartz function `h` on `ℝ` and every non-real `z`, the equation
`-u'' + z u = h` has a Schwartz solution `u`, obtained by dividing the Fourier transform of `h`
by the symbol `4 π² ξ² + z`.

Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex SchwartzMap Real
open scoped Nat ContDiff FourierTransform SchwartzMap

namespace Brockian.Weyl

/-- A one-dimensional function all of whose iterated derivatives are bounded has temperate
growth. -/
