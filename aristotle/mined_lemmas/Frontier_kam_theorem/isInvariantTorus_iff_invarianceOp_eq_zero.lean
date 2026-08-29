/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

noncomputable section

/-! ## The `n`-dimensional torus and rotations -/

/-- The `n`-dimensional torus `𝕋ⁿ = (ℝ/ℤ)ⁿ`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- The rigid rotation of `𝕋ⁿ` by the frequency vector `ω`. -/

lemma isInvariantTorus_iff_invarianceOp_eq_zero {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    (F : C(X, X)) (ω : Fin n → ℝ) (p : C(Torus n, X)) :
    IsInvariantTorus F ω p ↔ invarianceOp F ω p = 0 := by
  constructor
  · intro h
    ext θ
    simp [invarianceOp, h θ]
  · intro h θ
    have := ContinuousMap.congr_fun h θ
    simpa [invarianceOp, sub_eq_zero] using this

/-! ## A Newton–Kantorovich persistence lemma (the analytic core of a KAM step) -/

/-- **Quantitative Newton step.**  If a (possibly nonlinear) map `Φ` between Banach spaces is,
on a ball around `u₀`, approximated by an invertible linear operator `A` with error constant `κ`
satisfying `‖A⁻¹‖ κ ≤ 1/2`, and if the residual `Φ u₀` is small, then `Φ` has a zero in the ball.
This is the fixed-point mechanism behind the KAM iteration. -/
