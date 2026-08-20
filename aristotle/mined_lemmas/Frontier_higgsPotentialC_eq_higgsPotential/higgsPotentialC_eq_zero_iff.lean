import Mathlib

/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
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

/-- The "Mexican hat" scalar potential of the abelian Higgs model, written as a
function of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r² - v²)²`. -/

lemma higgsPotentialC_eq_zero_iff (lam v : ℝ) (hlam : 0 < lam) (phi : ℂ) :
    higgsPotentialC lam v phi = 0 ↔ ‖phi‖ ^ 2 = v ^ 2 := by
  simp only [higgsPotentialC]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hlam.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'
      linarith
  · intro h; rw [h]; ring

/-- On the vacuum configuration `φ = v` (constant, so `∂φ = 0`) the covariant kinetic
term reduces to the gauge boson mass term `m_A² A²`. -/
