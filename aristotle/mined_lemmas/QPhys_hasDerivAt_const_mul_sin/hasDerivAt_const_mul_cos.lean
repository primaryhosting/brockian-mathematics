/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The normalized stationary states of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

lemma hasDerivAt_const_mul_cos (C c x : ℝ) :
    HasDerivAt (fun y : ℝ => C * Real.cos (c * y)) (-(C * c) * Real.sin (c * x)) x := by
  have h : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have h2 := (h.cos).const_mul C
  convert h2 using 1
  ring

/-- `ψ_n` written with the wave number `k = nπ/L` factored out. -/
