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

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`Eₙ = n²π²ℏ²/(2mL²)`. -/

lemma const_of_hasDerivAt_zero {f : ℝ → ℝ} (h : ∀ x, HasDerivAt f 0 x) (x : ℝ) :
    f x = f 0 :=
  is_const_of_deriv_eq_zero (fun y => (h y).differentiableAt) (fun y => (h y).deriv) x 0

/-- Uniqueness for `g'' = k² g` with vanishing initial data. -/
