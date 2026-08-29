/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped BigOperators

/-- Physical space `ℝ³`. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

lemma deriv_shear_profile' (C k : ℝ) :
    deriv (fun s : ℝ => C * (k * Real.cos (k * s)))
      = fun s => C * (-(k ^ 2) * Real.sin (k * s)) := by
  funext s
  have h : HasDerivAt (fun s : ℝ => C * (k * Real.cos (k * s)))
      (C * (-(k ^ 2) * Real.sin (k * s))) s := by
    have h0 := (Real.hasDerivAt_cos (k * s)).comp s ((hasDerivAt_id s).const_mul k)
    have h1 := (h0.const_mul k).const_mul C
    convert h1 using 1
    ring
  exact h.deriv

