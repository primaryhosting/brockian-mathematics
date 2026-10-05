/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma huang_three_vars (t : Bool → Bool → Bool → Bool) :
    degree (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ≤
        sens (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ^ 2 ∧
      sens (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ≤
        degree (fun x : Fin 3 → Bool => t (x 0) (x 1) (x 2)) ^ 2 := by
  revert t
  decide

/-- **Huang's sensitivity theorem, base cases.**

Sensitivity and degree of Boolean functions are polynomially related.  We prove:

* (general `n`) the base cases of the relation: the sensitivity of `f` is `0` exactly
  when its degree is `0` (exactly when `f` is constant), and the sensitivity of `f` is
  at most `1` exactly when its degree is at most `1`;
* (`n = 3`) the full two-sided polynomial relation `deg f ≤ s(f)^2` (Huang's
  inequality) and `s(f) ≤ deg(f)^2`, verified for every Boolean function of three
  variables. -/
