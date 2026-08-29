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

def sensAt {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f (flipAt x i) ≠ f x)).card

/-- The sensitivity of `f`: the maximum of its local sensitivities. -/
