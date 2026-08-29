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

def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ :=
  ∏ i ∈ S, (if x i then (-1 : ℤ) else 1)

/-- The (unnormalized) Fourier coefficient of `f` at `S`, i.e. `∑_x (-1)^{f x} χ_S(x)`.
It is `2^n` times the usual Fourier coefficient of the `±1`-valued version of `f`. -/
