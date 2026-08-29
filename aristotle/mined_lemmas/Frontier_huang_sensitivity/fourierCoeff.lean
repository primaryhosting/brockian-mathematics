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

def fourierCoeff {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℤ :=
  ∑ x : Fin n → Bool, (if f x then (-1 : ℤ) else 1) * chi S x

/-- The degree of a Boolean function: the largest size of a set carrying a nonzero
Fourier coefficient, i.e. the degree of the unique multilinear polynomial
representing `f`. -/
