import Mathlib
/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The sine-kernel Hankel matrix of order 3. -/

def M : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The explicit inverse of `M`. -/
