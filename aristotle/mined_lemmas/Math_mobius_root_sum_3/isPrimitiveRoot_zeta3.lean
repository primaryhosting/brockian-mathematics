/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A fixed primitive cube root of unity in `ℂ`. -/

lemma isPrimitiveRoot_zeta3 : IsPrimitiveRoot zeta3 3 := by
  have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [zeta3, mul_comm, mul_assoc, mul_left_comm] using this

