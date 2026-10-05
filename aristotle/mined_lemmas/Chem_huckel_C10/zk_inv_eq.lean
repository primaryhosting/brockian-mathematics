/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma zk_inv_eq (k : Fin 10) : (zk k)⁻¹ = (zk k) ^ 9 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact zk_pow_ten k)

/-- The cyclic three-term recurrence satisfied by the powers of a 10-th root of unity. -/
