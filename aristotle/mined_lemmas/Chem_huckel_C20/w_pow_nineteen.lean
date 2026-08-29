import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma w_pow_nineteen (k : ℕ) (hk : k ≤ 20) : (w ^ k) ^ 19 = w ^ (20 - k) := by
  rw [← pow_mul]
  apply w_pow_mod
  have h1 : (k * 19 + k) % 20 = ((20 - k) + k) % 20 := by
    rw [show k * 19 + k = 20 * k by ring, Nat.sub_add_cancel hk]
    simp [Nat.mul_mod_right]
  exact Nat.ModEq.add_right_cancel' k h1

/-- The eigenvalues, in exponential form. -/
