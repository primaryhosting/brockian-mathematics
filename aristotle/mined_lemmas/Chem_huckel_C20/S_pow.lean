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

lemma S_pow (k : ℕ) : S ^ k = Matrix.of fun i j => if j = i + Fin.ofNat 20 k then 1 else 0 := by
  induction k with
  | zero => ext i j; simp [Matrix.one_apply, Fin.ofNat, eq_comm]
  | succ k ih =>
    ext i j
    rw [pow_succ', ih]
    simp only [Matrix.mul_apply, Matrix.of_apply, S]
    rw [Finset.sum_eq_single (i + 1)]
    · rw [ofNat_succ]; simp [add_comm, add_left_comm]
    · intro b _ hb; rw [if_neg hb, zero_mul]
    · intro h; simp at h

