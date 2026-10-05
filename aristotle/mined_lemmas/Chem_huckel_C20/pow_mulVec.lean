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

lemma pow_mulVec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {v : n → ℂ} {c : ℂ}
    (h : M *ᵥ v = c • v) (d : ℕ) : M ^ d *ᵥ v = c ^ d • v := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, pow_succ']
    simp [smul_smul, mul_comm]

/-- If `v` is an eigenvector of `M` with eigenvalue `c`, it is an eigenvector of `g(M)`. -/
