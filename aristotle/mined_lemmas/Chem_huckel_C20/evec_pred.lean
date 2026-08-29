import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma evec_pred (k : ℕ) (hk : k ≤ 20) (i : ZMod 20) :
    evec k (i - 1) = w ^ (20 - k) * evec k i := by
  have h := evec_succ k (i - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk, w_pow_20, one_mul]

