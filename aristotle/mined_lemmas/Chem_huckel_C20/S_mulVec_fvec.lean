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

lemma S_mulVec_fvec (k : ℕ) : S *ᵥ fvec k = w ^ k • fvec k := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, S, Pi.smul_apply, smul_eq_mul, fvec]
  rw [Finset.sum_eq_single (i + 1)]
  · rw [if_pos rfl, one_mul]
    have h1 : ((i + 1 : Fin 20)).val = (i.val + 1) % 20 := by simp [Fin.add_def]
    rw [h1, ← pow_add]
    apply w_pow_mod
    have h2 : ((i.val + 1) % 20) * k ≡ (i.val + 1) * k [MOD 20] :=
      Nat.ModEq.mul_right k (Nat.mod_modEq (i.val + 1) 20)
    calc ((i.val + 1) % 20) * k % 20 = ((i.val + 1) * k) % 20 := h2
      _ = (k + i.val * k) % 20 := by ring_nf
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · intro h; simp at h

