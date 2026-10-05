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

lemma C20_mulVec_evec (k : ℕ) (hk : k ≤ 20) :
    C20 *ᵥ evec k = ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ) • evec k := by
  funext i
  rw [mulVec_C20, evec_succ, evec_pred k hk, Pi.smul_apply, smul_eq_mul,
    ← w_pow_add_cos k hk]
  ring

