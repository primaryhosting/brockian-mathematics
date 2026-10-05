/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

lemma zeta16_pow_congr {a b : ℕ} (h : a % 16 = b % 16) : zeta16 ^ a = zeta16 ^ b := by
  rw [zeta16_pow_mod a, zeta16_pow_mod b, h]

