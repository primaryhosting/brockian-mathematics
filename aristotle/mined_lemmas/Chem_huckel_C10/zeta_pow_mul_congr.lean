/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

lemma zeta_pow_mul_congr {a b : ℕ} (k : ℕ) (h : a % 10 = b % 10) :
    zeta ^ (a * k) = zeta ^ (b * k) :=
  zeta_pow_congr (by rw [Nat.mul_mod, h, ← Nat.mul_mod])

