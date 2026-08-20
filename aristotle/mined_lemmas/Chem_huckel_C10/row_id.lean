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

lemma row_id {i n₁ n₂ : ℕ} (k : ℕ) (h₁ : n₁ % 10 = (i + 1) % 10)
    (h₂ : n₂ % 10 = (i + 9) % 10) :
    zeta ^ (n₁ * k) + zeta ^ (n₂ * k) = zeta ^ (i * k) * (zeta ^ k + zeta ^ (9 * k)) := by
  rw [zeta_pow_mul_congr k h₁, zeta_pow_mul_congr k h₂, mul_add, ← pow_add, ← pow_add]
  ring_nf

