/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma pow_val_add {x : ℂ} (hx : x ^ 16 = 1) (a b : Fin 16) :
    x ^ ((a + b) : Fin 16).val = x ^ a.val * x ^ b.val := by
  have key : ∀ n : ℕ, x ^ (n % 16) = x ^ n := by
    intro n
    conv_rhs => rw [← Nat.div_add_mod n 16]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  rw [Fin.val_add, key, pow_add]

/-- The vertex-`i` entry of the `k`-th Fourier eigenvector. -/
