/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma C14vand_pred (i k : Fin 14) : C14vand (i - 1) k = C14vand i k * w14 ^ (13 * k.val) := by
  have hval : ∀ u : Fin 14, (u - 1 : Fin 14).val = (u.val + 13) % 14 := by decide
  rw [C14vand_apply, C14vand_apply, hval,
    w14_pow_congr (b := (i.val + 13) * k.val) ((Nat.mod_modEq (i.val + 13) 14).mul_right k.val),
    show (i.val + 13) * k.val = i.val * k.val + 13 * k.val by ring, pow_add]

