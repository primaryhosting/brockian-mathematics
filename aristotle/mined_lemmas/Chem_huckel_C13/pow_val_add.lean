import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma pow_val_add {w : ℂ} (hw : w ^ 13 = 1) (a b : Fin 13) :
    w ^ ((a + b) : Fin 13).val = w ^ a.val * w ^ b.val := by
  have hmod : ∀ m : ℕ, w ^ (m % 13) = w ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 13]
    rw [pow_add, pow_mul, hw, one_pow, one_mul]
  rw [Fin.val_add, hmod, pow_add]

/-- The character `Fin 13 → ℂ`, `a ↦ ζ ^ a`. -/
