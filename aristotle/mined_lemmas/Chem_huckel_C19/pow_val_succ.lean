import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma pow_val_succ (w : ℂ) (hw : w ^ 19 = 1) (i : Fin 19) :
    w ^ ((i + 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w := by
  have hval : ((i + 1 : Fin 19) : ℕ) = (i.val + 1) % 19 := by
    simp [Fin.val_add]
  have hmod : w ^ ((i.val + 1) % 19) = w ^ (i.val + 1) := by
    conv_rhs => rw [← Nat.div_add_mod (i.val + 1) 19]
    rw [pow_add, pow_mul, hw, one_pow, one_mul]
  rw [hval, hmod, pow_succ]

