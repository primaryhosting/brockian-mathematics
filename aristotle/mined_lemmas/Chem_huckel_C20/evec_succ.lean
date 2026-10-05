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

lemma evec_succ (k : ℕ) (i : ZMod 20) : evec k (i + 1) = w ^ k * evec k i := by
  have hone : (ZMod.val (1 : ZMod 20)) = 1 := by decide
  have hval : (i + 1 : ZMod 20).val = (i.val + 1) % 20 := by
    rw [ZMod.val_add, hone]
  have h2 : w ^ (k * (i + 1 : ZMod 20).val) = w ^ (k * (i.val + 1)) := by
    apply w_pow_mod
    rw [hval, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
    exact dvd_rfl
  simp only [evec, h2, Nat.mul_add, mul_one, pow_add]
  ring

