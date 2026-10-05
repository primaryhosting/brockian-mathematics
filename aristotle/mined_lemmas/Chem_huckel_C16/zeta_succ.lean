import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/

lemma zeta_succ (i k : ZMod 16) :
    zeta ^ ((i + 1).val * k.val) = zeta ^ (i.val * k.val) * zeta ^ k.val := by
  rw [← pow_add]
  apply zeta_pow_congr
  have hone : (1 : ZMod 16).val = 1 := by decide
  have h1 : (i + 1).val ≡ i.val + 1 [MOD 16] := by
    have h := ZMod.val_add i (1 : ZMod 16)
    rw [hone] at h
    unfold Nat.ModEq
    rw [h, Nat.mod_mod]
  have h2 := h1.mul_right k.val
  unfold Nat.ModEq at h2
  rw [h2]
  ring_nf

