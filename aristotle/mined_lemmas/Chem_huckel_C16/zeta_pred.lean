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

lemma zeta_pred (i k : ZMod 16) :
    zeta ^ ((i - 1).val * k.val) * zeta ^ k.val = zeta ^ (i.val * k.val) := by
  rw [← pow_add]
  apply zeta_pow_congr
  have hone : (1 : ZMod 16).val = 1 := by decide
  have hval : ((i - 1) + 1 : ZMod 16) = i := by ring
  have h0 := ZMod.val_add (i - 1) (1 : ZMod 16)
  rw [hval, hone] at h0
  have h1 : (i - 1).val + 1 ≡ i.val [MOD 16] := by
    unfold Nat.ModEq
    rw [← h0]
    exact (Nat.mod_eq_of_lt (ZMod.val_lt i)).symm
  have h2 := h1.mul_right k.val
  unfold Nat.ModEq at h2
  calc ((i - 1).val * k.val + k.val) % 16 = (((i - 1).val + 1) * k.val) % 16 := by ring_nf
    _ = i.val * k.val % 16 := h2

