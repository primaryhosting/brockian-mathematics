/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## Machine model

We work with a *non-uniform* space-bounded machine model.  A machine works on inputs of one
fixed length; a language belongs to a space class if for every input length there is a machine
of the appropriate size deciding the language on inputs of that length.

A machine is described by its set of configurations `Cfg` (which is the whole memory of the
machine: the space used is `log₂ (card Cfg)`), a designated start configuration, a function
`head` telling which position of the (read-only) input is currently scanned, and a transition
which may depend on the current configuration and on the single input bit that is being read.
Note that the machine has *no* other access to the input, which is what makes the space measure
meaningful. -/

/-- The `i`-th bit of an input word; `false` beyond the end of the word. -/

lemma card_savCfg_le (M : NSM) (d : ℕ) (hA : NN M ≤ 2 ^ d) :
    Fintype.card (SavCfg M d) ≤ 2 ^ ((3 * d + 3) * (d + 1) + 1) := by
  have hA1 : 1 ≤ NN M := NN_pos M
  have hframe : Fintype.card (Frame M) + 1 ≤ 2 ^ (3 * d + 3) := by
    have hcf : Fintype.card (Frame M) = NN M * (NN M * ((NN M + 1) * 3)) := by
      simp [Frame, NN, Fintype.card_prod]
    have h8 : NN M * (NN M * ((NN M + 1) * 3)) + 1 ≤ 8 * NN M ^ 3 := by nlinarith
    have hpow : (8 : ℕ) * NN M ^ 3 ≤ 2 ^ (3 * d + 3) := by
      have : NN M ^ 3 ≤ (2 ^ d) ^ 3 := Nat.pow_le_pow_left hA 3
      calc 8 * NN M ^ 3 ≤ 8 * (2 ^ d) ^ 3 := by omega
        _ = 2 ^ (3 * d + 3) := by rw [← pow_mul]; ring
    omega
  have hcard : Fintype.card (SavCfg M d)
      = Fintype.card {l : List (Frame M) // l.length ≤ d + 1} * 2 := by
    show Fintype.card ({l : List (Frame M) // l.length ≤ d + 1} × Bool) = _
    simp [Fintype.card_prod]
  have hlist : Fintype.card {l : List (Frame M) // l.length ≤ d + 1}
      ≤ (Fintype.card (Frame M) + 1) ^ (d + 1) := card_listLe_le (d + 1)
  calc Fintype.card (SavCfg M d)
      = Fintype.card {l : List (Frame M) // l.length ≤ d + 1} * 2 := hcard
    _ ≤ (Fintype.card (Frame M) + 1) ^ (d + 1) * 2 := by omega
    _ ≤ (2 ^ (3 * d + 3)) ^ (d + 1) * 2 := by
        exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_left hframe (d + 1))
    _ = 2 ^ ((3 * d + 3) * (d + 1) + 1) := by rw [← pow_mul, pow_succ]

/-- **Savitch's theorem**: every language accepted by a nondeterministic machine using space
`f` is decided by a deterministic machine using space `O(f ^ 2)`. -/
