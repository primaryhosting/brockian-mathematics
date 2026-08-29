import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

lemma takeF_prefix (f : ℕ → A) {m n : ℕ} (h : m ≤ n) : takeF f m <+: takeF f n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ n hn ih => exact ih.trans (by rw [takeF_succ]; exact List.prefix_append _ _)

