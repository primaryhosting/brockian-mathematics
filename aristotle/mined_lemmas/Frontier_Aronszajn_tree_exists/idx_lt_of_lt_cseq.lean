/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem idx_lt_of_lt_cseq {l ξ : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) {N : ℕ}
    (h : ξ < cseq l N) : idx l ξ < N := by
  cases N with
  | zero => rw [(cseq_spec hl hcl).1] at h; exact absurd h (by simp)
  | succ M =>
    have : idx l ξ ≤ M := Nat.sInf_le h
    omega

/-! ## `E` is finite-to-one and coherent -/

/-- `E o` is finite-to-one on `Set.Iio o`. -/
