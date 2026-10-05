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

theorem idx_spec {l ξ : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) (hξ : ξ < l) :
    ξ < cseq l (idx l ξ + 1) := by
  have hne : {n : ℕ | ξ < cseq l (n + 1)}.Nonempty := by
    obtain ⟨n, hn⟩ := (cseq_spec hl hcl).2.2.2 ξ hξ
    cases n with
    | zero => rw [(cseq_spec hl hcl).1] at hn; exact absurd hn (by simp)
    | succ m => exact ⟨m, hn⟩
  exact Nat.sInf_mem hne

