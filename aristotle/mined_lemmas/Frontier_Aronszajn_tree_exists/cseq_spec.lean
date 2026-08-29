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

theorem cseq_spec {l : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) :
    IsCofSeq l (cseq l) := by
  have h : ∃ c, IsCofSeq l c := exists_cofSeq hl hcl
  unfold cseq
  rw [dif_pos h]
  exact h.choose_spec

