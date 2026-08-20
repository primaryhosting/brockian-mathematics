import Mathlib
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header comment is reproduced verbatim immediately below.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Set Cardinal
open scoped Ordinal

namespace Aronszajn

/-! ## Countable ordinals -/

/-- An ordinal is countable (i.e. its set of predecessors is countable) iff it is `< ω₁`. -/

lemma kk_le {α ξ : Ordinal.{0}} {m : ℕ} (hm : Good α ξ m) : kk α ξ ≤ m := by
  classical
  rw [kk, dif_pos ⟨m, hm⟩]; exact Nat.find_le hm

/-- The coherent sequence: `ee α` is a finite-to-one function on `α`, and for `β < α` the
restriction of `ee α` to `β` differs from `ee β` in only finitely many places. -/
