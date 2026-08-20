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

lemma countable_Iio_iff (o : Ordinal.{0}) : (Set.Iio o).Countable ↔ o < ω₁ := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one,
    ← Cardinal.ord_aleph, Cardinal.lt_ord]

/-! ## A coherent sequence of finite-to-one functions -/

/-- For `α < ω₁`, a sequence of ordinals `< α` which is cofinal in `α` in the weak sense that
every `ξ < α` satisfies `ξ ≤ cs α n` for some `n`.  Junk value otherwise. -/
