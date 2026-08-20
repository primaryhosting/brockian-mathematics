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

noncomputable def predIso (a : Tree) : {b : Tree // b < a} ≃o Set.Iio (lvl a) where
  toFun b := ⟨lvl b.1, (lt_iff.1 b.2).1⟩
  invFun γ := ⟨trunc a γ.1 γ.2.le, trunc_lt a γ.1 γ.2⟩
  left_inv b := Subtype.ext (eq_trunc_of_lt b.2).symm
  right_inv γ := Subtype.ext rfl
  map_rel_iff' := by
    rintro ⟨b, hb⟩ ⟨b', hb'⟩
    simp only [Subtype.mk_le_mk]
    constructor
    · intro hle
      refine le_def.2 ⟨hle, fun ξ hξ => ?_⟩
      rw [(lt_iff.1 hb).2 ξ hξ, ← (lt_iff.1 hb').2 ξ (lt_of_lt_of_le hξ hle)]
    · intro hle
      exact (le_def.1 hle).1

