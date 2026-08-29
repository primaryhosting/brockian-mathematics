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

noncomputable def canonical (α : Ordinal) (hα : α < ω₁) : Node where
  len := α
  fn := fun ξ => if ξ < α then E α ξ else 0
  len_lt := hα
  fn_zero := fun ξ hξ => if_neg (not_lt.mpr hξ)
  fn_coh := by
    apply Set.Finite.subset Set.finite_empty
    rintro ξ ⟨h1, h2⟩
    rw [if_pos h1] at h2
    exact absurd rfl h2

