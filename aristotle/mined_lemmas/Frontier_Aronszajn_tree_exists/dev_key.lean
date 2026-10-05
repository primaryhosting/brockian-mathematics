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

theorem dev_key {s t : Node} (hsub : dev s ⊆ dev t) {ξ : Ordinal}
    (h1 : ξ < s.len) (h2 : s.fn ξ ≠ E s.len ξ) : t.fn ξ = s.fn ξ := by
  obtain ⟨ξ', -, h⟩ : (ξ, s.fn ξ) ∈ dev t := hsub ⟨ξ, ⟨h1, h2⟩, rfl⟩
  have h₁ : ξ' = ξ := congrArg Prod.fst h
  have h₂ : t.fn ξ' = s.fn ξ := congrArg Prod.snd h
  rwa [h₁] at h₂

