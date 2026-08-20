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

lemma le_finite_of_fibers {γ : Ordinal.{0}}
    (h : ∀ n : ℕ, {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ = n}.Finite) (n : ℕ) :
    {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ ≤ n}.Finite := by
  have hEq : {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ ≤ n}
      = ⋃ w ∈ Set.Iic n, {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ = w} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨ee γ ξ, h2, h1, rfl⟩
    · rintro ⟨w, hw, h1, rfl⟩; exact ⟨h1, hw⟩
  rw [hEq]
  exact Set.Finite.biUnion (Set.finite_Iic n) fun w _ => h w

/-- The two properties, proved by simultaneous transfinite induction:
finite fibers, and coherence with all earlier functions. -/
