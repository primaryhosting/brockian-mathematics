/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

theorem Covering.determined {B : Type u} (cov : Covering A B) {S : Set (ℕ → A)}
    (h : Determined (cov.push ⁻¹' S)) : Determined S := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · refine Or.inl ⟨cov.liftI σ, fun x hx => ?_⟩
    obtain ⟨y, hy, hpush⟩ := cov.liftI_spec σ x hx
    have := hσ y hy
    rwa [Set.mem_preimage, hpush] at this
  · refine Or.inr ⟨cov.liftII τ, fun x hx => ?_⟩
    obtain ⟨y, hy, hpush⟩ := cov.liftII_spec τ x hx
    have := hτ y hy
    rwa [Set.mem_preimage, hpush] at this

/-! ## Borel determinacy -/

/-- Martin's *unravelling* hypothesis: every Borel payoff set admits a covering in which it
becomes clopen.  This is the deep combinatorial content of Martin's theorem. -/
