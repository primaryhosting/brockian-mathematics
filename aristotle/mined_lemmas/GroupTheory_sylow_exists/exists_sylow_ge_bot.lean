/-
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GroupTheory

variable {G : Type*} [Group G]

/-- Key intermediate lemma: the trivial subgroup is a `p`-group, hence it is contained in
some Sylow `p`-subgroup. -/

theorem exists_sylow_ge_bot (p : ℕ) [Fact p.Prime] [Finite G] :
    ∃ Q : Sylow p G, (⊥ : Subgroup G) ≤ (Q : Subgroup G) := by
  have hbot : IsPGroup p (⊥ : Subgroup G) := by
    intro g
    exact ⟨0, by
      have : g = 1 := Subsingleton.elim _ _
      simp [this]⟩
  obtain ⟨Q, hQ⟩ := hbot.exists_le_sylow
  exact ⟨Q, hQ⟩

/-- **Sylow's first theorem**: for a finite group `G` and a prime `p`, a Sylow `p`-subgroup
exists, i.e. the type `Sylow p G` is nonempty. -/
