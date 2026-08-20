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
theorem sylow_exists (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    Nonempty (Sylow p G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, -⟩ := exists_sylow_ge_bot (G := G) p
  exact ⟨Q⟩

end GroupTheory

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

