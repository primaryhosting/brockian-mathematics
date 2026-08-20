/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command; the header above is repeated below
-- as a module docstring.)

import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Finset

/-! ## Generalities on monochromatic cliques -/

section General

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

/-- The set of vertices of `W` adjacent to `v` in `G`. -/

lemma mono_two {s : ℕ} {A : Finset V} (h : s ≤ A.card) : Mono G 2 s A := by
  by_cases hred : ∃ x ∈ A, ∃ y ∈ A, G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hred
    refine Or.inl ⟨{x, y}, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; subst hz; exact hy
    · refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [G.symm hxy]
      · exact Finset.card_pair (G.ne_of_adj hxy)
  · push_neg at hred
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
    refine Or.inr ⟨t, ht, ⟨?_, htc⟩⟩
    intro a ha b hb hab
    refine ⟨hab, hred a (ht ha) b (ht hb)⟩

/-- R(3,3) ≤ 6. -/
