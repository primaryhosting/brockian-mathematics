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

lemma mono_three_three {W : Finset V} (h : 6 ≤ W.card) : Mono G 3 3 W := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
  have hsplit := card_nbr_add_card_nbr_compl (G := G) hv
  by_cases ha : 3 ≤ (nbr G v W).card
  · rcases mono_two (G := G) (s := 3) ha with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact Or.inl (extend hv ht hc)
    · exact Or.inr ⟨t, ht.trans (nbr_subset _ _ _), hc⟩
  · have hb : 3 ≤ (nbr Gᶜ v W).card := by omega
    rcases mono_two (G := Gᶜ) (s := 3) hb with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact Or.inr (extend (G := Gᶜ) hv ht hc)
    · rw [compl_compl] at hc
      exact Or.inl ⟨t, ht.trans (nbr_subset _ _ _), hc⟩

/-- Handshake lemma, relative to a finite set of vertices. -/
