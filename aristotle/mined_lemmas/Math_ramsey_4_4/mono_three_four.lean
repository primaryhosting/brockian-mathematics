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

lemma mono_three_four {W : Finset V} (h : 9 ≤ W.card) : Mono G 3 4 W := by
  obtain ⟨W', hsub, hcard⟩ := Finset.exists_subset_card_eq h
  suffices hM : Mono G 3 4 W' from hM.subset hsub
  by_contra hcon
  rw [Mono, not_or] at hcon
  obtain ⟨hno3, hno4⟩ := hcon
  push_neg at hno3 hno4
  have hdeg : ∀ v ∈ W', (nbr G v W').card = 3 := by
    intro v hv
    have hsplit := card_nbr_add_card_nbr_compl (G := G) hv
    have ha : (nbr G v W').card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      rcases mono_two (G := G) (s := 4) hgt with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
      · obtain ⟨u, hu, hcu⟩ := extend hv ht hc
        exact hno3 u hu hcu
      · exact hno4 t (ht.trans (nbr_subset _ _ _)) hc
    have hb : (nbr Gᶜ v W').card ≤ 5 := by
      by_contra hgt
      push_neg at hgt
      rcases mono_three_three (G := Gᶜ) hgt with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
      · obtain ⟨u, hu, hcu⟩ := extend (G := Gᶜ) hv ht hc
        exact hno4 u hu hcu
      · rw [compl_compl] at hc
        exact hno3 t (ht.trans (nbr_subset _ _ _)) hc
    omega
  have hsum : ∑ v ∈ W', (nbr G v W').card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hcard, smul_eq_mul]
  have heven := even_sum_nbr_card G W'
  rw [hsum, Nat.even_iff] at heven
  omega

/-- R(4,4) ≤ 18. -/
