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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-! ## Relative (Finset-localized) triangles and independent sets -/

section Rel

variable {V : Type*} [LinearOrder V]

/-- `t` is an independent set of `G`. -/

lemma key2 (G : SimpleGraph V) (s : Finset V) (hs : 3 ≤ s.card) :
    HasTriIn G s ∨ HasIndepIn G 2 s := by
  classical
  obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ s := hts (by simp)
  have hb : b ∈ s := hts (by simp)
  have hc : c ∈ s := hts (by simp)
  by_cases h1 : G.Adj a b
  · by_cases h2 : G.Adj a c
    · by_cases h3 : G.Adj b c
      · refine Or.inl ⟨{a, b, c}, hts, hcard, ?_⟩
        intro x hx y hy hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hxy
            | assumption
            | exact h1.symm
            | exact h2.symm
            | exact h3.symm
      · exact Or.inr ⟨{b, c}, Finset.insert_subset hb (Finset.singleton_subset_iff.mpr hc),
          Finset.card_pair hbc, indepOn_pair h3⟩
    · exact Or.inr ⟨{a, c}, Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hc),
        Finset.card_pair hac, indepOn_pair h2⟩
  · exact Or.inr ⟨{a, b}, Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb),
      Finset.card_pair hab, indepOn_pair h1⟩

/-- The Ramsey recursion `R(3, k+1) ≤ R(3,k) + k + 1`. -/
