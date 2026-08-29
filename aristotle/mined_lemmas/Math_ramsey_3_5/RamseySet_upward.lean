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

open Finset SimpleGraph

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/

lemma RamseySet_upward {N M : ℕ} (hNM : N ≤ M) (hN : N ∈ RamseySet) : M ∈ RamseySet := by
  intro G
  set f : Fin N ↪ Fin M := (Fin.castLEEmb hNM) with hf
  set H : SimpleGraph (Fin N) := SimpleGraph.comap f G with hH
  have hadj : ∀ a b : Fin N, H.Adj a b ↔ G.Adj (f a) (f b) := fun a b => Iff.rfl
  rcases hN H with ⟨s, hs⟩ | ⟨t, ht⟩
  · refine Or.inl ⟨s.map f, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : a ≠ b := fun h => hxy (by rw [h])
      exact (hadj a b).1 (hs.1 ha hb hab)
    · rw [Finset.card_map, hs.2]
  · refine Or.inr ⟨t.map f, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : a ≠ b := fun h => hxy (by rw [h])
      have := ht.1 ha hb hab
      rw [SimpleGraph.compl_adj] at this ⊢
      exact ⟨hxy, fun hcon => this.2 ((hadj a b).2 hcon)⟩
    · rw [Finset.card_map, ht.2]

end Ramsey35

namespace Math

/-- **R(3,5) = 14**: fourteen is the least `N` such that every graph on `N` vertices
contains a triangle or an independent set of size 5. -/
