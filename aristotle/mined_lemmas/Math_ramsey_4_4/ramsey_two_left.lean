/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/

theorem ramsey_two_left (q : ℕ) : RamseyProp q 2 q := by
  intro V G t ht
  by_cases h : ∃ x ∈ t, ∃ y ∈ t, G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := h
    refine Or.inl ⟨{x, y}, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · have h1 : G.IsNClique 1 {y} := by simp
      have h2 := h1.insert (a := x) (fun b hb => by
        simp only [Finset.mem_singleton] at hb
        subst hb
        exact hxy)
      simpa using h2
  · push_neg at h
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq ht
    refine Or.inr ⟨s, hs, ⟨?_, hcard⟩⟩
    intro x hx y hy hne
    simp only [Finset.mem_coe] at hx hy
    exact ⟨hne, h x (hs hx) y (hs hy)⟩

/-- The number of ordered pairs of adjacent vertices inside a finite set is even
(the handshake lemma). -/
