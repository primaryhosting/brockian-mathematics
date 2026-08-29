/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

open Finset

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s` or an independent set (a clique in the complement) of size `t`. -/

lemma clique_map {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) (n : ℕ) (S : Finset V)
    (h : (SimpleGraph.comap f G).IsNClique n S) : G.IsNClique n (S.map f) := by
  rw [isNClique_iff'] at h ⊢
  refine ⟨?_, by simpa using h.2⟩
  intro x hx y hy hxy
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hab : a ≠ b := fun h => hxy (by rw [h])
  exact SimpleGraph.comap_adj.1 (h.1 ha hb hab)

