/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Math

open SimpleGraph

/-- `RamseyProp n` says that every simple graph on `n` vertices contains either a triangle
(a clique of size `3`) or an independent set of size `4`. -/

lemma isNIndepSet_map_of_comap {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph W}
    (f : V ↪ W) {k : ℕ} {s : Finset V} (h : (G.comap f).IsNIndepSet k s) :
    G.IsNIndepSet k (s.map f) := by
  constructor
  · intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact h.isIndepSet hx hy (fun hxy => hab (by rw [hxy]))
  · rw [Finset.card_map]; exact h.card_eq

