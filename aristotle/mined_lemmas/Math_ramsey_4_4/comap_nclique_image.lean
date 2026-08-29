/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem comap_nclique_image {V W : Type*} [DecidableEq V] [DecidableEq W] {H : SimpleGraph W}
    {f : V → W} (hf : Function.Injective f) {k : ℕ} {s : Finset V}
    (h : (H.comap f).IsNClique k s) : H.IsNClique k (s.image f) := by
  refine ⟨?_, ?_⟩
  · rintro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact h.1 ha hb (fun hab => hxy (by rw [hab]))
  · rw [Finset.card_image_of_injective _ hf, h.2]

