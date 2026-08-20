import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

open scoped Classical

namespace Ramsey44

variable {V : Type*}

/-- `Arr G s p q` says that inside the vertex set `s` there is either a `p`-clique of `G`
or a `q`-clique of the complement of `G` (i.e. an independent set of size `q`). -/

lemma clique_image {N M : ℕ} {f : Fin N → Fin M} (hf : Function.Injective f)
    {G : SimpleGraph (Fin M)} {s : Finset (Fin N)} {n : ℕ}
    (hs : (SimpleGraph.comap f G).IsNClique n s) : G.IsNClique n (s.image f) := by
  obtain ⟨hcl, hcard⟩ := (SimpleGraph.isNClique_iff _).1 hs
  rw [SimpleGraph.isNClique_iff]
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hcl (Finset.mem_coe.2 hx') (Finset.mem_coe.2 hy') (fun h => hxy (by rw [h]))
  · rw [Finset.card_image_of_injective _ hf, hcard]

