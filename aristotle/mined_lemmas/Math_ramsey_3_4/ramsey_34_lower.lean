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

open Finset SimpleGraph

namespace Math

/-- The `(3,4)`-Ramsey property for `n`: every simple graph on `n` vertices contains
either a triangle (a `3`-clique) or an independent set of size `4`. -/

theorem ramsey_34_lower {n : ℕ} (h : RamseyProp34 n) : 9 ≤ n := by
  by_contra hn
  push_neg at hn
  have hn8 : n ≤ 8 := by omega
  set f : Fin n → Fin 8 := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn8⟩ with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (f a).val = (f b).val := by rw [hab]
    exact Fin.ext h1
  rcases h (G8.comap f) with ⟨s, hs⟩ | ⟨t, ht⟩
  · refine G8_no_triangle (s.image f) ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hs.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_image_of_injective _ hfinj, hs.2]
  · refine G8_no_indep4 (t.image f) ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ht.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_image_of_injective _ hfinj, ht.2]

/-- **R(3,4) = 9**: `9` is the least `n` such that every two-colouring of the edges of `K_n`
contains a triangle in the first colour or an independent set of size 4 (i.e. a `4`-clique in
the second colour). -/
