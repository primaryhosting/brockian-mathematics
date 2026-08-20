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

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/

theorem isNIndepSet_map_comap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph β) (f : α ↪ β) {s : ℕ} {B : Finset α}
    (h : (G.comap f).IsNIndepSet s B) : G.IsNIndepSet s (B.map f) := by
  refine ⟨?_, by simpa using h.card_eq⟩
  intro x hx y hy hxy
  simp only [coe_map, Set.mem_image, mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact h.isIndepSet (mem_coe.mpr ha) (mem_coe.mpr hb) (fun hab => hxy (by rw [hab]))

