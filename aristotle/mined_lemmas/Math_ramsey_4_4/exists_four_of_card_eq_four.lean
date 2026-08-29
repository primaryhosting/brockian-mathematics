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

We show that the two-colour Ramsey number `R(4,4)` equals `18`:

* every symmetric two-colouring of the edges of the complete graph on `18` vertices
  contains a monochromatic set of `4` vertices;
* there is a symmetric two-colouring of the edges of the complete graph on `17` vertices
  (the Paley graph of order `17`) with no monochromatic set of `4` vertices.
-/

namespace Math

open Finset

/-- `MonoSet f b S` says that every pair of distinct vertices of `S` receives colour `b`. -/

lemma exists_four_of_card_eq_four {V : Type*} [DecidableEq V] {S : Finset V} (h : S.card = 4) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ S = {a, b, c, d} := by
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hat
  exact ⟨a, x, y, z, hat.1, hat.2.1, hat.2.2, hxy, hxz, hyz, rfl⟩

/-- The Paley colouring of `K₁₇` has no monochromatic set of four vertices. -/
