/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

theorem FinOne.le_finite {f : Ordinal → ℕ} {a : Ordinal} (h : FinOne f a) (n : ℕ) :
    {x | x < a ∧ f x ≤ n}.Finite := by
  have hset : {x : Ordinal | x < a ∧ f x ≤ n} = ⋃ v ∈ Set.Iic n, {x | x < a ∧ f x = v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, exists_prop]
    constructor
    · rintro ⟨hx, hv⟩; exact ⟨f x, hv, hx, rfl⟩
    · rintro ⟨v, hv, hx, rfl⟩; exact ⟨hx, hv⟩
  rw [hset]
  exact Set.Finite.biUnion (Set.finite_Iic n) (fun v _ => h v)

