import Mathlib
import RequestProject.Paley

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-! ## Monochromatic cliques for a two-colouring -/

variable {α : Type*} [DecidableEq α] {c : α → α → Bool} {x : Bool}

/-- `S` is a monochromatic clique of colour `x` for the two-colouring `c`. -/

lemma key_red {V : Finset α} {v : α} (hv : v ∈ V) (hsym : ∀ a b, c a b = c b a)
    {T : Finset α} (hT : T ⊆ redN c V v) :
    (∃ S ⊆ V, S.card = 3 ∧ MonoClique c true S) ∨ MonoClique c false T := by
  by_cases hc : ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ c i j = true
  · obtain ⟨i, hi, j, hj, hij, hcij⟩ := hc
    have hi' := mem_redN.1 (hT hi)
    have hj' := mem_redN.1 (hT hj)
    refine Or.inl ⟨{v, i, j}, ?_, ?_, monoClique_triple hsym hi'.2 hj'.2 hcij⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hv
      · exact hi'.1.1
      · exact hj'.1.1
    · exact Finset.card_eq_three.2 ⟨v, i, j, (hi'.1.2).symm, (hj'.1.2).symm, hij, rfl⟩
  · push_neg at hc
    exact Or.inr fun i hi j hj hij => by simpa using hc i hi j hj hij

