/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The first-order language of arithmetic, with function symbols `0, 1, +, *`
and no relation symbols. -/

theorem isArithmetical_compl_diagonal {R : Set (ℕ × ℕ)} (hR : IsArithmetical₂ R) :
    IsArithmetical {n : ℕ | (n, n) ∉ R} := by
  obtain ⟨φ, hφ⟩ := hR
  refine ⟨(φ.relabel (fun _ => (0 : Fin 1))).not, fun n => ?_⟩
  have h := hφ (fun _ => n)
  simp only [Set.mem_setOf_eq, Formula.realize_not, Formula.realize_relabel] at *
  rw [show ((fun _ => n) ∘ (fun _ : Fin 2 => (0 : Fin 1))) = (fun _ : Fin 2 => n) from rfl]
  exact not_congr h

/-- **Tarski's undefinability theorem** (universality form): no arithmetical binary relation is
universal for the arithmetical sets, i.e. no single arithmetical relation `U` has the property
that every arithmetical set of naturals occurs as a section `{n | (a, n) ∈ U}` of `U`. -/
