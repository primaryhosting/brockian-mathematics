import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma rounds_of_pos {ℓ : ℕ} (h : 0 < ℓ) : rounds ℓ = rounds (ℓ / 2) + 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rw [rounds]

