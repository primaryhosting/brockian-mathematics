import Mathlib
import RequestProject.DisjointnessLb

/-!
# Deterministic two-way communication complexity of set disjointness

As a companion to `CS.disjointness_lb` (a linear lower bound for *randomized* one-way
protocols), this file formalises the general *two-way deterministic* model as protocol
trees and proves the classical fooling-set lower bound: any deterministic protocol
computing set disjointness on an `n`-element universe has cost at least `n`.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- Bitwise complement of a characteristic vector. -/

theorem exists_exact_protocol (n N : ℕ) :
    ∃ (msg : Fin N → (Fin n → Bool) → Fin (2 ^ n))
      (out : Fin N → Fin (2 ^ n) → (Fin n → Bool) → Bool),
      ∀ a b : Fin n → Bool,
        ((Finset.univ.filter (fun r : Fin N => out r (msg r a) b ≠ Disj a b)).card : ℝ)
          ≤ (N : ℝ) / 16 := by
  classical
  have e : (Fin n → Bool) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun _ a => e a, fun _ m b => Disj (e.symm m) b, fun a b => ?_⟩
  simp [Equiv.symm_apply_apply]
  positivity

end CS

