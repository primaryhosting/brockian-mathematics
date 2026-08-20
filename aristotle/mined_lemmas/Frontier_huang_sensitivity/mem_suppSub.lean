import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

lemma mem_suppSub {S : Finset (Q n)} {v : Q n → ℝ} :
    v ∈ suppSub S ↔ ∀ x, x ∉ S → v x = 0 := by
  constructor
  · intro hv x hx
    have := congrFun (LinearMap.mem_ker.1 hv) ⟨x, hx⟩
    simpa using this
  · intro hv
    refine LinearMap.mem_ker.2 ?_
    funext y
    simpa using hv y.1 y.2

