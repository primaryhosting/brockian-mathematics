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

lemma Disj_eq_false_of_mem {a b : Fin n → Bool} {i : Fin n} (h1 : a i = true)
    (h2 : b i = false) : Disj a (negVec b) = false := by
  simp only [Disj, negVec, decide_eq_false_iff_not, not_forall, not_not]
  exact ⟨i, h1, by simp [h2]⟩

/-- A deterministic two-party communication protocol tree: at each internal node either
Alice or Bob sends one bit, computed from her/his own input. -/
inductive Proto (n : ℕ) where
  | leaf : Bool → Proto n
  | alice : ((Fin n → Bool) → Bool) → (Bool → Proto n) → Proto n
  | bob : ((Fin n → Bool) → Bool) → (Bool → Proto n) → Proto n

namespace Proto

/-- The cost (depth, i.e. worst-case number of communicated bits) of a protocol. -/
