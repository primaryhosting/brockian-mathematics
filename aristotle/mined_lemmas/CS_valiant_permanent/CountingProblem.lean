import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

def CountingProblem.InSharpP (P : CountingProblem) : Prop :=
  ∃ (wlen : ℕ → ℕ) (C : ∀ n, Circuit (Fin (P.isize n) ⊕ Fin (wlen n))),
    IsPolyBounded wlen ∧ IsPolyBounded (fun n => (C n).size) ∧
      ∀ (n : ℕ) (x : Fin (P.isize n) → Bool),
        P.count n x = Nat.card {y : Fin (wlen n) → Bool // (C n).eval (Sum.elim x y) = true}

/-- The 0/1 matrix encoded by a bit string of length `n * n`. -/
