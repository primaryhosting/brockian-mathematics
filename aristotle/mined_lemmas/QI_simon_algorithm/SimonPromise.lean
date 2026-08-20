/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

lemma SimonPromise.period {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s)
    (x : BV n) : f (x + s) = f x := by
  exact ((h.fibre x (x + s)).2 (Or.inr rfl)).symm

end QI

import RequestProject.Simon.Defs

/-!
# The classical lower bound for Simon's problem

A deterministic classical algorithm with oracle access to `f` is modelled by two functions:
given the history of query/answer pairs seen so far, it either asks a new query or produces its
output.  `QI.ClassicalAlg.Solves` says that after `m` queries the algorithm outputs the hidden
period for *every* instance satisfying Simon's promise.

The main result, `QI.classical_query_lower_bound`, is the adversary argument showing that such
an algorithm needs `m ≥ 2^{(n-1)/2}` queries.
-/

namespace QI

open Finset

/-- A deterministic classical query algorithm: `query h` is the next query to make after seeing
the history `h` of query/answer pairs, and `output h` is the answer it returns. -/
structure ClassicalAlg (n : ℕ) where
  /-- The next query, as a function of the history. -/
  query : List (BV n × BV n) → BV n
  /-- The final output, as a function of the history. -/
  output : List (BV n × BV n) → BV n

/-- The history of query/answer pairs produced by running `A` on the oracle `f` for `k` steps. -/
