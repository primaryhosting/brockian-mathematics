import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Frontier

section Aux

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Cauchy–Schwarz for finite sums, in absolute-value / square-root form. -/

lemma sum_mul_indicator (T : Finset V) (g : V → ℝ) :
    ∑ y, g y * (if y ∈ T then (1:ℝ) else 0) = ∑ y ∈ T, g y := by
  simp

end Aux

section Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Expander mixing lemma, matrix form.**  Let `A` be a real matrix all of whose row sums and
column sums equal `d` (e.g. the adjacency matrix of a `d`-regular graph), and suppose that `A`
contracts every vector orthogonal to the all-ones vector by a factor `lam`.  Then for all
`S T : Finset V` the number of (ordered) edges between `S` and `T` differs from its "expected"
value `d * |S| * |T| / n` by at most `lam * √(|S| * |T|)`. -/
