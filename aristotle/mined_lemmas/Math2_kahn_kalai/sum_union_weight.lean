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

lemma sum_union_weight (a b : ℝ) (f : Finset α → ℝ) :
    ∑ W : Finset α, ∑ V : Finset α, weight a W * weight b V * f (W ∪ V)
      = ∑ U : Finset α, weight (1 - (1 - a) * (1 - b)) U * f U := by
  have h := sum_union_pw a b (univ : Finset α) f
  rwa [Finset.powerset_univ] at h

end Fintype2

end Math2

import Mathlib
import RequestProject.KahnKalai.Fragment

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The key lemma of Park–Pham: the cover made of the large minimum fragments has small
expected cost.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Reweighting identity: adding a set `T` disjoint from `W` trades a factor `q ^ |T|`
for a factor `(1-q) ^ |T|`. -/
