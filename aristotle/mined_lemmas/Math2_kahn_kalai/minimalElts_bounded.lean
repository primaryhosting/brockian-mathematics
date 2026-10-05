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

lemma minimalElts_bounded (F : Finset (Finset α)) :
    ∀ S ∈ minimalElts F, S.card ≤ ell F := fun S hS =>
  le_trans (Finset.le_sup (f := Finset.card) hS) (le_max_right _ _)

/-! ### From the iteration to the threshold -/

/-- If `H` is `ℓ`-bounded and not `q`-small, then a random set of density at least
`64 q * rounds ℓ` contains an edge of `H` with probability more than `1/2`. -/
