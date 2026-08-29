import Mathlib
/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased weight of a subset `T` of the (finite) ground set. -/

def IsSpread (κ : ℝ) (H : Finset (Finset α)) : Prop :=
  ∀ Z : Finset α, ((H.filter (fun S => Z ⊆ S)).card : ℝ) ≤ κ ^ Z.card * H.card

/-! ### Basic facts about the `p`-biased measure -/

