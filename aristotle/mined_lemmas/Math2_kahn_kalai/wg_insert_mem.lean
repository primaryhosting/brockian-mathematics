import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham proof):
the Bernoulli product measure on subsets of a finite ground set, covers,
`p`-smallness, up-sets, and the parameters `q(F)`, `p_c(F)`, `ℓ(F)`.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bernoulli(`p`) product weight of a subset `A` inside the ground set `g`. -/

lemma wg_insert_mem {x : α} {g₀ A : Finset α} (hx : x ∉ g₀) (hA : A ⊆ g₀) (p : ℝ) :
    wg (insert x g₀) p (insert x A) = p * wg g₀ p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have h1 : (insert x g₀).card = g₀.card + 1 := Finset.card_insert_of_notMem hx
  have h3 : (insert x A).card = A.card + 1 := Finset.card_insert_of_notMem hxA
  have h2 : A.card ≤ g₀.card := Finset.card_le_card hA
  simp only [wg, h1, h3]
  rw [show g₀.card + 1 - (A.card + 1) = g₀.card - A.card by omega, pow_succ]
  ring

/-- Union of two independent Bernoulli random subsets: the union of a `s`-random and an
independent `t`-random subset is `(s + t - s t)`-random. -/
