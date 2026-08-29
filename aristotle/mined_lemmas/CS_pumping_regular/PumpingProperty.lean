/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- The (classical) pumping property of a language `L`: there is a pumping length `p > 0`
such that every word `w ∈ L` of length at least `p` can be split as `w = x ++ y ++ z`
with `|x ++ y| ≤ p`, `y ≠ []`, and `x ++ yⁿ ++ z ∈ L` for every `n : ℕ`. -/

def PumpingProperty {α : Type*} (L : Language α) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
    ∃ x y z : List α, w = x ++ y ++ z ∧ (x ++ y).length ≤ p ∧ y ≠ [] ∧
      ∀ n : ℕ, x ++ (List.replicate n y).flatten ++ z ∈ L

/-- Auxiliary: any finite concatenation of copies of `b` lies in the Kleene star `{b}∗`. -/
