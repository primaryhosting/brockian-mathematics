import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

namespace Frontier

/-! ## The Kneser graph -/

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

lemma arc_period (i : ℕ) : arc k (i + (2 * k + 1) * k) = arc k i := by
  have haux : ∀ t : ℕ, (i + (2 * k + 1) * k + t) % (2 * k + 1) = (i + t) % (2 * k + 1) := by
    intro t
    rw [show i + (2 * k + 1) * k + t = (i + t) + (2 * k + 1) * k by ring,
      Nat.add_mul_mod_self_left]
  ext x
  simp only [mem_arc]
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, by rw [hx, haux]⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, by rw [hx, haux]⟩

/-- The arc `arc k i` viewed as a vertex of `KG_{2k+1,k}`. -/
