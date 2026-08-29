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

theorem kneser_odd_chromaticNumber (hk : 1 ≤ k) :
    (kneserGraph (2 * k + 1) k).chromaticNumber = 3 := by
  have hcol : (kneserGraph (2 * k + 1) k).Colorable 3 := by
    have h := kneser_colorable (2 * k + 1) k hk (by omega)
    have he : 2 * k + 1 - 2 * k + 2 = 3 := by omega
    rwa [he] at h
  have h3 : ((2 : ℕ) : ℕ∞) + 1 = 3 := by norm_num
  rw [← h3, SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  exact ⟨hcol, kneser_odd_not_colorable_two k hk⟩

end Odd

/-! ## The case `n = 2k`: a perfect matching -/

/-- The case `n = 2k`: `KG_{2k,k}` is a perfect matching, so `χ = 2`. -/
