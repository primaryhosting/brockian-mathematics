/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma primesBelow_card_pos {X : ℕ} (hX : 3 ≤ X) : 0 < (primesBelow X).card :=
  Finset.card_pos.2 ⟨2, by simp [primesBelow, Nat.prime_two]; omega⟩

/-! ### The main equidistribution statement -/

/-- From equidistribution against continuous test functions we obtain equidistribution
against intervals: the proportion of primes `p < X` whose Frobenius angle lies in `[α, β]`
converges to the Sato–Tate mass of `[α, β]`. -/
