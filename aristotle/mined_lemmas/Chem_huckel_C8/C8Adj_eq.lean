import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₈`; this is the Hückel matrix of
cyclooctatetraene in the units where the Coulomb integral is `0` and the resonance
integral is `1`. -/

lemma C8Adj_eq : C8Adj = shift + shift ^ 7 := by
  rw [shift_pow_seven]
  ext i j
  rw [C8Adj, SimpleGraph.adjMatrix_apply, Matrix.add_apply, shift_apply, shiftInv_apply]
  by_cases h1 : j = i - 1
  · have h2 : ¬ (j = i + 1) := by rw [h1]; exact fin8_sub_one_ne_add_one i
    rw [if_pos ((cycleGraph8_adj_iff i j).2 (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : j = i + 1
    · rw [if_pos ((cycleGraph8_adj_iff i j).2 (Or.inr h2)), if_neg h1, if_pos h2, zero_add]
    · rw [if_neg (fun hA => ((cycleGraph8_adj_iff i j).1 hA).elim h1 h2), if_neg h1, if_neg h2,
        add_zero]

/-- `C₈`'s adjacency matrix is annihilated by `X⁵ - 6X³ + 8X = X(X²-2)(X²-4)`.
This follows purely from `shift ^ 8 = 1`, since modulo `X⁸ - 1` the polynomial
`(X + X⁷)⁵ - 6(X + X⁷)³ + 8(X + X⁷)` vanishes. -/
