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

namespace Math2

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

lemma card_le_sum_tent {theta : ℕ → ℝ} {a b delta : ℝ} (hd : 0 < delta) (N : ℕ) :
    (((primesBelow N).filter (fun p => theta p ∈ Set.Icc a b)).card : ℝ)
      ≤ ∑ p ∈ primesBelow N, tent (a - delta) (b + delta) delta (theta p) := by
  classical
  rw [← Finset.sum_boole (fun p => theta p ∈ Set.Icc a b) (primesBelow N)]
  refine Finset.sum_le_sum ?_
  intro p _
  by_cases hp : theta p ∈ Set.Icc a b
  · rw [if_pos hp]
    rw [Set.mem_Icc] at hp
    exact le_of_eq (tent_eq_one hd (by linarith [hp.1]) (by linarith [hp.2])).symm
  · rw [if_neg hp]
    exact tent_nonneg _ _ _ _

/-! ## The main theorem -/

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `W` be an integral Weierstrass model of an elliptic curve and let
`θ_p = arccos (a_p / (2√p))` be its Frobenius angles, where `a_p = p + 1 - #E(𝔽_p)`.
Assume the Sato–Tate equidistribution law (`SatoTateHolds W`), stated in Weyl form for
continuous test functions; by the theorem of Clozel–Harris–Shepherd-Barron–Taylor this
holds for every elliptic curve over `ℚ` without complex multiplication.

Then, for every subinterval `[α, β] ⊆ [0, π]`, the natural density of the primes whose
Frobenius angle lies in `[α, β]` exists and equals the Sato–Tate measure of `[α, β]`:
`(2/π) ∫_α^β sin²θ dθ`. -/
