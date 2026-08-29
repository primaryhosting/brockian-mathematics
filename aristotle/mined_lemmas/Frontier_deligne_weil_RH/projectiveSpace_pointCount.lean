/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

namespace Frontier

/-- The cohomological data attached to a smooth projective variety of dimension `dim`
over the finite field `𝔽_q`: for each degree `i`, the multiset `eigen i` of eigenvalues
of the geometric Frobenius acting on the `i`-th ℓ-adic cohomology group. -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The base field is a genuine finite field. -/
  hq : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- Multiset of Frobenius eigenvalues in cohomological degree `i`. -/
  eigen : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanish : ∀ i, 2 * dim < i → eigen i = 0
  /-- Frobenius acts invertibly, so all eigenvalues are nonzero. -/
  nonzero : ∀ i, ∀ a ∈ eigen i, a ≠ 0

namespace WeilData

variable (W : WeilData)

/-- The Lefschetz trace formula prediction for the number of `𝔽_{q^m}`-rational points:
`N_m = ∑_i (-1)^i tr(Frob^m ∣ H^i)`. -/

theorem projectiveSpace_pointCount (n q : ℕ) (hq : 1 < q) (m : ℕ) :
    (projectiveSpace n q hq).pointCount m = ∑ j ∈ Finset.range (n + 1), (q : ℂ) ^ (j * m) := by
  rw [← sum_even_range n m (q : ℂ)]
  unfold WeilData.pointCount projectiveSpace
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  have hle : i ≤ 2 * n := by omega
  by_cases h : i % 2 = 0
  · have hs : (-1 : ℂ) ^ i = 1 := (Nat.even_iff.mpr h).neg_one_pow
    simp [h, hle, hs, ← pow_mul]
  · have hs : (-1 : ℂ) ^ i = -1 := (Nat.odd_iff.mpr (by omega)).neg_one_pow
    simp [h, hs]

/-- **Base case of the Weil Riemann hypothesis**: it holds for projective space. -/
