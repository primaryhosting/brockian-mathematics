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

/-- Cohomological data attached to a smooth projective variety of dimension `dim` over the
finite field `𝔽_q`: for each degree `i` the (multi)set `frobEigenvalues i` of eigenvalues of
the geometric Frobenius acting on the `i`-th étale cohomology group, which vanishes outside
degrees `0, …, 2 dim`.

Étale cohomology is not available in Mathlib, so the cohomological input of the Weil
conjectures is packaged here as data; all statements below are statements about this data. -/
structure WeilData where
  /-- The size of the base field. -/
  q : ℕ
  /-- The base field is a genuine finite field, so it has at least two elements. -/
  one_lt_q : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- The eigenvalues of the geometric Frobenius on the `i`-th cohomology group. -/
  frobEigenvalues : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobEigenvalues i = 0

namespace WeilData

variable (W : WeilData)

/-- The number of `𝔽_{q^m}`-rational points of the variety, as computed by the
Grothendieck–Lefschetz trace formula
`N_m = ∑_i (-1)^i ∑_j α_{i,j}^m`. -/

theorem projectiveSpaceData_pointCount (q n : ℕ) (hq : 1 < q) (m : ℕ) :
    (projectiveSpaceData q n hq).pointCount m =
      ∑ j ∈ Finset.range (n + 1), ((q : ℂ) ^ m) ^ j := by
  rw [WeilData.pointCount]
  have key : ∀ i ∈ Finset.range (2 * (projectiveSpaceData q n hq).dim + 1),
      (-1 : ℂ) ^ i * (((projectiveSpaceData q n hq).frobEigenvalues i).map (fun α => α ^ m)).sum
        = if Even i then ((q : ℂ) ^ m) ^ (i / 2) else 0 := by
    intro i hi
    simp only [Finset.mem_range, projectiveSpaceData] at hi ⊢
    by_cases he : Even i
    · rw [if_pos ⟨he, by omega⟩, if_pos he, he.neg_one_pow]
      simp [← pow_mul, Nat.mul_comm]
    · rw [if_neg (by tauto), if_neg he]
      simp
  rw [Finset.sum_congr rfl key]
  exact sum_even_range n _

/-- The Lefschetz point count of the Weil data of `ℙ^n` over `𝔽_q` really is the number of
points of `ℙ^n` over a field with `q^m` elements. -/
