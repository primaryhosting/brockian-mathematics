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

theorem projectiveSpace_zeta (n q : ℕ) (hq : 1 < q) (T : ℂ) :
    (projectiveSpace n q hq).zeta T = 1 / ∏ j ∈ Finset.range (n + 1), (1 - (q : ℂ) ^ j * T) := by
  have heig : ∀ i, (projectiveSpace n q hq).eigen i
      = if i % 2 = 0 ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0 := fun _ => rfl
  have hdim : (projectiveSpace n q hq).dim = n := rfl
  have hodd : ∀ i ∈ (Finset.range (2 * n + 1)).filter (fun i => i % 2 = 1),
      (projectiveSpace n q hq).charPoly i T = 1 := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    have h : ¬ (i % 2 = 0 ∧ i ≤ 2 * n) := by omega
    simp [WeilData.charPoly, heig i, h]
  have heven : ∀ i ∈ (Finset.range (2 * n + 1)).filter (fun i => i % 2 = 0),
      (projectiveSpace n q hq).charPoly i T = 1 - (q : ℂ) ^ (i / 2) * T := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have h : i % 2 = 0 ∧ i ≤ 2 * n := ⟨hi.2, by omega⟩
    simp [WeilData.charPoly, heig i, h]
  rw [WeilData.zeta, hdim, Finset.prod_congr rfl hodd, Finset.prod_congr rfl heven,
    Finset.prod_const_one, prod_filter_even_range n (fun j => 1 - (q : ℂ) ^ j * T)]

/-- **The critical-line reformulation.** Writing `T = q^{-s}`, the statement that all
Frobenius eigenvalues in degree `i` have absolute value `q^{i/2}` is equivalent to the
statement that all zeros of `P_i(q^{-s})` lie on the line `Re s = i / 2`. -/
