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

theorem hasse_weil_bound (W : WeilData) (g : ℕ) (hdim : W.dim = 1)
    (h0 : W.eigen 0 = {1}) (h2 : W.eigen 2 = {(W.q : ℂ)})
    (hg : (W.eigen 1).card = 2 * g) (hRH : W.RH) (m : ℕ) :
    ‖W.pointCount m - ((W.q : ℂ) ^ m + 1)‖ ≤ 2 * g * (W.q : ℝ) ^ ((m : ℝ) / 2) := by
  have hq0 : (0 : ℝ) < (W.q : ℝ) := by
    have h1 := W.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le
  set S : ℂ := ((W.eigen 1).map (fun a => a ^ m)).sum with hS
  have hpc : W.pointCount m = 1 - S + (W.q : ℂ) ^ m := by
    rw [WeilData.pointCount, hdim, show 2 * 1 + 1 = 3 from rfl, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h2]
    simp [hS]
    ring
  have hdiff : W.pointCount m - ((W.q : ℂ) ^ m + 1) = -S := by rw [hpc]; ring
  rw [hdiff, norm_neg]
  have hbound : ‖S‖ ≤ ((W.eigen 1).map (fun a => ‖a ^ m‖)).sum := by
    rw [hS]
    simpa [Multiset.map_map, Function.comp] using
      norm_multiset_sum_le ((W.eigen 1).map (fun a => a ^ m))
  have hconst : ((W.eigen 1).map (fun a => ‖a ^ m‖))
      = Multiset.replicate (W.eigen 1).card ((W.q : ℝ) ^ ((m : ℝ) / 2)) := by
    rw [← Multiset.map_const']
    refine Multiset.map_congr rfl ?_
    intro a ha
    rw [norm_pow, hRH 1 a ha,
      ← Real.rpow_natCast ((W.q : ℝ) ^ (((1 : ℕ) : ℝ) / 2)) m, ← Real.rpow_mul hq0.le]
    norm_num
    ring_nf
  rw [hconst, Multiset.sum_replicate, hg] at hbound
  simpa [nsmul_eq_mul] using hbound

/-- **Deligne's Riemann hypothesis for varieties over finite fields.**

The Frobenius-eigenvalue formulation of the Weil Riemann hypothesis is `Frontier.WeilData.RH`:
every eigenvalue of the geometric Frobenius on the degree-`i` cohomology of a smooth
projective variety over `𝔽_q` has absolute value `q^{i/2}`.  This theorem records:

* a Lean-checked reduction: that formulation is *equivalent* to the classical statement
  that, writing `T = q^{-s}`, all zeros of the degree-`i` factor `P_i(T)` of the zeta
  function lie on the critical line `Re s = i / 2`;
* a Lean-checked reduction to low degrees: under Poincaré duality, the Riemann hypothesis
  in degrees `i ≤ dim` implies it in all degrees;
* stability under products (Künneth);
* the classical consequence for curves, the Hasse–Weil bound
  `|N_m - (q^m + 1)| ≤ 2g·q^{m/2}`;
* the base case of the conjecture, for projective space `ℙ^n` over `𝔽_q`, together with
  its point counts `1 + q^m + ⋯ + q^{nm}` and its zeta function `1/∏_{j≤n}(1 - q^j T)`. -/
