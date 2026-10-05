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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Brockian.BetrothedNumbers.Basic

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Elementary analytic input: numbers of large abundancy are rare

This file proves, unconditionally, the analytic-number-theory ingredients of the
reduction:

* `Brockian.BetrothedNumbers.sum_divisors_swap`: Dirichlet's hyperbola-style
  interchange `∑_{n ≤ x} ∑_{d ∣ n} f d = ∑_{d ≤ x} ⌊x/d⌋ f d`;
* `Brockian.BetrothedNumbers.sum_sigma_div_self_le`: the mean value bound
  `∑_{n ≤ x} σ(n)/n ≤ 2x`;
* `Brockian.BetrothedNumbers.abundant_count_le`: the Markov/Chebyshev bound
  `#{n ≤ x : σ(n) > K n} ≤ 2x/K`;
* `Brockian.BetrothedNumbers.hasDensityZero_of_forall_le`: a convenient
  criterion for asymptotic density zero.
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- The set of integers of abundancy larger than `K`, i.e. `σ(n) > K n`. -/

theorem countUpTo_skew_le (K x : ℕ) (hK : 1 ≤ K) :
    countUpTo (skewBetrothedSet K) x ≤ countUpTo (abundantSet K) x := by
  refine Set.ncard_le_ncard_of_injOn partner ?_ ?_ (finite_inter_Iic _ x)
  · rintro n ⟨⟨hb, hlt⟩, hx⟩
    have hple : partner n ≤ K * partner n := Nat.le_mul_of_pos_left _ (by omega)
    have hpn : partner n < n := lt_of_le_of_lt hple hlt
    refine ⟨⟨hb.partner_pos, ?_⟩, ?_⟩
    · have : sigma 1 (partner n) = n + partner n + 1 := hb.sigma_partner_eq
      omega
    · exact le_trans hpn.le hx
  · rintro a ⟨⟨hba, -⟩, -⟩ b ⟨⟨hbb, -⟩, -⟩ hab
    have := hba.partner_partner
    rw [hab, hbb.partner_partner] at this
    exact this.symm

/-- Counting bound: for every `K`, the betrothed numbers up to `x` are at most
`2 · #{n ≤ x : σ n > K n}` plus the balanced betrothed numbers up to `x`. -/
