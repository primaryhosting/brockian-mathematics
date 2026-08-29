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

theorem sum_divisors_swap (x : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc 0 x, ∑ d ∈ n.divisors, f d
      = ∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * f d := by
  classical
  have step1 : ∀ n ∈ Finset.Ioc 0 x, ∑ d ∈ n.divisors, f d
      = ∑ d ∈ Finset.Ioc 0 x, if d ∣ n then f d else 0 := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨hdvd, hn0⟩
      have := Nat.le_of_dvd hn.1 hdvd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn.1, by omega⟩, hdvd⟩
    · rintro ⟨⟨hd0, -⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  exact Nat.Ioc_filter_dvd_card_eq_div x d

/-- The abundancy of `n` is the sum of the reciprocals of its divisors. -/
