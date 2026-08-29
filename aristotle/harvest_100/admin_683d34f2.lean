/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers.Dynamics

/-- The divisor-sum function `σ₁ n = ∑_{d ∣ n} d`, computed as the sum of all
divisors of `n` in `{0, 1, …, n}` (note `0 ∣ n` only when `n = 0`, in which case
the contribution is `0`, so `sigma1 0 = 0`).

This file is deliberately free of `import` statements, because the required
header comment must be the very first thing in the file and Lean does not allow
any command (including a module docstring) to precede `import`.  The companion
file `RequestProject/BetrothedNumbersMathlib.lean` proves that `sigma1` agrees
with Mathlib's `ArithmeticFunction.sigma 1` and restates the main theorem in
Mathlib's language. -/
def sigma1 (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => decide (d ∣ n))).sum

/-- The "betrothed partner" map `partner n = σ₁(n) - n - 1`: the sum of the
divisors of `n` other than `1` and `n` itself (truncated natural subtraction). -/
def partner (n : Nat) : Nat := sigma1 n - n - 1

/-- Two positive integers `m ≠ n` form a *betrothed* (quasi-amicable) pair when
`σ₁(m) = σ₁(n) = m + n + 1`, i.e. each is the sum of the nontrivial proper
divisors (proper divisors excluding `1`) of the other. -/
def IsBetrothedPair (m n : Nat) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma1 m = m + n + 1 ∧ sigma1 n = m + n + 1

/-- If `partner m = n` with `n` positive, then the truncated subtraction in the
definition of `partner` is exact: `σ₁(m) = m + n + 1`. -/
theorem sigma1_eq_of_partner_eq {m n : Nat} (hn : 0 < n) (h : partner m = n) :
    sigma1 m = m + n + 1 := by
  unfold partner at h
  omega

/-- **Betrothed pairs are exactly the positive nontrivial `2`-cycles of the
partner map** `partner n = σ₁(n) - n - 1`. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : Nat) :
    IsBetrothedPair m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> unfold partner <;> omega
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    have h₁ := sigma1_eq_of_partner_eq hn hpm
    have h₂ := sigma1_eq_of_partner_eq hm hpn
    exact ⟨hm, hn, hmn, h₁, by omega⟩

/-- Sanity check: `(48, 75)` is the smallest betrothed pair. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩ <;> rfl

end Brockian.BetrothedNumbers.Dynamics

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

import Mathlib
import RequestProject.BetrothedNumbers

/-!
# Betrothed numbers: bridge to Mathlib's `ArithmeticFunction.sigma`

The target theorem
`Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle`
lives in `RequestProject/BetrothedNumbers.lean`, a file that carries a mandated
header comment as its very first content and therefore cannot contain any
`import` command.  Here we check that the self-contained divisor-sum function
`sigma1` used there is literally Mathlib's `σ₁ = ArithmeticFunction.sigma 1`,
and we restate the characterization in Mathlib's language.
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers.Dynamics

/-- Summing a filtered `List.range` is the same as an `if`-guarded `Finset.range` sum. -/
theorem sum_list_range_filter_dvd (m n : ℕ) :
    ((List.range m).filter (fun d => decide (d ∣ n))).sum
      = ∑ d ∈ Finset.range m, if d ∣ n then d else 0 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.sum_append, ih, Finset.sum_range_succ]
    by_cases h : k ∣ n <;> simp [h]

/-- The self-contained `sigma1` agrees with Mathlib's `σ₁`. -/
theorem sigma1_eq_sigma (n : ℕ) : sigma1 n = sigma 1 n := by
  rw [sigma1, sum_list_range_filter_dvd, sigma_one_apply,
    show n.divisors = Finset.filter (· ∣ n) (Finset.Ico 1 (n + 1)) from rfl,
    Finset.sum_filter, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp

/-- The partner map in Mathlib's language: `partner n = σ₁(n) - n - 1`. -/
theorem partner_eq (n : ℕ) : partner n = sigma 1 n - n - 1 := by
  rw [partner, sigma1_eq_sigma]

/-- Betrothed pairs, stated with Mathlib's `σ₁`, are exactly the positive
nontrivial `2`-cycles of `n ↦ σ₁(n) - n - 1`. -/
theorem isBetrothedPair_iff_nontrivial_twoCycle_sigma (m n : ℕ) :
    (0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1) ↔
      (0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m - m - 1 = n ∧ sigma 1 n - n - 1 = m) := by
  have h := isBetrothedPair_iff_nontrivial_twoCycle m n
  rw [IsBetrothedPair] at h
  simpa [partner_eq, sigma1_eq_sigma] using h

end Brockian.BetrothedNumbers.Dynamics

