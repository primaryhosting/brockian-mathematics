import Mathlib
/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

namespace QI

open Finset Complex

/-!
## The Shor sampling distribution

We model the period-finding core of Shor's algorithm.  Fix a modulus `N`, a unit
`u : (ZMod N)ˣ` and a power-of-two-sized (any size, really) register `Q`.
The algorithm prepares

  `Q^{-1/2} ∑_{j < Q} |j⟩ |u ^ j⟩`,

applies the quantum Fourier transform modulo `Q` to the first register and
measures.  The probability of observing `c` in the first register and `y` in the
second one is `Q^{-2} ‖∑_{j < Q, u ^ j = y} e^{2πι c j / Q}‖^2`, so the marginal
probability of observing `c` is the following quantity.
-/

/-- Probability that Shor's period-finding circuit, run with modulus `N`, base `u`
and register size `Q`, outputs the value `c`. -/

lemma determines_of_close {Q M r s : ℕ} (hr : 0 < r) (hrM : r ≤ M) (hMQ : M ^ 2 < Q)
    (hs : Nat.Coprime s r) {c : ℕ} (hc : |(c : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q)) :
    DeterminesPeriod Q M r c := by
  have hQ : 0 < Q := lt_of_le_of_lt (Nat.zero_le _) hMQ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨⟨s, hs, hc⟩, ?_⟩
  intro s' r' hr' hr'M hs' hc'
  have hr'R : (0 : ℝ) < r' := by exact_mod_cast hr'
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htri : |(s : ℝ) / r - (s' : ℝ) / r'| ≤ 1 / Q := by
    calc |(s : ℝ) / r - (s' : ℝ) / r'|
        = |((c : ℝ) / Q - (s' : ℝ) / r') - ((c : ℝ) / Q - (s : ℝ) / r)| := by ring_nf
      _ ≤ |(c : ℝ) / Q - (s' : ℝ) / r'| + |(c : ℝ) / Q - (s : ℝ) / r| := abs_sub _ _
      _ ≤ 1 / (2 * Q) + 1 / (2 * Q) := by linarith
      _ = 1 / Q := by field_simp; ring
  have hnum : (s : ℤ) * r' = (s' : ℤ) * r := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |((s : ℤ) * r' - (s' : ℤ) * r : ℤ)| := by
      have h1' : (1 : ℤ) ≤ |((s : ℤ) * r' - (s' : ℤ) * r)| := Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast h1'
    have heq : (s : ℝ) / r - (s' : ℝ) / r'
        = (((s : ℤ) * r' - (s' : ℤ) * r : ℤ) : ℝ) / (r * r') := by
      push_cast
      field_simp
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (r : ℝ) * r')] at htri
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at htri
    have hrr : ((r : ℝ) * r') ≤ (M : ℝ) * M := by
      have k1 : (r : ℝ) ≤ M := by exact_mod_cast hrM
      have k2 : (r' : ℝ) ≤ M := by exact_mod_cast hr'M
      nlinarith
    have hMQ' : ((M : ℝ) * M) < Q := by
      have : ((M : ℝ) ^ 2) < Q := by exact_mod_cast hMQ
      nlinarith
    push_cast at htri h1
    nlinarith [htri, h1]
  have h0 : (s * r' : ℕ) = s' * r := by exact_mod_cast hnum
  have hdvd1 : r ∣ r' := by
    have hd : r ∣ s * r' := ⟨s', by rw [h0, mul_comm]⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hd
  have hdvd2 : r' ∣ r := by
    have hd : r' ∣ s' * r := ⟨s, by rw [← h0, mul_comm]⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs') hd
  exact Nat.dvd_antisymm hdvd2 hdvd1

/-- The rounded sample `c_s = round (s Q / r)`. -/
