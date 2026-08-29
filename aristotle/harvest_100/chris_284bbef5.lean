import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede every other command, including module
doc comments, so this header follows the single `import Mathlib` line.)
-/

namespace QI

/-!
## Overview

Shor's algorithm finds the period `r` of the modular exponentiation function
`x ↦ a ^ x mod N` (for `a` coprime to `N`).  Its structure is:

* the function `x ↦ a ^ x mod N` really is periodic, with least period the
  multiplicative order `r` of `a` modulo `N`;
* the quantum phase-estimation stage produces, with probability bounded below by
  some constant `c > 0`, a measurement outcome `y` whose rescaling `y / M`
  approximates a fraction `s / r` with `gcd (s, r) = 1` to within `1 / (2 M)`
  (such an approximating outcome always exists, by rounding);
* the classical post-processing stage (continued fractions) then recovers `r`
  *exactly*, because a rational number with a sufficiently small denominator is
  uniquely determined by an approximation of this quality: any fraction `p / q`
  in lowest terms with `q * r < M` that is that close to `y / M` must have
  `q = r`;
* repeating the experiment amplifies the success probability to `1`.

The theorem `QI.shor_period` below bundles these statements.  The quantum stage
enters only through the abstract success probability `c`, since the amplitude
analysis is not part of the number-theoretic content formalized here.
-/

/-- Two rational numbers with small denominators cannot both be very close to the
same rational `x`: this is the uniqueness statement underlying the classical
continued-fraction post-processing of Shor's algorithm. -/
theorem approx_unique {x Q : ℚ} {p q s r : ℤ} (hq : 0 < q) (hr : 0 < r)
    (hQ : (q : ℚ) * r < Q ^ 2)
    (hp : |x - (p : ℚ) / q| ≤ 1 / (2 * Q ^ 2))
    (hs : |x - (s : ℚ) / r| ≤ 1 / (2 * Q ^ 2)) :
    (p : ℚ) / q = (s : ℚ) / r := by
  have hq' : (0:ℚ) < q := by exact_mod_cast hq
  have hr' : (0:ℚ) < r := by exact_mod_cast hr
  have hQ2 : (0:ℚ) < Q ^ 2 := lt_of_le_of_lt (by positivity) hQ
  by_contra hne
  have hdiff : |(p : ℚ) / q - (s : ℚ) / r| ≤ 1 / Q ^ 2 := by
    calc |(p : ℚ) / q - (s : ℚ) / r| ≤ |(p:ℚ)/q - x| + |x - (s:ℚ)/r| := abs_sub_le _ _ _
      _ ≤ 1/(2*Q^2) + 1/(2*Q^2) := by
          gcongr
          · rw [abs_sub_comm]; exact hp
      _ = 1/Q^2 := by field_simp; ring
  have hnum : ((p * r - s * q : ℤ) : ℚ) ≠ 0 := by
    intro h
    apply hne
    push_cast at h
    field_simp
    linarith
  have h1 : (1:ℚ) ≤ |((p * r - s * q : ℤ) : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by exact_mod_cast hnum)
  have heq : (p:ℚ)/q - (s:ℚ)/r = ((p*r - s*q : ℤ):ℚ)/((q:ℚ)*r) := by
    push_cast; field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℚ) < (q:ℚ)*r)] at hdiff
  have h2 : (1:ℚ)/((q:ℚ)*r) ≤ 1/Q^2 := le_trans (by gcongr) hdiff
  have hlt : (1:ℚ)/Q^2 < 1/((q:ℚ)*r) := one_div_lt_one_div_of_lt (by positivity) hQ
  linarith

/-- Equal fractions in lowest terms have equal (positive) denominators. -/
theorem denom_eq_of_div_eq_div {p q s r : ℤ} (hq : 0 < q) (hr : 0 < r)
    (hpq : IsCoprime p q) (hsr : IsCoprime s r) (h : (p : ℚ) / q = (s : ℚ) / r) :
    q = r := by
  have hq' : (0:ℚ) < q := by exact_mod_cast hq
  have hr' : (0:ℚ) < r := by exact_mod_cast hr
  have hcross : p * r = s * q := by
    have : (p:ℚ) * r = (s:ℚ) * q := by field_simp at h; linarith
    exact_mod_cast this
  have h1 : q ∣ r := (hpq.symm).dvd_of_dvd_mul_left ⟨s, by linarith [hcross]⟩
  have h2 : r ∣ q := (hsr.symm).dvd_of_dvd_mul_left ⟨p, by linarith [hcross]⟩
  exact Int.dvd_antisymm hq.le hr.le h1 h2

/-- The classical post-processing step of Shor's algorithm: from a rational `x`
approximating `s / r` (with `s` coprime to `r`) to within `1 / (2 Q ^ 2)`, the
period `r` is recovered uniquely, i.e. any reduced fraction `p / q` with
`q * r < Q ^ 2` and the same approximation quality has `q = r`. -/
theorem period_recovery {x Q : ℚ} {p q s r : ℤ} (hq : 0 < q) (hr : 0 < r)
    (hpq : IsCoprime p q) (hsr : IsCoprime s r)
    (hQ : (q : ℚ) * r < Q ^ 2)
    (hp : |x - (p : ℚ) / q| ≤ 1 / (2 * Q ^ 2))
    (hs : |x - (s : ℚ) / r| ≤ 1 / (2 * Q ^ 2)) :
    q = r :=
  denom_eq_of_div_eq_div hq hr hpq hsr (approx_unique hq hr hQ hp hs)

/-- Existence of a good measurement outcome: for every target fraction `z` and
every scale `M > 0` there is an integer `y` with `|y / M - z| ≤ 1 / (2 M)`. -/
theorem exists_good_outcome (z : ℚ) {M : ℚ} (hM : 0 < M) :
    ∃ y : ℤ, |(y : ℚ) / M - z| ≤ 1 / (2 * M) := by
  refine ⟨round (M * z), ?_⟩
  have hkey : |(round (M * z) : ℚ) - M * z| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round (M * z)
  have : (round (M * z) : ℚ) / M - z = ((round (M * z) : ℚ) - M * z) / M := by
    field_simp
  rw [this, abs_div, abs_of_pos hM]
  calc |(round (M * z) : ℚ) - M * z| / M ≤ (1/2) / M := by gcongr
    _ = 1 / (2 * M) := by field_simp

/-- Probability amplification: if each run succeeds with probability at least
`c > 0`, the probability that at least one of `k` independent runs succeeds
tends to `1`. -/
theorem success_amplification {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto (fun k : ℕ => 1 - (1 - c) ^ k) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun k : ℕ => (1 - c) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  simpa using h.const_sub (1 : ℝ)

/-- **Shor's period finding.**

For `a` coprime to `N > 1` there is a positive integer `r` such that:

1. `x ↦ a ^ x mod N` is periodic with period `r`;
2. `r` is the *least* period (so `r` is exactly the quantity Shor's algorithm
   must output);
3. for any scale `M > 0` there is an integer measurement outcome `y` with
   `y / M` within `1 / (2 M)` of `s / r` — the outcomes the phase-estimation
   stage concentrates on;
4. such an outcome determines `r` uniquely: any reduced fraction `p / q` with
   `q * r < Q ^ 2` lying within `1 / (2 Q ^ 2)` of the same value as a reduced
   fraction `s / r` satisfies `q = r`, i.e. the classical continued-fraction
   post-processing recovers the period exactly;
5. if a single run succeeds with probability at least `c > 0`, then repeating
   the algorithm drives the overall success probability to `1` — the algorithm
   succeeds with high probability. -/
theorem shor_period (N a : ℕ) (hN : 1 < N) (hcop : Nat.Coprime a N)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ r : ℕ, 0 < r ∧
      (∀ x : ℕ, a ^ (x + r) ≡ a ^ x [MOD N]) ∧
      (∀ t : ℕ, 0 < t → t < r → ¬ (∀ x : ℕ, a ^ (x + t) ≡ a ^ x [MOD N])) ∧
      (∀ (s : ℤ) (M : ℚ), 0 < M →
        ∃ y : ℤ, |(y : ℚ) / M - (s : ℚ) / (r : ℚ)| ≤ 1 / (2 * M)) ∧
      (∀ (x Q : ℚ) (s p q : ℤ), 0 < q → IsCoprime p q → IsCoprime s (r : ℤ) →
        (q : ℚ) * (r : ℚ) < Q ^ 2 →
        |x - (s : ℚ) / (r : ℚ)| ≤ 1 / (2 * Q ^ 2) →
        |x - (p : ℚ) / (q : ℚ)| ≤ 1 / (2 * Q ^ 2) → q = (r : ℤ)) ∧
      Filter.Tendsto (fun k : ℕ => 1 - (1 - c) ^ k) Filter.atTop (nhds 1) := by
  haveI : NeZero N := ⟨(Nat.zero_lt_of_lt hN).ne'⟩
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime a hcop with hu
  set r : ℕ := orderOf u with hrdef
  have hcoe : ((u : ZMod N)) = (a : ZMod N) := ZMod.coe_unitOfCoprime a hcop
  have hrpos : 0 < r := orderOf_pos u
  have hpow : (a : ZMod N) ^ r = 1 := by
    rw [← hcoe, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]; rfl
  refine ⟨r, hrpos, ?_, ?_, ?_, ?_, success_amplification hc0 hc1⟩
  · -- periodicity
    intro x
    have : ((a ^ (x + r) : ℕ) : ZMod N) = ((a ^ x : ℕ) : ZMod N) := by
      push_cast
      rw [pow_add, hpow, mul_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  · -- minimality
    intro t ht0 htr hper
    have h1 : a ^ (0 + t) ≡ a ^ 0 [MOD N] := hper 0
    have h2 : ((a ^ t : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
      simpa using this
    have h3 : u ^ t = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, hcoe]
      push_cast at h2
      simpa using h2
    have h4 : r ∣ t := orderOf_dvd_of_pow_eq_one h3
    exact absurd (Nat.le_of_dvd ht0 h4) (not_le.mpr htr)
  · -- existence of a good outcome
    intro s M hM
    exact exists_good_outcome _ hM
  · -- unique recovery of the period
    intro x Q s p q hq hpq hsr hQ hs hp
    exact period_recovery hq (by exact_mod_cast hrpos) hpq hsr hQ hp hs

end QI

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

