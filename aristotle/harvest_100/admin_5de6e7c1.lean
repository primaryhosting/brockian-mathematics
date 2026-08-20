/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Shor's period-finding algorithm

This file formalises the mathematical content of Shor's period finding algorithm
for the modular exponentiation function `x ↦ a ^ x mod N`:

* the function is periodic with minimal period `r = orderOf (a : ZMod N)`;
* the quantum part: after the quantum Fourier transform of size `2 ^ n` is applied to
  the periodic superposition `∑_{j < M} |x₀ + j r⟩` (exact case `r * M = 2 ^ n`),
  the probability of measuring `c` is `1 / r` if `M ∣ c` and `0` otherwise, i.e.
  the measured `c` satisfies `c / 2 ^ n = s / r` for a uniformly random `s < r`;
* the classical post-processing: from a rational approximation of `s / r` within
  `1 / (2 R ^ 2)`, with `gcd (s, r) = 1` and `r ≤ R`, the denominator `r` is uniquely
  determined (this is the content of the continued fraction step);
* the success probability: the number of good `s < r` (those coprime to `r`) is
  `φ r`, so a single run succeeds with probability `φ r / r > 0`, and repeating
  the algorithm drives the failure probability to `0`.
-/

namespace QI

open Finset Complex
open scoped Classical

/-- The modular exponentiation function `x ↦ a ^ x` in `ZMod N`. -/
def modExp (N a x : ℕ) : ZMod N := (a : ZMod N) ^ x

/-- The period of the modular exponentiation function, i.e. the multiplicative order of
`a` modulo `N`. -/
noncomputable def period (N a : ℕ) : ℕ := orderOf ((a : ZMod N))

/-- The primitive `2 ^ n`-th root of unity used by the quantum Fourier transform. -/
noncomputable def qftRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ n))

/-- The amplitude of the basis state `|c⟩` after applying the quantum Fourier transform of
size `2 ^ n` to the normalised periodic superposition `M ^ (-1/2) ∑_{j < M} |x₀ + j r⟩`. -/
noncomputable def qftAmp (n r M x0 c : ℕ) : ℂ :=
  ((Real.sqrt ((M : ℝ) * 2 ^ n) : ℝ) : ℂ)⁻¹ *
    ∑ j ∈ Finset.range M, qftRoot n ^ ((x0 + j * r) * c)

/-- The probability of measuring the outcome `c` in Shor's algorithm. -/
noncomputable def shorProb (n r M x0 c : ℕ) : ℝ := ‖qftAmp n r M x0 c‖ ^ 2

/-- The classical post-processing step: the denominator of the (unique, if it exists)
rational number with denominator at most `R` lying within `1 / (2 R ^ 2)` of `x`.
This is exactly what the continued fraction expansion of `x` computes. -/
noncomputable def recoverDen (x : ℚ) (R : ℕ) : ℕ :=
  if h : ∃ y : ℚ, y.den ≤ R ∧ |x - y| < 1 / (2 * (R : ℚ) ^ 2) then h.choose.den else 0

/-! ### Part 1: periodicity -/

lemma period_pos {N a : ℕ} (hN : 1 < N) (ha : Nat.Coprime a N) : 0 < period N a := by
  have hN0 : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN.le
  haveI : NeZero N := ⟨hN0⟩
  have h : ((ZMod.unitOfCoprime a ha : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) :=
    ZMod.coe_unitOfCoprime a ha
  rw [period, ← h, orderOf_units]
  exact orderOf_pos _

lemma pow_period (N a : ℕ) : (a : ZMod N) ^ period N a = 1 := pow_orderOf_eq_one _

lemma modExp_periodic (N a x : ℕ) : modExp N a (x + period N a) = modExp N a x := by
  simp [modExp, pow_add, pow_period]

lemma modExp_ne_of_lt_period {N a : ℕ} (t : ℕ) (ht : 0 < t) (htr : t < period N a) :
    modExp N a t ≠ modExp N a 0 := by
  simpa [modExp] using pow_ne_one_of_lt_orderOf ht.ne' htr

/-! ### Part 2: the quantum Fourier transform -/

/-- `qftRoot n` is a primitive `2 ^ n`-th root of unity. -/
lemma qftRoot_pow_eq_one_iff (n k : ℕ) : qftRoot n ^ k = 1 ↔ 2 ^ n ∣ k := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h2n : ((2:ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hI := Complex.I_ne_zero
  rw [qftRoot, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    field_simp at hm
    have hz : (k : ℤ) = 2 ^ n * m := by exact_mod_cast hm
    have hdvd : ((2 ^ n : ℕ) : ℤ) ∣ (k : ℤ) := ⟨m, by push_cast; exact hz⟩
    exact_mod_cast hdvd
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    push_cast
    field_simp

lemma norm_qftRoot (n : ℕ) : ‖qftRoot n‖ = 1 := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I / 2 ^ n)
      = ((2 * Real.pi / 2 ^ n : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    push_cast
    ring
  rw [qftRoot, hre, Complex.norm_exp_ofReal_mul_I]

/-- The geometric sum of the phases occurring in Shor's algorithm: it vanishes unless
`M ∣ c`, in which case it equals `M`.  This is the interference effect that makes the
algorithm work. -/
lemma geom_sum_qftRoot {n r M c : ℕ} (h : r * M = 2 ^ n) :
    ∑ j ∈ Finset.range M, qftRoot n ^ (j * r * c) = if M ∣ c then (M : ℂ) else 0 := by
  have hpos : 0 < r * M := by rw [h]; exact Nat.two_pow_pos n
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hzeta : ∀ j : ℕ, qftRoot n ^ (j * r * c) = (qftRoot n ^ (r * c)) ^ j := by
    intro j
    rw [← pow_mul]
    ring_nf
  simp only [hzeta]
  by_cases hd : M ∣ c
  · have h1 : qftRoot n ^ (r * c) = 1 := by
      rw [qftRoot_pow_eq_one_iff, ← h]
      exact mul_dvd_mul_left r hd
    simp [h1, hd]
  · have h1 : qftRoot n ^ (r * c) ≠ 1 := by
      rw [Ne, qftRoot_pow_eq_one_iff, ← h]
      intro hcon
      exact hd ((mul_dvd_mul_iff_left (a := r) hr.ne').1 hcon)
    have h2 : (qftRoot n ^ (r * c)) ^ M = 1 := by
      rw [← pow_mul, qftRoot_pow_eq_one_iff, ← h]
      exact ⟨c, by ring⟩
    rw [geom_sum_eq h1, h2, if_neg hd]
    simp

/-- **The measurement statistics of Shor's algorithm** (exact case `r * M = 2 ^ n`):
the outcome `c` occurs with probability `1 / r` if `M ∣ c`, and with probability `0`
otherwise. -/
lemma shorProb_eq {n r M x0 c : ℕ} (h : r * M = 2 ^ n) :
    shorProb n r M x0 c = if M ∣ c then 1 / (r : ℝ) else 0 := by
  have hpos : 0 < r * M := by rw [h]; exact Nat.two_pow_pos n
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hM : 0 < M := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hsum : ∑ j ∈ Finset.range M, qftRoot n ^ ((x0 + j * r) * c)
      = qftRoot n ^ (x0 * c) * (if M ∣ c then (M:ℂ) else 0) := by
    rw [← geom_sum_qftRoot (r := r) h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_add]
    ring_nf
  rw [shorProb, qftAmp, hsum, norm_mul, norm_mul, mul_pow, mul_pow]
  have h1 : ‖qftRoot n ^ (x0 * c)‖ = 1 := by rw [norm_pow, norm_qftRoot, one_pow]
  have hinv : ‖((Real.sqrt ((M:ℝ) * 2 ^ n) : ℝ) : ℂ)⁻¹‖ = (Real.sqrt ((M:ℝ) * 2 ^ n))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [h1, hinv, one_pow, one_mul]
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsq : (Real.sqrt ((M:ℝ) * 2 ^ n)) ^ 2 = (M:ℝ) * 2 ^ n := Real.sq_sqrt (by positivity)
  have hcast : ((2:ℝ) ^ n) = (r : ℝ) * M := by
    have h2 : ((r * M : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at h2
    linarith
  split_ifs with hd
  · rw [Complex.norm_natCast, inv_pow, hsq, hcast]
    field_simp
  · simp

/-- The number of multiples of `M` below `r * M` is `r`. -/
lemma card_multiples_lt (r M : ℕ) (hM : 0 < M) :
    ((Finset.range (r * M)).filter (fun c => M ∣ c)).card = r := by
  have himg : ((Finset.range (r * M)).filter (fun c => M ∣ c))
      = (Finset.range r).image (fun s => s * M) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hc, k, rfl⟩
      exact ⟨k, by nlinarith [hc], by ring⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by nlinarith, ⟨s, mul_comm _ _⟩⟩
  rw [himg, Finset.card_image_of_injective _ (fun x y hxy => by
    simpa [Nat.mul_left_inj hM.ne'] using hxy), Finset.card_range]

/-- The measurement probabilities sum to `1`: they do form a probability distribution. -/
lemma shorProb_sum {n r M x0 : ℕ} (h : r * M = 2 ^ n) :
    ∑ c ∈ Finset.range (2 ^ n), shorProb n r M x0 c = 1 := by
  have hpos : 0 < r * M := by rw [h]; exact Nat.two_pow_pos n
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hM : 0 < M := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  rw [← h]
  simp only [shorProb_eq h]
  rw [← Finset.sum_filter, Finset.sum_const, card_multiples_lt r M hM, nsmul_eq_mul]
  field_simp

/-! ### Part 3: classical post-processing (continued fractions) -/

/-- Two distinct rationals are at distance at least the inverse of the product of their
denominators. -/
lemma rat_dist_ge {y z : ℚ} (h : y ≠ z) : 1 / ((y.den : ℚ) * z.den) ≤ |y - z| := by
  have hy : (0:ℚ) < y.den := by exact_mod_cast y.pos
  have hz : (0:ℚ) < z.den := by exact_mod_cast z.pos
  set A : ℤ := y.num * z.den - z.num * y.den with hA
  have key : (y - z) * ((y.den : ℚ) * z.den) = (A : ℚ) := by
    have h1 : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
    have h2 : (z.num : ℚ) = z * z.den := (Rat.mul_den_eq_num z).symm
    push_cast [hA, h1, h2]
    ring
  have hAne : A ≠ 0 := by
    intro h0
    apply h
    have hzero : (y - z) * ((y.den : ℚ) * z.den) = 0 := by rw [key, h0]; simp
    rcases mul_eq_zero.1 hzero with h' | h'
    · linarith [sub_eq_zero.1 h']
    · exact absurd h' (ne_of_gt (mul_pos hy hz))
  have h1A : (1:ℚ) ≤ |(A:ℚ)| := by
    have h1 : (1:ℤ) ≤ |A| := Int.one_le_abs (by omega)
    calc (1:ℚ) ≤ ((|A| : ℤ) : ℚ) := by exact_mod_cast h1
      _ = |(A:ℚ)| := by push_cast; ring
  rw [div_le_iff₀ (mul_pos hy hz)]
  calc (1:ℚ) ≤ |(A:ℚ)| := h1A
    _ = |y - z| * ((y.den:ℚ) * z.den) := by
        rw [← key, abs_mul, abs_of_pos (mul_pos hy hz)]

/-- A fraction `s / r` in lowest terms has denominator `r`. -/
lemma den_div_of_coprime {s r : ℕ} (hr : 0 < r) (h : Nat.Coprime s r) :
    ((s : ℚ) / (r : ℚ)).den = r := by
  have hb : (0:ℤ) < (r:ℤ) := by exact_mod_cast hr
  have hd := Rat.den_div_eq_of_coprime (a := (s:ℤ)) (b := (r:ℤ)) hb (by simpa using h)
  have hcast : ((s:ℤ):ℚ) / ((r:ℤ):ℚ) = (s:ℚ)/(r:ℚ) := by push_cast; ring
  rw [hcast] at hd
  exact_mod_cast hd

/-- **Continued fraction step.**  If `x` approximates the reduced fraction `s / r` with
`r ≤ R` to within `1 / (2 R ^ 2)`, then `r` is uniquely determined by `x` and `R`, and the
post-processing returns it. -/
lemma recoverDen_eq {x : ℚ} {s r R : ℕ} (hr : 0 < r) (hrR : r ≤ R) (h : Nat.Coprime s r)
    (hx : |x - (s : ℚ) / (r : ℚ)| < 1 / (2 * (R : ℚ) ^ 2)) : recoverDen x R = r := by
  have hRpos : 0 < R := lt_of_lt_of_le hr hrR
  have hRQ : (0:ℚ) < R := by exact_mod_cast hRpos
  have hden0 : ((s : ℚ) / (r : ℚ)).den = r := den_div_of_coprime hr h
  have hex : ∃ y : ℚ, y.den ≤ R ∧ |x - y| < 1 / (2 * (R : ℚ) ^ 2) :=
    ⟨(s : ℚ) / (r : ℚ), by rw [hden0]; exact hrR, hx⟩
  rw [recoverDen, dif_pos hex]
  obtain ⟨hy1, hy2⟩ := hex.choose_spec
  set y := hex.choose with hyd
  by_cases hyy : y = (s : ℚ) / (r : ℚ)
  · rw [hyy, hden0]
  · exfalso
    have h1 : 1 / ((y.den : ℚ) * ((s : ℚ)/(r:ℚ)).den) ≤ |y - (s:ℚ)/(r:ℚ)| := rat_dist_ge hyy
    have h2 : |y - (s:ℚ)/(r:ℚ)| ≤ |x - y| + |x - (s:ℚ)/(r:ℚ)| := by
      have hrw : y - (s:ℚ)/(r:ℚ) = -(x - y) + (x - (s:ℚ)/(r:ℚ)) := by ring
      rw [hrw]
      calc |-(x - y) + (x - (s:ℚ)/(r:ℚ))| ≤ |-(x-y)| + |x - (s:ℚ)/(r:ℚ)| := abs_add_le _ _
        _ = |x - y| + |x - (s:ℚ)/(r:ℚ)| := by rw [abs_neg]
    have hdy : (0:ℚ) < y.den := by exact_mod_cast y.pos
    have hdyR : (y.den : ℚ) ≤ R := by exact_mod_cast hy1
    have hrQ : (r:ℚ) ≤ R := by exact_mod_cast hrR
    have hrQ0 : (0:ℚ) < r := by exact_mod_cast hr
    have h3 : 1 / ((R:ℚ) * R) ≤ 1 / ((y.den : ℚ) * ((s : ℚ)/(r:ℚ)).den) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hden0]
      exact mul_le_mul hdyR hrQ (le_of_lt hrQ0) (le_of_lt hRQ)
    have h4 : |x - y| + |x - (s:ℚ)/(r:ℚ)| < 1 / ((R:ℚ)*R) := by
      have hsplit : (1:ℚ) / (2 * (R:ℚ)^2) + 1/(2*(R:ℚ)^2) = 1/((R:ℚ)*R) := by
        field_simp; ring
      linarith [hy2, hx]
    linarith

/-! ### Part 4: the success probability -/

/-- The number of outcomes `s < r` from which the period can be recovered is `φ r`. -/
lemma card_good_outcomes (r : ℕ) :
    ((Finset.range r).filter (fun s => Nat.Coprime s r)).card = Nat.totient r := by
  rw [Nat.totient]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [Nat.coprime_comm]

/-- Repeating the algorithm makes the failure probability arbitrarily small. -/
lemma failure_prob_tendsto {r : ℕ} (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, (1 - (Nat.totient r : ℝ) / r) ^ k < ε := by
  have h0 : 0 < (Nat.totient r : ℝ) / r := by
    have hpos : 0 < Nat.totient r := Nat.totient_pos.2 hr
    have hposR : (0:ℝ) < Nat.totient r := by exact_mod_cast hpos
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (show (1 - (Nat.totient r : ℝ)/r) < 1 by linarith)
  exact ⟨k, hk⟩

/-! ### Main theorem -/

/-- **Shor's period finding algorithm.**

Let `a` be invertible modulo `N` and let `r` be the period of `x ↦ a ^ x mod N`.
Assume the exact case `r * M = 2 ^ n` for the quantum Fourier transform register size,
and `r ≤ R` for the classical bound `R`.  Then:

1. `x ↦ a ^ x mod N` is periodic with period `r`, and `r` is the least such period;
2. after the quantum Fourier transform, the outcome `c` is measured with probability
   `0` unless `M ∣ c`, and each `c = s * M` occurs with probability `1 / r`; these
   probabilities sum to `1`;
3. whenever the measured `s` is coprime to `r`, the classical post-processing applied to
   `c / 2 ^ n = s / r` returns exactly `r`;
4. the number of good values `s < r` is `φ r`, so a single run succeeds with probability
   `φ r / r > 0`, and repeated runs make the failure probability arbitrarily small:
   Shor's algorithm recovers the period with high probability. -/
theorem shor_period (N a n R r M x0 : ℕ) (hN : 1 < N) (ha : Nat.Coprime a N)
    (hr : r = period N a) (hrM : r * M = 2 ^ n) (hrR : r ≤ R) :
    -- (1) periodicity with minimal period `r`
    (0 < r ∧ (∀ x : ℕ, modExp N a (x + r) = modExp N a x) ∧
      (∀ t : ℕ, 0 < t → t < r → modExp N a t ≠ modExp N a 0)) ∧
    -- (2) the measurement statistics of the quantum part
    ((∀ c : ℕ, ¬ M ∣ c → shorProb n r M x0 c = 0) ∧
      (∀ s : ℕ, shorProb n r M x0 (s * M) = 1 / (r : ℝ)) ∧
      ∑ c ∈ Finset.range (2 ^ n), shorProb n r M x0 c = 1) ∧
    -- (3) the classical post-processing recovers `r` exactly from a good outcome
    (∀ s : ℕ, Nat.Coprime s r →
      recoverDen (((s * M : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ)) R = r) ∧
    -- (4) the success probability of one run, and amplification by repetition
    (((Finset.range r).filter (fun s => Nat.Coprime s r)).card = Nat.totient r ∧
      0 < (Nat.totient r : ℝ) / r ∧
      ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, (1 - (Nat.totient r : ℝ) / r) ^ k < ε) := by
  subst hr
  have hrpos : 0 < period N a := period_pos hN ha
  refine ⟨⟨hrpos, fun x => modExp_periodic N a x, fun t ht htr => modExp_ne_of_lt_period t ht htr⟩,
    ⟨fun c hc => by rw [shorProb_eq hrM, if_neg hc],
     fun s => by rw [shorProb_eq hrM, if_pos ⟨s, mul_comm s M⟩],
     shorProb_sum hrM⟩, ?_, card_good_outcomes _, ?_, failure_prob_tendsto hrpos⟩
  · intro s hs
    have hkey : ((s * M : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ) = (s : ℚ) / ((period N a : ℕ) : ℚ) := by
      rw [← hrM]
      have hMpos : 0 < M := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at hrM
        exact absurd hrM.symm (Nat.two_pow_pos n).ne'
      have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
      push_cast
      rw [mul_comm ((period N a : ℚ)) (M : ℚ), ← div_div, mul_div_assoc, mul_comm,
        mul_div_assoc, div_self hM', one_mul]
    rw [hkey]
    refine recoverDen_eq hrpos hrR hs ?_
    have hRpos : 0 < (R : ℚ) := by exact_mod_cast lt_of_lt_of_le hrpos hrR
    simp only [sub_self, abs_zero]
    positivity
  · have := Nat.totient_pos.2 hrpos
    positivity

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

