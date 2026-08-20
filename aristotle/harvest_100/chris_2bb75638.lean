/-
# Lagrange Four Squares
Category: Pure Mathematics
Target: Math.lagrange_four_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede any module docstring (`/-! ... -/`),
-- so the header above is written as an ordinary block comment.

import Mathlib

/-!
This file contains a self-contained proof of Lagrange's four-square theorem, following
Lagrange's classical descent argument:

* `Math.euler_identity` : Euler's four-square identity;
* `Math.IsSum4.mul` : the sums of four squares are closed under multiplication;
* `Math.exists_mul_isSum4_of_prime` : some multiple `m * p` with `0 < m < p` of a prime `p`
  is a sum of four squares;
* `Math.isSum4_of_two_mul` and `Math.descent_odd` : the two descent steps;
* `Math.prime_isSum4` : every prime is a sum of four squares;
* `Math.lagrange_four_squares` : every natural number is a sum of four squares.
-/

namespace Math

/-- `IsSum4 n` states that the integer `n` is a sum of four integer squares. -/
def IsSum4 (n : ℤ) : Prop := ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n

/-- **Euler's four-square identity**. -/
theorem euler_identity (a b c d A B C D : ℤ) :
    (a * A + b * B + c * C + d * D) ^ 2 + (a * B - b * A + c * D - d * C) ^ 2 +
      (a * C - b * D - c * A + d * B) ^ 2 + (a * D + b * C - c * B - d * A) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
  ring

/-- Sums of four squares are closed under multiplication. -/
theorem IsSum4.mul {m n : ℤ} (hm : IsSum4 m) (hn : IsSum4 n) : IsSum4 (m * n) := by
  obtain ⟨a, b, c, d, rfl⟩ := hm
  obtain ⟨A, B, C, D, rfl⟩ := hn
  exact ⟨_, _, _, _, euler_identity a b c d A B C D⟩

/-- Four integers whose squares sum to zero all vanish. -/
private theorem eq_zero_of_sum_sq_eq_zero {A B C D : ℤ}
    (h : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 0) : A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hA : A ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  have hB : B ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  have hC : C ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  have hD : D ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [pow_eq_zero_iff]

/-- The parity of `x ^ 2` is the parity of `x`. -/
private theorem sq_emod_two (x : ℤ) : x ^ 2 % 2 = x % 2 := by
  have h : Even (x ^ 2) ↔ Even x := by simp [Int.even_pow]
  rcases Int.even_or_odd x with hx | hx
  · rw [Int.even_iff.mp (h.mpr hx), Int.even_iff.mp hx]
  · have h1 : ¬ Even x := Int.not_even_iff_odd.mpr hx
    have h2 : ¬ Even (x ^ 2) := fun hc => h1 (h.mp hc)
    rw [Int.not_even_iff.mp h2, Int.not_even_iff.mp h1]

/-- Halving step: if `a ≡ b` and `c ≡ d` mod `2`, a representation of `2 * m` gives one of `m`. -/
private theorem isSum4_of_pairs {a b c d m : ℤ} (hab : (a - b) % 2 = 0) (hcd : (c - d) % 2 = 0)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m) : IsSum4 m := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, a - b = 2 * k := ⟨(a - b) / 2, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l : ℤ, a + b = 2 * l := ⟨(a + b) / 2, by omega⟩
  obtain ⟨i, hi⟩ : ∃ i : ℤ, c - d = 2 * i := ⟨(c - d) / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, c + d = 2 * j := ⟨(c + d) / 2, by omega⟩
  refine ⟨k, l, i, j, ?_⟩
  have h4 : 4 * (k ^ 2 + l ^ 2 + i ^ 2 + j ^ 2) = 4 * m := by
    have e : (2 * k) ^ 2 + (2 * l) ^ 2 + (2 * i) ^ 2 + (2 * j) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      rw [← hk, ← hl, ← hi, ← hj]; ring
    rw [h] at e
    nlinarith [e]
  linarith

/-- If `2 * m` is a sum of four squares, so is `m`. -/
theorem isSum4_of_two_mul {m : ℤ} (h : IsSum4 (2 * m)) : IsSum4 m := by
  obtain ⟨a, b, c, d, h⟩ := h
  have ha := sq_emod_two a
  have hb := sq_emod_two b
  have hc := sq_emod_two c
  have hd := sq_emod_two d
  have hsum : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 2 = 0 := by omega
  by_cases h1 : (a - b) % 2 = 0
  · exact isSum4_of_pairs h1 (show (c - d) % 2 = 0 by omega) h
  · by_cases h2 : (a - c) % 2 = 0
    · exact isSum4_of_pairs (a := a) (b := c) (c := b) (d := d) h2
        (show (b - d) % 2 = 0 by omega) (by linarith)
    · exact isSum4_of_pairs (a := a) (b := d) (c := b) (d := c)
        (show (a - d) % 2 = 0 by omega) (show (b - c) % 2 = 0 by omega) (by linarith)

/-- Representatives of least absolute value modulo an odd number `m`. -/
private theorem exists_rep {m : ℤ} (hm : 0 < m) (hodd : m % 2 = 1) (x : ℤ) :
    ∃ y t : ℤ, x = y + m * t ∧ 2 * |y| < m := by
  refine ⟨(x + m / 2) % m - m / 2, (x + m / 2) / m, ?_, ?_⟩
  · have := Int.emod_add_mul_ediv (x + m / 2) m
    omega
  · have h1 : 0 ≤ (x + m / 2) % m := Int.emod_nonneg _ (by omega)
    have h2 : (x + m / 2) % m < m := Int.emod_lt_of_pos _ hm
    rcases abs_cases ((x + m / 2) % m - m / 2) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega

/-- If `2 * |A| < M` then `4 * A ^ 2 < M ^ 2`. -/
private theorem sq_lt_of_two_abs_lt {A M : ℤ} (h : 2 * |A| < M) : 4 * A ^ 2 < M ^ 2 := by
  nlinarith [abs_nonneg A, sq_abs A]

/-- The core of the descent step: dividing out `m` after applying Euler's identity. -/
private theorem isSum4_of_euler_quotient {m p r A B C D α β γ δ : ℤ} (hm : m ≠ 0)
    (hN : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = m * r)
    (h : (A + m * α) ^ 2 + (B + m * β) ^ 2 + (C + m * γ) ^ 2 + (D + m * δ) ^ 2 = m * p) :
    IsSum4 (r * p) := by
  set a := A + m * α with ha
  set b := B + m * β with hb
  set c := C + m * γ with hc
  set d := D + m * δ with hd
  refine ⟨r + (α * A + β * B + γ * C + δ * D), α * B - β * A + γ * D - δ * C,
    α * C - β * D - γ * A + δ * B, α * D + β * C - γ * B - δ * A, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 2 hm) ?_
  have e1 : m * (r + (α * A + β * B + γ * C + δ * D)) = a * A + b * B + c * C + d * D := by
    rw [ha, hb, hc, hd]; linear_combination -hN
  have e2 : m * (α * B - β * A + γ * D - δ * C) = a * B - b * A + c * D - d * C := by
    rw [ha, hb, hc, hd]; ring
  have e3 : m * (α * C - β * D - γ * A + δ * B) = a * C - b * D - c * A + d * B := by
    rw [ha, hb, hc, hd]; ring
  have e4 : m * (α * D + β * C - γ * B - δ * A) = a * D + b * C - c * B - d * A := by
    rw [ha, hb, hc, hd]; ring
  have key : m ^ 2 * ((r + (α * A + β * B + γ * C + δ * D)) ^ 2 +
      (α * B - β * A + γ * D - δ * C) ^ 2 + (α * C - β * D - γ * A + δ * B) ^ 2 +
      (α * D + β * C - γ * B - δ * A) ^ 2)
      = (m * (r + (α * A + β * B + γ * C + δ * D))) ^ 2 + (m * (α * B - β * A + γ * D - δ * C)) ^ 2
        + (m * (α * C - β * D - γ * A + δ * B)) ^ 2
        + (m * (α * D + β * C - γ * B - δ * A)) ^ 2 := by ring
  rw [key, e1, e2, e3, e4, euler_identity, h, hN]
  ring

/-- Descent step for odd `m`. -/
private theorem descent_odd {p m : ℕ} (hp : p.Prime) (hm1 : 1 < m) (hmp : m < p)
    (hodd : m % 2 = 1) (h : IsSum4 ((m : ℤ) * p)) :
    ∃ r : ℕ, 0 < r ∧ r < m ∧ IsSum4 ((r : ℤ) * p) := by
  obtain ⟨a, b, c, d, h⟩ := h
  have hM0 : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1.le
  have hModd : (m : ℤ) % 2 = 1 := by omega
  obtain ⟨A, α, haA, hA⟩ := exists_rep hM0 hModd a
  obtain ⟨B, β, hbB, hB⟩ := exists_rep hM0 hModd b
  obtain ⟨C, γ, hcC, hC⟩ := exists_rep hM0 hModd c
  obtain ⟨D, δ, hdD, hD⟩ := exists_rep hM0 hModd d
  subst haA hbB hcC hdD
  set M : ℤ := (m : ℤ) with hMdef
  set r : ℤ := p - 2 * (A * α + B * β + C * γ + D * δ) - M * (α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2)
    with hrdef
  have hN : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = M * r := by rw [hrdef]; linear_combination h
  have hA4 := sq_lt_of_two_abs_lt hA
  have hB4 := sq_lt_of_two_abs_lt hB
  have hC4 := sq_lt_of_two_abs_lt hC
  have hD4 := sq_lt_of_two_abs_lt hD
  have hsqM : M ^ 2 = M * M := sq M
  have hr0 : 0 ≤ r := by
    have h2 : M * 0 ≤ M * r := by rw [← hN]; positivity
    exact le_of_mul_le_mul_left h2 hM0
  have hrM : r < M := by
    have h1 : M * r < M * M := by rw [← hN, ← hsqM]; linarith
    exact lt_of_mul_lt_mul_left h1 hM0.le
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hz : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 0 := by rw [hN, ← h']; ring
      obtain ⟨hA0, hB0, hC0, hD0⟩ := eq_zero_of_sum_sq_eq_zero hz
      subst hA0 hB0 hC0 hD0
      have hp' : (p : ℤ) = (m : ℤ) * (α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2) := by
        refine mul_left_cancel₀ (ne_of_gt hM0) ?_
        linear_combination -h
      have hmp' : m ∣ p := Int.natCast_dvd_natCast.mp ⟨α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2, hp'⟩
      rcases hp.eq_one_or_self_of_dvd m hmp' with h1 | h1 <;> omega
  refine ⟨r.toNat, by omega, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hr0]
  exact isSum4_of_euler_quotient (ne_of_gt hM0) hN h

/-- Some multiple `m * p`, with `0 < m < p`, of a prime `p` is a sum of four squares. -/
theorem exists_mul_isSum4_of_prime {p : ℕ} (hp : p.Prime) :
    ∃ m : ℕ, 0 < m ∧ m < p ∧ IsSum4 ((m : ℤ) * p) := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, B, hAB⟩ := ZMod.sq_add_sq p (-1)
  set a : ℤ := A.valMinAbs with hadef
  set b : ℤ := B.valMinAbs with hbdef
  have hA : a.natAbs ≤ p / 2 := ZMod.natAbs_valMinAbs_le A
  have hB : b.natAbs ≤ p / 2 := ZMod.natAbs_valMinAbs_le B
  have hdvd : (p : ℤ) ∣ a ^ 2 + b ^ 2 + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hadef, hbdef, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, hAB]
    ring
  obtain ⟨t, ht⟩ := hdvd
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have ht0 : 0 < t := by
    rcases lt_trichotomy t 0 with h | h | h
    · nlinarith [sq_nonneg a, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_nonneg b]
    · exact h
  have hk : 2 * ((p / 2 : ℕ) : ℤ) ≤ (p : ℤ) := by
    have := Nat.div_mul_le_self p 2
    push_cast
    omega
  have haa : a ^ 2 ≤ ((p / 2 : ℕ) : ℤ) ^ 2 := by
    have h1 : |a| ≤ ((p / 2 : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA
    nlinarith [abs_nonneg a, sq_abs a]
  have hbb : b ^ 2 ≤ ((p / 2 : ℕ) : ℤ) ^ 2 := by
    have h1 : |b| ≤ ((p / 2 : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hB
    nlinarith [abs_nonneg b, sq_abs b]
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hlt : (p : ℤ) * t < (p : ℤ) * p := by
    rw [← ht]
    nlinarith [Nat.cast_nonneg (α := ℤ) (p / 2)]
  have htp : t < p := lt_of_mul_lt_mul_left hlt hp0.le
  refine ⟨t.toNat, by omega, by omega, a, b, 1, 0, ?_⟩
  rw [Int.toNat_of_nonneg ht0.le]
  linarith [ht]

/-- Descent: if some `m * p` with `0 < m < p` is a sum of four squares, then so is `p`. -/
private theorem isSum4_of_multiple {p : ℕ} (hp : p.Prime) :
    ∀ m : ℕ, 0 < m → m < p → IsSum4 ((m : ℤ) * p) → IsSum4 (p : ℤ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hmp h
    by_cases hm1 : m = 1
    · subst hm1; simpa using h
    · by_cases hpar : m % 2 = 0
      · obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
        have h2 : IsSum4 (2 * ((m' : ℤ) * p)) := by
          have e : ((2 * m' : ℕ) : ℤ) * p = 2 * ((m' : ℤ) * p) := by push_cast; ring
          rwa [e] at h
        exact ih m' (by omega) (by omega) (by omega) (isSum4_of_two_mul h2)
      · obtain ⟨r, hr0, hrm, hr⟩ := descent_odd hp (by omega) hmp (by omega) h
        exact ih r hrm hr0 (by omega) hr

/-- Every prime is a sum of four squares. -/
theorem prime_isSum4 {p : ℕ} (hp : p.Prime) : IsSum4 (p : ℤ) := by
  obtain ⟨m, hm0, hmp, hm⟩ := exists_mul_isSum4_of_prime hp
  exact isSum4_of_multiple hp m hm0 hmp hm

/-- Every natural number is a sum of four integer squares. -/
theorem isSum4_natCast (n : ℕ) : IsSum4 (n : ℤ) := by
  induction n using Nat.recOnMul with
  | zero => exact ⟨0, 0, 0, 0, by norm_num⟩
  | one => exact ⟨1, 0, 0, 0, by norm_num⟩
  | prime p hp => exact prime_isSum4 hp
  | mul m n hm hn => push_cast; exact hm.mul hn

/-- **Lagrange's four-square theorem**: every natural number `n` can be written as
`a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2` for natural numbers `a`, `b`, `c`, `d`. -/
theorem lagrange_four_squares (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  obtain ⟨a, b, c, d, h⟩ := isSum4_natCast n
  refine ⟨a.natAbs, b.natAbs, c.natAbs, d.natAbs, ?_⟩
  have : ((a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2 : ℕ) : ℤ) = (n : ℤ) := by
    push_cast [Int.natAbs_sq, sq_abs]
    simpa using h
  exact_mod_cast this

end Math

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

