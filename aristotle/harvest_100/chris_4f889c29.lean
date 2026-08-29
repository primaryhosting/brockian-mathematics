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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` whose sums of prime factors,
counted with multiplicity, agree; e.g. `(5, 6)`, `(8, 9)`, `(714, 715)`.  Whether there are
infinitely many such pairs is a well-known open problem (Erdős).

This file gives a Lean-checked conditional proof: assuming **Schinzel's Hypothesis H**, there
are infinitely many Ruth–Aaron pairs.  The reduction goes through the polynomial identity
```
(12u² + 36u + 23)(4u + 9) + 1 = 4 (12u² + 39u + 26)(u + 2)
```
together with the matching identity of sums
```
(12u² + 36u + 23) + (4u + 9) = 4 + (12u² + 39u + 26) + (u + 2) .
```
Hence whenever the four polynomial values are simultaneously prime, `n = (12u²+36u+23)(4u+9)`
and `n + 1 = 2 · 2 · (12u²+39u+26) · (u+2)` have the same sum of prime factors.  The four
polynomials are irreducible, have positive leading coefficients, and have no fixed prime
divisor (`u = 5` already gives the Ruth–Aaron pair `(14587, 14588)`), so Hypothesis H supplies
arbitrarily large such `u`.
-/

namespace Brockian.RuthAaronPairs

open Polynomial

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 1 = 0`, `sopfr 12 = 2 + 2 + 3 = 7`). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- The set of Ruth–Aaron numbers: positive integers `n` for which `n` and `n + 1`
have the same sum of prime factors (counted with multiplicity).  Such an `n`
together with `n + 1` is called a *Ruth–Aaron pair*. -/
def RuthAaron : Set ℕ := {n : ℕ | 0 < n ∧ sopfr n = sopfr (n + 1)}

/-! ## Basic properties of `sopfr` -/

lemma sopfr_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sopfr (a * b) = sopfr a + sopfr b := by
  unfold sopfr
  rw [(Nat.perm_primeFactorsList_mul ha hb).sum_eq, List.sum_append]

lemma sopfr_of_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  unfold sopfr
  rw [Nat.primeFactorsList_prime hp]
  simp

lemma sopfr_four : sopfr 4 = 4 := by
  have h : (4 : ℕ) = 2 * 2 := by norm_num
  rw [h, sopfr_mul (by norm_num) (by norm_num), sopfr_of_prime Nat.prime_two]

/-! ## The key algebraic family -/

/-- If `p, q, r, s` are primes with `p * q + 1 = 4 * (r * s)` and `p + q = 4 + (r + s)`,
then `(p * q, p * q + 1)` is a Ruth–Aaron pair. -/
lemma mem_ruthAaron_of_primes {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (h1 : p * q + 1 = 4 * (r * s)) (h2 : p + q = 4 + (r + s)) :
    p * q ∈ RuthAaron := by
  refine ⟨Nat.mul_pos hp.pos hq.pos, ?_⟩
  rw [sopfr_mul hp.ne_zero hq.ne_zero, sopfr_of_prime hp, sopfr_of_prime hq, h1,
    sopfr_mul (by norm_num) (Nat.mul_ne_zero hr.ne_zero hs.ne_zero), sopfr_four,
    sopfr_mul hr.ne_zero hs.ne_zero, sopfr_of_prime hr, sopfr_of_prime hs, h2]

/-- The polynomial identity underlying the family:
`(12u² + 36u + 23)(4u + 9) + 1 = 4 (12u² + 39u + 26)(u + 2)`. -/
lemma family_identity (u : ℕ) :
    (12 * u ^ 2 + 36 * u + 23) * (4 * u + 9) + 1 =
      4 * ((12 * u ^ 2 + 39 * u + 26) * (u + 2)) := by
  ring

/-- The matching sum-of-prime-factors identity for the family. -/
lemma family_sum (u : ℕ) :
    (12 * u ^ 2 + 36 * u + 23) + (4 * u + 9) =
      4 + ((12 * u ^ 2 + 39 * u + 26) + (u + 2)) := by
  ring

/-- If the four values of the family are simultaneously prime, we obtain a Ruth–Aaron pair. -/
lemma mem_ruthAaron_family {u : ℕ} (h1 : Nat.Prime (12 * u ^ 2 + 36 * u + 23))
    (h2 : Nat.Prime (4 * u + 9)) (h3 : Nat.Prime (12 * u ^ 2 + 39 * u + 26))
    (h4 : Nat.Prime (u + 2)) :
    (12 * u ^ 2 + 36 * u + 23) * (4 * u + 9) ∈ RuthAaron :=
  mem_ruthAaron_of_primes h1 h2 h3 h4 (family_identity u) (family_sum u)

/-- An instance of Schinzel's Hypothesis H: the four polynomials
`12u² + 36u + 23`, `4u + 9`, `12u² + 39u + 26`, `u + 2`
take prime values simultaneously for arbitrarily large `u`. -/
def SchinzelQuadruple : Prop :=
  ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ Nat.Prime (12 * u ^ 2 + 36 * u + 23) ∧ Nat.Prime (4 * u + 9) ∧
    Nat.Prime (12 * u ^ 2 + 39 * u + 26) ∧ Nat.Prime (u + 2)

/-- The reduction: the prime-quadruple statement implies that there are infinitely many
Ruth–Aaron numbers. -/
theorem infinite_ruthAaron_of_schinzelQuadruple (h : SchinzelQuadruple) : RuthAaron.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨u, hu, h1, h2, h3, h4⟩ := h a
  exact ⟨_, mem_ruthAaron_family h1 h2 h3 h4, by nlinarith⟩

/-! ## Irreducibility of the four polynomials -/

lemma isPrimitive_quad {a b c : ℤ} (hprim : ∀ r : ℤ, r ∣ a → r ∣ b → r ∣ c → IsUnit r) :
    (C a * X ^ 2 + C b * X + C c : ℤ[X]).IsPrimitive := by
  intro r hr
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at h0 h1 h2
  norm_num at h0 h1 h2
  exact hprim r h2 h1 h0

lemma isPrimitive_lin {a b : ℤ} (hprim : ∀ r : ℤ, r ∣ a → r ∣ b → IsUnit r) :
    (C a * X + C b : ℤ[X]).IsPrimitive := by
  intro r hr
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
  have h0 := hr 0
  have h1 := hr 1
  simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C] at h0 h1
  norm_num at h0 h1
  exact hprim r h1 h0

/-- A primitive integer quadratic without rational roots is irreducible in `ℤ[X]`. -/
lemma irreducible_quad {a b c : ℤ} (ha : a ≠ 0)
    (hprim : ∀ r : ℤ, r ∣ a → r ∣ b → r ∣ c → IsUnit r)
    (hroot : ∀ x : ℚ, (a : ℚ) * x ^ 2 + (b : ℚ) * x + (c : ℚ) ≠ 0) :
    Irreducible (C a * X ^ 2 + C b * X + C c : ℤ[X]) := by
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (isPrimitive_quad hprim)]
  have hmap : ((C a * X ^ 2 + C b * X + C c : ℤ[X]).map (Int.castRingHom ℚ))
      = C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) := by
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  have hdeg : (C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) : ℚ[X]).natDegree = 2 := by
    have ha' : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
    compute_degree!
  rw [hmap]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, hdeg]
    omega
  · intro x hx
    rw [IsRoot] at hx
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx
    exact hroot x hx

/-- A primitive integer linear polynomial is irreducible in `ℤ[X]`. -/
lemma irreducible_lin {a b : ℤ} (ha : a ≠ 0) (hprim : ∀ r : ℤ, r ∣ a → r ∣ b → IsUnit r) :
    Irreducible (C a * X + C b : ℤ[X]) := by
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (isPrimitive_lin hprim)]
  have hmap : ((C a * X + C b : ℤ[X]).map (Int.castRingHom ℚ)) = C (a : ℚ) * X + C (b : ℚ) := by
    simp [Polynomial.map_add, Polynomial.map_mul]
  have hdeg : (C (a : ℚ) * X + C (b : ℚ) : ℚ[X]).degree = 1 := by
    have ha' : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
    compute_degree!
  rw [hmap]
  exact Polynomial.irreducible_of_degree_eq_one hdeg

/-! ## The family has no fixed prime divisor -/

/-- For every prime `p ≥ 7` there is a residue at which none of the four forms vanishes. -/
lemma exists_good_residue {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ x : ZMod p, 12 * x ^ 2 + 36 * x + 23 ≠ 0 ∧ 4 * x + 9 ≠ 0 ∧
      12 * x ^ 2 + 39 * x + 26 ≠ 0 ∧ x + 2 ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set G : (ZMod p)[X] := (C 12 * X ^ 2 + C 36 * X + C 23) *
      ((C 4 * X + C 9) * ((C 12 * X ^ 2 + C 39 * X + C 26) * (X + C 2))) with hG
  have hdeg : G.natDegree ≤ 6 := by rw [hG]; compute_degree
  have hp576 : ¬ (p ∣ 576) := by
    intro hdvd
    have h2 : p ∣ 2 ^ 6 * 3 ^ 2 := by norm_num at hdvd ⊢; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3); omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3); omega
  have h576 : ((576 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp576
  have hcoeff : G.coeff 6 = 576 := by rw [hG]; compute_degree!
  have hGne : G ≠ 0 := by
    intro h
    rw [h] at hcoeff
    simp only [coeff_zero] at hcoeff
    exact h576 (by exact_mod_cast hcoeff.symm)
  by_contra hcon
  push_neg at hcon
  refine hGne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero G
    (f := (id : ZMod p → ZMod p)) Function.injective_id ?_ ?_)
  · intro x
    rw [hG]
    simp only [eval_mul, eval_add, eval_C, eval_X, eval_pow, id]
    rcases eq_or_ne (12 * x ^ 2 + 36 * x + 23) 0 with h | h
    · rw [h]; ring
    rcases eq_or_ne (4 * x + 9) 0 with h2 | h2
    · rw [h2]; ring
    rcases eq_or_ne (12 * x ^ 2 + 39 * x + 26) 0 with h3 | h3
    · rw [h3]; ring
    · rw [hcon x h h2 h3]; ring
  · rw [ZMod.card]
    omega

/-- No prime divides the product of the four forms at every integer. -/
lemma no_fixed_prime_divisor (p : ℕ) (hp : p.Prime) :
    ∃ t : ℤ, ¬ ((p : ℤ) ∣ 12 * t ^ 2 + 36 * t + 23) ∧ ¬ ((p : ℤ) ∣ 4 * t + 9) ∧
      ¬ ((p : ℤ) ∣ 12 * t ^ 2 + 39 * t + 26) ∧ ¬ ((p : ℤ) ∣ t + 2) := by
  rcases lt_or_ge p 7 with hlt | h7
  · -- small primes: `t = 5` gives the values `503, 29, 521, 7`
    refine ⟨5, ?_, ?_, ?_, ?_⟩ <;>
      · have h2 := hp.two_le
        interval_cases p <;> simp_all
  · haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ := exists_good_residue hp h7
    refine ⟨(x.val : ℤ), ?_, ?_, ?_, ?_⟩ <;> intro hdvd <;>
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd <;>
      push_cast at hdvd <;>
      rw [ZMod.natCast_val, ZMod.cast_id] at hdvd
    · exact hx1 hdvd
    · exact hx2 hdvd
    · exact hx3 hdvd
    · exact hx4 hdvd

/-! ## Schinzel's Hypothesis H -/

/-- **Schinzel's Hypothesis H**.  Given finitely many irreducible integer polynomials with
positive leading coefficients such that no prime divides the product of their values at every
integer, there are arbitrarily large integers `t` at which all of them take prime values. -/
def HypothesisH : Prop :=
  ∀ (k : ℕ) (f : Fin k → Polynomial ℤ),
    (∀ i, 0 < (f i).natDegree) →
    (∀ i, Irreducible (f i)) →
    (∀ i, 0 < (f i).leadingCoeff) →
    (∀ p : ℕ, p.Prime → ∃ t : ℤ, ∀ i, ¬ ((p : ℤ) ∣ (f i).eval t)) →
    ∀ N : ℤ, ∃ t : ℤ, N ≤ t ∧ ∀ i, Prime ((f i).eval t)

/-- Hypothesis H implies the prime-quadruple statement for our family. -/
theorem schinzelQuadruple_of_hypothesisH (h : HypothesisH) : SchinzelQuadruple := by
  intro N
  have hd1 : (C 12 * X ^ 2 + C 36 * X + C 23 : ℤ[X]).natDegree = 2 := by compute_degree!
  have hd2 : (C 4 * X + C 9 : ℤ[X]).natDegree = 1 := by compute_degree!
  have hd3 : (C 12 * X ^ 2 + C 39 * X + C 26 : ℤ[X]).natDegree = 2 := by compute_degree!
  have hd4 : (C 1 * X + C 2 : ℤ[X]).natDegree = 1 := by compute_degree!
  have hl1 : (C 12 * X ^ 2 + C 36 * X + C 23 : ℤ[X]).leadingCoeff = 12 := by
    rw [Polynomial.leadingCoeff, hd1]; compute_degree!
  have hl2 : (C 4 * X + C 9 : ℤ[X]).leadingCoeff = 4 := by
    rw [Polynomial.leadingCoeff, hd2]; compute_degree!
  have hl3 : (C 12 * X ^ 2 + C 39 * X + C 26 : ℤ[X]).leadingCoeff = 12 := by
    rw [Polynomial.leadingCoeff, hd3]; compute_degree!
  have hl4 : (C 1 * X + C 2 : ℤ[X]).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff, hd4]; compute_degree!
  have he1 : ∀ t : ℤ,
      (C 12 * X ^ 2 + C 36 * X + C 23 : ℤ[X]).eval t = 12 * t ^ 2 + 36 * t + 23 := by
    intro t; simp
  have he2 : ∀ t : ℤ, (C 4 * X + C 9 : ℤ[X]).eval t = 4 * t + 9 := by intro t; simp
  have he3 : ∀ t : ℤ,
      (C 12 * X ^ 2 + C 39 * X + C 26 : ℤ[X]).eval t = 12 * t ^ 2 + 39 * t + 26 := by
    intro t; simp
  have he4 : ∀ t : ℤ, (C 1 * X + C 2 : ℤ[X]).eval t = t + 2 := by intro t; simp
  set F : Fin 4 → ℤ[X] := ![C 12 * X ^ 2 + C 36 * X + C 23, C 4 * X + C 9,
    C 12 * X ^ 2 + C 39 * X + C 26, C 1 * X + C 2] with hF
  have hF0 : F 0 = C 12 * X ^ 2 + C 36 * X + C 23 := rfl
  have hF1 : F 1 = C 4 * X + C 9 := rfl
  have hF2 : F 2 = C 12 * X ^ 2 + C 39 * X + C 26 := rfl
  have hF3 : F 3 = C 1 * X + C 2 := rfl
  have hdeg : ∀ i, 0 < (F i).natDegree := by
    intro i
    fin_cases i
    · rw [hF0]; omega
    · rw [hF1]; omega
    · rw [hF2]; omega
    · rw [hF3]; omega
  have hirr : ∀ i, Irreducible (F i) := by
    intro i
    fin_cases i
    · rw [hF0]
      exact irreducible_quad (by norm_num)
        (fun r h12 _ h23 => isUnit_of_dvd_one (by simpa using dvd_sub (h12.mul_left 2) h23))
        (fun x hx => by
          have h2 : (6 * x + 9) ^ 2 = 12 := by nlinarith
          exact (by norm_num : ¬ IsSquare (12 : ℚ)) ⟨6 * x + 9, by rw [← h2]; ring⟩)
    · rw [hF1]
      exact irreducible_lin (by norm_num)
        (fun r h4 h9 => isUnit_of_dvd_one (by simpa using dvd_sub h9 (h4.mul_left 2)))
    · rw [hF2]
      exact irreducible_quad (by norm_num)
        (fun r h12 h39 h26 => isUnit_of_dvd_one
          (by simpa using dvd_sub (dvd_sub (h26.mul_left 2) h12) h39))
        (fun x hx => by
          have h2 : (24 * x + 39) ^ 2 = 273 := by nlinarith
          exact (by norm_num : ¬ IsSquare (273 : ℚ)) ⟨24 * x + 39, by rw [← h2]; ring⟩)
    · rw [hF3]
      exact irreducible_lin (by norm_num) (fun r h1 _ => isUnit_of_dvd_one h1)
  have hlead : ∀ i, 0 < (F i).leadingCoeff := by
    intro i
    fin_cases i
    · rw [hF0, hl1]; norm_num
    · rw [hF1, hl2]; norm_num
    · rw [hF2, hl3]; norm_num
    · rw [hF3, hl4]; norm_num
  have hadm : ∀ p : ℕ, p.Prime → ∃ t : ℤ, ∀ i, ¬ ((p : ℤ) ∣ (F i).eval t) := by
    intro p hp
    obtain ⟨t, h1, h2, h3, h4⟩ := no_fixed_prime_divisor p hp
    refine ⟨t, ?_⟩
    intro i
    fin_cases i
    · rw [hF0, he1]; exact h1
    · rw [hF1, he2]; exact h2
    · rw [hF2, he3]; exact h3
    · rw [hF3, he4]; exact h4
  obtain ⟨t, hNt, hpr⟩ := h 4 F hdeg hirr hlead hadm (N : ℤ)
  have p1 : Prime (12 * t ^ 2 + 36 * t + 23) := by
    have := hpr 0; rwa [hF0, he1] at this
  have p2 : Prime (4 * t + 9) := by
    have := hpr 1; rwa [hF1, he2] at this
  have p3 : Prime (12 * t ^ 2 + 39 * t + 26) := by
    have := hpr 2; rwa [hF2, he3] at this
  have p4 : Prime (t + 2) := by
    have := hpr 3; rwa [hF3, he4] at this
  have ht0 : (0 : ℤ) ≤ t := le_trans (Int.natCast_nonneg N) hNt
  obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = (u : ℤ) := ⟨t.toNat, (Int.toNat_of_nonneg ht0).symm⟩
  refine ⟨u, by exact_mod_cast hNt, ?_, ?_, ?_, ?_⟩ <;>
    refine Nat.prime_iff_prime_int.mpr ?_ <;>
    push_cast <;> [exact p1; exact p2; exact p3; exact p4]

/-! ## Main result -/

/-- **Ruth–Aaron infinitude, conditional on Schinzel's Hypothesis H.**
There are infinitely many `n` such that `n` and `n + 1` have the same sum of prime
factors counted with multiplicity. -/
theorem RuthAaronInfinitude (h : HypothesisH) : RuthAaron.Infinite :=
  infinite_ruthAaron_of_schinzelQuadruple (schinzelQuadruple_of_hypothesisH h)

/-! ## Unconditional examples -/

/-- `(5, 6)` is a Ruth–Aaron pair: `5 = 5` and `6 = 2 · 3`. -/
example : (5 : ℕ) ∈ RuthAaron := by
  refine ⟨by norm_num, ?_⟩
  rw [show (5 : ℕ) + 1 = 2 * 3 by norm_num, sopfr_mul (by norm_num) (by norm_num),
    sopfr_of_prime Nat.prime_two, sopfr_of_prime Nat.prime_three,
    sopfr_of_prime (by norm_num : Nat.Prime 5)]

/-- The member `u = 5` of the family: `14587 = 29 · 503` and `14588 = 2 · 2 · 7 · 521`,
both with sum of prime factors `532`. -/
example : (14587 : ℕ) ∈ RuthAaron := by
  have h := mem_ruthAaron_family (u := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end Brockian.RuthAaronPairs

