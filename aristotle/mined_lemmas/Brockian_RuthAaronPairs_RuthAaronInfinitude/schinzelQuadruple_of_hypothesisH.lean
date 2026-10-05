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
