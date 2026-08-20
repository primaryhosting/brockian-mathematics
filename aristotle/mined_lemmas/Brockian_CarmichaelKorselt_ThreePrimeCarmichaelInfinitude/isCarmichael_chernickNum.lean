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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `n ∣ a ^ n - a` for all integers `a`. -/

theorem isCarmichael_chernickNum {k : ℕ} (h : ChernickTriple k) :
    IsCarmichael (chernickNum k) := by
  obtain ⟨hp, hq, hr⟩ := h
  have hk : 0 < k := chernick_pos ⟨hp, hq, hr⟩
  set X : ℕ := 36 * k ^ 2 + 11 * k + 1 with hX
  have hn : chernickNum k = 1 + 36 * k * X := chernickNum_eq k
  have h1 : chernickNum k = 1 + ((6 * k + 1) - 1) * (6 * X) := by
    rw [hn]; simp only [Nat.add_sub_cancel]; ring
  have h2 : chernickNum k = 1 + ((12 * k + 1) - 1) * (3 * X) := by
    rw [hn]; simp only [Nat.add_sub_cancel]; ring
  have h3 : chernickNum k = 1 + ((18 * k + 1) - 1) * (2 * X) := by
    rw [hn]; simp only [Nat.add_sub_cancel]; ring
  have hpq : (6 * k + 1) ≠ (12 * k + 1) := by omega
  have hpr : (6 * k + 1) ≠ (18 * k + 1) := by omega
  have hqr : (12 * k + 1) ≠ (18 * k + 1) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hn]; nlinarith
  · intro hprime
    have hdvd : (6 * k + 1) ∣ chernickNum k :=
      ⟨(12 * k + 1) * (18 * k + 1), by unfold chernickNum; ring⟩
    rcases hprime.eq_one_or_self_of_dvd _ hdvd with hcase | hcase
    · omega
    · have hfac : chernickNum k = (6 * k + 1) * ((12 * k + 1) * (18 * k + 1)) := by
        unfold chernickNum; ring
      rw [hcase] at hfac
      nlinarith [hfac]
  · intro a
    have d1 : ((6 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      prime_dvd_pow_sub_self hp h1 a
    have d2 : ((12 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      prime_dvd_pow_sub_self hq h2 a
    have d3 : ((18 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      prime_dvd_pow_sub_self hr h3 a
    have cpq : IsCoprime ((6 * k + 1 : ℕ) : ℤ) ((12 * k + 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
    have cpr : IsCoprime ((6 * k + 1 : ℕ) : ℤ) ((18 * k + 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hr).mpr hpr)
    have cqr : IsCoprime ((12 * k + 1 : ℕ) : ℤ) ((18 * k + 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hr).mpr hqr)
    have d12 : ((6 * k + 1 : ℕ) : ℤ) * ((12 * k + 1 : ℕ) : ℤ) ∣ a ^ chernickNum k - a :=
      cpq.mul_dvd d1 d2
    have d123 : ((6 * k + 1 : ℕ) : ℤ) * ((12 * k + 1 : ℕ) : ℤ) * ((18 * k + 1 : ℕ) : ℤ) ∣
        a ^ chernickNum k - a := (cpr.mul_left cqr).mul_dvd d12 d3
    simpa [chernickNum] using d123

/-- A Chernick number has exactly three prime factors. -/
