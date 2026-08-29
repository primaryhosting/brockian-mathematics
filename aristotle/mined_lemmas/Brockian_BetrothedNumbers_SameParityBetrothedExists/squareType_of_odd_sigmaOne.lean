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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- `sigmaOne n` is the sum of all divisors of `n`. -/

theorem squareType_of_odd_sigmaOne {n : ℕ} (hn : 0 < n) (h : Odd (sigmaOne n)) :
    SquareType n := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have ha2 : ∀ {d : ℕ}, d.Prime → d ∣ a → d = 2 := by
    intro d hd hda
    by_contra hne
    have hdn : n.factorization d = 2 * b.factorization d + a.factorization d := by
      rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb.ne') ha.ne']
      simp [Nat.factorization_pow, two_mul]
    have h1 : a.factorization d = 1 :=
      le_antisymm (hsq.natFactorization_le_one d) (hd.factorization_pos_of_dvd ha.ne' hda)
    obtain ⟨c, hc⟩ := even_factorization_of_odd_sigmaOne hn.ne' h hd hne
    omega
  have hpow : a = 2 ^ a.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd ha.ne' ha2
  have hL : a.primeFactorsList.length ≤ 1 := by
    have h2 := hsq.natFactorization_le_one 2
    rw [hpow] at h2
    simpa [Nat.Prime.factorization_pow, Nat.prime_two] using h2
  interval_cases hle : a.primeFactorsList.length
  · exact ⟨b, Or.inl (by simp [hpow] at *; omega)⟩
  · refine ⟨b, Or.inr ?_⟩
    rw [hpow] at hab
    simp at hab
    omega

end SigmaParity

/-- Both members of a same-parity betrothed pair are of square type. -/
