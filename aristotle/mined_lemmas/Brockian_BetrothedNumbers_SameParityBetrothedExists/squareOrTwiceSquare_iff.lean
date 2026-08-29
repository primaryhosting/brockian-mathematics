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

-- (Lean does not permit a `/-!` module docstring before `import`; the header above is the
-- same text as a plain block comment, and is repeated as a module docstring below.)
import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals `m + n + 1`. -/

theorem squareOrTwiceSquare_iff {n : ℕ} (hn : n ≠ 0) :
    SquareOrTwiceSquare n ↔ ∀ p, p ≠ 2 → Even (n.factorization p) := by
  constructor
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩) p hp
    · exact (isSquare_iff_even_factorization hn).mp ⟨k, rfl⟩ p
    · have hk : k ≠ 0 := by rintro rfl; simp at hn
      rw [Nat.factorization_mul (by norm_num) (by positivity), Nat.factorization_pow]
      simp [Nat.Prime.factorization Nat.prime_two, hp, Nat.two_mul]
  · intro h
    rcases Nat.even_or_odd (n.factorization 2) with he | ho
    · left
      refine (isSquare_iff_even_factorization hn).mpr fun p => ?_
      by_cases hp : p = 2
      · subst hp; exact he
      · exact h p hp
    · right
      have h2 : 2 ∣ n := by
        refine (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).mpr ?_
        rcases ho with ⟨c, hc⟩; omega
      obtain ⟨m, rfl⟩ := h2
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hfac : (2 * m).factorization = Nat.factorization 2 + m.factorization :=
        Nat.factorization_mul (by norm_num) hm
      have hsq : ∃ k, m = k ^ 2 := by
        refine (isSquare_iff_even_factorization hm).mpr fun p => ?_
        by_cases hp : p = 2
        · subst hp
          rw [hfac] at ho
          simp [Nat.Prime.factorization Nat.prime_two, Nat.odd_iff, Nat.even_iff] at ho ⊢
          omega
        · have hnp := h p hp
          rw [hfac] at hnp
          simpa [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply,
            Ne.symm hp] using hnp
      obtain ⟨k, hk⟩ := hsq
      exact ⟨k, by rw [hk]⟩

/-- For odd `p`, the sum `∑_{i<k} p^i` has the same parity as `k`. -/
