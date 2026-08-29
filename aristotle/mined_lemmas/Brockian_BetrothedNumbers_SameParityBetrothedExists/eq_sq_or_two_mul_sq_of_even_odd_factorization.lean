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

-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands.)

import Mathlib

open Nat ArithmeticFunction

namespace Brockian
namespace BetrothedNumbers

/-- Two positive naturals `m`, `n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the *proper* divisors of each,
excluding `1`, gives the other number. -/

theorem eq_sq_or_two_mul_sq_of_even_odd_factorization {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → Even (n.factorization p)) :
    ∃ k : ℕ, n = k ^ 2 ∨ n = 2 * k ^ 2 := by
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree n
  have ha0 : a ≠ 0 := hsq.ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hab
    exact hn hab.symm
  have key : ∀ p : ℕ, p.Prime → p ∣ a → p = 2 := by
    intro p hp hpa
    by_contra hp2
    have hfa : a.factorization p = 1 := by
      have hle : a.factorization p ≤ 1 := by
        by_contra hc
        have hpp : p ^ 2 ∣ a :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp ha0).mpr (by omega)
        exact hp.not_isUnit (hsq p (by simpa [pow_two] using hpp))
      have hge : 1 ≤ a.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp ha0).mp (by simpa using hpa)
      omega
    have hfn : n.factorization p = 2 * b.factorization p + 1 := by
      rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0]
      simp [Nat.factorization_pow, hfa]
    have := h p hp hp2
    rw [hfn, Nat.even_iff] at this
    omega
  rcases eq_one_or_two_of_squarefree hsq key with rfl | rfl
  · exact ⟨b, Or.inl (by rw [← hab]; ring)⟩
  · exact ⟨b, Or.inr (by rw [← hab]; ring)⟩

/-- If a betrothed pair has both members of the same parity, then each member is either a perfect
square or twice a perfect square. -/
