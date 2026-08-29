import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
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

set_option grind.warning false

namespace Frontier

/-- The statement "the Fermat equation `x ^ n + y ^ n = z ^ n` has no solution in positive
integers", phrased directly in terms of positivity, agrees with Mathlib's
`FermatLastTheoremFor n`. -/
theorem fermatLastTheoremFor_iff_pos (n : ℕ) :
    FermatLastTheoremFor n ↔
      ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n := by
  constructor
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'
  · intro h x y z hx hy hz
    exact h x y z (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz)

/-- Every exponent `n ≥ 3` is divisible by `4` or by an odd prime. -/
theorem four_dvd_or_odd_prime_dvd {n : ℕ} (hn : 3 ≤ n) :
    4 ∣ n ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    by_cases hme : Even m
    · obtain ⟨k, hk⟩ := hme
      exact Or.inl ⟨k, by omega⟩
    · have hm1 : m ≠ 1 := by rintro rfl; omega
      have hm0 : m ≠ 0 := by rintro rfl; omega
      refine Or.inr ⟨m.minFac, Nat.minFac_prime hm1, ?_, ?_⟩
      · rcases Nat.even_or_odd m.minFac with h2 | h2
        · exfalso
          have h2m : (2 : ℕ) ∣ m := dvd_trans h2.two_dvd (Nat.minFac_dvd m)
          rw [Nat.even_iff] at hme
          omega
        · exact h2
      · exact dvd_trans (Nat.minFac_dvd m) ⟨2, by omega⟩
  · have hn1 : n ≠ 1 := by omega
    refine Or.inr ⟨n.minFac, Nat.minFac_prime hn1, ?_, Nat.minFac_dvd n⟩
    rcases Nat.even_or_odd n.minFac with h2 | h2
    · exfalso
      have h2n : (2 : ℕ) ∣ n := dvd_trans h2.two_dvd (Nat.minFac_dvd n)
      rw [Nat.odd_iff] at ho
      omega
    · exact h2

/-- **Fermat's Last Theorem**, formalized statement together with two Lean-checked results:

* a *reduction*: if the Fermat equation has no positive solution for every **odd prime**
  exponent, then it has no positive solution for any exponent `n > 2` (the exponent `4` case
  being supplied unconditionally);
* the *base cases* `n = 3` and `n = 4`, proved unconditionally.
-/
theorem FLT_statement :
    ((∀ p : ℕ, p.Prime → Odd p → ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ p + y ^ p ≠ z ^ p) →
        ∀ n x y z : ℕ, 2 < n → 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n) ∧
      (∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ 3 + y ^ 3 ≠ z ^ 3) ∧
      (∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ 4 + y ^ 4 ≠ z ^ 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h n x y z hn
    have key : FermatLastTheoremFor n := by
      rcases four_dvd_or_odd_prime_dvd hn with h4 | ⟨p, hp, hodd, hpn⟩
      · exact FermatLastTheoremFor.mono h4 fermatLastTheoremFour
      · exact FermatLastTheoremFor.mono hpn
          ((fermatLastTheoremFor_iff_pos p).2 (h p hp hodd))
    exact (fermatLastTheoremFor_iff_pos n).1 key x y z
  · exact (fermatLastTheoremFor_iff_pos 3).1 fermatLastTheoremThree
  · exact (fermatLastTheoremFor_iff_pos 4).1 fermatLastTheoremFour

end Frontier

