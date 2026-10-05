/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction
/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive and distinct, and
the sum of the divisors of each, other than the number itself and `1`, is the other member;
equivalently `sigma m = sigma n = m + n + 1`. -/

theorem isSquare_of_odd_sigma_one :
    ∀ n : ℕ, n ≠ 0 → Odd n → Odd (ArithmeticFunction.sigma 1 n) → IsSquare n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hodd hsig
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn0) with h1 | h1
    · exact ⟨1, by omega⟩
    · have hq : (n.minFac).Prime := Nat.minFac_prime (by omega)
      set q := n.minFac with hqdef
      set e := n.factorization q with hedef
      set m := n / q ^ e with hmdef
      have hsplit : q ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n q
      have hcop : Nat.Coprime (q ^ e) m :=
        Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hn0)
      have hm0 : m ≠ 0 := (Nat.ordCompl_pos q hn0).ne'
      have hsigmul : ArithmeticFunction.sigma 1 n
          = ArithmeticFunction.sigma 1 (q ^ e) * ArithmeticFunction.sigma 1 m := by
        rw [← hsplit]
        exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
      rw [hsigmul] at hsig
      obtain ⟨hs1, hs2⟩ := Nat.odd_mul.mp hsig
      have hqodd : Odd q := hodd.of_dvd_nat (Nat.minFac_dvd n)
      have he : Even e := by
        rw [sigma_one_prime_pow hq, Nat.odd_iff] at hs1
        have h2 := sum_pow_mod_two hqodd (e + 1)
        rw [Nat.even_iff]
        omega
      have hmodd : Odd m := hodd.of_dvd_nat (Nat.ordCompl_dvd n q)
      have hmlt : m < n := by
        have hepos : 0 < e := Nat.Prime.factorization_pos_of_dvd hq hn0 (Nat.minFac_dvd n)
        have hqe : 1 < q ^ e := Nat.one_lt_pow hepos.ne' hq.one_lt
        calc m = 1 * m := (one_mul m).symm
          _ < q ^ e * m := Nat.mul_lt_mul_of_lt_of_le hqe (le_refl m) (Nat.pos_of_ne_zero hm0)
          _ = n := hsplit
      obtain ⟨t, ht⟩ := ih m hmlt hm0 hmodd hs2
      obtain ⟨k, hk⟩ := he
      exact ⟨q ^ k * t, by rw [← hsplit, ht, hk]; ring⟩

/-! ### The structure of a prime power member -/

/-- If `p ^ a` belongs to a betrothed pair with partner `n`, then `a = b + 1` with `b ≥ 1`,
`n = p (1 + p + ⋯ + p ^ (b-1))`, and `p` does not divide that geometric sum. -/
