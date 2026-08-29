/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M(n) = ∑_{k=1}^{n} μ(k)`, where `μ` is the Möbius function. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

private lemma not_squarefree_of_four_dvd {n : ℕ} (h : 4 ∣ n) : ¬ Squarefree n := by
  intro hs
  have := hs 2 (by simpa using h)
  simp at this

private lemma moebius_four : moebius 4 = 0 :=
  moebius_eq_zero_of_not_squarefree (not_squarefree_of_four_dvd (by norm_num))

private lemma moebius_eight : moebius 8 = 0 :=
  moebius_eq_zero_of_not_squarefree (not_squarefree_of_four_dvd (by norm_num))

private lemma moebius_nine : moebius 9 = 0 := by
  refine moebius_eq_zero_of_not_squarefree ?_
  intro hs
  have := hs 3 (by norm_num)
  simp at this

private lemma moebius_six : moebius 6 = 1 := by
  have h := isMultiplicative_moebius.map_mul_of_coprime (m := 2) (n := 3) (by norm_num)
  simpa [moebius_apply_prime, Nat.prime_two, Nat.prime_three] using h

private lemma moebius_ten : moebius 10 = 1 := by
  have h := isMultiplicative_moebius.map_mul_of_coprime (m := 2) (n := 5) (by norm_num)
  simpa [moebius_apply_prime, Nat.prime_two, show Nat.Prime 5 by norm_num] using h

/-- The Mertens function at `10`: `M(10) = ∑_{k=1}^{10} μ(k) = -1`. -/
theorem value_at_ten : mertens 10 = -1 := by
  have h1 : moebius 1 = 1 := moebius_apply_one
  have h2 : moebius 2 = -1 := moebius_apply_prime Nat.prime_two
  have h3 : moebius 3 = -1 := moebius_apply_prime Nat.prime_three
  have h5 : moebius 5 = -1 := moebius_apply_prime (by norm_num)
  have h7 : moebius 7 = -1 := moebius_apply_prime (by norm_num)
  simp only [mertens]
  simp [Finset.sum_Icc_succ_top, h1, h2, h3, h5, h7,
    moebius_four, moebius_six, moebius_eight, moebius_nine, moebius_ten]

end Riemann.Mertens

