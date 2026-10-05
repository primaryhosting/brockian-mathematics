import Mathlib


theorem not_quasiperfect_prime {p : ℕ} (hp : Nat.Prime p) :
    ¬ Quasiperfect p := by
  rintro ⟨hpos, hsum⟩
  rw [sigma1, hp.divisors, Finset.sum_pair hp.one_lt.ne] at hsum
  omega

#print axioms not_quasiperfect_prime

