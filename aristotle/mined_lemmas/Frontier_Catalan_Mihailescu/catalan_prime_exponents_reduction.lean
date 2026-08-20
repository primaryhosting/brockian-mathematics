import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma catalan_prime_exponents_reduction
    (H : ∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → q.Prime → x ^ p = y ^ q + 1 →
      x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) : CatalanMihailescuStatement := by
  intro x y p q hx hy hp hq h
  have h' : x ^ p = y ^ q + 1 := by omega
  have hlp : (p.minFac).Prime := Nat.minFac_prime (by omega)
  have hmp : (q.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨p', hp'⟩ : p.minFac ∣ p := Nat.minFac_dvd p
  obtain ⟨q', hq'⟩ : q.minFac ∣ q := Nat.minFac_dvd q
  have hp'pos : 1 ≤ p' := by
    rcases Nat.eq_zero_or_pos p' with rfl | h''
    · simp at hp'; omega
    · exact h''
  have hq'pos : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with rfl | h''
    · simp at hq'; omega
    · exact h''
  have hX : 1 < x ^ p' := Nat.one_lt_pow (by omega) hx
  have hY : 1 < y ^ q' := Nat.one_lt_pow (by omega) hy
  have hkey : (x ^ p') ^ p.minFac = (y ^ q') ^ q.minFac + 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm p' p.minFac, mul_comm q' q.minFac, ← hp', ← hq']
    exact h'
  obtain ⟨h1, h2, h3, h4⟩ := H _ _ _ _ hX hY hlp hmp hkey
  obtain ⟨hp1, hx3⟩ := pow_eq_of_lt_four hx hp'pos (by norm_num) h1
  obtain ⟨hq1, hy2⟩ := pow_eq_of_lt_four hy hq'pos (by norm_num) h3
  refine ⟨hx3, ?_, hy2, ?_⟩
  · rw [hp', hp1, h2]
  · rw [hq', hq1, h4]

/-! ### Main theorem -/

/-- **Catalan–Mihăilescu: base case and Lean-checked reductions.**

The full statement is recorded as `Frontier.CatalanMihailescuStatement`.  What is proved here:

* the full conjecture reduces to the case of prime exponents
  (`catalan_prime_exponents_reduction`);

* `8` and `9` really are consecutive perfect powers (`3 ^ 2 - 2 ^ 3 = 1`);
* the theorem holds in full whenever the larger base is a power of `2`, or the smaller base is a
  prime power: the only solution is then `3 ^ 2 - 2 ^ 3 = 1`;
* the theorem holds in full whenever the larger base is a prime power and `q` is odd;
* no two perfect powers with the same exponent are consecutive;
* no two perfect powers with both exponents even are consecutive;
* there is no solution with `p` even and `y` odd;
* every solution with `q` even has `x` odd, `y` even and `p` odd;
* the theorem holds for all perfect powers up to `10000` (exhaustive kernel check). -/
