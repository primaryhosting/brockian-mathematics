import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

lemma belyiPoly_critical_value {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (z : ℂ)
    (hz : aeval z (derivative (belyiPoly m n)) = 0) :
    aeval z (belyiPoly m n) = 0 ∨ aeval z (belyiPoly m n) = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have hc : bcoef (a + 1) (b + 1) ≠ 0 := (bcoef_pos hm hn).ne'
  have hcK : algebraMap ℚ ℂ (bcoef (a + 1) (b + 1)) ≠ 0 := by
    simpa using (algebraMap ℚ ℂ).injective.ne hc
  rw [belyiPoly_derivative] at hz
  simp only [map_mul, map_sub, aeval_C, aeval_X, map_pow, map_one, map_add, map_natCast,
    map_ofNat] at hz
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h hcK
  rcases mul_eq_zero.1 h with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · -- z = 0
      have hz0 : z = 0 := pow_eq_zero_iff' .. |>.1 h'' |>.1
      left
      rw [belyiPoly_aeval, hz0]
      simp
    · -- z = 1
      have hz1 : z = 1 := by
        have h3 : (1 : ℂ) - z = 0 := pow_eq_zero_iff' (M₀ := ℂ) (a := 1 - z) (n := b) |>.1 h'' |>.1
        linear_combination -h3
      left
      rw [belyiPoly_aeval, hz1]
      simp
  · -- z = (a+1)/(a+b+2)
    right
    set q : ℚ := ((a : ℚ) + 1) / (((a : ℚ) + 1) + ((b : ℚ) + 1)) with hq
    have hden : (((a : ℂ) + 1) + ((b : ℂ) + 1)) ≠ 0 := by
      intro hcon
      have h1 : (((a + b + 2 : ℕ) : ℂ)) = 0 := by push_cast; linear_combination hcon
      simp only [Nat.cast_eq_zero] at h1
      omega
    have hzq : z = (q : ℂ) := by
      rw [hq]
      push_cast
      field_simp
      linear_combination -h'
    rw [hzq, aeval_rat]
    have : (belyiPoly (a + 1) (b + 1)).eval q = 1 := by
      have := belyiPoly_eval_lambda (m := a + 1) (n := b + 1) (by omega) (by omega)
      rw [hq]
      push_cast at this ⊢
      exact this
    rw [this]
    norm_num

end CriticalValues

section UnitInterval

/-- A form of the weighted AM-GM inequality, proved from `1 + t ≤ exp t`. -/
