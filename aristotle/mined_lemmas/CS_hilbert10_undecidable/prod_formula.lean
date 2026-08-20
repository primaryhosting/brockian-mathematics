import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/

theorem prod_formula (y t : ℕ) :
    ∏ i ∈ range y, (1 + (i + 1) * t)
      = t ^ y * (y ! * (((t - 1) * (1 + y * t) ^ y + 1 + y).choose y))
          % (t * (1 + y * t) ^ y + 1) + (1 - t) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Nat.mod_one]
  · set K := (1 + y * t) ^ y with hK
    set M := t * K + 1 with hM
    set r := (t - 1) * K + 1 with hr
    have htr : t * r = (t - 1) * M + 1 := by
      rw [hr, hM]
      cases t with
      | zero => omega
      | succ s => ring_nf; simp; omega
    have hprod : ∏ i ∈ range y, (r + 1 + i) = y ! * (r + y).choose y := by
      rw [← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]
    have hcong := prod_modEq y t M r htr
    rw [hprod] at hcong
    have hlt : ∏ i ∈ range y, (1 + (i + 1) * t) < M := by
      have h1 := prod_le_pow y t
      have h2 : K ≤ t * K := Nat.le_mul_of_pos_left _ ht
      omega
    have h0 : (1 : ℕ) - t = 0 := by omega
    rw [h0, Nat.add_zero]
    have h3 := hcong.symm
    unfold Nat.ModEq at h3
    rw [Nat.mod_eq_of_lt hlt] at h3
    rw [← h3]

open Dioph in
/-- **The products `(y, t) ↦ ∏_{k=1}^{y} (1 + k * t)` form a Diophantine function.**
These products supply the pairwise coprime moduli used in the Chinese-remainder coding of
finite sequences in the proof of the MRDP theorem. -/
