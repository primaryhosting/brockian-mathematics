import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_p_dvd_yz_of_dvd_K_q1
    {n q K p : ℕ} {x y z : ℤ}
    (hp : Nat.Prime p) (hp4 : p % 4 = 3)
    (hpK : p ∣ K) (hp_not_dvd_n : ¬ p ∣ n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = (q : ℤ) * (K : ℤ)) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  have hpK_int : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hpK
  have hk0' : (K : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff K p).2 hpK

  -- Cast the equation into `ZMod p` and use `K = 0` there.
  have hZ0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0 := by
    have := congrArg (fun t : ℤ => (t : ZMod p)) h_eqK
    -- RHS: `q*K = 0` in `ZMod p` because `K = 0`.
    simpa [hk0', mul_assoc, mul_left_comm, mul_comm] using this

  -- From `p ∣ K = n - x^2`, we have `n = x^2` in `ZMod p`.
  have hn_mod : (n : ZMod p) = (x : ZMod p) ^ 2 := by
    have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by simpa [hK_eq] using hpK_int
    have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_dvd_nmx
    have hn_cast : ((n : ℤ) : ZMod p) = (x ^ 2 : ZMod p) := by
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      exact sub_eq_zero.mp this
    simpa [pow_two, mul_assoc] using hn_cast

  exact ankeny_p_dvd_yz_of_zmod_zero (n := n) (p := p) (x := x) (y := y) (z := z)
    hp hp4 hp_not_dvd_n hn_mod hZ0

/-- The remaining local kernel needed for `Nat.eq_sq_add_sq_iff` in the Ankeny reduction.

For a prime `p ≡ 3 (mod 4)` dividing `K = (n - x^2).natAbs`, show that the exponent of `p` in `K`
is even, i.e. `Even (padicValNat p K)`.

This is the bootstrapping step sketched in the comment inside `reduction_to_sum_three_squares`:
use `ankeny_p_dvd_yz_of_dvd_K` to force `p ∣ y` and `p ∣ z`, then descend on `K / p^2`.

This lemma is intentionally stated so its eventual proof can be developed (and tested) in isolation.
-/
