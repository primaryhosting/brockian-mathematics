import Mathlib
namespace MS2.NT2


theorem mobius_inversion (f g : ℕ → ℤ) (h : ∀ n, 0 < n → g n = ∑ d ∈ Nat.divisors n, f d) (n : ℕ)
    (hn : 0 < n) :
    f n = ∑ d ∈ Nat.divisors n, (ArithmeticFunction.moebius (n/d)) * g d := by
  have h' : ∀ m : ℕ, 0 < m → ∑ d ∈ Nat.divisors m, f d = g m := fun m hm => (h m hm).symm
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)).mp h' n hn
  rw [← key]
  simp only [Int.cast_id]
  exact Nat.sum_divisorsAntidiagonal' (fun x y => (ArithmeticFunction.moebius x : ℤ) * g y)

end MS2.NT2

