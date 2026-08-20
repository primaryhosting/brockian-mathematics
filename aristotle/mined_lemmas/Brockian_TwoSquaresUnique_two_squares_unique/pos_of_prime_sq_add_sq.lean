import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

private lemma pos_of_prime_sq_add_sq {p a b : ℕ} (hp : p.Prime) (h : p = a ^ 2 + b ^ 2) :
    0 < a := by
  by_contra ha
  push_neg at ha
  interval_cases a
  simp at h
  subst h
  rcases b with _ | _ | b <;> simp_all [Nat.Prime]
  have : (b + 1 + 1) ^ 2 = (b + 1 + 1) * (b + 1 + 1) := by ring
  rw [this] at hp
  rcases hp.isUnit_or_isUnit rfl with h | h <;> simp at h

/-- If `p` is prime and `p = a^2 + b^2`, then `a` and `b` are coprime. -/
