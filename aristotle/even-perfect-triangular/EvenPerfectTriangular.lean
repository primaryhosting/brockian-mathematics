import Mathlib
namespace Brockian.EvenPerfectTriangular
/-- Every even perfect number is a triangular number: n = k(k+1)/2 for some k.
    (Euclid–Euler: n = 2^(p-1)(2^p-1) = T_{2^p-1}.) Replace the sorry; axiom-clean, no sorry. -/
theorem even_perfect_triangular {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    ∃ k : ℕ, n = k * (k + 1) / 2 := by
  sorry
end Brockian.EvenPerfectTriangular
