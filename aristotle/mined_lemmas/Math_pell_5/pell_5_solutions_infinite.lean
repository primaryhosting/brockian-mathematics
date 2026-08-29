/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.** The equation `x² - 5·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (so that `x ≠ ±1`): take `(x, y) = (9, 4)`,
since `9² - 5·4² = 81 - 80 = 1`. -/

theorem pell_5_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 5 * p.2 ^ 2 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨a, b⟩, hb⟩
  obtain ⟨x, y, hxy, hy⟩ := pell_5_infinitely_many b
  have := hb (show (x, y) ∈ {p : ℤ × ℤ | p.1 ^ 2 - 5 * p.2 ^ 2 = 1} from hxy)
  exact absurd this.2 (by omega)

end Math

