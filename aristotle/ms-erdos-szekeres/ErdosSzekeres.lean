import Mathlib
namespace Brockian.ErdosSzekeres
/-- Erdős–Szekeres: any sequence of r·s+1 distinct reals has a monotone subsequence of length
    r+1 (increasing) or s+1 (decreasing). -/
theorem erdos_szekeres (r s : ℕ) (f : Fin (r * s + 1) → ℝ) (hf : Function.Injective f) :
    (∃ t : Finset (Fin (r * s + 1)), t.card = r + 1 ∧
        StrictMonoOn f ↑t) ∨
    (∃ t : Finset (Fin (r * s + 1)), t.card = s + 1 ∧
        StrictAntiOn f ↑t) := by
  sorry
end Brockian.ErdosSzekeres
