import Mathlib

/-!
# Hückel π-energies of the cycle graph `C n`

The adjacency (Hückel) matrix of the cycle graph `C n` (`n ≥ 3`) has spectrum
`{2 cos (2 π k / n) : k = 0, …, n-1}`, and its characteristic polynomial is
`∏ k, (X - 2 cos (2 π k / n))`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma sub_one_ne_add_one {m : ℕ} (i : Fin (m + 3)) : (i - 1 : Fin (m + 3)) ≠ i + 1 := by
  intro h
  have h2 : (2 : Fin (m + 3)) = 0 := by
    have hz : (i + 1) - (i - 1) = (0 : Fin (m + 3)) := by rw [h, sub_self]
    rw [← hz, show (2 : Fin (m + 3)) = 1 + 1 from rfl]
    abel
  have h3 := congrArg Fin.val h2
  rw [show ((2 : Fin (m + 3)) : ℕ) = 2 % (m + 3) from rfl, Nat.mod_eq_of_lt (by omega)] at h3
  simp at h3

/-- The eigen-equation for the cycle: `A * F = F * D`, where `F` is the Fourier matrix and
`D` is the diagonal matrix of Hückel energies. -/
