/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem image_range_eq (hr : 0 < r) (hrQ : r ≤ Q)
    (hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r) :
    (Finset.range Q).image f = (Finset.range r).image f := by
  apply Finset.Subset.antisymm
  · intro y hy
    simp only [Finset.mem_image, Finset.mem_range] at hy ⊢
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨j % r, Nat.mod_lt _ hr, ?_⟩
    rw [hf, Nat.mod_mod_of_dvd _ dvd_rfl]
  · exact Finset.image_subset_image (by
      intro x hx; simp only [Finset.mem_range] at *; omega)

/-- The measurement distribution of the first register, expressed through the
`r` geometric sums coming from the residue classes modulo the period. -/
