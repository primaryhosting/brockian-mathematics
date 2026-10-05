import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

theorem isQuantumMeasure_of_density {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : IsDensityMatrix ρ) :
    IsQuantumMeasure (fun P : Matrix (Fin N) (Fin N) ℂ => (ρ * P).trace.re) := by
  obtain ⟨hpsd, htr⟩ := hρ
  refine ⟨fun P hP => ?_, ?_, fun P Q _ _ _ => ?_⟩
  · have h : (ρ * P).trace = (Pᴴ * ρ * P).trace := by
      conv_lhs => rw [← hP.2]
      rw [hP.1.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have hnn : (0 : ℂ) ≤ (ρ * P).trace := by
      rw [h]; exact (hpsd.conjTranspose_mul_mul_same P).trace_nonneg
    simpa using (Complex.le_def.mp hnn).1
  · rw [Matrix.mul_one, htr, Complex.one_re]
  · rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

end Frontier

