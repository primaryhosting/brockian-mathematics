import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

lemma qubitMeasure_add_compl {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) :
    qubitMeasure P + qubitMeasure (1 - P) = 1 := by
  have hentry : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 0 = 1 - P 0 0 := by
    simp [Matrix.sub_apply]
  have hentry' : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 1 = -P 0 1 := by
    simp [Matrix.sub_apply]
  have hre : ((1 : ℂ) - P 0 0).re = 1 - (P 0 0).re := by simp
  unfold qubitMeasure
  rw [hentry, hentry', hre]
  split_ifs <;>
    first
      | linarith
      | exact tieBreak_add_neg (proj2_offdiag_ne_zero hP (by linarith))

