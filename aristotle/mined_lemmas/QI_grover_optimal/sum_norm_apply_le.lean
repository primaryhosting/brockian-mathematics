import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-- The Hilbert space of a quantum query algorithm searching a database of `N` items:
the index register `Fin N` together with an arbitrary workspace register `K`. -/
abbrev HSpace (N : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Fin N => K)

variable {N : ℕ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The (phase) query operator for the database whose unique marked item is `x`:
it flips the sign of the component of the index register at `x`. -/

lemma sum_norm_apply_le (psi : HSpace N K) :
    ∑ x : Fin N, ‖psi x‖ ≤ Real.sqrt N * ‖psi‖ := by
  have hsq : ‖psi‖ ^ 2 = ∑ x : Fin N, ‖psi x‖ ^ 2 := by
    rw [PiLp.norm_eq_of_L2, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => by positivity
  have h2 : (0 : ℝ) ≤ ∑ x : Fin N, ‖psi x‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have h1 : (∑ x : Fin N, ‖psi x‖) ^ 2 ≤ (N : ℝ) * ‖psi‖ ^ 2 := by
    rw [hsq]
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun x => ‖psi x‖)
  calc ∑ x : Fin N, ‖psi x‖ = Real.sqrt ((∑ x : Fin N, ‖psi x‖) ^ 2) := (Real.sqrt_sq h2).symm
    _ ≤ Real.sqrt ((N : ℝ) * ‖psi‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt N * ‖psi‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq (norm_nonneg _)]

/-- The state of the oracle-free run keeps the norm of the initial state. -/
