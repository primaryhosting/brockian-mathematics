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

theorem grover_optimal_sqrt (T : ℕ) (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (psi0 : HSpace N K)
    (hpsi0 : ‖psi0‖ = 1)
    (hsucc : ∀ x : Fin N, (2 : ℝ) / 3 ≤ ‖(run U (phaseOracle x) psi0 T) x‖ ^ 2) :
    Real.sqrt N ≤ 3 * ((T : ℝ) + 1) := by
  have hmain := grover_optimal T U psi0 hpsi0 hsucc
  have hprod : Real.sqrt (2 * N / 3) = Real.sqrt N * Real.sqrt (2 / 3) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
    ring_nf
  have hc : (4 : ℝ) / 5 ≤ Real.sqrt (2 / 3) := by
    rw [show (4 : ℝ) / 5 = Real.sqrt ((4 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsq : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith [hmain, hprod, hc, hsq]

end QI

