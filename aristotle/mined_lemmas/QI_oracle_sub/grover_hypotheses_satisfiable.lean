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

namespace QI

variable {N M : ℕ}

/-- The state space of a quantum query algorithm searching a database of size `N`:
an index register `Fin N` together with an arbitrary finite workspace `Fin M`. -/
abbrev State (N M : ℕ) : Type := EuclideanSpace ℂ (Fin N × Fin M)

/-- The standard phase oracle marking the index `i`: it flips the sign of every
amplitude whose index register holds `i`, and does nothing otherwise. -/

theorem grover_hypotheses_satisfiable :
    ∃ (U : ℕ → (State 1 1 ≃ₗᵢ[ℂ] State 1 1)) (psi0 : State 1 1),
      ‖psi0‖ = 1 ∧
      ∀ i : Fin 1, (2 : ℝ) ≤ ‖run U psi0 (oracle i) 1 - run U psi0 id 1‖ := by
  refine ⟨fun _ => LinearIsometryEquiv.refl ℂ (State 1 1), WithLp.toLp 2 (fun _ => 1), ?_, ?_⟩
  · rw [show ‖(WithLp.toLp 2 (fun _ => 1) : State 1 1)‖
        = √(‖(WithLp.toLp 2 (fun _ => 1) : State 1 1)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm, EuclideanSpace.norm_sq_eq]
    simp
  · intro i
    have hall : ∀ x : Fin 1 × Fin 1, x.1 = i := fun x => Subsingleton.elim _ _
    have hsq : ‖run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) (oracle i) 1
        - run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) id 1‖ ^ 2 = 4 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [run, hall]
      norm_num
    nlinarith [norm_nonneg (run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) (oracle i) 1
        - run (fun _ => LinearIsometryEquiv.refl ℂ (State 1 1))
          (WithLp.toLp 2 (fun _ => 1)) id 1)]

end QI

