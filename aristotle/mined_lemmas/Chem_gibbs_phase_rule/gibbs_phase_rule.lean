import Mathlib
/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

namespace Chem

/-! ## An affine dimension count for linear systems -/

/-- For a surjective linear map `f`, the solution set of `f v = b` is nonempty and its
direction (the vector span of the solution set) is exactly `ker f`. -/

theorem gibbs_phase_rule (C P : ℕ) (hP : 1 ≤ P)
    (equil : PhaseState C P →ₗ[ℝ] (Fin (P - 1) → Fin C → ℝ))
    (hsurj : Function.Surjective (constraints C P equil)) :
    ({s : PhaseState C P | (∀ j, ∑ i, s.2.2 j i = 1) ∧ equil s = 0}).Nonempty ∧
      Module.finrank ℝ
          (vectorSpan ℝ {s : PhaseState C P | (∀ j, ∑ i, s.2.2 j i = 1) ∧ equil s = 0})
        + P = C + 2 := by
  have hset : {s : PhaseState C P | (∀ j, ∑ i, s.2.2 j i = 1) ∧ equil s = 0}
      = {s : PhaseState C P | constraints C P equil s = (1, 0)} := by
    ext s
    simp only [Set.mem_setOf_eq, constraints, LinearMap.prod_apply, Pi.prod, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨funext fun j => by simpa [normalization] using h1 j, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ?_, h2⟩
      have := congrFun h1 j
      simpa [normalization] using this
  rw [hset]
  obtain ⟨hne, hrank⟩ :=
    finrank_vectorSpan_solution_set (constraints C P equil) hsurj (1, 0)
  refine ⟨hne, ?_⟩
  rw [finrank_phaseState, finrank_constraintSpace] at hrank
  have hrank' : Module.finrank ℝ
      (vectorSpan ℝ {s : PhaseState C P | constraints C P equil s = (1, 0)})
      + (P + (P - 1) * C) = 2 + P * C := hrank
  have h1 : (P - 1) * C = P * C - C := by
    cases P with
    | zero => simp
    | succ n => simp [Nat.succ_mul]
  have h2 : C ≤ P * C := Nat.le_mul_of_pos_left C hP
  omega

/-- Non-vacuity check: for a one-phase system with at least one component the nondegeneracy
hypothesis of `Chem.gibbs_phase_rule` is satisfiable (so the phase rule applies, giving
`F = C + 1` degrees of freedom). -/
