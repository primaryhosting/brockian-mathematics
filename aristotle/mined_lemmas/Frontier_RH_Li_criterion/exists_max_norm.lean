/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem exists_max_norm {z : ℕ → ℂ} (he : Summable fun k => max 0 (‖z k‖ - 1)) {j : ℕ}
    (hj : 1 < ‖z j‖) : ∃ M : ℝ, 1 < M ∧ (∃ k, ‖z k‖ = M) ∧ ∀ k, ‖z k‖ ≤ M := by
  set η : ℝ := (‖z j‖ - 1) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hfin := finite_large_norm he hη
  set S : Finset ℕ := hfin.toFinset with hS
  have hjS : j ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq, hηdef]
    linarith
  obtain ⟨k0, hk0S, hk0⟩ := S.exists_max_image (fun k => ‖z k‖) ⟨j, hjS⟩
  refine ⟨‖z k0‖, lt_of_lt_of_le hj (hk0 j hjS), ⟨k0, rfl⟩, fun k => ?_⟩
  by_cases hk : k ∈ S
  · exact hk0 k hk
  · rw [hS, Set.Finite.mem_toFinset] at hk
    simp only [Set.mem_setOf_eq, not_le] at hk
    have hjk : ‖z j‖ ≤ ‖z k0‖ := hk0 j hjS
    rw [hηdef] at hk
    linarith

/-- There is a gap below the maximal norm: the indices attaining the maximum form a
nonempty finite set `F`, and all other members have norm at most some `M' < M`. -/
