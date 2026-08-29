/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The `n`-dimensional torus `𝕋ⁿ = (ℝ/ℤ)ⁿ`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- `W` parametrizes an invariant torus of the map `f` on which the dynamics is
conjugate to the rigid rotation by the frequency vector `ω`:
`f (W θ) = W (θ + ω)` for all angles `θ ∈ 𝕋ⁿ`. -/

theorem kam_theorem_nonvacuous (ω : Torus 1) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ W : C(Torus 1, ℝ), IsInvariantTorus (exFam ε) ω W ∧ dist W 0 ≤ 2 * ε := by
  have hW₀ : IsInvariantTorus (exFam 0) ω (0 : C(Torus 1, ℝ)) := by
    intro θ; simp [exFam]
  have hmain := kam_theorem (V := ℝ) exFam ω 0 (exOp ω) (1/2) 1 ε
    (by norm_num) (by norm_num) (by norm_num) hε hW₀
    (fun x => by simp [exFam, abs_of_nonneg hε])
    (fun W => exOp_fix ω 0 W) (fun W => exOp_fix ω ε W)
    (exOp_lipschitz ω ε)
    (fun W θ => by
      simp only [exOp, exFam, ContinuousMap.coe_mk, Real.dist_eq, Real.norm_eq_abs]
      have h1 : (W (θ - ω) / 2 + ε) - (W (θ - ω) / 2 + 0) = ε := by ring
      have h2 : (W θ / 2 + ε) - (W θ / 2 + 0) = ε := by ring
      rw [h1, h2, one_mul])
  obtain ⟨W, hW, hd⟩ := hmain
  exact ⟨W, hW, by
    refine hd.trans ?_
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 1/2)]
    linarith⟩

end Frontier

