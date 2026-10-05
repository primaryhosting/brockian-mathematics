/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The finite square-lattice Ising model on an `L × L` torus -/

/-- The cyclic shift `i ↦ i + 1` on `Fin L` (periodic boundary conditions). -/

lemma abs_energy_le (L : ℕ) (σ : Config L) : |energy L σ| ≤ 2 * (L * L : ℕ) := by
  rw [energy, abs_neg]
  calc |∑ x : Fin L × Fin L,
          (spin (σ x) * spin (σ (shift x.1, x.2)) + spin (σ x) * spin (σ (x.1, shift x.2)))|
      ≤ ∑ x : Fin L × Fin L,
          |spin (σ x) * spin (σ (shift x.1, x.2)) + spin (σ x) * spin (σ (x.1, shift x.2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin L × Fin L, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        calc |spin (σ x) * spin (σ (shift x.1, x.2)) + spin (σ x) * spin (σ (x.1, shift x.2))|
            ≤ |spin (σ x) * spin (σ (shift x.1, x.2))| +
              |spin (σ x) * spin (σ (x.1, shift x.2))| := abs_add_le _ _
          _ = 2 := by rw [abs_mul, abs_mul, abs_spin, abs_spin, abs_spin]; norm_num
    _ = 2 * (L * L : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [mul_comm]

/-- Two-sided bound on the partition function. -/
