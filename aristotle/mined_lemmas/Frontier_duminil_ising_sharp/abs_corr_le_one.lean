/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The finite-volume Ising model -/

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real spin value `±1` attached to a Boolean spin variable. -/

lemma abs_corr_le_one (β : ℝ) (J : V → V → ℝ) (x y : V) : |corr β J x y| ≤ 1 := by
  have hZ := Z_pos (V := V) β J
  rw [corr, abs_div, abs_of_pos hZ, div_le_one hZ]
  calc |∑ σ : V → Bool, weight β J σ * (spin (σ x) * spin (σ y))|
      ≤ ∑ σ : V → Bool, |weight β J σ * (spin (σ x) * spin (σ y))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = Z β J := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [abs_mul, abs_mul, abs_spin, abs_spin, one_mul, mul_one,
          abs_of_pos (weight_pos β J σ)]

