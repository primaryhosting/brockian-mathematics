import Mathlib

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

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The required header comment is placed immediately after `import Mathlib`, since Lean 4 does not
-- allow a module doc comment to precede the `import` commands.)

open scoped LinearPMap ComplexConjugate

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

/-- The Hilbert space `ℓ²(ℤ, ℂ)` of square-summable two-sided sequences. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

/-- A densely defined operator is *essentially self-adjoint* when its adjoint is self-adjoint;
equivalently, when its closure is its unique self-adjoint extension. -/

def multCLM (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : L2Z →L[ℂ] L2Z :=
  (multLM V C hV).mkContinuous C (by
    intro f
    have hC : 0 ≤ C := le_trans (abs_nonneg _) (hV 0)
    have hf : Summable fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal :=
      (lp.memℓp f).summable (by norm_num)
    refine lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hC (norm_nonneg f)) ?_
    have hle : ∀ n : ℤ, ‖(multLM V C hV f) n‖ ^ (2 : ENNReal).toReal
        ≤ C ^ (2 : ENNReal).toReal * ‖f n‖ ^ (2 : ENNReal).toReal := by
      intro n
      have h1 : ‖(multLM V C hV f) n‖ = |V n| * ‖f n‖ := by
        show ‖(V n : ℂ) * f n‖ = _
        simp [Complex.norm_real]
      rw [h1, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
      gcongr
      exact hV n
    calc ∑' n, ‖(multLM V C hV f) n‖ ^ (2 : ENNReal).toReal
        ≤ ∑' n, C ^ (2 : ENNReal).toReal * ‖f n‖ ^ (2 : ENNReal).toReal :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le
            (fun n => Real.rpow_nonneg (norm_nonneg _) _) hle (hf.mul_left _)) (hf.mul_left _)
      _ = C ^ (2 : ENNReal).toReal * ∑' n, ‖f n‖ ^ (2 : ENNReal).toReal := tsum_mul_left
      _ = (C * ‖f‖) ^ (2 : ENNReal).toReal := by
          rw [Real.mul_rpow hC (norm_nonneg f), ← lp.norm_rpow_eq_tsum (by norm_num) f])

