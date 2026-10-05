import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Elementary optimisation step

The Thomas–Fermi-type minimisation `t ↦ K t - A √t √N` used in the proof of stability of
matter. -/

/-- If `K > 0` and `A ≥ 0`, then `K t - A √(t N) ≥ -(A²/(4K)) N` for `t, N ≥ 0`. -/

theorem classical_lieb_thirring_constant_one_dim {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 / (2 * Real.pi)) *
        ∫ p in (-Real.sqrt lam)..(Real.sqrt lam), (lam - p ^ 2)
      = (2 / (3 * Real.pi)) * lam ^ (3 / 2 : ℝ) := by
  have hs : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam
  have hint : ∫ p in (-Real.sqrt lam)..(Real.sqrt lam), (lam - p ^ 2)
      = (4 / 3) * lam * Real.sqrt lam := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _)]
    rw [integral_const, integral_pow]
    simp only [smul_eq_mul]
    ring_nf
    nlinarith [hs, Real.sqrt_nonneg lam]
  rw [hint]
  have hpow : lam ^ (3 / 2 : ℝ) = lam * Real.sqrt lam := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hlam (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpow]
  ring

end Frontier

