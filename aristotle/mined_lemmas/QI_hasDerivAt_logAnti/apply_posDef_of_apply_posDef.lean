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

import RequestProject.QI.Spectral

/-!
# An integral formula for the relative entropy

The elementary scalar identity

`∫_0^∞ (a²/(b + t a) - a/(1 + t)) dt = a (log a - log b)`  (`QI.integral_scalar`)

for `a, b > 0`, combined with the spectral formulas of `RequestProject.QI.Spectral`, gives the
integral representation

`relEntropy ρ σ = ∫_{t ∈ (0, ∞)} (Rval ρ σ t - (tr ρ).re / (1 + t)) dt`

(`QI.relEntropy_eq_integral`) for positive definite `ρ`, `σ`.  Since `Rval` is monotone under
quantum channels, this immediately yields the data-processing inequality.
-/

namespace QI

open Real MeasureTheory Filter Set Matrix
open scoped Topology ComplexOrder BigOperators MatrixOrder

/-! ### The scalar integral -/

/-- The antiderivative of `t ↦ a²/(b + t a) - a/(1 + t)`. -/

theorem apply_posDef_of_apply_posDef {X Y : Matrix n n ℂ} (hX : X.PosDef)
    (hY : (Φ.apply Y).PosDef) : (Φ.apply X).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (Φ.apply_posSemidef hX.posSemidef).isHermitian
    fun v hv => ?_
  have hYv := hY.dotProduct_mulVec_pos hv
  rw [Φ.dotProduct_apply_mulVec Y v] at hYv
  have hex : ∃ i : ι, (Φ.K i)ᴴ *ᵥ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hzero : ∀ i : ι, star ((Φ.K i)ᴴ *ᵥ v) ⬝ᵥ (Y *ᵥ ((Φ.K i)ᴴ *ᵥ v)) = 0 := by
      intro i; rw [hc i]; simp
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hzero i] at hYv
    simp at hYv
  obtain ⟨i₀, hi₀⟩ := hex
  rw [Φ.dotProduct_apply_mulVec X v]
  refine lt_of_lt_of_le (hX.dotProduct_mulVec_pos hi₀) ?_
  exact Finset.single_le_sum (f := fun i => star ((Φ.K i)ᴴ *ᵥ v) ⬝ᵥ (X *ᵥ ((Φ.K i)ᴴ *ᵥ v)))
    (fun i _ => hX.posSemidef.dotProduct_mulVec_nonneg _) (Finset.mem_univ i₀)

/-- The adjoint map is positive. -/
