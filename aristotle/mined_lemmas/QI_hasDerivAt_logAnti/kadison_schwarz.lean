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

theorem kadison_schwarz (Y : Matrix m m ℂ) :
    (Φ.adjoint (Yᴴ * Y) - (Φ.adjoint Y)ᴴ * Φ.adjoint Y).PosSemidef := by
  set A := Φ.adjoint Y with hA
  have key : ∑ i, (Y * Φ.K i - Φ.K i * A)ᴴ * (Y * Φ.K i - Φ.K i * A)
      = Φ.adjoint (Yᴴ * Y) - Aᴴ * A := by
    have expand : ∀ i : ι, (Y * Φ.K i - Φ.K i * A)ᴴ * (Y * Φ.K i - Φ.K i * A)
        = (Φ.K i)ᴴ * (Yᴴ * Y) * Φ.K i - ((Φ.K i)ᴴ * Yᴴ * Φ.K i) * A
          - Aᴴ * ((Φ.K i)ᴴ * Y * Φ.K i) + Aᴴ * ((Φ.K i)ᴴ * Φ.K i) * A := by
      intro i
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul,
        Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => expand i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ i : ι, (Φ.K i)ᴴ * (Yᴴ * Y) * Φ.K i = Φ.adjoint (Yᴴ * Y) := rfl
    have h2 : ∑ i : ι, ((Φ.K i)ᴴ * Yᴴ * Φ.K i) * A = Aᴴ * A := by
      rw [← Finset.sum_mul]
      congr 1
      rw [hA, ← Φ.adjoint_conjTranspose]
      simp [adjoint, Matrix.mul_assoc]
    have h3 : ∑ i : ι, Aᴴ * ((Φ.K i)ᴴ * Y * Φ.K i) = Aᴴ * A := by
      rw [← Finset.mul_sum]
      rfl
    have h4 : ∑ i : ι, Aᴴ * ((Φ.K i)ᴴ * Φ.K i) * A = Aᴴ * A := by
      have hstep : ∑ i : ι, Aᴴ * ((Φ.K i)ᴴ * Φ.K i) * A
          = Aᴴ * ((∑ i : ι, (Φ.K i)ᴴ * Φ.K i) * A) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_assoc]
      rw [hstep, Φ.complete, Matrix.one_mul]
    rw [h1, h2, h3, h4]
    abel
  rw [← key]
  exact Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_conjTranspose_mul_self _

/-- The other form of the Kadison–Schwarz inequality: `(Φ*Y) (Φ*Y)ᴴ ≤ Φ*(Y Yᴴ)`. -/
