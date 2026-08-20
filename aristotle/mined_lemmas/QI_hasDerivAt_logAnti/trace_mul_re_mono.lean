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

theorem trace_mul_re_mono {A B ρ : Matrix n n ℂ} (h : (B - A).PosSemidef) (hρ : ρ.PosSemidef) :
    (Matrix.trace (A * ρ)).re ≤ (Matrix.trace (B * ρ)).re := by
  have := trace_mul_re_nonneg h hρ
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

/-! ### Quantum channels in Kraus form -/

/-- A quantum channel from `n × n` matrices to `m × m` matrices, presented by a
finite family of Kraus operators satisfying the trace-preservation (completeness)
relation `∑ i, (K i)ᴴ * K i = 1`. -/
structure Channel (n m ι : Type*) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype ι] where
  /-- The Kraus operators of the channel. -/
  K : ι → Matrix m n ℂ
  /-- Completeness relation, equivalent to trace preservation. -/
  complete : ∑ i, (K i)ᴴ * K i = 1

namespace Channel

variable (Φ : Channel n m ι)

/-- The action of the channel on states (Schrödinger picture): `X ↦ ∑ i, K i * X * (K i)ᴴ`. -/
