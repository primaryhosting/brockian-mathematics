/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The symmetric partial sum of the Fourier series of `f` at `x`:
`∑_{n = -N}^{N} (fourierCoeff f n) e^{2πinx/T}`. -/

lemma coeFn_finset_sum_Lp {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {ι : Type*}
    (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    ((∑ i ∈ s, F i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, (F i : α → ℂ) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Lp.coeFn_zero ℂ 2 μ
  | insert i s hi ih =>
      filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x hx hx2
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hx, Pi.add_apply, hx2]

/-- The `L²`-partial sum agrees almost everywhere with the pointwise partial sum. -/
