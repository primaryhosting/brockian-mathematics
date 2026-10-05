import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
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

namespace Math2

open MeasureTheory Filter Topology AddCircle

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle T → ℂ`,
i.e. `∑_{|n| ≤ N} (fourierCoeff f n) * e^{2πinx/T}`. -/

lemma coeFn_finset_sum_Lp {ι : Type*} (s : Finset ι) (F : ι → Lp ℂ 2 (@haarAddCircle T hT)) :
    ⇑(∑ i ∈ s, F i) =ᵐ[@haarAddCircle T hT] fun x => ∑ i ∈ s, (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Lp.coeFn_zero ℂ 2 (@haarAddCircle T hT))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x hx hx'
      rw [hx]
      simp only [Pi.add_apply, hx', Finset.sum_insert ha]

/-- The `Lp`-valued partial sum of the Fourier series agrees a.e. with the explicit
pointwise partial sum. -/
