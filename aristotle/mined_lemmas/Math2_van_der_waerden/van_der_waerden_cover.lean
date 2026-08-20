import Mathlib
/-!
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- **Van der Waerden's theorem**: for any coloring `C : ℕ → κ` of the naturals by a finite
set of colors `κ`, and any length `k`, there is a monochromatic arithmetic progression
`b, b + a, …, b + (k-1) * a` with common difference `a > 0`.

This is deduced from the Hales–Jewett theorem, via Mathlib's
`Combinatorics.exists_mono_homothetic_copy`. -/

theorem van_der_waerden_cover {ι : Type*} [Finite ι] (S : ι → Set ℕ)
    (hcover : ∀ n : ℕ, ∃ i, n ∈ S i) (k : ℕ) :
    ∃ i, ∃ a > 0, ∃ b, ∀ j < k, b + j * a ∈ S i := by
  classical
  choose C hC using hcover
  obtain ⟨a, ha, b, c, hc⟩ := van_der_waerden C k
  refine ⟨c, a, ha, b, fun j hj => ?_⟩
  have := hC (b + j * a)
  rwa [hc j hj] at this

end Math2

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

