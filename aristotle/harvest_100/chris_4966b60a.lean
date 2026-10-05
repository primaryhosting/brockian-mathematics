import Mathlib

/-!
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
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


namespace Math2

/-- **Van der Waerden's theorem**: any coloring `C : ℕ → κ` of the natural numbers by a finite
set of colors `κ` admits arbitrarily long monochromatic arithmetic progressions: for every
length `k` there are a common difference `a > 0`, a starting point `b`, and a color `c` such
that `C (b + i * a) = c` for all `i < k`. -/
theorem van_der_waerden {κ : Type*} [Finite κ] (C : ℕ → κ) (k : ℕ) :
    ∃ a > 0, ∃ b : ℕ, ∃ c : κ, ∀ i < k, C (b + i * a) = c := by
  obtain ⟨a, ha, b, c, hc⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range k) C
  refine ⟨a, ha, b, c, fun i hi => ?_⟩
  have := hc i (Finset.mem_range.mpr hi)
  rwa [smul_eq_mul, mul_comm a i, add_comm (i * a) b] at this

end Math2

