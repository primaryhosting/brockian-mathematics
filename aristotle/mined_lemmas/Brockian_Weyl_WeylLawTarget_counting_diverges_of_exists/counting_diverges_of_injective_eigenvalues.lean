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

/-
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`countingFunction S t` is the number of points of `S` that are `≤ t`.
(As usual for `Set.ncard`, this is `0` when `S ∩ Set.Iic t` is infinite; in the Weyl-law
setting the spectrum is locally finite, so this degenerate case does not occur.) -/

theorem counting_diverges_of_injective_eigenvalues (lam : ℕ → ℝ)
    (hinj : Function.Injective lam)
    (hlf : ∀ t : ℝ, (Set.range lam ∩ Set.Iic t).Finite) :
    Filter.Tendsto (countingFunction (Set.range lam)) Filter.atTop Filter.atTop :=
  counting_diverges_of_exists _ hlf ⟨lam, hinj, fun n => Set.mem_range_self n⟩

/-- Non-vacuity check: the hypotheses of `counting_diverges_of_exists` are satisfiable,
e.g. by the model spectrum `{0, 1, 2, …} ⊆ ℝ`. -/
example : Filter.Tendsto (countingFunction (Set.range (fun n : ℕ => (n : ℝ))))
    Filter.atTop Filter.atTop := by
  refine counting_diverges_of_injective_eigenvalues _ Nat.cast_injective (fun t => ?_)
  apply Set.Finite.subset ((Set.finite_Icc 0 ⌊t⌋₊).image (fun n : ℕ => (n : ℝ)))
  rintro x ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, ⟨Nat.zero_le n, Nat.le_floor hx⟩, rfl⟩

end Brockian.Weyl.WeylLawTarget

