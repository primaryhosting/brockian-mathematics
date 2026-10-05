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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a family of eigenvalues `lam : ι → ℝ`:
`counting lam t` is the number of indices `i` with `lam i ≤ t`. -/

theorem counting_diverges_dirichlet_interval :
    Filter.Tendsto (counting (fun n : ℕ => ((n : ℝ) + 1) ^ 2)) Filter.atTop Filter.atTop := by
  refine counting_diverges_of_exists _ (fun t => ?_)
  apply Set.Finite.subset (Set.finite_Iic ⌈t⌉₊)
  intro n hn
  have hn' : ((n : ℝ) + 1) ^ 2 ≤ t := hn
  have h1 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h2 : (n : ℝ) ≤ t := by linarith
  exact Set.mem_Iic.2 (Nat.cast_le.mp (h2.trans (Nat.le_ceil t)))

end Brockian.Weyl.WeylLawTarget

