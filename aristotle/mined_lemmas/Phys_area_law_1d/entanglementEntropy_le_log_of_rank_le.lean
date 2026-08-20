/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

namespace Phys

open Matrix
open scoped ComplexOrder

/-- Von Neumann entropy of a spectrum `p` (a list of eigenvalues of a density matrix). -/

theorem entanglementEntropy_le_log_of_rank_le {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (M : Matrix A B ℂ) (hM : ∑ a : A, ∑ b : B, ‖M a b‖ ^ 2 = 1) {D : ℕ}
    (hrank : M.rank ≤ D) : entanglementEntropy M ≤ Real.log D := by
  classical
  refine vnEntropy_le_log_of_card_support_le (reducedSpectrum_nonneg M)
    (sum_reducedSpectrum M hM) ?_
  rw [card_support_reducedSpectrum M]
  exact hrank

/-- A matrix product state factors, across any cut, through the `D`-dimensional bond space. -/
