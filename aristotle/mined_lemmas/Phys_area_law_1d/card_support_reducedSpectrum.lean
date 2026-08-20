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

lemma card_support_reducedSpectrum {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) :
    (Finset.univ.filter fun a => reducedSpectrum M a ≠ 0).card = M.rank := by
  classical
  have h := (Matrix.isHermitian_mul_conjTranspose_self M).rank_eq_card_non_zero_eigs
  rw [Matrix.rank_self_mul_conjTranspose] at h
  rw [h, Fintype.card_subtype]
  rfl

/-- **Rank bound on entanglement entropy**: a normalized bipartite pure state whose coefficient
matrix has rank (Schmidt rank) at most `D` has entanglement entropy at most `log D`. -/
