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

lemma rank_mpsCoeff_le {d D k m : ℕ}
    (AL : Fin k → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (AR : Fin m → Fin d → Matrix (Fin D) (Fin D) ℂ) (u v : Fin D → ℂ) :
    (mpsCoeff AL AR u v).rank ≤ D := by
  rw [mpsCoeff_eq_mul]
  refine le_trans (Matrix.rank_mul_le_right _ _) ?_
  have h := Matrix.rank_le_card_height
    (R := ℂ) (Matrix.of fun (x : Fin D) (sR : Fin m → Fin d) => (blockProd AR sR *ᵥ v) x)
  simpa using h

/-- **Area law for gapped 1D ground states (Hastings).**

A gapped local Hamiltonian on a 1D chain has a ground state that is (arbitrarily well
approximated by) a matrix product state whose bond dimension `D` depends only on the spectral
gap and the local dimension, not on the length of the chain.  The theorem below is the
entanglement-entropy area law for such states: for a matrix product state of bond dimension `D`
on a chain split into a left block of `k` sites and a right block of `m` sites, the entanglement
entropy across the cut is bounded by `log D`, a constant that is independent of the block sizes
`k`, `m` and hence of the size of the subsystem — the entropy scales like the size of the
boundary of the region (a single point in 1D), which is exactly the area law. -/
