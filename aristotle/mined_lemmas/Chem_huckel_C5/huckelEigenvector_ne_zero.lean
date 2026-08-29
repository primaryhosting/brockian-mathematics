/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

theorem huckelEigenvector_ne_zero (k : ZMod 5) : huckelEigenvector k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [huckelEigenvector, Pi.zero_apply, zero_mul] at h0
  exact e5_ne_zero 0 h0

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₅`.** A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₅` if and only if `μ = 2 cos (2πk/5)` for some
`k ∈ {0, 1, 2, 3, 4}`. -/
