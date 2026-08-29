import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
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

namespace Chem

open Matrix Complex

/-! ## The `n`-th root of unity and its basic arithmetic -/

section Roots

variable (n : ℕ) [NeZero n]

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

theorem huckel_cycle_charpoly (n : ℕ) (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ).charpoly
      = ∏ k : Fin n, (Polynomial.X
          - Polynomial.C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [adjMatrix_eq_conj n hn, Matrix.charpoly_units_conj, huckelDiag, Matrix.charpoly_diagonal]

/-- The explicit Hückel molecular orbitals: the vector `j ↦ ζ^(jk)` (with `ζ = exp (2πi/n)`)
is an eigenvector of the adjacency matrix of `C n` with eigenvalue `2 cos (2 π k / n)`. -/
