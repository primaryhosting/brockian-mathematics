/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

namespace Chem

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

theorem huckel_C20_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ)
      = Set.range fun k : Fin 20 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C20, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, (sub_eq_zero.mp (by simpa using hk)).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ _, by simp [← hk]⟩

/-- The explicit Hückel molecular orbitals of C₂₀: for each `k`, the vector
`j ↦ exp(2πi jk/20)` is a nonzero eigenvector of the adjacency matrix with
eigenvalue `2·cos(2πk/20)`. -/
