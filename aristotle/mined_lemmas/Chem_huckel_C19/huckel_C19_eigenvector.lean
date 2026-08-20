/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem huckel_C19_eigenvector (k : Fin 19) :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ *ᵥ
        (fun j : Fin 19 => Complex.exp (2 * Real.pi * (j : ℕ) * (k : ℕ) / 19 * I)) =
      (2 * (Real.cos (2 * Real.pi * (k : ℕ) / 19) : ℂ)) •
        (fun j : Fin 19 => Complex.exp (2 * Real.pi * (j : ℕ) * (k : ℕ) / 19 * I)) := by
  have hval : ∀ j : Fin 19,
      ee (j * k) = Complex.exp (2 * Real.pi * (j : ℕ) * (k : ℕ) / 19 * I) := by
    intro j
    rw [ee, Fin.val_mul, om_pow_mod, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h := adjMatrix_mulVec_ee k
  simp only [hval] at h
  simpa [AC19, mu] using h

end Chem

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

