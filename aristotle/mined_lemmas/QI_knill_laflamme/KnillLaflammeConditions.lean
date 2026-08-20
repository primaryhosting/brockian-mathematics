/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : ℕ}

/-! ## Definitions -/

/-- `P` is (the matrix of) an orthogonal projection onto a nonzero code subspace. -/
structure IsCode (P : Matrix (Fin n) (Fin n) ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for a code with projection `P` and error operators `E`:
there is a matrix of scalars `c` with `P Eₐ† E_b P = c a b • P`. -/

def KnillLaflammeConditions (P : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin m → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : Matrix (Fin m) (Fin m) ℂ, ∀ a b, P * (E a)ᴴ * E b * P = c a b • P

/-- The code with projection `P` corrects the error operators `E` (the Kraus operators of the
error channel): there is a quantum channel, given by Kraus operators `R` with `∑ Rₖ† Rₖ = 1`,
which undoes the error channel on every operator supported on the code. -/
