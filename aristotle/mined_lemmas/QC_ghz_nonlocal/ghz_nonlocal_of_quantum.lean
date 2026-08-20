/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
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

namespace QC

/-! ## The quantum side: the GHZ state is a joint eigenvector of the Mermin observables -/

/-- Index type for the computational basis of three qubits. -/
abbrev Idx : Type := Fin 2 × Fin 2 × Fin 2

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/

theorem ghz_nonlocal_of_quantum :
    ((kron3 pauliX pauliY pauliY).mulVec ghz = -ghz ∧
     (kron3 pauliY pauliX pauliY).mulVec ghz = -ghz ∧
     (kron3 pauliY pauliY pauliX).mulVec ghz = -ghz ∧
     (kron3 pauliX pauliX pauliX).mulVec ghz = ghz ∧ ghz ≠ 0) ∧
    ∀ A B C : Bool → ℤ, (∀ s, A s = 1 ∨ A s = -1) → (∀ s, B s = 1 ∨ B s = -1) →
      (∀ s, C s = 1 ∨ C s = -1) →
      ¬ (A true * B false * C false = -1 ∧
         A false * B true * C false = -1 ∧
         A false * B false * C true = -1 ∧
         A true * B true * C true = 1) :=
  ⟨⟨ghz_eigen_XYY, ghz_eigen_YXY, ghz_eigen_YYX, ghz_eigen_XXX, ghz_ne_zero⟩, ghz_nonlocal⟩

end QC

