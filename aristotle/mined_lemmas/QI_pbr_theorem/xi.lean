import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

noncomputable def xi : Fin 4 → Vec4 :=
  ![fun x => s * (tens ket0 ket1 x + tens ket1 ket0 x),
    fun x => s * (tens ket0 ketM x + tens ket1 ketP x),
    fun x => s * (tens ketP ket1 x + tens ketM ket0 x),
    fun x => s * (tens ketP ketM x + tens ketM ketP x)]

/-- The preparation used in the PBR argument: `prep 0 = |0⟩`, `prep 1 = |+⟩`. -/
