import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

section

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a weight matrix `A`. -/

lemma bil_polarization {A : V → V → ℝ} (hsymm : ∀ i j, A i j = A j i) (x y : V → ℝ) :
    bil A (fun i => x i + y i) (fun i => x i + y i)
      - bil A (fun i => x i - y i) (fun i => x i - y i) = 4 * bil A x y := by
  have h1 : bil A (fun i => x i + y i) (fun i => x i + y i)
      = bil A x x + bil A x y + (bil A y x + bil A y y) := by
    rw [bil_add_left, bil_add_right, bil_add_right]
  have h2 : bil A (fun i => x i - y i) (fun i => x i - y i)
      = bil A x x - bil A x y - (bil A y x - bil A y y) := by
    rw [bil_sub_left, bil_sub_right, bil_sub_right]
  rw [h1, h2, bil_symm hsymm y x]
  ring

/-! ### From the Rayleigh bound to the bilinear bound -/

/-- Half-and-half bound obtained from the Rayleigh quotient bound by polarization. -/
