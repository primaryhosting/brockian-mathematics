/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
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

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

def Determines {n m : ℕ} (y : Fin m → BV n) (s : BV n) : Prop :=
  ∀ t : BV n, (∀ i, dot (y i) t = 0) → t = 0 ∨ t = s

/-- All possible outcomes of `m` runs of Simon's circuit (each run returns a vector of
`Orth s`). -/
