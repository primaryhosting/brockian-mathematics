/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- A quantum code, given by the orthogonal projection `P` onto the code subspace. -/
structure IsCodeProj (P : Matrix n n ℂ) : Prop where
  /-- The projection is self-adjoint. -/
  herm : Pᴴ = P
  /-- The projection is idempotent. -/
  idem : P * P = P

/-- The Knill–Laflamme conditions for the code with projection `P` and the error set `E`:
there is a matrix of scalars `c` with `P * (E a)ᴴ * (E b) * P = c a b • P` for all errors
`E a`, `E b`. -/

def KnillLaflammeCond (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∃ c : Matrix ι ι ℂ, ∀ a b : ι, P * (E a)ᴴ * E b * P = c a b • P

/-- The code with projection `P` corrects the error set `E`: there is a recovery quantum
operation, given by a trace preserving family of Kraus operators `R k`
(`∑ k, (R k)ᴴ * R k = 1`), which restores every state supported on the code after any one of
the errors `E a` acted on it, up to a factor `c` (independent of the state) accounting for the
fact that a single error `E a` need not be trace preserving.  Operators `ρ` with `P * ρ * P = ρ`
are exactly the linear combinations of density matrices supported on the code, so quantifying
over all of them is the linear extension of the condition on code states.  -/
