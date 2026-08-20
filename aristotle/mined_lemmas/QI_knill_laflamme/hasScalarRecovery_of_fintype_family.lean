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

lemma hasScalarRecovery_of_fintype_family {κ : Type*} [Fintype κ] (P : Matrix n n ℂ)
    (E : ι → Matrix n n ℂ) (S : κ → Matrix n n ℂ) (h1 : ∑ o, (S o)ᴴ * S o = 1)
    (h2 : ∀ (a : ι) (o : κ), ∃ l : ℂ, S o * E a * P = l • P) : HasScalarRecovery P E := by
  refine ⟨Fintype.card κ, fun i => S ((Fintype.equivFin κ).symm i), ?_, fun a i => h2 a _⟩
  rw [← h1]
  exact Equiv.sum_comp (Fintype.equivFin κ).symm (fun o => (S o)ᴴ * S o)

/-- The main construction: from a family of errors which is orthogonal on the code (with
"weights" `d k ≥ 0`) and which spans the errors on the code, one builds a recovery. -/
