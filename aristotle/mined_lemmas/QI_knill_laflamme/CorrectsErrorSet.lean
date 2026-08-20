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

def CorrectsErrorSet (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∃ (m : ℕ) (R : Fin m → Matrix n n ℂ), (∑ k, (R k)ᴴ * R k = 1) ∧
    ∀ a : ι, ∃ c : ℂ, ∀ ρ : Matrix n n ℂ, P * ρ * P = ρ →
      ∑ k, R k * (E a * ρ * (E a)ᴴ) * (R k)ᴴ = c • ρ

/-- The operator form of correctability: there is a trace preserving family of Kraus operators
`R k` such that each `R k ∘ E a` acts on the code as a scalar. -/
