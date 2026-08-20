/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean 4 requires `import` commands to
-- precede every other command, including module doc-strings.)

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

/-- Spin configurations of a chain of `N` sites (each site carries a qubit). -/
abbrev Config (N : ℕ) := Fin N → Fin 2

/-- Observables of the spin chain: linear operators on the `2^N`-dimensional Hilbert space,
represented as matrices indexed by spin configurations. -/
abbrev SpinOp (N : ℕ) := Matrix (Config N) (Config N) ℂ

/-- `Supported S M` says that the observable `M` acts only on the sites in `S`, i.e.
`M = M₀ ⊗ 1` with `M₀` acting on the sites of `S`.  Concretely, matrix elements vanish
unless the configurations agree off `S`, and they depend only on the restrictions to `S`. -/

theorem supported_sum {ι : Type*} {S : Set (Fin N)} (s : Finset ι) (f : ι → SpinOp N)
    (hf : ∀ i ∈ s, Supported S (f i)) : Supported S (∑ i ∈ s, f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simpa using supported_zero S
  | insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    exact supported_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

