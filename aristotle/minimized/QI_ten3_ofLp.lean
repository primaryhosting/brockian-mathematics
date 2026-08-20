import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Statement: There is no unitary that deletes an unknown quantum state (no-deleting theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-- A qubit: the two dimensional complex Hilbert space. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The ancilla register: an `m`-dimensional complex Hilbert space. -/
abbrev Anc (m : ℕ) : Type := EuclideanSpace ℂ (Fin m)

/-- The full register: two qubits together with an `m`-dimensional ancilla,
realized concretely as the Hilbert space with index set `Fin 2 × Fin 2 × Fin m`. -/
abbrev Reg (m : ℕ) : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin m)

/-- The (unnormalized) product state `a ⊗ b ⊗ c` inside `Reg m`. -/

def ten3 {m : ℕ} (a b : Qubit) (c : Anc m) : Reg m :=
  WithLp.toLp 2 (fun p => a.ofLp p.1 * b.ofLp p.2.1 * c.ofLp p.2.2)

@[simp]

lemma ten3_ofLp {m : ℕ} (a b : Qubit) (c : Anc m) (p : Fin 2 × Fin 2 × Fin m) :
    (ten3 a b c).ofLp p = a.ofLp p.1 * b.ofLp p.2.1 * c.ofLp p.2.2 := rfl

/-- Inner products of product states factor as the product of the inner products. -/
