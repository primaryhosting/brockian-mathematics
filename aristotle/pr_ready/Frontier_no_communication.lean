/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Statement: Local operations on one half of an entangled pair cannot transmit information.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-!
# No-communication theorem (finite-dimensional Kraus form)

We model a bipartite quantum system with Alice's Hilbert space indexed by a finite
type `A` and Bob's by a finite type `B`, so that joint states are matrices indexed
by `A × B`.  A local operation performed by Alice is a quantum channel given by
Kraus operators `K i` acting on Alice's factor only, i.e. `K i ⊗ 1` on the joint
space, with `∑ i, (K i)ᴴ * (K i) = 1` (trace preservation).

The main result `Frontier.no_communication` says that Bob's reduced state
(the partial trace over Alice's subsystem) is completely unaffected by such an
operation, for *every* joint state `ρ` — in particular for entangled ones.
Consequently (`Frontier.no_communication_expectation`) the expectation value of
every observable measured by Bob alone is unchanged, so no information can be
transmitted.
-/

namespace Frontier

open scoped Matrix Kronecker

variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq A] [DecidableEq B]

/-- The partial trace over Alice's subsystem: Bob's reduced density matrix. -/
noncomputable def ptraceA (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- A local operation performed by Alice, in Kraus form: the Kraus operators act as
`K i ⊗ 1` on the joint system. -/
noncomputable def localChannelA (K : ι → Matrix A A ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ i : ι, ((K i ⊗ₖ (1 : Matrix B B ℂ))) * ρ *
    ((K i ⊗ₖ (1 : Matrix B B ℂ)))ᴴ

private lemma sum_swap4 {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (f : X → Y → Z → W → ℂ) :
    ∑ x : X, ∑ y : Y, ∑ z : Z, ∑ w : W, f x y z w =
      ∑ z : Z, ∑ w : W, ∑ y : Y, ∑ x : X, f x y z w := by
  have h : ∑ p : X × Y × Z × W, f p.1 p.2.1 p.2.2.1 p.2.2.2
      = ∑ q : Z × W × Y × X, f q.2.2.2 q.2.2.1 q.1 q.2.1 :=
    Fintype.sum_equiv
      (Equiv.mk (fun p : X × Y × Z × W => (p.2.2.1, p.2.2.2, p.2.1, p.1))
        (fun q : Z × W × Y × X => (q.2.2.2, q.2.2.1, q.1, q.2.1)) (fun _ => rfl) (fun _ => rfl))
      _ _ (fun _ => rfl)
  simpa [Fintype.sum_prod_type] using h

/-- **No-communication theorem.**  Any trace-preserving local operation performed by
Alice leaves Bob's reduced state (the partial trace over Alice) unchanged, whatever
the joint state `ρ` is — in particular for entangled states. -/
theorem no_communication (K : ι → Matrix A A ℂ) (hK : ∑ i : ι, (K i)ᴴ * K i = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceA (localChannelA K ρ) = ptraceA ρ := by
  ext b b'
  simp only [ptraceA, localChannelA, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, apply_ite (Star.star (R := ℂ)),
    star_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  have key : ∀ a1 a2 : A,
      ∑ i : ι, ∑ x : A, Star.star (K i x a2) * K i x a1 = if a2 = a1 then 1 else 0 := by
    intro a1 a2
    have h := congrFun (congrFun hK a2) a1
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      using h
  rw [sum_swap4 (fun (x : A) (i : ι) (a2 : A) (a1 : A) =>
    K i x a1 * ρ (a1, b) (a2, b') * Star.star (K i x a2))]
  have step : ∀ a2 a1 : A,
      ∑ i : ι, ∑ x : A, K i x a1 * ρ (a1, b) (a2, b') * Star.star (K i x a2)
        = (if a2 = a1 then 1 else 0) * ρ (a1, b) (a2, b') := by
    intro a2 a1
    rw [← key a1 a2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [step, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [DecidableEq B] in
/-- Bob's expectation values are computed from his reduced state. -/
theorem trace_mul_kronecker_one (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) :
    (ρ * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace = (ptraceA ρ * M).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, ptraceA, Fintype.sum_prod_type,
    Matrix.one_apply, Matrix.kroneckerMap_apply, mul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b2 _ => (Finset.mul_sum _ _ _).symm

/-- **No signalling.**  The expectation value of any observable `M` measured by Bob
alone is unaffected by Alice's local operation. -/
theorem no_communication_expectation (K : ι → Matrix A A ℂ) (hK : ∑ i : ι, (K i)ᴴ * K i = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) :
    (localChannelA K ρ * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace =
      (ρ * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace := by
  rw [trace_mul_kronecker_one, trace_mul_kronecker_one, no_communication K hK]

/-- The maximally entangled two-qubit (Bell) state `|Φ⁺⟩⟨Φ⁺|`, where
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 / 2 : ℂ) else 0

/-- Bob's half of the Bell state is the maximally mixed qubit state. -/
lemma ptraceA_bellState :
    ptraceA bellState = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext b b'
  fin_cases b <;> fin_cases b' <;>
    simp [ptraceA, bellState, Fin.sum_univ_two]

/-- **Base case:** whatever unitary Alice applies to her half of a Bell pair, Bob's
qubit stays maximally mixed, so he learns nothing about her choice. -/
theorem bell_no_communication (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    ptraceA (localChannelA (fun _ : Fin 1 => U) bellState)
      = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [no_communication _ (by simpa using hU), ptraceA_bellState]

end Frontier

#print axioms Frontier.no_communication
#print axioms Frontier.no_communication_expectation
#print axioms Frontier.bell_no_communication

