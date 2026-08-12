import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Kronecker
open scoped Matrix

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
# The no-communication theorem (finite-dimensional base case)

A bipartite quantum system with Alice's finite-dimensional factor indexed by `A` and Bob's
by `B` is modelled by density matrices `Matrix (A × B) (A × B) ℂ`; an arbitrary (possibly
entangled) joint state is such a matrix `rho`.

Alice performs an arbitrary local operation: a quantum channel acting on her factor only,
given in Kraus form by operators `K i : Matrix A A ℂ` with `∑ i, (K i)ᴴ * K i = 1`
(this includes unitaries, and also measurements whose outcome is discarded).  The
corresponding operation on the joint system is
`rho ↦ ∑ i, (K i ⊗ₖ 1) * rho * (K i ⊗ₖ 1)ᴴ`, i.e. it acts as the identity on Bob's factor.

The main theorem `Frontier.no_communication` states that Bob's reduced density matrix — the
partial trace over Alice's factor — is completely unaffected by such an operation.
Consequently (`Frontier.no_communication_prob`, `Frontier.no_communication_indistinguishable`)
the probability of every outcome of every measurement Bob can perform is unchanged, so no
information whatsoever is transmitted by Alice's choice of local operation.
-/

namespace Frontier

variable {A B ι κ : Type*} [Fintype A] [Fintype B] [Fintype ι] [Fintype κ]
  [DecidableEq A] [DecidableEq B]

/-- Bob's reduced density matrix: the partial trace of a bipartite operator over Alice's
factor `A`. -/
noncomputable def ptraceLeft (rho : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, rho (a, b) (a, b')

/-- The action on the joint system of a local operation of Alice given in Kraus form by the
operators `K i` acting on her factor alone. -/
noncomputable def aliceChannel (K : ι → Matrix A A ℂ) (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ i, (K i ⊗ₖ (1 : Matrix B B ℂ)) * rho * (K i ⊗ₖ (1 : Matrix B B ℂ))ᴴ

/-- Reordering a quadruple sum. -/
private theorem sum_comm₄ {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (g : α → β → γ → δ → ℂ) :
    ∑ a, ∑ i, ∑ e, ∑ c, g a i e c = ∑ e, ∑ c, ∑ a, ∑ i, g a i e c := by
  have h1 : ∀ a : α, ∑ i, ∑ e, ∑ c, g a i e c = ∑ e, ∑ c, ∑ i, g a i e c := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_comm

/-- Reordering a triple sum. -/
private theorem sum_comm₃ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (g : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ b, ∑ c, ∑ a, g a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- **No-communication theorem** (finite-dimensional base case).

If Alice applies an arbitrary local quantum channel — Kraus operators `K i` on her factor,
satisfying the trace-preservation condition `∑ i, (K i)ᴴ * K i = 1`, tensored with the
identity on Bob's factor — to a joint (possibly entangled) state `rho`, then Bob's reduced
density matrix is unchanged. Hence Alice's local operations transmit no information to Bob. -/
theorem no_communication (rho : Matrix (A × B) (A × B) ℂ) (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    ptraceLeft (aliceChannel K rho) = ptraceLeft rho := by
  have key : ∀ c e : A, ∑ a : A, ∑ i : ι, K i a c * star (K i a e) =
      if e = c then (1 : ℂ) else 0 := by
    intro c e
    have h := congrFun (congrFun hK e) c
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] at h
    rw [← h, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => mul_comm _ _
  ext b b'
  simp only [ptraceLeft, aliceChannel, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, mul_one, apply_ite (star : ℂ → ℂ), star_zero]
  simp only [Finset.sum_mul]
  rw [sum_comm₄ (fun a i e c => K i a c * rho (c, b) (e, b') * star (K i a e))]
  have hinner : ∀ e c : A, (∑ a : A, ∑ i : ι, K i a c * rho (c, b) (e, b') * star (K i a e))
      = (if e = c then (1 : ℂ) else 0) * rho (c, b) (e, b') := by
    intro e c
    rw [← key c e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hinner, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Special case: Alice applies a unitary `U` (`Uᴴ * U = 1`) to her factor.  Bob's reduced
density matrix is unchanged. -/
theorem no_communication_unitary (rho : Matrix (A × B) (A × B) ℂ) (U : Matrix A A ℂ)
    (hU : Uᴴ * U = 1) :
    ptraceLeft ((U ⊗ₖ (1 : Matrix B B ℂ)) * rho * (U ⊗ₖ (1 : Matrix B B ℂ))ᴴ)
      = ptraceLeft rho := by
  have h := no_communication (ι := Unit) rho (fun _ => U) (by simpa using hU)
  simpa [aliceChannel] using h

omit [DecidableEq B] in
/-- Any expectation value of an observable/POVM element `M` acting on Bob's factor alone is
computed from Bob's reduced density matrix. -/
theorem trace_mul_one_kronecker (rho : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) :
    ((rho * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace) = ((ptraceLeft rho * M).trace) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ptraceLeft, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_mul, mul_ite, mul_zero, one_mul]
  have h2 : ∀ a : A, ∀ b : B,
      (∑ a' : A, ∑ b' : B, if a' = a then rho (a, b) (a', b') * M b' b else 0)
        = ∑ b' : B, rho (a, b) (a, b') * M b' b := by
    intro a b
    rw [Finset.sum_comm]
    simp
  simp only [h2]
  exact sum_comm₃ (fun (a : A) (b b' : B) => rho (a, b) (a, b') * M b' b)

/-- Bob's measurement statistics are unaffected by Alice's local operation: for every operator
`M` on Bob's factor (e.g. a POVM element, so that the trace below is the probability of the
corresponding outcome), the expectation value after Alice's channel equals the one before. -/
theorem no_communication_prob (rho : Matrix (A × B) (A × B) ℂ) (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (M : Matrix B B ℂ) :
    (aliceChannel K rho * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace
      = (rho * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace := by
  rw [trace_mul_one_kronecker, trace_mul_one_kronecker, no_communication rho K hK]

/-- Bob cannot tell which local operation Alice performed: any two local channels of Alice
produce exactly the same statistics for every measurement Bob can make. -/
theorem no_communication_indistinguishable (rho : Matrix (A × B) (A × B) ℂ)
    (K : ι → Matrix A A ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (L : κ → Matrix A A ℂ) (hL : ∑ j, (L j)ᴴ * L j = 1) (M : Matrix B B ℂ) :
    (aliceChannel K rho * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace
      = (aliceChannel L rho * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace := by
  rw [no_communication_prob rho K hK M, no_communication_prob rho L hL M]

/-! ### A concrete instance: the two-qubit Bell state -/

/-- The density matrix of the Bell state `(|00⟩ + |11⟩)/√2` on two qubits, in the basis
`Fin 2 × Fin 2`. -/
noncomputable def bellRho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun x y =>
    (if x.1 = x.2 then (1 : ℂ) else 0) * (if y.1 = y.2 then (1 : ℂ) else 0) / 2

/-- Bob's half of the Bell state is the maximally mixed qubit state. -/
theorem ptraceLeft_bellRho : ptraceLeft bellRho = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext b b'
  fin_cases b <;> fin_cases b' <;>
    simp [ptraceLeft, bellRho, Fin.sum_univ_succ]

/-- Whatever local operation Alice performs on her half of a Bell pair, Bob still holds the
maximally mixed state: he learns nothing. -/
theorem bell_no_communication (K : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    ptraceLeft (aliceChannel K bellRho) = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [no_communication bellRho K hK, ptraceLeft_bellRho]

end Frontier

#print axioms Frontier.no_communication
#print axioms Frontier.no_communication_unitary
#print axioms Frontier.no_communication_prob
#print axioms Frontier.no_communication_indistinguishable
#print axioms Frontier.bell_no_communication

