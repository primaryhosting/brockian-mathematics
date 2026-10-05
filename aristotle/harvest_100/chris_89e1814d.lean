/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Local operations performed by Alice on her half of a bipartite (possibly entangled)
system cannot change Bob's reduced state, hence cannot transmit any information.

The bipartite system is modelled by matrices indexed by `A × B` over `ℂ`
(`A` = Alice's factor, `B` = Bob's factor).  Alice's local operation is an
arbitrary quantum channel given in Kraus form by operators `K i` acting on her
factor only, i.e. `K i ⊗ I`, subject to trace preservation `∑ i, (K i)ᴴ * K i = 1`.
Bob's reduced state is the partial trace over Alice's factor.
-/

namespace Frontier

open scoped Matrix
open Finset

variable {A B ι : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype ι]

/-- Partial trace over the first (Alice) factor of a bipartite operator:
Bob's reduced state. -/
noncomputable def ptraceA (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- A local operator on Alice's side, i.e. `K ⊗ I` acting on `A × B`. -/
noncomputable def locA (K : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => K p.1 q.1 * (if p.2 = q.2 then 1 else 0)

omit [DecidableEq A] [DecidableEq B] in
/-- Reordering a quadruple sum of complex numbers. -/
private theorem sum_comm4 {f : A → ι → A → A → ℂ} :
    (∑ a, ∑ i, ∑ e, ∑ c, f a i e c) = ∑ c, ∑ e, ∑ i, ∑ a, f a i e c := by
  rw [show (∑ a, ∑ i, ∑ e, ∑ c, f a i e c) = ∑ x : A × ι × A × A, f x.1 x.2.1 x.2.2.1 x.2.2.2 by
        simp [Fintype.sum_prod_type],
      show (∑ c, ∑ e, ∑ i, ∑ a, f a i e c) = ∑ y : A × A × ι × A, f y.2.2.2 y.2.2.1 y.2.1 y.1 by
        simp [Fintype.sum_prod_type]]
  exact Fintype.sum_equiv
    { toFun := fun x : A × ι × A × A => (x.2.2.2, x.2.2.1, x.2.1, x.1),
      invFun := fun y : A × A × ι × A => (y.2.2.2, y.2.2.1, y.2.1, y.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun _ => rfl)

/-- **No-communication theorem** (finite-dimensional, Kraus form).

Alice applies an arbitrary quantum operation to her half of a bipartite state `ρ`,
described by Kraus operators `K i` acting on her factor only (tensored with the
identity on Bob's factor) and satisfying the trace-preservation condition
`∑ i, (K i)ᴴ * K i = 1`.  Then Bob's reduced state, the partial trace over
Alice's factor, is completely unchanged: no information can be transmitted. -/
theorem no_communication (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = 1) (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceA (∑ i, locA (K i) * ρ * (locA (K i))ᴴ) = ptraceA ρ := by
  classical
  have key : ∀ c e : A, ∑ i, ∑ a, star (K i a e) * K i a c = (1 : Matrix A A ℂ) e c := by
    intro c e
    have := congrFun (congrFun hK e) c
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] using this
  ext b b'
  simp only [ptraceA, Matrix.sum_apply, locA, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, apply_ite (star : ℂ → ℂ), star_zero]
  have step : ∀ c e : A, (∑ i, ∑ a, K i a c * ρ (c, b) (e, b') * star (K i a e))
      = (1 : Matrix A A ℂ) e c * ρ (c, b) (e, b') := by
    intro c e
    rw [← key c e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  calc (∑ a, ∑ i, ∑ e, (∑ c, K i a c * ρ (c, b) (e, b')) * star (K i a e))
      = ∑ a, ∑ i, ∑ e, ∑ c, K i a c * ρ (c, b) (e, b') * star (K i a e) := by
        simp [Finset.sum_mul]
    _ = ∑ c, ∑ e, ∑ i, ∑ a, K i a c * ρ (c, b) (e, b') * star (K i a e) := sum_comm4
    _ = ∑ c, ∑ e, (1 : Matrix A A ℂ) e c * ρ (c, b) (e, b') :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => step c e
    _ = ∑ a, ρ (a, b) (a, b') := by simp [Matrix.one_apply]

/-- Special case: a local **unitary** applied by Alice leaves Bob's reduced state
unchanged. -/
theorem no_communication_unitary (U : Matrix A A ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceA (locA U * ρ * (locA U)ᴴ) = ptraceA ρ := by
  have := no_communication (B := B) (fun _ : Unit => U) (by simpa using hU) ρ
  simpa using this

/-- Operational form of the no-communication theorem: the expectation value
`tr(ρ_B M)` of *any* observable `M` measured by Bob is unaffected by Alice's
local operation, so Bob's measurement statistics carry no information about it. -/
theorem no_communication_expectation (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = 1) (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) :
    (ptraceA (∑ i, locA (K i) * ρ * (locA (K i))ᴴ) * M).trace = (ptraceA ρ * M).trace := by
  rw [no_communication K hK ρ]

/-- The maximally entangled two-qubit (Bell) state `|Φ⁺⟩⟨Φ⁺|`, where
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 / 2 else 0

/-- Bob's half of the Bell state is the maximally mixed qubit state `I/2`. -/
theorem ptraceA_bellState :
    ptraceA bellState = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext b b'
  fin_cases b <;> fin_cases b' <;> simp [ptraceA, bellState, Fin.sum_univ_two]

/-- Concrete instance of the no-communication theorem for an entangled pair:
whatever local operation Alice performs on her qubit of a Bell pair, Bob's qubit
stays maximally mixed. -/
theorem bellState_no_communication (K : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = 1) :
    ptraceA (∑ i, locA (K i) * bellState * (locA (K i))ᴴ)
      = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [no_communication K hK bellState, ptraceA_bellState]

end Frontier

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

