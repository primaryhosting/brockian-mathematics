import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires all `import` commands to precede any other command,
including module doc comments, so `import Mathlib` appears on the first line and the
required header block follows immediately after it.

Statement formalized: local operations on one half of an entangled pair cannot transmit
information.  Concretely, for a bipartite system with Hilbert space `ℂ^A ⊗ ℂ^B`, any
quantum operation performed by Alice (a completely positive trace preserving map given in
Kraus form by operators `K i ⊗ 1`, with `∑ i, (K i)ᴴ * (K i) = 1`) leaves Bob's reduced
density matrix - the partial trace over Alice's factor - completely unchanged.  Hence no
measurement statistics available to Bob depend on Alice's choice of operation.
-/

namespace Frontier

open Matrix

variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq A] [DecidableEq B]

/-- Partial trace over the first (Alice) factor of a bipartite operator on `ℂ^A ⊗ ℂ^B`;
the result is an operator on Bob's factor `ℂ^B`. -/
noncomputable def ptraceFst (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- The operator `K ⊗ 1`: `K` acts on Alice's factor, the identity acts on Bob's factor. -/
noncomputable def localOp (K : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => K p.1 q.1 * (if p.2 = q.2 then 1 else 0)

/-- **No-communication theorem** (finite-dimensional, Kraus form).

If Alice applies to her half of a bipartite state `ρ` an arbitrary quantum operation, given
by Kraus operators `K i` acting on her factor only (i.e. `K i ⊗ 1`) and satisfying the
trace-preservation condition `∑ i, (K i)ᴴ * K i = 1`, then Bob's reduced density matrix
(the partial trace over Alice's factor) is unchanged.  Since every statistic Bob can obtain
is a function of his reduced density matrix, Alice's local operations transmit no
information to Bob. -/
theorem no_communication (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceFst (∑ i, localOp (B := B) (K i) * ρ * (localOp (K i))ᴴ) = ptraceFst ρ := by
  -- Reordering of a fourfold finite sum, obtained from `Finset.sum_comm` on product types.
  have swap : ∀ G : A → ι → A → A → ℂ,
      ∑ a, ∑ i, ∑ a2, ∑ a1, G a i a2 a1 = ∑ a2, ∑ a1, ∑ a, ∑ i, G a i a2 a1 := by
    intro G
    have h := Finset.sum_comm (s := (Finset.univ : Finset (A × ι)))
      (t := (Finset.univ : Finset (A × A))) (f := fun x y => G x.1 x.2 y.1 y.2)
    simpa [Fintype.sum_prod_type] using h
  -- The completeness relation `∑ i, (K i)ᴴ * K i = 1`, read off entrywise.
  have key : ∀ a1 a2 : A, (∑ a : A, ∑ i, K i a a1 * star (K i a a2))
      = if a2 = a1 then 1 else 0 := by
    intro a1 a2
    have h := congrFun (congrFun hK a2) a1
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] at h
    rw [Finset.sum_comm, ← h]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  ext b b'
  simp only [ptraceFst, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, localOp, Fintype.sum_prod_type, ite_mul, zero_mul,
    mul_ite, mul_one, mul_zero, apply_ite (star : ℂ → ℂ),
    star_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_mul]
  rw [swap (fun a i a2 a1 => K i a a1 * ρ (a1, b) (a2, b') * star (K i a a2))]
  have step : ∀ a2 a1 : A, (∑ a, ∑ i, K i a a1 * ρ (a1, b) (a2, b') * star (K i a a2))
      = (if a2 = a1 then (1:ℂ) else 0) * ρ (a1, b) (a2, b') := by
    intro a2 a1
    rw [← key a1 a2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [step, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Corollary: two different local operations by Alice (with Kraus families `K` and `L`)
produce exactly the same reduced state for Bob, so Bob cannot tell which one Alice chose. -/
theorem no_communication_indistinguishable (K : ι → Matrix A A ℂ) (L : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hL : ∑ i, (L i)ᴴ * L i = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptraceFst (∑ i, localOp (B := B) (K i) * ρ * (localOp (K i))ᴴ)
      = ptraceFst (∑ i, localOp (B := B) (L i) * ρ * (localOp (L i))ᴴ) := by
  rw [no_communication K hK ρ, no_communication L hL ρ]

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

