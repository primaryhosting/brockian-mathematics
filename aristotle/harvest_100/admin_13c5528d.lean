/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above uses `/- ... -/` rather than `/-! ... -/` because Lean 4 does not allow a
-- module docstring to precede the `import` block.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

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
## Setting

A bipartite quantum system with finite-dimensional factors `A` (Alice) and `B` (Bob) is modelled
by matrices indexed by `A × B` over `ℂ`; a state is such a matrix `ρ` (no positivity or unit-trace
hypothesis is needed for the result below, so none is imposed).

* `Frontier.ptA ρ` is the partial trace over Alice's factor, i.e. Bob's reduced density matrix.
* `Frontier.extA K` is a local operator `K ⊗ I_B` acting on Alice's side only.
* `Frontier.extB M` is a local operator `I_A ⊗ M` acting on Bob's side only.
* `Frontier.krausA K ρ = ∑ i, (K i ⊗ I) ρ (K i ⊗ I)†` is the most general local quantum
  operation Alice can perform, written in Kraus form; the channel is trace preserving exactly
  when `∑ i, (K i)ᴴ * K i = 1`.

The theorem `Frontier.no_communication` says that any such local operation of Alice leaves Bob's
reduced density matrix *exactly* unchanged, and `Frontier.bob_statistics_unchanged` concludes that
therefore every expectation value `Tr(ρ (I ⊗ M))` of a Bob-local observable is unchanged, so no
information reaches Bob.

Remark on existing Mathlib support: a search of Mathlib turns up no partial-trace or
quantum-channel API (there is no `Matrix.partialTrace` / Kraus-operator development), so the
statement is built from the basic matrix API (`Matrix.mul_apply`, `Matrix.conjTranspose_apply`,
`Matrix.trace`, `Finset.sum_comm`, `Fintype.sum_prod_type`) rather than closed by a single
existing lemma.
-/

namespace Frontier

variable {A B ι : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype ι]

/-- The partial trace over Alice's factor: Bob's reduced density matrix. -/
noncomputable def ptA (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- A local operator on Alice's factor, extended to the joint system as `K ⊗ I_B`. -/
def extA (K : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => K p.1 q.1 * (if p.2 = q.2 then 1 else 0)

/-- A local operator on Bob's factor, extended to the joint system as `I_A ⊗ M`. -/
def extB (M : Matrix B B ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => (if p.1 = q.1 then 1 else 0) * M p.2 q.2

/-- Alice's local quantum operation with Kraus operators `K i`, acting on the joint state. -/
noncomputable def krausA (K : ι → Matrix A A ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  ∑ i, extA (K i) * ρ * (extA (K i))ᴴ

private lemma sum_reorder3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  have h1 : (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ q : β × γ, f a q.1 q.2 := by
    simp [Fintype.sum_prod_type]
  have h2 : (∑ b, ∑ c, ∑ a, f a b c) = ∑ q : β × γ, ∑ a, f a q.1 q.2 := by
    simp [Fintype.sum_prod_type]
  rw [h1, h2, Finset.sum_comm]

private lemma sum_reorder4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
      = ∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2 := by
    simp [Fintype.sum_prod_type]
  have h2 : (∑ c, ∑ d, ∑ a, ∑ b, f a b c d)
      = ∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2 := by
    simp [Fintype.sum_prod_type]
  rw [h1, h2, Finset.sum_comm]

/-- **No-communication theorem.**  If Alice applies an arbitrary trace-preserving local quantum
operation (Kraus operators `K i` on her factor, satisfying the completeness relation
`∑ i, (K i)ᴴ * K i = 1`, tensored with the identity on Bob's factor) to a joint state `ρ` of the
bipartite system `A ⊗ B` — for instance to one half of an entangled pair — then Bob's reduced
density matrix, the partial trace over Alice's factor, is completely unchanged. -/
theorem no_communication (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = (1 : Matrix A A ℂ))
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ptA (krausA K ρ) = ptA ρ := by
  -- The completeness relation, read off entrywise.
  have key : ∀ a1 a2 : A, (∑ a : A, ∑ i : ι, star (K i a a2) * K i a a1)
      = if a2 = a1 then (1 : ℂ) else 0 := by
    intro a1 a2
    have h := congrFun (congrFun hK a2) a1
    rw [Matrix.sum_apply] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    rw [Finset.sum_comm] at h
    exact h
  ext b b'
  simp only [ptA, krausA, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, extA, Fintype.sum_prod_type, mul_ite, ite_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one, apply_ite (star : ℂ → ℂ), star_zero]
  simp only [Finset.sum_mul]
  rw [sum_reorder4 (fun x i a2 a1 => K i x a1 * ρ (a1, b) (a2, b') * star (K i x a2))]
  have step : ∀ a2 a1 : A,
      (∑ x : A, ∑ i : ι, K i x a1 * ρ (a1, b) (a2, b') * star (K i x a2))
      = ρ (a1, b) (a2, b') * (if a2 = a1 then (1 : ℂ) else 0) := by
    intro a2 a1
    rw [← key a1 a2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [step, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [DecidableEq B] in
/-- Expectation values of Bob-local observables are computed from Bob's reduced density matrix:
`Tr(ρ (I_A ⊗ M)) = Tr((ptA ρ) M)`. -/
theorem trace_extB (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) :
    (ρ * extB M).trace = ((ptA ρ) * M).trace := by
  have inner : ∀ (a : A) (b : B),
      (∑ a' : A, ∑ b' : B, ρ (a, b) (a', b') * ((if a' = a then (1 : ℂ) else 0) * M b' b))
      = ∑ b' : B, ρ (a, b) (a, b') * M b' b := by
    intro a b
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b' _ => by simp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, extB, ptA, Matrix.of_apply,
    Fintype.sum_prod_type, inner]
  rw [sum_reorder3 (fun (a : A) (b b' : B) => ρ (a, b) (a, b') * M b' b)]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => (Finset.sum_mul _ _ _).symm

/-- **No signalling.**  Bob's measurement statistics are unaffected by Alice's local operation:
for every Bob-local observable `M`, the expectation value `Tr(ρ (I_A ⊗ M))` is the same before and
after Alice acts.  Hence no information can be transmitted by local operations on one half of an
entangled pair. -/
theorem bob_statistics_unchanged (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = (1 : Matrix A A ℂ))
    (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) :
    (krausA K ρ * extB M).trace = (ρ * extB M).trace := by
  rw [trace_extB, trace_extB, no_communication K hK ρ]

end Frontier

