/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
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

set_option grind.warning false

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

def IsTriangulation : ℕ → Finset ℕ → Finset (Finset V) → (V → Finset ℕ) → Prop
  | 0, A, K, carr =>
      A.card = 1 ∧ K.Nonempty ∧ (∀ s ∈ K, s.card = 1) ∧ (∀ s ∈ K, ∀ v ∈ s, carr v ⊆ A) ∧
      (∀ f ∈ facets K 0,
        (K.filter (fun s => f ⊆ s)).card = if f.biUnion carr = A then 2 else 1)
  | (n + 1), A, K, carr =>
      A.card = n + 2 ∧ K.Nonempty ∧ (∀ s ∈ K, s.card = n + 2) ∧ (∀ s ∈ K, ∀ v ∈ s, carr v ⊆ A) ∧
      (∀ f ∈ facets K (n + 1),
        (K.filter (fun s => f ⊆ s)).card = if f.biUnion carr = A then 2 else 1) ∧
      (∀ a ∈ A, IsTriangulation n (A.erase a) (subComplex K carr (A.erase a) (n + 1)) carr)

/-- Codimension-one faces of a nonempty finite set are exactly its one-point deletions. -/
