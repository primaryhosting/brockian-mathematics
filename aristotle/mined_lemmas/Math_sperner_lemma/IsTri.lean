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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of cells of `K` that contain the face `τ`. -/

def IsTri (s : V → Finset ℕ) : ℕ → Finset (Finset V) → Prop
  | 0, K => ∃ v : V, K = {({v} : Finset V)} ∧ s v ⊆ range 1
  | (n + 1), K =>
      (∀ σ ∈ K, σ.card = n + 2) ∧
      (∀ σ ∈ K, ∀ v ∈ σ, s v ⊆ range (n + 2)) ∧
      (∀ τ ∈ faces K (n + 1), deg K τ = 1 ∨ deg K τ = 2) ∧
      (∀ τ ∈ faces K (n + 1), deg K τ = 1 → ∃ i ∈ range (n + 2), ∀ v ∈ τ, i ∉ s v) ∧
      IsTri s n (bdry s K n)

/-- The cells of `K` that are *rainbow*: their vertices carry all of the `n + 1` colours. -/
