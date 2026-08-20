/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to come before any module docstring, so the header
-- above is reproduced verbatim as the module docstring immediately after the imports.)

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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
set_option pp.piBinderTypes true
set_option pp.letVarTypes true
set_option pp.funBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ComplexOrder InnerProductSpace

/-! ## States on a unital ⋆-algebra over `ℂ` -/

/-- A *state* on a unital `ℂ`-⋆-algebra `A`: a positive, normalized linear functional. -/
structure IsState {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) : Prop where
  /-- Positivity: `phi (a⋆ * a)` is a nonnegative real number. -/
  nonneg : ∀ a : A, 0 ≤ phi (star a * a)
  /-- Normalization. -/
  map_one : phi 1 = 1

namespace IsState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {phi : A →ₗ[ℂ] ℂ}


theorem kadison_singer_existsUnique {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ι) :
    ∃! phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ,
      IsState phi ∧ ∀ a, IsDiagonal b a → phi a = ⟪b k, a (b k)⟫_ℂ := by
  have hnorm : ‖b k‖ = 1 := b.orthonormal.1 k
  refine ⟨vectorState (b k), ⟨isState_vectorState hnorm, fun a _ => rfl⟩, ?_⟩
  rintro phi ⟨hphi, hphid⟩
  exact (kadison_singer b k phi (vectorState (b k)) hphi (isState_vectorState hnorm) hphid
    (fun a _ => rfl)).2

end KadisonSinger

/-! ## Weaver's `KS₂` in dimension one

The Kadison–Singer problem was solved by Marcus, Spielman and Srivastava by proving Weaver's
discrepancy-theoretic conjecture `KS₂`: if `v 1, …, v m` are vectors in `ℂ^d` with
`∑ i, v i * (v i)⋆ = 1` and `‖v i‖ ^ 2 ≤ eps`, then the index set can be partitioned into two
parts `S`, `Sᶜ` with `‖∑ i ∈ S, v i * (v i)⋆‖ ≤ (1 / √2 + √eps) ^ 2`.

The following is the one-dimensional (`d = 1`) case of that statement, where the operator norm
is just the sum of the weights `‖v i‖ ^ 2`. It is proved by a greedy/maximality argument. -/

section Weaver

/-- A finite family of real weights summing to `1`, each at most `eps`, can be split into two
parts each of total weight at most `1 / 2 + eps`. -/
