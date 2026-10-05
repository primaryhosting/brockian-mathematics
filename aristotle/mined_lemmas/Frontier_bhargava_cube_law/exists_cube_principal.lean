/-
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
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

/-- An integral binary quadratic form `A x ^ 2 + B x y + C y ^ 2`, recorded by its
coefficient triple `(A, B, C)`. -/
structure BQF where
  A : ℤ
  B : ℤ
  C : ℤ
deriving DecidableEq

namespace BQF

/-- The discriminant `B ^ 2 - 4 A C` of a binary quadratic form. -/

lemma exists_cube_principal (q : BQF) :
    ∃ K : Cube, K.Q₁ = principalForm q.disc ∧ K.Q₂ = q ∧ K.Q₃ = q.opposite := by
  rcases Int.even_or_odd q.B with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `q.B = k + k` is even; take `f = k`, `g = -k`.
    refine ⟨⟨0, 1, 1, 0, q.A, k, -k, -q.C⟩, ?_, ?_, ?_⟩
    · have hD : q.disc = 4 * (k ^ 2 - q.A * q.C) := by
        simp only [BQF.disc, hk]; ring
      obtain ⟨m, hm⟩ : ∃ m : ℤ, q.disc = 4 * m := ⟨_, hD⟩
      have hmk : m = k ^ 2 - q.A * q.C := by linarith
      have hpar : q.disc % 2 = 0 := by omega
      have hdiv : q.disc / 4 = m := by omega
      rw [principalForm, if_pos hpar, hdiv, hmk, Cube.Q₁]
      simp only [BQF.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    · simp only [Cube.Q₂]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩
    · simp only [Cube.Q₃, BQF.opposite]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩
  · -- `q.B = 2 * k + 1` is odd; take `f = k + 1`, `g = -k`.
    refine ⟨⟨0, 1, 1, 0, q.A, k + 1, -k, -q.C⟩, ?_, ?_, ?_⟩
    · have hD : q.disc = 4 * (k ^ 2 + k - q.A * q.C) + 1 := by
        simp only [BQF.disc, hk]; ring
      obtain ⟨m, hm⟩ : ∃ m : ℤ, q.disc = 4 * m + 1 := ⟨_, hD⟩
      have hmk : m = k ^ 2 + k - q.A * q.C := by linarith
      have hpar : ¬ (q.disc % 2 = 0) := by omega
      have hdiv : (1 - q.disc) / 4 = -m := by omega
      rw [principalForm, if_neg hpar, hdiv, hmk, Cube.Q₁]
      simp only [BQF.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    · simp only [Cube.Q₂]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩
    · simp only [Cube.Q₃, BQF.opposite]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩

/-! ### Gauss/Dirichlet composition arises from a cube -/

/-- The cube realizing Dirichlet's composition of the two concordant forms
`(a₁, b, a₂ c)` and `(a₂, b, a₁ c)`, whose composite is `(a₁ a₂, b, c)`. -/
