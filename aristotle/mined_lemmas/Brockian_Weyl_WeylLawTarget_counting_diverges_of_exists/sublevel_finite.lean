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

/-
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a sequence `lam : ℕ → ℝ` of eigenvalues:
`spectralCounting lam t` is the number of indices `n` with `lam n ≤ t`.
(If that index set were infinite the `Set.ncard` would be `0`; under the escape
hypothesis used below the set is always finite.) -/

theorem sublevel_finite {lam : ℕ → ℝ}
    (hesc : ∀ t : ℝ, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → t < lam n) (t : ℝ) :
    {n : ℕ | lam n ≤ t}.Finite := by
  obtain ⟨M, hM⟩ := hesc t
  apply Set.Finite.subset (Set.finite_Iio M)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iio]
  by_contra h
  exact absurd hn (not_le.2 (hM n (not_lt.1 h)))

/-- **Weyl-law target (unconditional form).**
If the eigenvalue sequence escapes to infinity — i.e. for every level `t` there *exists*
an index `M` past which all eigenvalues exceed `t` — then the eigenvalue counting function
diverges: `spectralCounting lam t → ∞` as `t → ∞`.

This is the previously assumed hypothesis, now discharged: no extra assumption is needed
beyond the escape condition, in particular no monotonicity or injectivity of `lam`. -/
