/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Setting

We work with the standard "conjugacy" formulation of KAM theory.  The phase space is an
arbitrary type `P`, the `n`-dimensional torus is modelled by its universal cover
`Fin n → ℝ` (all objects below are invariant under the choice of representative, so
nothing is lost), and a *torus with rotation vector `ω`* for a dynamical system
`f : P → P` is an embedding `Ψ : (Fin n → ℝ) → P` satisfying the conjugacy equation

  `f (Ψ θ) = Ψ (θ + ω)`  for all `θ`,

i.e. `f` restricted to the image of `Ψ` is the rigid rotation by `ω`.
-/

/-- `IsInvariantTorus n f ω Ψ` : the parametrised torus `Ψ` is invariant under the
dynamics `f` and the induced motion on it is the rigid rotation by the frequency
vector `ω`. -/

theorem small_divisor_bound {n : ℕ} {ω : Fin n → ℝ} {γ τ : ℝ} (hω : Diophantine ω γ τ)
    {k : Fin n → ℤ} (hk : k ≠ 0) (c : ℝ) :
    ∃ x : ℝ, (∑ i, (k i : ℝ) * ω i) * x = c ∧ |x| ≤ |c| * (multiIndexNorm k) ^ τ / γ := by
  obtain ⟨hγ, hdio⟩ := hω
  set d : ℝ := ∑ i, (k i : ℝ) * ω i with hd
  have hnpos : 0 < multiIndexNorm k := multiIndexNorm_pos hk
  have hpow : 0 < (multiIndexNorm k) ^ τ := Real.rpow_pos_of_pos hnpos τ
  have hlow : 0 < γ / (multiIndexNorm k) ^ τ := div_pos hγ hpow
  have habs : γ / (multiIndexNorm k) ^ τ ≤ |d| := hdio k hk
  have hdpos : 0 < |d| := lt_of_lt_of_le hlow habs
  have hdne : d ≠ 0 := by
    intro h
    rw [h] at hdpos
    simp at hdpos
  refine ⟨c / d, by field_simp, ?_⟩
  have h1 : |c / d| = |c| / |d| := abs_div c d
  have h2 : |c| / |d| ≤ |c| / (γ / (multiIndexNorm k) ^ τ) :=
    div_le_div_of_nonneg_left (abs_nonneg c) hlow habs
  have h3 : |c| / (γ / (multiIndexNorm k) ^ τ) = |c| * (multiIndexNorm k) ^ τ / γ := by
    field_simp
  rw [h1, ← h3]
  exact h2

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

