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

theorem multiIndexNorm_pos {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < multiIndexNorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext fun i => by simpa using h i)
  have hpos : 0 < |(k i : ℝ)| := by
    simpa using (Int.cast_ne_zero (α := ℝ)).2 hi
  refine Finset.sum_pos' (fun j _ => abs_nonneg _) ⟨i, Finset.mem_univ i, hpos⟩

/-- **Small divisor estimate.**  For a `(γ, τ)`-Diophantine frequency vector `ω` and a
nonzero multi-index `k`, the `k`-th Fourier coefficient equation `⟨k, ω⟩ * x = c` coming from
the homological equation is uniquely solvable, and the solution loses only the polynomial
factor `‖k‖^τ / γ` in size. -/
