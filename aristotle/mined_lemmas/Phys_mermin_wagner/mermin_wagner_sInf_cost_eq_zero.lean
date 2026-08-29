/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
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

/-!
## Mermin–Wagner: absence of continuous symmetry breaking in dimensions `d ≤ 2`

The mechanism behind the Mermin–Wagner theorem is an *energy–entropy* (spin-wave) estimate.
In a lattice system with a continuous internal symmetry, a configuration may be deformed by a
slowly varying, *finitely supported* rotation field `u : ℤ^d → ℝ`; to second order (which is
the relevant order, the first order term vanishing by the symmetry `θ ↦ -θ`) the free-energy
cost of the deformation at temperature `T` and coupling `J` is

  `(J / (2T)) * ∑_{⟨x,y⟩} (u x - u y)^2`,

i.e. `J / (2T)` times the *Dirichlet energy* of `u`.  Spontaneous breaking of the continuous
symmetry requires this cost to stay bounded away from zero when a fixed finite region is
rotated by a fixed angle `α` and the rotation is relaxed back to `0` at infinity; this
infimum is (up to the factor `J / (2T)`) the *capacity* of the region.

The theorem `Phys.mermin_wagner` below is exactly the statement that in dimension `d ≤ 2`
this cost vanishes: for every temperature `T > 0`, every coupling `J > 0`, every finite
region `A`, every rotation angle `α` and every `ε > 0`, there is a finitely supported
rotation field which rotates all of `A` by the full angle `α` at a free-energy cost less
than `ε`.  Equivalently: finite subsets of `ℤ^d` have zero capacity for `d ≤ 2` (`ℤ^d` is
recurrent/parabolic), so no continuous symmetry can be broken at any positive temperature.

The dimension enters through the divergence of the harmonic series: the shells
`{x : ‖x‖_∞ = s}` of `ℤ^d` with `d ≤ 2` contain `O(s)` points, so the harmonic profile
`u x = φ(‖x‖_∞)` used below has Dirichlet energy `O(1 / ∑_{s ≤ N} 1/s) → 0`.  In dimension
`d ≥ 3` shells contain `≍ s^{d-1}` points, the estimate fails, and indeed symmetry breaking
does occur.
-/

namespace Phys

variable {d : ℕ}

/-- The `i`-th unit vector of the lattice `ℤ^d`. -/

theorem mermin_wagner_sInf_cost_eq_zero {d : ℕ} (hd : d ≤ 2) {T J : ℝ} (hT : 0 < T) (hJ : 0 < J)
    (α : ℝ) (A : Finset (Fin d → ℤ)) :
    sInf {r : ℝ | ∃ u : (Fin d → ℤ) → ℝ,
      (Function.support u).Finite ∧ (∀ x ∈ A, u x = α) ∧ r = J / (2 * T) * dirichlet u} = 0 := by
  set S : Set ℝ := {r : ℝ | ∃ u : (Fin d → ℤ) → ℝ,
    (Function.support u).Finite ∧ (∀ x ∈ A, u x = α) ∧ r = J / (2 * T) * dirichlet u} with hS
  have hc : 0 < J / (2 * T) := by positivity
  have hnonneg : ∀ r ∈ S, 0 ≤ r := by
    rintro r ⟨u, -, -, rfl⟩
    exact mul_nonneg hc.le (dirichlet_nonneg u)
  have hne : S.Nonempty := by
    obtain ⟨u, hfin, hval, -⟩ := mermin_wagner hd hT hJ α A (ε := 1) one_pos
    exact ⟨J / (2 * T) * dirichlet u, ⟨u, hfin, hval, rfl⟩⟩
  have hbdd : BddBelow S := ⟨0, hnonneg⟩
  refine le_antisymm ?_ (le_csInf hne hnonneg)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨u, hfin, hval, hlt⟩ := mermin_wagner hd hT hJ α A hε
  have hmem : J / (2 * T) * dirichlet u ∈ S := ⟨u, hfin, hval, rfl⟩
  have := csInf_le hbdd hmem
  linarith

end Phys

