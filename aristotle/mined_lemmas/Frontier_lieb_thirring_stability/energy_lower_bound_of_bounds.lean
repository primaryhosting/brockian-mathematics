/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-- The Lieb–Thirring constant appearing in the kinetic energy inequality that is dual to
the Lieb–Thirring eigenvalue bound with constant `L` (in dimension `3`, exponent `γ = 1`). -/

theorem energy_lower_bound_of_bounds
    {K C X N T A E : ℝ} (hK : 0 < K) (hX : 0 ≤ X) (hN : 0 ≤ N)
    (hT : T ≥ K * X) (hA : A ≤ C * Real.sqrt X * Real.sqrt N) (hE : E = T - A) :
    E ≥ - (C ^ 2 * N) / (4 * K) := by
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℝ, 0 ≤ u ∧ X = u ^ 2 :=
    ⟨Real.sqrt X, Real.sqrt_nonneg X, (Real.sq_sqrt hX).symm⟩
  obtain ⟨v, hv0, hv⟩ : ∃ v : ℝ, 0 ≤ v ∧ N = v ^ 2 :=
    ⟨Real.sqrt N, Real.sqrt_nonneg N, (Real.sq_sqrt hN).symm⟩
  have hsu : Real.sqrt X = u := by rw [hu, Real.sqrt_sq hu0]
  have hsv : Real.sqrt N = v := by rw [hv, Real.sqrt_sq hv0]
  rw [hsu, hsv] at hA
  have key : K * X - C * u * v ≥ - (C ^ 2 * N) / (4 * K) := by
    rw [ge_iff_le, div_le_iff₀ (by positivity), hu, hv]
    nlinarith [sq_nonneg (2 * K * u - C * v)]
  linarith

/-- **Lieb–Thirring inequality and stability of matter.**

A Lean-checked reduction of stability of matter to the Lieb–Thirring inequality.

Assume:
* `ρ ≥ 0` is the one-particle density of a fermionic state, with `∫ ρ = N` particles and
  finite Thomas–Fermi energy `∫ ρ^(5/3)`;
* `hLT`: the Lieb–Thirring eigenvalue bound in its variational (dual) form, i.e. for every
  nonnegative potential `V`, the kinetic energy satisfies
  `T - ∫ V ρ ≥ -L ∫ V^(5/2)` — this is precisely the statement that the sum of the negative
  eigenvalues of `-Δ - V` is at least `-L ∫ V₊^(5/2)`, applied to the given state;
* `hCoul`: the (scaling correct) bound on the attractive Coulomb energy
  `A ≤ C * (∫ ρ^(5/3))^(1/2) * N^(1/2)`.

Then the total energy `E = T - A` satisfies the stability bound `E ≥ -c N` with the
explicit constant `c = C² / (4 K_L)`, `K_L = (3/5) (2/(5L))^(2/3)`: the energy is bounded
below by a constant times the number of particles. -/
