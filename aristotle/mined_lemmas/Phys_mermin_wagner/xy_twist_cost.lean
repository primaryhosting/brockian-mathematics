/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated below as a module docstring; Lean requires `import` commands to
-- precede any module docstring.)

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized

We formalize the Mermin–Wagner theorem for the classical XY model, the standard model with a
continuous internal symmetry group (rotations of the spin circle `Spin = ℝ / 2πℤ`).

*The model.*  Sites are the lattice points of the box `Λ_L = {x ∈ ℤ^d : ‖x‖_∞ ≤ L}`; a
configuration assigns a spin angle to each site; the a priori measure is the uniform (Haar)
measure on `Λ_L → Spin`.  The energy is
`H(θ) = - ∑_{x,y} J x y * cos (θ x - θ y) + W θ`,
where `J` is an arbitrary nearest-neighbour coupling of strength at most `1` and `W` is an
arbitrary continuous boundary term depending only on the spins of the outermost shell of the box
(this encodes an arbitrary boundary condition, possibly strongly favouring one direction).
The thermal average of an observable is `gibbsAvg β H f`.

*The theorem* (`Phys.mermin_wagner`).  For `d ≤ 2`, any `β = 1/T < ∞` and any `ε > 0`, there is
`L₀` such that for all `L ≥ L₀` the magnetization at the centre of the box in any direction `c`
satisfies `|⟨cos (θ x₀ - c)⟩| ≤ ε`, uniformly in the coupling and in the boundary condition:
there is no spontaneous breaking of the rotation symmetry.  `Phys.mermin_wagner_magnetization`
restates this for the magnetization vector.

*The proof* is the spin-wave (twisting) argument.  Twisting a configuration by a slowly varying
radial profile `a` which equals `π` at the centre and `0` on the boundary shell costs, in the
symmetrized sense, at most the Dirichlet energy `K` of the profile, and one deduces from
`H(θ+a) + H(θ-a) ≤ 2 H(θ) + K` together with the arithmetic–geometric mean inequality that
`|magnetization| ≤ β K / 2`.  In dimension `d ≤ 2` the profile built from partial sums of the
harmonic series has Dirichlet energy `O(1 / harm L) → 0`, because the number of sites at distance
`r` grows at most like `r`, whereas the harmonic series diverges.
-/

open scoped BigOperators
open scoped Real
open MeasureTheory

set_option maxHeartbeats 1000000

namespace Phys

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The single–spin space: the circle `ℝ / 2πℤ`.  The continuous internal symmetry group of the
model is this circle acting on itself by rotations. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-! ## Part 1: an abstract twisting (spin–wave) inequality -/

section Abstract

variable {V : Type*} [Fintype V]

/-- Every continuous function on the (compact) configuration space is integrable. -/

lemma xy_twist_cost {d L : ℕ} (J : Site d L → Site d L → ℝ)
    (W : (Site d L → Spin) → ℝ)
    (hJ1 : ∀ x y, |J x y| ≤ 1)
    (hJ0 : ∀ x y : Site d L, ¬ Adj (x : Fin d → ℤ) (y : Fin d → ℤ) → J x y = 0)
    (hW : ∀ θ θ' : Site d L → Spin,
      (∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → θ x = θ' x) → W θ = W θ')
    (hL : 1 ≤ L) (θ : Site d L → Spin) :
    xyHamiltonian J W (θ + twist d L) + xyHamiltonian J W (θ - twist d L)
      ≤ 2 * xyHamiltonian J W θ
        + ∑ x : Site d L, ∑ y : Site d L,
            (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
              then (profile L (latticeNorm (x : Fin d → ℤ))
                      - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) := by
  have hu : ∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → twist d L x = 0 := by
    intro x hx
    rw [twist, hx, profile_zero_of_norm_eq hL]
    simp
  have hW1 : W (θ + twist d L) = W θ := hW _ _ (fun x hx => by simp [hu x hx])
  have hW2 : W (θ - twist d L) = W θ := hW _ _ (fun x hx => by simp [hu x hx])
  have hdiffp : ∀ x y : Site d L, ((θ + twist d L) x - (θ + twist d L) y : Spin)
      = (θ x - θ y : Spin) + (((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin) := by
    intro x y
    show θ x + twist d L x - (θ y + twist d L y) = _
    rw [twist, twist, show ((((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin))
        = ((profile L (latticeNorm (x : Fin d → ℤ)) : ℝ) : Spin)
          - ((profile L (latticeNorm (y : Fin d → ℤ)) : ℝ) : Spin) from
      (Real.Angle.coe_sub _ _)]
    abel
  have hdiffm : ∀ x y : Site d L, ((θ - twist d L) x - (θ - twist d L) y : Spin)
      = (θ x - θ y : Spin) - (((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin) := by
    intro x y
    show θ x - twist d L x - (θ y - twist d L y) = _
    rw [twist, twist, show ((((profile L (latticeNorm (x : Fin d → ℤ))
          - profile L (latticeNorm (y : Fin d → ℤ))) : ℝ) : Spin))
        = ((profile L (latticeNorm (x : Fin d → ℤ)) : ℝ) : Spin)
          - ((profile L (latticeNorm (y : Fin d → ℤ)) : ℝ) : Spin) from
      (Real.Angle.coe_sub _ _)]
    abel
  have hterm : ∀ x y : Site d L,
      -(J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * (J x y * Real.Angle.cos ((θ x - θ y : Spin)))
      ≤ (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) := by
    intro x y
    by_cases hadj : Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
    · rw [if_pos hadj, hdiffp, hdiffm]
      exact pair_bound (J x y) (hJ1 x y) _ _
    · rw [if_neg hadj, hJ0 x y hadj]
      simp
  have hsum : (∑ x : Site d L, ∑ y : Site d L,
      (-(J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * (J x y * Real.Angle.cos ((θ x - θ y : Spin)))))
      ≤ ∑ x : Site d L, ∑ y : Site d L,
          (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
            then (profile L (latticeNorm (x : Fin d → ℤ))
                    - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  have hexp : (∑ x : Site d L, ∑ y : Site d L,
      (-(J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * (J x y * Real.Angle.cos ((θ x - θ y : Spin)))))
      = -(∑ x : Site d L, ∑ y : Site d L,
            J x y * Real.Angle.cos ((θ + twist d L) x - (θ + twist d L) y))
        - (∑ x : Site d L, ∑ y : Site d L,
            J x y * Real.Angle.cos ((θ - twist d L) x - (θ - twist d L) y))
        + 2 * ∑ x : Site d L, ∑ y : Site d L, J x y * Real.Angle.cos ((θ x - θ y : Spin)) := by
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hexp] at hsum
  unfold xyHamiltonian
  rw [hW1, hW2]
  linarith

