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

theorem mermin_wagner {d : ℕ} (hd : d ≤ 2) (β : ℝ) (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ (J : Site d L → Site d L → ℝ) (W : (Site d L → Spin) → ℝ) (c : Spin) (x₀ : Site d L),
        (∀ x y, |J x y| ≤ 1) →
        (∀ x y : Site d L, ¬ Adj (x : Fin d → ℤ) (y : Fin d → ℤ) → J x y = 0) →
        Continuous W →
        (∀ θ θ' : Site d L → Spin,
          (∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → θ x = θ' x) → W θ = W θ') →
        (x₀ : Fin d → ℤ) = 0 →
        |gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.cos ((θ x₀ - c : Spin))| ≤ ε := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1
    (harm_tendsto.eventually_ge_atTop (max 1 (81 * Real.pi ^ 2 * β / (2 * ε))))
  refine ⟨L₀, ?_⟩
  intro L hL J W c x₀ hJ1 hJ0 hWc hW hx₀
  have hA := hL₀ L hL
  have hA1 : (1 : ℝ) ≤ harm L := le_trans (le_max_left _ _) hA
  have hA2 : 81 * Real.pi ^ 2 * β / (2 * ε) ≤ harm L := le_trans (le_max_right _ _) hA
  have hA0 : 0 < harm L := lt_of_lt_of_le zero_lt_one hA1
  have hL1 : 1 ≤ L := by
    by_contra h
    have : L = 0 := by omega
    rw [this] at hA1
    simp [harm] at hA1
    linarith [hA1]
  set K : ℝ := ∑ x : Site d L, ∑ y : Site d L,
      (if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
        then (profile L (latticeNorm (x : Fin d → ℤ))
                - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0) with hKdef
  have hK0 : 0 ≤ K := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
    split <;> positivity
  have hKb : K ≤ 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 :=
    dirichlet_energy_bound hd hL1
  have hcost := xy_twist_cost J W hJ1 hJ0 hW hL1
  have hx₀t : twist d L x₀ = ((Real.pi : ℝ) : Spin) := by
    have : latticeNorm (x₀ : Fin d → ℤ) = 0 := by
      rw [hx₀]; simp [latticeNorm]
    rw [twist, this, profile_origin]
  have hmain := abs_gibbs_cos_le β hβ (xyHamiltonian J W)
    (xyHamiltonian_continuous J W hWc) (twist d L) K hK0 hcost x₀ hx₀t c
  refine hmain.trans ?_
  -- quantitative estimate: β K / 2 ≤ ε
  have hstep : 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 ≤ 81 * Real.pi ^ 2 / harm L := by
    rw [div_le_div_iff₀ (by positivity) hA0]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 9 * Real.pi ^ 2) hA0.le)
      (by linarith : (0:ℝ) ≤ harm L - 1)]
  have hKfin : K ≤ 81 * Real.pi ^ 2 / harm L := hKb.trans hstep
  have : β * K / 2 ≤ β * (81 * Real.pi ^ 2 / harm L) / 2 := by
    have := mul_le_mul_of_nonneg_left hKfin hβ
    linarith
  refine this.trans ?_
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at *
  have h2 : 81 * Real.pi ^ 2 * β ≤ harm L * (2 * ε) := by
    rw [div_le_iff₀ (by positivity)] at hA2
    linarith
  rw [mul_div_assoc'] at *
  rw [div_le_iff₀ hA0]
  nlinarith

/-- **Mermin–Wagner theorem, vector form.**  In dimension `d ≤ 2` and at any positive temperature,
the mean magnetization vector `(⟨cos θ₀⟩, ⟨sin θ₀⟩)` at the centre of the box has length at most
`ε` once the box is large enough, uniformly over couplings and boundary conditions. -/
