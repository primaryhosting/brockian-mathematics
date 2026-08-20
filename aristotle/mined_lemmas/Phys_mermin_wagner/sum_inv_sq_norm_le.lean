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

lemma sum_inv_sq_norm_le {d : ℕ} (hd : d ≤ 2) (L : ℕ) :
    ∑ x : Site d L, (1 / max 1 ((latticeNorm (x : Fin d → ℤ)) : ℝ)) ^ 2 ≤ 1 + 8 * harm L := by
  classical
  have h1 : ∑ x : Site d L, (1 / max 1 ((latticeNorm (x : Fin d → ℤ)) : ℝ)) ^ 2
      = ∑ x ∈ box d L, (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_coe_sort (box d L) (fun x => (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2)
  rw [h1]
  have hmaps : ∀ x ∈ box d L, latticeNorm x ∈ Finset.range (L + 1) := by
    intro x hx
    rw [Finset.mem_range]
    rw [mem_box_iff] at hx
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2)]
  have hterm : ∀ r ∈ Finset.range (L + 1),
      (∑ x ∈ box d L with latticeNorm x = r, (1 / max 1 ((latticeNorm x : ℕ) : ℝ)) ^ 2)
        = ({x ∈ box d L | latticeNorm x = r}).card * (1 / max 1 (r : ℝ)) ^ 2 := by
    intro r _
    rw [Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter] at hx
      rw [hx.2])]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ']
  have hzero : (({x ∈ box d L | latticeNorm x = 0}).card : ℝ)
      * (1 / max 1 ((0 : ℕ) : ℝ)) ^ 2 ≤ 1 := by
    have hsub : {x ∈ box d L | latticeNorm x = 0} ⊆ {(0 : Fin d → ℤ)} := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp only [Finset.mem_singleton]
      funext i
      have hle : (x i).natAbs ≤ latticeNorm x :=
        Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)
      rw [hx.2] at hle
      simp only [Pi.zero_apply]
      omega
    have hcard : ({x ∈ box d L | latticeNorm x = 0}).card ≤ 1 :=
      le_trans (Finset.card_le_card hsub) (by simp)
    have hcast : (({x ∈ box d L | latticeNorm x = 0}).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    norm_num
    linarith
  have hrest : ∀ m ∈ Finset.range L,
      (({x ∈ box d L | latticeNorm x = m + 1}).card : ℝ) * (1 / max 1 ((m + 1 : ℕ) : ℝ)) ^ 2
        ≤ 8 * (1 / ((m : ℝ) + 1)) := by
    intro m _
    have hc : (({x ∈ box d L | latticeNorm x = m + 1}).card : ℝ) ≤ 8 * ((m : ℝ) + 1) := by
      have h8 := card_sphere_le hd L m
      have hcast : (({x ∈ box d L | latticeNorm x = m + 1}).card : ℝ) ≤ ((8 * (m + 1) : ℕ) : ℝ) := by
        exact_mod_cast h8
      push_cast at hcast
      linarith
    have hmax : max 1 (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by
      push_cast
      refine max_eq_right ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hgoal : ((m : ℝ) + 1) ^ 2 * (8 * (1 / ((m : ℝ) + 1))) = 8 * ((m : ℝ) + 1) := by
      field_simp
    rw [hmax, div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity)]
    linarith [hc, hgoal]
  have hfinal := add_le_add (Finset.sum_le_sum hrest) hzero
  refine le_trans hfinal ?_
  rw [← Finset.mul_sum]
  have hh : harm L = ∑ m ∈ Finset.range L, (1 : ℝ) / ((m : ℝ) + 1) := rfl
  rw [hh]
  linarith

/-- The Dirichlet energy of the spin-wave profile is small in dimension `d ≤ 2`. -/
