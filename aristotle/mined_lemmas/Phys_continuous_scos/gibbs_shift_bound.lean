import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

theorem gibbs_shift_bound (β : ℝ) (hβ : 0 ≤ β) (H : (ι → Spin) → ℝ) (hH : Continuous H)
    (F : (ι → Spin) → ℝ) (hF : Continuous F) (C : ℝ) (hC : ∀ θ, |F θ| ≤ C)
    (g : ι → Spin) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ θ, H (θ + g) + H (θ - g) - 2 * H θ ≤ K) :
    |gAvg β H (fun θ => F (θ + g)) - gAvg β H F| ≤ C * Real.sqrt (2 * β * K) := by
  classical
  -- notation
  have hZpos : 0 < gPart β H := gPart_pos β hH
  set Z : ℝ := gPart β H with hZdef
  set u : (ι → Spin) → ℝ := fun θ => Real.exp (-β * H (θ - g) / 2) with hudef
  set v : (ι → Spin) → ℝ := fun θ => Real.exp (-β * H θ / 2) with hvdef
  set p : (ι → Spin) → ℝ := fun θ => Real.exp (-β * (H (θ + g) + H θ) / 2) with hpdef
  -- continuity
  have hHm : Continuous fun θ : ι → Spin => H (θ - g) :=
    hH.comp (continuous_id.sub continuous_const)
  have hHp : Continuous fun θ : ι → Spin => H (θ + g) :=
    hH.comp (continuous_id.add continuous_const)
  have hcu : Continuous u := Real.continuous_exp.comp (by fun_prop)
  have hcv : Continuous v := Real.continuous_exp.comp (by fun_prop)
  have hcp : Continuous p := Real.continuous_exp.comp (by fun_prop)
  -- squares
  have hv2 : ∀ θ, v θ ^ 2 = gWeight β H θ := by
    intro θ; simp only [hvdef, gWeight, sq, ← Real.exp_add]; ring_nf
  have hu2 : ∀ θ, u θ ^ 2 = gWeight β H (θ - g) := by
    intro θ; simp only [hudef, gWeight, sq, ← Real.exp_add]; ring_nf
  have hupos : ∀ θ, 0 < u θ := fun θ => Real.exp_pos _
  have hvpos : ∀ θ, 0 < v θ := fun θ => Real.exp_pos _
  -- basic integrals
  have hIv2 : ∫ θ, v θ ^ 2 = Z := by
    rw [hZdef, gPart]; exact integral_congr_ae (Filter.Eventually.of_forall hv2)
  have hIu2 : ∫ θ, u θ ^ 2 = Z := by
    have h1 : ∫ θ, u θ ^ 2 = ∫ θ, gWeight β H (θ - g) :=
      integral_congr_ae (Filter.Eventually.of_forall hu2)
    have h2 : ∫ θ, gWeight β H (θ + (-g)) = ∫ θ, gWeight β H θ :=
      integral_add_right_eq_self (gWeight β H) (-g)
    rw [h1, hZdef, gPart, ← h2]
    congr 1 with θ
    rw [← sub_eq_add_neg]
  -- the symmetrized overlap
  set S : ℝ := ∫ θ, u θ * v θ with hSdef
  have hSp : S = ∫ θ, p θ := by
    have h2 : ∫ θ, (u (θ + g) * v (θ + g)) = ∫ θ, u θ * v θ :=
      integral_add_right_eq_self (fun θ => u θ * v θ) g
    have h3 : ∀ θ : ι → Spin, u (θ + g) * v (θ + g) = p θ := by
      intro θ
      simp only [hudef, hvdef, hpdef, add_sub_cancel_right, ← Real.exp_add]
      ring_nf
    rw [hSdef, ← h2, integral_congr_ae (Filter.Eventually.of_forall h3)]
  -- integrability
  have iu2 : Integrable (fun θ => u θ ^ 2) (volume : Measure (ι → Spin)) :=
    torus_integrable (by fun_prop)
  have iv2 : Integrable (fun θ => v θ ^ 2) (volume : Measure (ι → Spin)) :=
    torus_integrable (by fun_prop)
  have iuv : Integrable (fun θ => u θ * v θ) (volume : Measure (ι → Spin)) :=
    torus_integrable (by fun_prop)
  have ip : Integrable p (volume : Measure (ι → Spin)) := torus_integrable hcp
  -- lower bound on the overlap
  have hSlow : (2 - β * K / 2) * Z ≤ 2 * S := by
    have key : ∀ θ : ι → Spin, v θ ^ 2 * (2 - β * K / 2) ≤ u θ * v θ + p θ := by
      intro θ
      have e1 : u θ * v θ = v θ ^ 2 * Real.exp (-β * (H (θ - g) - H θ) / 2) := by
        simp only [hudef, hvdef, sq, ← Real.exp_add]; ring_nf
      have e2 : p θ = v θ ^ 2 * Real.exp (-β * (H (θ + g) - H θ) / 2) := by
        simp only [hpdef, hvdef, sq, ← Real.exp_add]; ring_nf
      have b1 : 1 + (-β * (H (θ - g) - H θ) / 2) ≤ Real.exp (-β * (H (θ - g) - H θ) / 2) := by
        have := Real.add_one_le_exp (-β * (H (θ - g) - H θ) / 2); linarith
      have b2 : 1 + (-β * (H (θ + g) - H θ) / 2) ≤ Real.exp (-β * (H (θ + g) - H θ) / 2) := by
        have := Real.add_one_le_exp (-β * (H (θ + g) - H θ) / 2); linarith
      have hvsq : 0 < v θ ^ 2 := pow_pos (hvpos θ) 2
      have hKθ := hK θ
      have hstep : (2 - β * K / 2) ≤
          (1 + (-β * (H (θ - g) - H θ) / 2)) + (1 + (-β * (H (θ + g) - H θ) / 2)) := by
        nlinarith [hβ, hKθ]
      calc v θ ^ 2 * (2 - β * K / 2)
          ≤ v θ ^ 2 * ((1 + (-β * (H (θ - g) - H θ) / 2)) +
              (1 + (-β * (H (θ + g) - H θ) / 2))) := by
            exact mul_le_mul_of_nonneg_left hstep (le_of_lt hvsq)
        _ ≤ v θ ^ 2 * (Real.exp (-β * (H (θ - g) - H θ) / 2) +
              Real.exp (-β * (H (θ + g) - H θ) / 2)) := by
            have := add_le_add b1 b2
            exact mul_le_mul_of_nonneg_left this (le_of_lt hvsq)
        _ = u θ * v θ + p θ := by rw [e1, e2]; ring
    have iL : Integrable (fun θ => v θ ^ 2 * (2 - β * K / 2))
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have iR : Integrable (fun θ => u θ * v θ + p θ)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have hmono := integral_mono iL iR key
    have hL : ∫ θ, v θ ^ 2 * (2 - β * K / 2) = (2 - β * K / 2) * Z := by
      rw [integral_mul_const, hIv2]; ring
    have hR : ∫ θ, (u θ * v θ + p θ) = 2 * S := by
      have := integral_lin2 iuv ip 1 1
      simp only [one_mul] at this
      rw [this, ← hSp, ← hSdef]; ring
    rw [hL, hR] at hmono
    exact hmono
  -- the overlap is at most Z
  have hSle : S ≤ Z := by
    have key : ∀ θ : ι → Spin, u θ * v θ ≤ (u θ ^ 2 + v θ ^ 2) / 2 := by
      intro θ; nlinarith [sq_nonneg (u θ - v θ)]
    have iR : Integrable (fun θ => (u θ ^ 2 + v θ ^ 2) / 2)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have hmono := integral_mono iuv iR key
    have hR : ∫ θ, (u θ ^ 2 + v θ ^ 2) / 2 = Z := by
      have h := integral_lin2 iu2 iv2 (1/2) (1/2)
      have h2 : ∀ θ : ι → Spin, (u θ ^ 2 + v θ ^ 2) / 2
          = (1/2 : ℝ) * u θ ^ 2 + (1/2 : ℝ) * v θ ^ 2 := by intro θ; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall h2), h, hIu2, hIv2]; ring
    rw [hR] at hmono
    exact hmono
  -- the L¹ distance of the two Boltzmann weights
  set D : ℝ := ∫ θ, |u θ ^ 2 - v θ ^ 2| with hDdef
  have hDnonneg : 0 ≤ D := integral_nonneg (fun θ => abs_nonneg _)
  have hDlam : ∀ lam : ℝ, 0 < lam →
      D ≤ (1 / (2 * lam)) * (2 * Z - 2 * S) + (lam / 2) * (2 * Z + 2 * S) := by
    intro lam hlam
    have key : ∀ θ : ι → Spin, |u θ ^ 2 - v θ ^ 2| ≤
        (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2 := by
      intro θ
      have hpos : 0 < u θ + v θ := add_pos (hupos θ) (hvpos θ)
      have habs : |u θ ^ 2 - v θ ^ 2| = |u θ - v θ| * (u θ + v θ) := by
        rw [← abs_of_pos hpos, ← abs_mul]
        congr 1
        ring
      rw [habs, ← sub_nonneg]
      have hA2 : |u θ - v θ| ^ 2 = (u θ - v θ) ^ 2 := sq_abs _
      have expand : (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2
          - |u θ - v θ| * (u θ + v θ)
          = (1 / (2 * lam)) * (|u θ - v θ| - lam * (u θ + v θ)) ^ 2 := by
        rw [← hA2]
        field_simp
        ring
      rw [expand]
      positivity
    have iabs : Integrable (fun θ => |u θ ^ 2 - v θ ^ 2|) (volume : Measure (ι → Spin)) :=
      torus_integrable (by fun_prop)
    have irhs : Integrable
        (fun θ => (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    have hmono := integral_mono iabs irhs key
    have hexp : ∀ θ : ι → Spin,
        (1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2
        = (1 / (2 * lam) + lam / 2) * u θ ^ 2 + (1 / (2 * lam) + lam / 2) * v θ ^ 2
          + (lam - 1 / lam) * (u θ * v θ) := by
      intro θ
      field_simp
      ring
    have hRint : ∫ θ, ((1 / (2 * lam)) * (u θ - v θ) ^ 2 + (lam / 2) * (u θ + v θ) ^ 2)
        = (1 / (2 * lam) + lam / 2) * Z + (1 / (2 * lam) + lam / 2) * Z
          + (lam - 1 / lam) * S := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
        integral_lin3 iu2 iv2 iuv _ _ _, hIu2, hIv2, ← hSdef]
    rw [hRint] at hmono
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have : (1 / (2 * lam) + lam / 2) * Z + (1 / (2 * lam) + lam / 2) * Z + (lam - 1 / lam) * S
        = (1 / (2 * lam)) * (2 * Z - 2 * S) + (lam / 2) * (2 * Z + 2 * S) := by
      field_simp
      ring
    rw [this] at hmono
    exact hmono
  -- the small-difference bound
  have hsmall : 2 * Z - 2 * S ≤ β * K / 2 * Z := by nlinarith [hSlow, hZpos]
  set c : ℝ := Real.sqrt (2 * β * K) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 2 * β * K := Real.sq_sqrt (by positivity)
  have hDc : D ≤ c * Z := by
    rcases eq_or_lt_of_le hc0 with hc | hc
    · -- c = 0, hence β K = 0 and the two weights agree
      have hbk : β * K = 0 := by nlinarith [hc2, hc.symm]
      have hzero : 2 * Z - 2 * S ≤ 0 := by rw [hbk] at hsmall; linarith
      have hD0 : D ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have hlam := hDlam (D / (4 * Z)) (by positivity)
        have hnn : (0:ℝ) ≤ 1 / (2 * (D / (4 * Z))) := by positivity
        have h1 : (1 / (2 * (D / (4 * Z)))) * (2 * Z - 2 * S) ≤ 0 := by nlinarith
        have hSZ : 2 * Z + 2 * S ≤ 4 * Z := by linarith
        have h3 : (D / (4 * Z)) / 2 * (2 * Z + 2 * S) ≤ (D / (4 * Z)) / 2 * (4 * Z) :=
          mul_le_mul_of_nonneg_left hSZ (by positivity)
        have h4 : (D / (4 * Z)) / 2 * (4 * Z) = D / 2 := by field_simp
        linarith
      have : c * Z = 0 := by rw [← hc]; ring
      linarith
    · have hcne : c ≠ 0 := ne_of_gt hc
      have hlam := hDlam (c / 4) (by positivity)
      have hSZ : 2 * Z + 2 * S ≤ 4 * Z := by linarith
      have e1 : (1 / (2 * (c / 4))) * (2 * Z - 2 * S) ≤ (2 / c) * (β * K / 2 * Z) := by
        have : (1 : ℝ) / (2 * (c / 4)) = 2 / c := by field_simp; norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      have e2 : (c / 4) / 2 * (2 * Z + 2 * S) ≤ (c / 4) / 2 * (4 * Z) :=
        mul_le_mul_of_nonneg_left hSZ (by positivity)
      have e3 : (2 / c) * (β * K / 2 * Z) = c * Z / 2 := by
        have hbk : β * K = c ^ 2 / 2 := by rw [hc2]; ring
        rw [hbk]
        field_simp
      have e4 : (c / 4) / 2 * (4 * Z) = c * Z / 2 := by ring
      linarith
  -- transfer to the observable
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC (fun _ => 0))
  have hshift : ∫ θ, F (θ + g) * gWeight β H θ = ∫ θ, F θ * gWeight β H (θ - g) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure (ι → Spin)))
      (fun θ => F θ * gWeight β H (θ - g)) g
    rw [← h]
    congr 1 with θ
    simp [add_sub_cancel_right]
  have hnum : |(∫ θ, F (θ + g) * gWeight β H θ) - ∫ θ, F θ * gWeight β H θ| ≤ C * D := by
    rw [hshift]
    have iL : Integrable (fun θ => F θ * gWeight β H (θ - g)) (volume : Measure (ι → Spin)) :=
      torus_integrable (hF.mul (Real.continuous_exp.comp (by fun_prop)))
    have iR : Integrable (fun θ => F θ * gWeight β H θ) (volume : Measure (ι → Spin)) :=
      torus_integrable (hF.mul (continuous_gWeight β hH))
    have hdiff : (∫ θ, F θ * gWeight β H (θ - g)) - ∫ θ, F θ * gWeight β H θ
        = ∫ θ, F θ * (gWeight β H (θ - g) - gWeight β H θ) := by
      rw [← integral_sub iL iR]
      congr 1 with θ
      ring
    rw [hdiff]
    have hbnd : ∀ θ : ι → Spin, |F θ * (gWeight β H (θ - g) - gWeight β H θ)|
        ≤ C * |u θ ^ 2 - v θ ^ 2| := by
      intro θ
      rw [abs_mul, hu2 θ, hv2 θ]
      exact mul_le_mul_of_nonneg_right (hC θ) (abs_nonneg _)
    have iabs2 : Integrable (fun θ => C * |u θ ^ 2 - v θ ^ 2|)
        (volume : Measure (ι → Spin)) := torus_integrable (by fun_prop)
    calc |∫ θ, F θ * (gWeight β H (θ - g) - gWeight β H θ)|
        ≤ ∫ θ, |F θ * (gWeight β H (θ - g) - gWeight β H θ)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ θ, C * |u θ ^ 2 - v θ ^ 2| := by
          refine integral_mono ?_ iabs2 hbnd
          exact torus_integrable (by fun_prop)
      _ = C * D := by rw [integral_const_mul, hDdef]
  -- conclude
  have hgoal : |gAvg β H (fun θ => F (θ + g)) - gAvg β H F| = |(∫ θ, F (θ + g) * gWeight β H θ) -
      ∫ θ, F θ * gWeight β H θ| / Z := by
    unfold gAvg
    rw [← hZdef, div_sub_div_same, abs_div, abs_of_pos hZpos]
  rw [hgoal]
  rw [div_le_iff₀ hZpos]
  calc |(∫ θ, F (θ + g) * gWeight β H θ) - ∫ θ, F θ * gWeight β H θ| ≤ C * D := hnum
    _ ≤ C * (c * Z) := by exact mul_le_mul_of_nonneg_left hDc hCnn
    _ = C * c * Z := by ring

end

end Phys

/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Spin
import RequestProject.Gibbs
import RequestProject.Lattice

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

/-!
## The Mermin–Wagner theorem

We consider the classical XY model on the lattice `ℤ^d`: spins take values in the circle
`Spin = ℝ / 2πℤ`, the spins inside the box `box d N` fluctuate, the spins outside are
frozen to an arbitrary boundary condition `τ`, and the (nearest neighbour, ferromagnetic)
Hamiltonian is

`xyHam N τ θ = ∑_{x, i} (1 - cos (θ x - θ (x + e i)))`,

the sum ranging over the bonds `{x, x + e i}` with `x` in the box of radius `N + 1`.  This
includes every bond meeting the box of radius `N` (the fluctuating spins), together with
finitely many bonds joining two frozen spins, which contribute an additive constant and
hence do not affect the Gibbs measure.  The Gibbs expectation at inverse
temperature `β > 0` (i.e. at temperature `T = 1/β > 0`) is `gAvg β (xyHam N τ)`, and the
two components of the magnetisation at the origin are `magCos` and `magSin`.

The theorem `Phys.mermin_wagner` states that in dimension `d ≤ 2` and at any positive
temperature the magnetisation at the origin is arbitrarily small in absolute value, for
all sufficiently large boxes and *uniformly in the boundary condition*: the continuous
`O(2)` symmetry of the model is not spontaneously broken.

The proof is the spin-wave (Bogoliubov) argument: a slowly varying rotation of the spins,
equal to `π` at the origin and vanishing outside a large box, costs an energy of order
`1 / log R`, which vanishes in dimension `d ≤ 2`; by `Phys.gibbs_shift_bound` this forces
the magnetisation to be equal to its own opposite, up to an arbitrarily small error.
-/

namespace Phys

noncomputable section

open MeasureTheory Finset

variable {d : ℕ}

/-- Configurations of the spins in the box of radius `N`. -/
abbrev BoxCfg (d N : ℕ) := {x : Site d // x ∈ box d N} → Spin

/-- Extend a configuration in the box by the boundary condition `τ` outside the box. -/
