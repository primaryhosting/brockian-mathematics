import Mathlib
import Archive.Sensitivity

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
# Huang's sensitivity theorem: degree is at most sensitivity squared

We formalize the sensitivity conjecture (Huang, 2019) for Boolean functions
`f : (ι → Bool) → Bool` on a finite set `ι` of variables:

  `degree f ≤ (sensitivity f)^2`.

Here `degree f` is the Fourier degree: the largest cardinality of a set `S` of variables
whose Fourier–Walsh coefficient `fourierCoeff f S` is non-zero (equivalently, the degree
of the unique multilinear real polynomial representing `f`), and `sensitivity f` is the
maximum over inputs `x` of the number of coordinates `i` such that flipping `x i`
changes the value of `f`.

The combinatorial core (Huang's degree theorem on the hypercube: every set of more than
half of the vertices of the `n`-dimensional hypercube induces a subgraph with a vertex of
degree at least `√n`) is taken from `Archive.Sensitivity`.  The remaining work here is the
Gotsman–Linial style reduction from the sensitivity conjecture to that theorem:

* transferring Huang's theorem from the cube `Fin n → Bool` to a cube `ι → Bool` indexed by
  an arbitrary finite type (`Frontier.huang_flip`);
* the top-degree case: if the top Fourier coefficient of `f` is non-zero, then
  `√(card ι) ≤ sensitivity f` (`Frontier.sqrt_card_le_sensitivity_of_top_coeff`);
* the restriction argument: a non-zero coefficient at `S` survives in some restriction of
  the variables outside `S`, and restricting does not increase sensitivity.
-/

namespace Frontier

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Basic definitions -/

/-- Flip the `i`-th coordinate of a point of the hypercube. -/

theorem sqrt_card_le_sensitivity_of_top_coeff (f : (ι → Bool) → Bool)
    (hf : fourierCoeff f (univ : Finset ι) ≠ 0) :
    Real.sqrt (Fintype.card ι) ≤ sensitivity f := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · rw [hn]
    simp
  set A : Finset (ι → Bool) :=
    {x ∈ (univ : Finset (ι → Bool)) | bsign (f x) = chi (univ : Finset ι) x} with hAdef
  set B : Finset (ι → Bool) :=
    {x ∈ (univ : Finset (ι → Bool)) | ¬ bsign (f x) = chi (univ : Finset ι) x} with hBdef
  -- the two sets partition the cube
  have hpart : A.card + B.card = 2 ^ Fintype.card ι := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ]
  -- the Fourier coefficient computes the difference of their sizes
  have hsum : ∑ x : ι → Bool, bsign (f x) * chi (univ : Finset ι) x
      = (A.card : ℝ) - (B.card : ℝ) := by
    have hterm : ∀ x : ι → Bool, bsign (f x) * chi (univ : Finset ι) x
        = if bsign (f x) = chi (univ : Finset ι) x then (1 : ℝ) else -1 := by
      intro x
      rcases bsign_eq_one_or_neg_one (f x) with ha | ha <;>
        rcases chi_eq_one_or_neg_one (univ : Finset ι) x with hc | hc <;>
          rw [ha, hc] <;> norm_num
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite]
    simp [hAdef, hBdef, sub_eq_add_neg]
  have hne : A.card ≠ B.card := by
    intro h
    apply hf
    rw [fourierCoeff, hsum, h]
    simp
  -- hence one of them contains more than half of the cube
  have hhalf : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    conv_lhs => rw [show Fintype.card ι = (Fintype.card ι - 1) + 1 by omega]
    ring
  have hcase : 2 ^ (Fintype.card ι - 1) < A.card ∨ 2 ^ (Fintype.card ι - 1) < B.card := by
    rw [hhalf] at hpart
    omega
  rcases hcase with hbig | hbig
  · refine sqrt_card_le_sensitivity_of_big_set f A ?_ hbig
    intro x hx i hxi
    rw [hAdef, mem_filter] at hx hxi
    have h1 : bsign (f (flipAt x i)) = -bsign (f x) := by
      rw [hxi.2, chi_flipAt, hx.2]
    intro hcon
    have h2 : bsign (f (flipAt x i)) = bsign (f x) := by rw [hcon]
    rw [h1] at h2
    exact bsign_ne_zero (f x) (by linarith)
  · refine sqrt_card_le_sensitivity_of_big_set f B ?_ hbig
    intro x hx i hxi
    rw [hBdef, mem_filter] at hx hxi
    have hx2 : bsign (f x) = -chi (univ : Finset ι) x :=
      eq_neg_of_ne_of_sign (bsign_eq_one_or_neg_one _) (chi_eq_one_or_neg_one _ _) hx.2
    have hxi2 : bsign (f (flipAt x i)) = -chi (univ : Finset ι) (flipAt x i) :=
      eq_neg_of_ne_of_sign (bsign_eq_one_or_neg_one _) (chi_eq_one_or_neg_one _ _) hxi.2
    have h1 : bsign (f (flipAt x i)) = -bsign (f x) := by
      rw [hxi2, chi_flipAt, hx2]
    intro hcon
    have h2 : bsign (f (flipAt x i)) = bsign (f x) := by rw [hcon]
    rw [h1] at h2
    exact bsign_ne_zero (f x) (by linarith)

/-! ## Restrictions -/

/-- Merge a partial assignment on `S` with a partial assignment off `S`. -/
