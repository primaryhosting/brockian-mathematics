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

theorem sum_chi_mul_chi (x y : ι → Bool) :
    ∑ S : Finset ι, chi S x * chi S y = if x = y then (2 ^ Fintype.card ι : ℝ) else 0 := by
  have key : ∏ i : ι, (bsign (x i) * bsign (y i) + 1) = ∑ S : Finset ι, chi S x * chi S y := by
    rw [Finset.prod_add, Finset.powerset_univ]
    exact Finset.sum_congr rfl fun t _ => by
      rw [chi_mul_chi, Finset.prod_const_one, mul_one]
  rw [← key]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have : ∀ i ∈ (univ : Finset ι), bsign (x i) * bsign (x i) + 1 = (2 : ℝ) := by
      intro i _
      cases x i <;> norm_num [bsign]
    rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_univ]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (mem_univ i) ?_
    cases hx : x i <;> cases hy : y i <;> simp_all [bsign]

/-- The Fourier expansion: the `±1` encoding of `f` is recovered from its Fourier
coefficients. -/
