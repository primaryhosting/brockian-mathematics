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

theorem fourier_expansion (f : (ι → Bool) → Bool) (x : ι → Bool) :
    ∑ S : Finset ι, fourierCoeff f S * chi S x = bsign (f x) := by
  have h1 : ∀ S : Finset ι, fourierCoeff f S * chi S x
      = (2 ^ Fintype.card ι : ℝ)⁻¹ * ∑ y : ι → Bool, bsign (f y) * (chi S y * chi S x) := by
    intro S
    rw [fourierCoeff, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl fun S _ => h1 S, ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ y : ι → Bool, ∑ S : Finset ι, bsign (f y) * (chi S y * chi S x)
      = bsign (f y) * (if y = x then (2 ^ Fintype.card ι : ℝ) else 0) := by
    intro y
    rw [← Finset.mul_sum, sum_chi_mul_chi]
  rw [Finset.sum_congr rfl fun y _ => h2 y]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' univ x (fun y => bsign (f y) * (2 ^ Fintype.card ι : ℝ))]
  rw [if_pos (mem_univ x)]
  field_simp

/-- Only sets of size at most `degree f` occur in the Fourier expansion of `f`. -/
