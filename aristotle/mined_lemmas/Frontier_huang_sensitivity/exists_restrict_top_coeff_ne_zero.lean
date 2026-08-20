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

theorem exists_restrict_top_coeff_ne_zero (f : (ι → Bool) → Bool) (S : Finset ι)
    (hS : fourierCoeff f S ≠ 0) :
    ∃ r : {i // i ∉ S} → Bool, fourierCoeff (restrict f S r) (univ : Finset {i // i ∈ S}) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ r : {i // i ∉ S} → Bool,
      ∑ y : {i // i ∈ S} → Bool,
        bsign (restrict f S r y) * chi (univ : Finset {i // i ∈ S}) y = 0 := by
    intro r
    have := hcon r
    rw [fourierCoeff, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact h
  have hsum : ∑ z : ι → Bool, bsign (f z) * chi S z = 0 := by
    rw [← sum_restrict_top f S]
    exact Finset.sum_eq_zero fun r _ => hzero r
  rw [fourierCoeff, hsum, mul_zero] at hS
  exact hS rfl

/-! ## Justification of the definition of degree: the Fourier expansion

We check that `degree` really is the degree of the multilinear polynomial representing `f`:
the `±1` encoding `bsign ∘ f` of `f` is the sum of `fourierCoeff f S * chi S` over all `S`,
and only sets `S` of size at most `degree f` contribute. -/

omit [Fintype ι] [DecidableEq ι] in
