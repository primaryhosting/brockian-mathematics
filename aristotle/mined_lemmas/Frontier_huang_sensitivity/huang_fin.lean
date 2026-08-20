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

theorem huang_fin (m : ℕ) (A : Finset (Fin (m + 1) → Bool)) (hA : 2 ^ m < A.card) :
    ∃ x ∈ A, Real.sqrt (m + 1) ≤ #{i ∈ (univ : Finset (Fin (m + 1))) | flipAt x i ∈ A} := by
  let A₀ : Finset (Sensitivity.Q (m + 1)) := A
  obtain ⟨q, hqH, hq⟩ :=
    Sensitivity.huang_degree_theorem (m := m) (↑A₀ : Set (Sensitivity.Q (m + 1))) (by
      rw [Set.toFinset_card]
      simpa [A₀] using hA)
  have hqA : q ∈ A := by simpa [A₀] using hqH
  refine ⟨q, hqA, le_trans hq (Nat.cast_le.mpr ?_)⟩
  refine Finset.card_le_card_of_surjOn (fun i => flipAt q i) ?_
  intro p hp
  simp only [Finset.mem_coe, Set.mem_toFinset] at hp
  obtain ⟨hpA, i, hi, huniq⟩ := hp
  have hpflip : p = flipAt q i := eq_flipAt_of_unique_ne hi huniq
  refine ⟨i, ?_, hpflip.symm⟩
  simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
  rw [← hpflip]
  exact hpA

/-- Huang's degree theorem, in the cube indexed by an arbitrary finite type and phrased
with coordinate flips: if `A` contains more than half of the points of the cube, then some
point of `A` has at least `√(card ι)` neighbours in `A`. -/
