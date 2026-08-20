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

theorem huang_flip (A : Finset (ι → Bool)) (hA : 2 ^ (Fintype.card ι - 1) < A.card) :
    ∃ x ∈ A, Real.sqrt (Fintype.card ι) ≤ #{i ∈ (univ : Finset ι) | flipAt x i ∈ A} := by
  have hcard_le : A.card ≤ 2 ^ Fintype.card ι := by
    have h := Finset.card_le_card (Finset.subset_univ A)
    simpa [Finset.card_univ] using h
  -- the hypothesis forces the cube to have positive dimension
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · rw [h0] at hA hcard_le
      norm_num at hA hcard_le
      omega
    · exact ⟨Fintype.card ι - 1, by omega⟩
  -- transport everything to the standard cube `Fin (m+1) → Bool`
  let e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  let E : (ι → Bool) ≃ (Fin (m + 1) → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  have hE : ∀ (x : ι → Bool) (j : Fin (m + 1)), E x j = x (e.symm j) := fun _ _ => rfl
  have hEflip : ∀ (x : ι → Bool) (i : ι), E (flipAt x i) = flipAt (E x) (e i) := by
    intro x i
    funext j
    simp only [hE, flipAt_apply]
    by_cases hj : j = e i
    · subst hj
      simp
    · have hne : e.symm j ≠ i := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
      simp [hj, hne]
  obtain ⟨x', hx'A, hx'⟩ := huang_fin m (A.image E) (by
    rw [Finset.card_image_of_injective A E.injective]
    rw [hm] at hA
    simpa using hA)
  obtain ⟨x, hxA, hxx'⟩ := Finset.mem_image.mp hx'A
  refine ⟨x, hxA, ?_⟩
  have hcards : #{j ∈ (univ : Finset (Fin (m + 1))) | flipAt x' j ∈ A.image E}
      ≤ #{i ∈ (univ : Finset ι) | flipAt x i ∈ A} := by
    refine Finset.card_le_card_of_injOn (fun j => e.symm j) ?_ ?_
    · intro j hj
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hj ⊢
      have : flipAt x' j = E (flipAt x (e.symm j)) := by
        rw [hEflip, hxx', Equiv.apply_symm_apply]
      rw [this] at hj
      have := Finset.mem_image.mp hj
      obtain ⟨y, hy, hEy⟩ := this
      have : y = flipAt x (e.symm j) := E.injective hEy
      rwa [← this]
    · intro a _ b _ h
      exact e.symm.injective h
  have hcardsR : (#{j ∈ (univ : Finset (Fin (m + 1))) | flipAt x' j ∈ A.image E} : ℝ)
      ≤ (#{i ∈ (univ : Finset ι) | flipAt x i ∈ A} : ℝ) := by exact_mod_cast hcards
  refine le_trans ?_ hcardsR
  rw [hm]
  push_cast
  exact hx'

/-! ## The top-degree case -/

omit [Fintype ι] [DecidableEq ι] in
