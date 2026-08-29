import Mathlib

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

/-
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000

namespace Brockian.Weyl.WeylLawTarget

variable {ι : Type*}

/-- The eigenvalue counting function of a spectrum.

`lam : ι → ℝ` is the eigenvalue list, indexed by `ι` and repeated according to
multiplicity, and `counting lam Λ` is the number of eigenvalues that are `≤ Λ`,
counted with multiplicity.  (This is the function `N(Λ)` appearing in Weyl's law.) -/
noncomputable def counting (lam : ι → ℝ) (Λ : ℝ) : ℕ := {i | lam i ≤ Λ}.ncard

/-- **Discreteness of the spectrum**: below any threshold `Λ` there are only finitely
many eigenvalues, counted with multiplicity.  Equivalently, the spectrum is a discrete
subset of `ℝ` which is bounded below and has finite multiplicities. -/
def DiscreteSpectrum (lam : ι → ℝ) : Prop := ∀ Λ : ℝ, {i | lam i ≤ Λ}.Finite

/-- **RVM** (Rayleigh Variational Minimax): the spectrum admits a min–max enumeration.

That is, the Rayleigh–Ritz min–max principle over an infinite-dimensional form domain
produces an injective enumeration `e : ℕ → ι` of (part of) the eigenvalue list along
which the eigenvalues `k ↦ lam (e k)` are nondecreasing.  In particular the spectrum
contains infinitely many eigenvalues, counted with multiplicity. -/
def RVM (lam : ι → ℝ) : Prop :=
  ∃ e : ℕ → ι, Function.Injective e ∧ Monotone (lam ∘ e)

/-- The counting function is monotone in the threshold, provided the spectrum is
discrete (so that the relevant sublevel sets are finite). -/
theorem counting_mono {lam : ι → ℝ} (hdisc : DiscreteSpectrum lam) :
    Monotone (counting lam) := by
  intro Λ₁ Λ₂ hΛ
  refine Set.ncard_le_ncard ?_ (hdisc Λ₂)
  intro i hi
  exact le_trans hi hΛ

/-- Along a min–max enumeration, the first `k + 1` eigenvalues all lie below
`lam (e k)`, so the counting function at that threshold is at least `k + 1`. -/
theorem succ_le_counting_of_minmax {lam : ι → ℝ} (hdisc : DiscreteSpectrum lam)
    {e : ℕ → ι} (he : Function.Injective e) (hmono : Monotone (lam ∘ e)) (k : ℕ) :
    k + 1 ≤ counting lam (lam (e k)) := by
  have hsub : (((Finset.range (k + 1)).image e : Finset ι) : Set ι) ⊆
      {i | lam i ≤ lam (e k)} := by
    intro i hi
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact hmono (Nat.lt_succ_iff.mp hj)
  have hcard : ((Finset.range (k + 1)).image e).card = k + 1 := by
    rw [Finset.card_image_of_injective _ he, Finset.card_range]
  calc k + 1 = ((Finset.range (k + 1)).image e : Finset ι).card := hcard.symm
    _ = (((Finset.range (k + 1)).image e : Finset ι) : Set ι).ncard := by
        rw [Set.ncard_coe_finset]
    _ ≤ counting lam (lam (e k)) := Set.ncard_le_ncard hsub (hdisc _)

/-- **Target.**  If the spectrum is discrete and satisfies the Rayleigh variational
min–max principle (RVM), then the eigenvalue counting function diverges:
`N(Λ) → ∞` as `Λ → ∞`. -/
theorem counting_diverges_of_discrete_and_rvm {lam : ι → ℝ}
    (hdisc : DiscreteSpectrum lam) (hrvm : RVM lam) :
    Filter.Tendsto (counting lam) Filter.atTop Filter.atTop := by
  obtain ⟨e, he, hmono⟩ := hrvm
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro M
  refine ⟨lam (e M), fun Λ hΛ => ?_⟩
  calc M ≤ M + 1 := Nat.le_succ M
    _ ≤ counting lam (lam (e M)) := succ_le_counting_of_minmax hdisc he hmono M
    _ ≤ counting lam Λ := counting_mono hdisc hΛ

/-- Non-vacuity of the hypotheses: the model spectrum `λ_n = n` on `ι = ℕ`
(the prototypical discrete spectrum obtained from the min–max principle) satisfies both
`DiscreteSpectrum` and `RVM`. -/
theorem discrete_and_rvm_nonvacuous :
    DiscreteSpectrum (fun n : ℕ => (n : ℝ)) ∧ RVM (fun n : ℕ => (n : ℝ)) := by
  constructor
  · intro Λ
    apply Set.Finite.subset (Set.finite_Iic ⌈Λ⌉₊)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have h : (n : ℝ) ≤ (⌈Λ⌉₊ : ℕ) := hn.trans (Nat.le_ceil Λ)
    exact Set.mem_Iic.mpr (by exact_mod_cast h)
  · refine ⟨id, Function.injective_id, fun a b hab => ?_⟩
    simp only [Function.comp_apply, id_eq]
    exact_mod_cast hab

end Brockian.Weyl.WeylLawTarget

