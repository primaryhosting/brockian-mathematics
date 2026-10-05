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
