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

import Mathlib
import RequestProject.PolySpace

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Unbounded fan-in Boolean circuits and their low-degree approximation

We define constant-depth, unbounded fan-in Boolean circuits over the basis
`{¬, ∨, ∧}` and prove Razborov's approximation lemma: a circuit of size `s`
and depth `d` is computed by a function of `F₃`-degree at most `(2ℓ)^d`
on all but a `s·2^{-ℓ}` fraction of the inputs.
-/

namespace CS

open Finset

/-- Unbounded fan-in Boolean circuits on `n` inputs. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | cst : Bool → Circ n
  | neg : Circ n → Circ n
  | orG : (k : ℕ) → (Fin k → Circ n) → Circ n
  | andG : (k : ℕ) → (Fin k → Circ n) → Circ n

/-- The Boolean function computed by a circuit. -/

lemma card_zero_subset_sums {k : ℕ} (v : Fin k → F3) (i₀ : Fin k) (h₀ : v i₀ = 1) :
    2 * ((Finset.univ.filter
        (fun a : Fin k → Bool => ∑ i, (if a i then v i else 0) = 0)).card) ≤ 2 ^ k := by
  classical
  set Z := (Finset.univ.filter
      (fun a : Fin k → Bool => ∑ i, (if a i then v i else 0) = 0)) with hZ
  set φ : (Fin k → Bool) → (Fin k → Bool) := fun a => Function.update a i₀ (!a i₀) with hφ
  have hsum : ∀ a : Fin k → Bool, ∑ i, (if a i then v i else 0)
      = (if a i₀ then v i₀ else 0) + ∑ i ∈ Finset.univ.erase i₀, (if a i then v i else 0) := by
    intro a
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have hφsum : ∀ a : Fin k → Bool, ∑ i, (if φ a i then v i else 0)
      = (if !a i₀ then v i₀ else 0) + ∑ i ∈ Finset.univ.erase i₀, (if a i then v i else 0) := by
    intro a
    rw [hsum (φ a)]
    congr 1
    · simp [hφ]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have : i ≠ i₀ := (Finset.mem_erase.1 hi).1
      simp [hφ, Function.update_of_ne this]
  have hmaps : ∀ a ∈ Z, φ a ∈ Finset.univ \ Z := by
    intro a ha
    have ha' : ∑ i, (if a i then v i else 0) = 0 := by
      simpa [hZ] using ha
    have hT : ∑ i ∈ Finset.univ.erase i₀, (if a i then v i else 0)
        = -(if a i₀ then v i₀ else 0) := by
      have := hsum a
      rw [ha'] at this
      linear_combination -this
    have : ∑ i, (if φ a i then v i else 0) ≠ 0 := by
      rw [hφsum a, hT, h₀]
      cases a i₀ <;> decide
    simp [hZ, this]
  have hinj : Set.InjOn φ ↑Z := by
    intro a _ b _ hab
    have hinv : ∀ c : Fin k → Bool, φ (φ c) = c := by
      intro c
      funext i
      by_cases hi : i = i₀
      · subst hi; simp [hφ]
      · simp [hφ, Function.update_of_ne hi]
    have := hinv a
    have hb := hinv b
    rw [← this, ← hb, hab]
  have hcard : Z.card ≤ (Finset.univ \ Z).card :=
    Finset.card_le_card_of_injOn φ (fun a ha => by
      have h := hmaps a (by simpa using ha)
      simpa using h) hinj
  have huniv : (Finset.univ : Finset (Fin k → Bool)).card = 2 ^ k := by simp
  have hsub : (Finset.univ \ Z).card = 2 ^ k - Z.card := by
    rw [Finset.card_univ_diff]
    simp
  have hZle : Z.card ≤ 2 ^ k := by rw [← huniv]; exact Finset.card_le_univ Z
  omega

/-! ### The approximator for a single gate -/

/-- Razborov's approximator for an unbounded fan-in OR of the functions `g i`,
using the `ℓ` random subsets given by `r`. -/
