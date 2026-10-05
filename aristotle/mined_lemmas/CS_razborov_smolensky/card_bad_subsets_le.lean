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
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma card_bad_subsets_le {k : ℕ} (hq : 2 ≤ q) (T : Fin k → Bool) (i₀ : Fin k)
    (hi₀ : T i₀ = true) :
    2 * #{S : Fin k → Bool | q ∣ cnt fun i => S i && T i} ≤ 2 ^ k := by
  classical
  set A : Finset (Fin k → Bool) := {S : Fin k → Bool | q ∣ cnt fun i => S i && T i} with hA
  set σ : (Fin k → Bool) → (Fin k → Bool) := fun S i => if i = i₀ then !(S i) else S i with hσ
  have hsplit : ∀ g : Fin k → Bool,
      cnt g = (if g i₀ then 1 else 0) + ∑ i ∈ univ.erase i₀, (if g i then 1 else 0) := by
    intro g
    rw [cnt_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have htail : ∀ S : Fin k → Bool,
      (∑ i ∈ univ.erase i₀, (if σ S i && T i then 1 else 0))
        = ∑ i ∈ univ.erase i₀, (if S i && T i then 1 else 0) := by
    intro S
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ i₀ := (Finset.mem_erase.1 hi).1
    simp [hσ, hne]
  have hcnt : ∀ S : Fin k → Bool,
      (cnt fun i => σ S i && T i) = (cnt fun i => S i && T i) + 1 ∨
      (cnt fun i => σ S i && T i) + 1 = (cnt fun i => S i && T i) := by
    intro S
    rw [hsplit (fun i => σ S i && T i), hsplit (fun i => S i && T i), htail S]
    cases h : S i₀
    · left; simp [hσ, h, hi₀]
    · right; simp [hσ, h, hi₀]
  have hnodvd : ∀ m : ℕ, q ∣ m → ¬ q ∣ (m + 1) := by
    intro m h1 h2
    have h3 : q ∣ 1 := by simpa using Nat.dvd_sub' h2 h1
    have := Nat.le_of_dvd one_pos h3
    omega
  have hmaps : ∀ S ∈ A, σ S ∈ Aᶜ := by
    intro S hS
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_compl, hA, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcnt S with h | h
    · rw [h]; exact hnodvd _ hS
    · intro hdvd
      exact hnodvd _ hdvd (by rw [h]; exact hS)
  have hinj : Set.InjOn σ (A : Set (Fin k → Bool)) := by
    intro S _ S' _ h
    funext i
    have hi' := congrFun h i
    by_cases hi : i = i₀
    · subst hi
      simp only [hσ, if_pos rfl] at hi'
      simpa using hi'
    · simpa [hσ, hi] using hi'
  have hcard : A.card ≤ Aᶜ.card := Finset.card_le_card_of_injOn σ (fun S hS => hmaps S hS) hinj
  have htot : A.card + Aᶜ.card = 2 ^ k := by
    rw [Finset.card_add_card_compl]
    simp [Fintype.card_fun]
  omega

/-- The core probabilistic estimate: for a fixed input `x` at which all children are computed
correctly, at most a `2^{-ℓ}` fraction of the choices `ω` give a wrong answer. -/
