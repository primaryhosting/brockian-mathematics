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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is a *Zumkeller number* if its set of divisors can be split into two
parts of equal sum, i.e. there is a set `S` of divisors of `n` whose sum is half of `σ(n)`. -/

lemma zumkeller_of_split {N b n k : ℕ} (hk : k ≠ 0) (hb : IsZumkeller b) (hn : IsZumkeller n)
    (hdisj : Disjoint b.divisors (n.divisors.image (fun d => k * d)))
    (hsplit : N.divisors = b.divisors ∪ n.divisors.image (fun d => k * d)) :
    IsZumkeller N := by
  obtain ⟨A, hA, hAsum⟩ := hb
  obtain ⟨B, hB, hBsum⟩ := hn
  have himg : Finset.image (fun d => k * d) B ⊆ Finset.image (fun d => k * d) n.divisors :=
    Finset.image_subset_image hB
  have himgsum : ∀ T : Finset ℕ, ∑ d ∈ T.image (fun d => k * d), d = k * ∑ d ∈ T, d := by
    intro T
    rw [Finset.sum_image (fun x _ y _ hxy =>
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) hxy), Finset.mul_sum]
  have hdA : Disjoint A (Finset.image (fun d => k * d) B) := hdisj.mono hA himg
  refine ⟨A ∪ Finset.image (fun d => k * d) B, ?_, ?_⟩
  · rw [hsplit]; exact Finset.union_subset_union hA himg
  · rw [Finset.sum_union hdA, hsplit, Finset.sum_union hdisj, himgsum, himgsum,
      Nat.mul_add, hAsum]
    have h2 : 2 * (k * ∑ d ∈ B, d) = k * ∑ d ∈ n.divisors, d := by rw [← hBsum]; ring
    omega

