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
Isolation (Valiant–Vazirani) lemma over `GF(2)`, in the counting form needed for
Toda's theorem.
-/
import Mathlib

namespace CS.Toda

open Finset

/-- Bit vectors of length `m`, as vectors over `GF(2)`. -/
abbrev Vec (m : ℕ) := Fin m → ZMod 2

/-- The standard `GF(2)`-bilinear form. -/

lemma exists_good_k {m a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ 2^m) :
    ∃ k, 1 ≤ k ∧ k ≤ m+1 ∧ 2 * a ≤ 2^k ∧ 2^k < 4 * a := by
  induction m with
  | zero =>
    simp only [pow_zero] at h2
    exact ⟨1, by norm_num, by norm_num, by norm_num; omega, by norm_num; omega⟩
  | succ n ih =>
    by_cases hle : a ≤ 2^n
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih h1 hle
      exact ⟨k, hk1, by omega, hk3, hk4⟩
    · push_neg at hle
      refine ⟨n+2, by omega, by omega, ?_, ?_⟩
      · have hp : (2:ℕ)^(n+2) = 2 * 2^(n+1) := by ring
        omega
      · have hp : (2:ℕ)^(n+2) = 4 * 2^n := by ring
        omega

/-- **Isolation lemma.**  For a nonempty set `A` of bit vectors, at least a `1/(8(m+2))`
fraction of the pairs `(k, h)` isolate exactly one element of `A`. -/
