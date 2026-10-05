import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open scoped Classical

namespace Math2

variable {n : ℕ}

/-- A subset of `𝔽₃ⁿ` is a *cap set* if it contains no line, i.e. no three points summing to
zero other than the degenerate ones `x + x + x = 0`.  Equivalently (see
`Math2.threeAPFree_of_isCapSet`) it contains no nontrivial three-term arithmetic progression. -/
def IsCapSet (A : Finset (Fin n → ZMod 3)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y ∧ y = z

lemma add_self_add_self_self (x : Fin n → ZMod 3) : x + x + x = 0 := by
  have h : ∀ a : ZMod 3, a + a + a = 0 := by decide
  funext i
  simpa using h (x i)

/-- A cap set contains no three-term arithmetic progression. -/
lemma threeAPFree_of_isCapSet {A : Finset (Fin n → ZMod 3)} (hA : IsCapSet A) :
    ThreeAPFree (A : Set (Fin n → ZMod 3)) := by
  intro a ha b hb c hc habc
  refine (hA a ha b hb c hc ?_).1
  have : a + b + c = a + c + b := by ring
  rw [this, habc]
  exact add_self_add_self_self b

/-- Being a cap set is exactly the same as containing no three-term arithmetic progression. -/
lemma isCapSet_iff_threeAPFree {A : Finset (Fin n → ZMod 3)} :
    IsCapSet A ↔ ThreeAPFree (A : Set (Fin n → ZMod 3)) := by
  refine ⟨threeAPFree_of_isCapSet, fun hA x hx y hy z hz hxyz => ?_⟩
  have key : ∀ u v w : Fin n → ZMod 3, u + v + w = 0 → u + w = v + v := by
    intro u v w h
    have h' : u + w - (v + v) = u + v + w - (v + v + v) := by abel
    rw [h, add_self_add_self_self v, sub_zero, sub_eq_zero] at h'
    exact h'
  have hzyx : z + y + x = 0 := by rw [← hxyz]; abel
  exact ⟨hA hx hy hz (key x y z hxyz), (hA hz hy hx (key z y x hzyx)).symm⟩

/-- **The cap set theorem** (Croot–Lev–Pach / Ellenberg–Gijswijt, here in the qualitative
`o(3ⁿ)` form): for every `ε > 0` there is an `N` such that for all `n ≥ N`, every cap set in
`𝔽₃ⁿ` (a set containing no three-term arithmetic progression) has size at most `ε · 3ⁿ`. -/
theorem cap_set (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3), IsCapSet A → (#A : ℝ) ≤ ε * 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hcard : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by simp
  refine roth_3ap_theorem ε hε ?_ A ?_ (threeAPFree_of_isCapSet hA)
  · rw [hcard]
    exact hn.trans (Nat.lt_pow_self (by norm_num)).le
  · rw [hcard]
    push_cast
    exact hlt.le

/-- The maximal size of a cap set in `𝔽₃ⁿ`. -/
noncomputable def capSetNumber (n : ℕ) : ℕ :=
  ((univ : Finset (Finset (Fin n → ZMod 3))).filter (fun A => IsCapSet A)).sup Finset.card

lemma exists_capSetNumber (n : ℕ) :
    ∃ A : Finset (Fin n → ZMod 3), IsCapSet A ∧ capSetNumber n = #A := by
  have hne : ((univ : Finset (Finset (Fin n → ZMod 3))).filter
      (fun A => IsCapSet A)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [IsCapSet]
  obtain ⟨A, hA, hAeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨A, (Finset.mem_filter.1 hA).2, hAeq⟩

/-- **The cap set theorem**, asymptotic form: the maximal size of a cap set in `𝔽₃ⁿ` is
`o(3ⁿ)`. -/
theorem capSetNumber_isLittleO :
    IsLittleO atTop (fun n : ℕ => (capSetNumber n : ℝ)) (fun n : ℕ => (3 : ℝ) ^ n) := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨A, hA, hAeq⟩ := exists_capSetNumber n
  have h := hN n hn A hA
  rw [hAeq, Real.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ n)]
  exact h

end Math2

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

