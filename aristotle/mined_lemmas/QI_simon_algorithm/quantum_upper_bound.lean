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
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


theorem quantum_upper_bound {Y : Type*} [DecidableEq Y] {s : Vec n} {f : Vec n → Y}
    (h : IsSimon s f) :
    ∃ B : Finset (Vec n), B.card = n - 1 ∧
      (∀ y ∈ B, ∃ z : Y, amp f y z ≠ 0) ∧
      (∀ t : Vec n, (∀ y ∈ B, dot t y = 0) → t = 0 ∨ t = s) := by
  obtain ⟨j, hj0⟩ : ∃ j, s j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h.1 (funext hc)
  have hj : s j = 1 := (zmod2_cases (s j)).resolve_left hj0
  classical
  refine ⟨(Finset.univ.erase j).image (simonBasis s j), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    intro a ha b _ hab
    have h1 : simonBasis s j a a = simonBasis s j b a := by rw [hab]
    have haj : a ≠ j := Finset.ne_of_mem_erase (Finset.mem_coe.mp ha)
    by_contra hne
    simp [simonBasis, haj, hne] at h1
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, _, rfl⟩ := hy
    refine ⟨f 0, ?_⟩
    rw [amp_of_dot_eq_zero h (dot_simonBasis_self hj i) 0]
    have h1 := chi_ne_zero (dot (0 : Vec n) (simonBasis s j i))
    have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
    exact mul_ne_zero (one_div_ne_zero h2) (mul_ne_zero two_ne_zero h1)
  · intro t ht
    have key : ∀ i, i ≠ j → t i = t j * s i := by
      intro i hi
      have hd := ht (simonBasis s j i)
        (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩))
      rw [dot_simonBasis] at hd
      have h3 : t i + (t j * s i + t j * s i) = t j * s i := by
        rw [← add_assoc, hd, zero_add]
      rwa [zmod2_add_self, add_zero] at h3
    rcases zmod2_cases (t j) with h0 | h1
    · left
      funext k
      by_cases hk : k = j
      · simp [hk, h0]
      · simp [key k hk, h0]
    · right
      funext k
      by_cases hk : k = j
      · simp [hk, h1, hj]
      · simp [key k hk, h1]

/-! ## Classical part: deterministic decision trees -/

/-- A deterministic classical query algorithm: a decision tree whose internal nodes
query the oracle at a point of `Vec n` and branch on the (natural number) answer,
and whose leaves output a candidate secret. -/
inductive DTree (n : ℕ) : Type
  | leaf (out : Vec n) : DTree n
  | node (q : Vec n) (k : ℕ → DTree n) : DTree n

namespace DTree

/-- The output of the tree on the oracle `f`. -/
