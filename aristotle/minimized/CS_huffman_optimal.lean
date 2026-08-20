/-
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Statement: Huffman coding minimizes expected codeword length among prefix codes.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

open List

variable {α : Type*} {ι : Type*}

/-! ## Extracting a minimum-weight element from a list -/

/-- `popMin f a l` returns a pair whose first component is an element of `a :: l`
minimizing `f`, and whose second component is the remaining list. -/

noncomputable def popMin (f : α → ℝ) : α → List α → α × List α
  | a, [] => (a, [])
  | a, b :: l =>
      if f b < f a then ((popMin f b l).1, a :: (popMin f b l).2)
      else ((popMin f a l).1, b :: (popMin f a l).2)

lemma popMin_cons (f : α → ℝ) (a b : α) (l : List α) :
    popMin f a (b :: l) =
      if f b < f a then ((popMin f b l).1, a :: (popMin f b l).2)
      else ((popMin f a l).1, b :: (popMin f a l).2) := rfl

@[simp] lemma popMin_length (f : α → ℝ) (a : α) (l : List α) :
    (popMin f a l).2.length = l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => by_cases h : f b < f a <;> simp [popMin_cons, h, ih]

def gw (w : ι → ℝ) (g : List (ι × List Bool)) : ℝ := (g.map fun p => w p.1).sum

/-- The total cost (weighted codeword length) of a group. -/

def gmerge (A B : List (ι × List Bool)) : List (ι × List Bool) :=
  A.map (fun p => (p.1, false :: p.2)) ++ B.map (fun p => (p.1, true :: p.2))

/-- One run of Huffman's algorithm: repeatedly merge two minimum-weight groups. -/

noncomputable def hstep (w : ι → ℝ) :
    List (ι × List Bool) → List (List (ι × List Bool)) → List (ι × List Bool)
  | g, [] => g
  | g, h :: F =>
      hstep w (gmerge (popMin (gw w) g (h :: F)).1
                (popMin (gw w) (popMin (gw w) g (h :: F)).2.headI
                  (popMin (gw w) g (h :: F)).2.tail).1)
            (popMin (gw w) (popMin (gw w) g (h :: F)).2.headI
                  (popMin (gw w) g (h :: F)).2.tail).2
  termination_by _ F => F.length
  decreasing_by
    simp [popMin_length]

/-- The cost of the Huffman code for a list of weights, defined by Huffman's recursion. -/

noncomputable def kraft (S : List (ℝ × ℕ)) : ℝ := (S.map fun p => (2:ℝ)⁻¹ ^ p.2).sum

/-- Expected codeword length of a list of (weight, codeword length) pairs. -/

lemma kraft_cons (p : ℝ × ℕ) (S : List (ℝ × ℕ)) :
    kraft (p :: S) = (2:ℝ)⁻¹ ^ p.2 + kraft S := by simp [kraft]

lemma nat_sum_even (L : List ℕ) (h : ∀ n ∈ L, n % 2 = 0) : L.sum % 2 = 0 := by
  induction L with
  | nil => simp
  | cons n L ih =>
      have h1 := h n (by simp)
      have h2 := ih (fun k hk => h k (by simp [hk]))
      simp only [List.sum_cons]
      omega

lemma kraft_mul_pow (m : ℕ) : ∀ (S : List (ℝ × ℕ)), (∀ p ∈ S, p.2 ≤ m) →
    (2:ℝ)^m * kraft S = ((S.map fun p => 2^(m - p.2)).sum : ℕ) := by
  intro S
  induction S with
  | nil => simp [kraft]
  | cons p S ih =>
      intro h
      have hp : p.2 ≤ m := h p (by simp)
      have key : (2:ℝ)^m * (2⁻¹)^p.2 = 2^(m - p.2) := by
        rw [pow_sub₀ (2:ℝ) (by norm_num) hp, inv_pow]
      have hIH := ih (fun q hq => h q (by simp [hq]))
      rw [kraft_cons, mul_add, key, hIH]
      simp only [List.map_cons, List.sum_cons]
      push_cast
      ring

/-- If the maximal depth `m` occurs only once, the Kraft sum leaves room to shorten it. -/

lemma kraft_shorten_unique_max (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (T : List (ℝ × ℕ))
    (hT : ∀ p ∈ T, p.2 < m) (hk : kraft ((x, m) :: T) ≤ 1) :
    kraft ((x, m - 1) :: T) ≤ 1 := by
  set N : ℕ := (((x, m) :: T).map fun p => 2^(m - p.2)).sum with hN
  have hle : ∀ p ∈ (x, m) :: T, p.2 ≤ m := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact le_rfl
    · exact (hT p hp').le
  have hkey : (2:ℝ)^m * kraft ((x, m) :: T) = (N : ℝ) := kraft_mul_pow m _ hle
  -- `N` is odd
  have hodd : N % 2 = 1 := by
    have heven : ((T.map fun p => 2^(m - p.2)).sum) % 2 = 0 := by
      refine nat_sum_even ?_
      intro n hn
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hn
      have h1 : 1 ≤ m - q.2 := by have := hT q hq; omega
      obtain ⟨j, hj⟩ : ∃ j, m - q.2 = j + 1 := ⟨m - q.2 - 1, by omega⟩
      rw [hj, pow_succ]
      omega
    have : N = 2^(m - m) + (T.map fun p => 2^(m - p.2)).sum := by
      rw [hN]; simp
    rw [this]
    simp only [Nat.sub_self, pow_zero]
    omega
  -- `N ≤ 2 ^ m`
  have hNle : (N : ℝ) ≤ 2^m := by
    rw [← hkey]
    have : (0:ℝ) < 2^m := by positivity
    nlinarith
  have hNle' : N ≤ 2^m := by exact_mod_cast hNle
  have hNlt : N < 2^m := by
    rcases lt_or_eq_of_le hNle' with h | h
    · exact h
    · exfalso
      have : (2:ℕ)^m % 2 = 0 := by
        obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [hj, pow_succ]; omega
      omega
  -- conclude
  have hpow : (0:ℝ) < 2^m := by positivity
  have h1 : kraft ((x, m) :: T) ≤ 1 - (2:ℝ)⁻¹^m := by
    have hNle2 : (N : ℝ) ≤ 2^m - 1 := by
      have : (N : ℝ) + 1 ≤ 2^m := by exact_mod_cast hNlt
      linarith
    have hmul : (2:ℝ)^m * kraft ((x, m) :: T) ≤ 2^m - 1 := by rw [hkey]; exact hNle2
    have h2 : kraft ((x, m) :: T) ≤ ((2:ℝ)^m - 1) / 2^m := by
      rw [le_div_iff₀ hpow]; linarith
    have h3 : ((2:ℝ)^m - 1)/2^m = 1 - (2:ℝ)⁻¹^m := by
      rw [inv_pow]; field_simp
    rw [h3] at h2
    exact h2
  have hstep : kraft ((x, m - 1) :: T) = kraft ((x, m) :: T) + (2:ℝ)⁻¹^m := by
    rw [kraft_cons, kraft_cons]
    have : (2:ℝ)⁻¹^(m-1) = 2 * 2⁻¹^m := by
      obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      subst hj
      simp [pow_succ]
      ring
    simp only [this]
    ring
  rw [hstep]
  linarith

end CS

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
