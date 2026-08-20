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

