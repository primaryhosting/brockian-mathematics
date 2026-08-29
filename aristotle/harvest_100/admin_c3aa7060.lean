/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kraft's inequality for prefix-free binary codes

A finite set `S` of binary codewords (lists of booleans) is *prefix-free* if no codeword
is a prefix of a different codeword.  The main result, `CS.pcp_pigeon_bound`, states
Kraft's inequality: `∑ w ∈ S, (1/2) ^ w.length ≤ 1`.
-/

namespace CS

/-- A finite set of binary codewords is *prefix-free* when no codeword is a prefix of
another codeword. -/
def PrefixFree (S : Finset (List Bool)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v

/-- The set of tails of the codewords of `S` beginning with the bit `b`. -/
def tailsOf (b : Bool) (S : Finset (List Bool)) : Finset (List Bool) :=
  (S.filter (fun w => w.headI = b)).image List.tail

lemma mem_tailsOf {b : Bool} {S : Finset (List Bool)} (h0 : [] ∉ S) {v : List Bool} :
    v ∈ tailsOf b S ↔ (b :: v) ∈ S := by
  classical
  constructor
  · intro hv
    simp only [tailsOf, Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨w, ⟨hwS, hwb⟩, rfl⟩ := hv
    have hne : w ≠ [] := by rintro rfl; exact h0 hwS
    have : w.headI :: w.tail = w := List.cons_head!_tail hne
    rw [hwb] at this
    rwa [this]
  · intro hv
    simp only [tailsOf, Finset.mem_image, Finset.mem_filter]
    exact ⟨b :: v, ⟨hv, rfl⟩, rfl⟩

lemma prefixFree_tailsOf {b : Bool} {S : Finset (List Bool)} (h0 : [] ∉ S)
    (hS : PrefixFree S) : PrefixFree (tailsOf b S) := by
  intro u hu v hv huv
  rw [mem_tailsOf h0] at hu hv
  have : (b :: u) <+: (b :: v) := by
    exact List.cons_prefix_cons.mpr ⟨rfl, huv⟩
  have := hS _ hu _ hv this
  exact List.cons_injective this

lemma sum_tailsOf {b : Bool} {S : Finset (List Bool)} (h0 : [] ∉ S) :
    ∑ v ∈ tailsOf b S, (1 / 2 : ℝ) ^ v.length
      = 2 * ∑ w ∈ S.filter (fun w => w.headI = b), (1 / 2 : ℝ) ^ w.length := by
  classical
  have hinj : ∀ x ∈ S.filter (fun w => w.headI = b), ∀ y ∈ S.filter (fun w => w.headI = b),
      x.tail = y.tail → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter] at hx hy
    have hxne : x ≠ [] := by rintro rfl; exact h0 hx.1
    have hyne : y ≠ [] := by rintro rfl; exact h0 hy.1
    have hx' : x.headI :: x.tail = x := List.cons_head!_tail hxne
    have hy' : y.headI :: y.tail = y := List.cons_head!_tail hyne
    rw [← hx', ← hy', hx.2, hy.2, hxy]
  rw [tailsOf, Finset.sum_image (fun x hx y hy h => hinj x hx y hy h), Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro w hw
  simp only [Finset.mem_filter] at hw
  have hne : w ≠ [] := by rintro rfl; exact h0 hw.1
  obtain ⟨a, t, rfl⟩ : ∃ a t, w = a :: t := by
    cases w with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  simp [pow_succ]
  ring

lemma kraft_aux : ∀ (n : ℕ) (S : Finset (List Bool)), PrefixFree S →
    (∀ w ∈ S, w.length ≤ n) → ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro S _ hlen
    have hsub : S ⊆ {[]} := by
      intro w hw
      have := hlen w hw
      simp only [Nat.le_zero, List.length_eq_zero_iff] at this
      simp [this]
    calc ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length
        ≤ ∑ w ∈ ({[]} : Finset (List Bool)), (1 / 2 : ℝ) ^ w.length := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro i _ _
          positivity
      _ = 1 := by simp
  | succ n ih =>
    intro S hS hlen
    classical
    by_cases h0 : ([] : List Bool) ∈ S
    · have hsub : S ⊆ {[]} := by
        intro w hw
        have := hS [] h0 w hw (List.nil_prefix)
        simp [← this]
      calc ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length
          ≤ ∑ w ∈ ({[]} : Finset (List Bool)), (1 / 2 : ℝ) ^ w.length := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro i _ _
            positivity
        _ = 1 := by simp
    · have key : ∀ b : Bool,
          ∑ w ∈ S.filter (fun w => w.headI = b), (1 / 2 : ℝ) ^ w.length ≤ 1 / 2 := by
        intro b
        have hpf := prefixFree_tailsOf (b := b) h0 hS
        have hlen' : ∀ v ∈ tailsOf b S, v.length ≤ n := by
          intro v hv
          rw [mem_tailsOf h0] at hv
          have := hlen _ hv
          simpa using this
        have hIH := ih (tailsOf b S) hpf hlen'
        rw [sum_tailsOf h0] at hIH
        linarith
      have hsplit :
          ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length
            = (∑ w ∈ S.filter (fun w => w.headI = true), (1 / 2 : ℝ) ^ w.length)
              + ∑ w ∈ S.filter (fun w => w.headI = false), (1 / 2 : ℝ) ^ w.length := by
        rw [← Finset.sum_filter_add_sum_filter_not S (fun w => w.headI = true)]
        congr 1
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        refine Finset.filter_congr ?_
        intro w _
        cases w.headI <;> simp
      rw [hsplit]
      have h1 := key true
      have h2 := key false
      linarith

/-- **Kraft's inequality.**  Any prefix-free binary code satisfies `∑ 2 ^ (-ℓᵢ) ≤ 1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool)) (hS : PrefixFree S) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  refine kraft_aux (S.sup List.length) S hS ?_
  intro w hw
  exact Finset.le_sup hw

/-- Sanity check: the hypothesis is satisfiable and the bound is tight for the code
`{[false], [true]}`. -/
example : PrefixFree {[false], [true]} ∧
    ∑ w ∈ ({[false], [true]} : Finset (List Bool)), (1 / 2 : ℝ) ^ w.length = 1 := by
  constructor
  · intro u hu v hv huv
    fin_cases hu <;> fin_cases hv <;> simp_all [List.prefix_iff_eq_take]
  · norm_num

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

