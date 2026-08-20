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

namespace CS

/-- The finite set of all binary words (lists of booleans) of length `n`. -/

theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v) :
    ∑ w ∈ S, ((2 : ℝ) ^ w.length)⁻¹ ≤ 1 := by
  classical
  set N : ℕ := S.sup List.length with hN
  have hle : ∀ w ∈ S, w.length ≤ N := fun w hw => Finset.le_sup (f := List.length) hw
  -- the extension sets are pairwise disjoint
  have hdisj : (↑S : Set (List Bool)).PairwiseDisjoint (extensions N) := by
    intro u hu v hv huv
    rw [Function.onFun, Finset.disjoint_left]
    intro l hlu hlv
    have h1 : u <+: l := prefix_of_mem_extensions hlu
    have h2 : v <+: l := prefix_of_mem_extensions hlv
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact huv (hpf u hu v hv h)
    · exact huv (hpf v hv u hu h).symm
  -- counting bound
  have hcount : ∑ w ∈ S, 2 ^ (N - w.length) ≤ 2 ^ N := by
    have hcard : (S.biUnion (extensions N)).card = ∑ w ∈ S, 2 ^ (N - w.length) := by
      rw [Finset.card_biUnion hdisj]
      exact Finset.sum_congr rfl fun w _ => card_extensions N w
    have hsub : S.biUnion (extensions N) ⊆ words N := by
      intro l hl
      obtain ⟨w, hw, hlw⟩ := Finset.mem_biUnion.mp hl
      exact extensions_subset (hle w hw) hlw
    calc ∑ w ∈ S, 2 ^ (N - w.length) = (S.biUnion (extensions N)).card := hcard.symm
      _ ≤ (words N).card := Finset.card_le_card hsub
      _ = 2 ^ N := card_words N
  -- move to the reals
  have hcountR : ∑ w ∈ S, (2 : ℝ) ^ (N - w.length) ≤ 2 ^ N := by
    have := (Nat.cast_le (α := ℝ)).mpr hcount
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have key : ∀ w ∈ S, ((2 : ℝ) ^ w.length)⁻¹ = (2 : ℝ) ^ (N - w.length) / 2 ^ N := by
    intro w hw
    have h : w.length ≤ N := hle w hw
    have hpow : (2 : ℝ) ^ (N - w.length) * 2 ^ w.length = 2 ^ N := by
      rw [← pow_add]
      congr 1
      omega
    field_simp
    linarith [hpow]
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, div_le_one hpos]
  exact hcountR

end CS

