/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- The finset of all binary strings (lists of booleans) of length `n`. -/
def boolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (Finset.univ : Finset Bool).biUnion
      (fun b => (boolLists n).image (fun l => b :: l))

lemma mem_boolLists {l : List Bool} {n : ℕ} : l ∈ boolLists n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [boolLists, List.length_eq_zero_iff]
  | succ n ih =>
    cases l with
    | nil => simp [boolLists]
    | cons b t =>
      have hlen : (b :: t).length = n + 1 ↔ t.length = n := by simp
      rw [hlen]
      simp only [boolLists, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and,
        List.cons.injEq]
      constructor
      · rintro ⟨b', l, hl, -, rfl⟩
        exact ih.1 hl
      · intro hl
        exact ⟨b, t, ih.2 hl, rfl, rfl⟩

lemma card_boolLists (n : ℕ) : (boolLists n).card = 2 ^ n := by
  induction n with
  | zero => simp [boolLists]
  | succ n ih =>
    have hdisj : ((Finset.univ : Finset Bool) : Set Bool).PairwiseDisjoint
        (fun b => (boolLists n).image (fun l => b :: l)) := by
      intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro a ha hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨u, _, hu⟩ := ha
      obtain ⟨v, _, hv⟩ := hb
      subst hu
      simp only [List.cons.injEq] at hv
      exact hxy hv.1.symm
    have hinj : ∀ b : Bool, Function.Injective (fun l : List Bool => b :: l) := by
      intro b x y h
      simpa using h
    rw [boolLists, Finset.card_biUnion hdisj]
    simp only [Finset.card_image_of_injective _ (hinj _), ih, Finset.sum_const,
      Finset.card_univ, Fintype.card_bool, smul_eq_mul]
    ring

/-- **Kraft's inequality.** For any finite prefix-free binary code `S` (a finite set of
binary strings none of which is a prefix of another), the sum of `2 ^ (-ℓ)` over the
codeword lengths `ℓ` is at most `1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b) :
    ∑ c ∈ S, (1 / 2 : ℝ) ^ c.length ≤ 1 := by
  classical
  set N : ℕ := S.sup (fun c => c.length) with hN
  have hlen : ∀ c ∈ S, c.length ≤ N := fun c hc => Finset.le_sup (f := fun c => c.length) hc
  -- the set of length-`N` extensions of a codeword
  set ext : List Bool → Finset (List Bool) :=
    fun c => (boolLists (N - c.length)).image (fun t => c ++ t) with hext
  have hsub : ∀ c ∈ S, ext c ⊆ boolLists N := by
    intro c hc x hx
    simp only [hext, Finset.mem_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [mem_boolLists] at ht ⊢
    have := hlen c hc
    simp [ht]
    omega
  have hcard : ∀ c : List Bool, (ext c).card = 2 ^ (N - c.length) := by
    intro c
    rw [hext]
    rw [Finset.card_image_of_injective _ (fun x y h => List.append_cancel_left h),
      card_boolLists]
  have hdisj : ((S : Set (List Bool))).PairwiseDisjoint ext := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro x hxa hxb
    simp only [hext, Finset.mem_image] at hxa hxb
    obtain ⟨s, _, hs⟩ := hxa
    obtain ⟨t, _, ht⟩ := hxb
    have hpa : a <+: x := ⟨s, hs⟩
    have hpb : b <+: x := ⟨t, ht⟩
    rcases le_total a.length b.length with h | h
    · exact hab (hpf a ha b hb (List.prefix_of_prefix_length_le hpa hpb h))
    · exact hab (hpf b hb a ha (List.prefix_of_prefix_length_le hpb hpa h)).symm
  have hsum : ∑ c ∈ S, 2 ^ (N - c.length) ≤ 2 ^ N := by
    calc ∑ c ∈ S, 2 ^ (N - c.length) = ∑ c ∈ S, (ext c).card := by
          exact Finset.sum_congr rfl (fun c _ => (hcard c).symm)
      _ = (S.biUnion ext).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (boolLists N).card := Finset.card_le_card (Finset.biUnion_subset.2 hsub)
      _ = 2 ^ N := card_boolLists N
  have hsumR : ∑ c ∈ S, (2 : ℝ) ^ (N - c.length) ≤ 2 ^ N := by
    exact_mod_cast hsum
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  calc ∑ c ∈ S, (1 / 2 : ℝ) ^ c.length
      = (∑ c ∈ S, (2 : ℝ) ^ (N - c.length)) / 2 ^ N := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun c hc => ?_)
        have h := hlen c hc
        rw [div_pow, one_pow, div_eq_div_iff (by positivity : ((2:ℝ) ^ c.length) ≠ 0)
          (by positivity : ((2:ℝ) ^ N) ≠ 0), one_mul, ← pow_add]
        congr 1
        omega
    _ ≤ 2 ^ N / 2 ^ N := by gcongr
    _ = 1 := div_self (ne_of_gt h2)

end CS

