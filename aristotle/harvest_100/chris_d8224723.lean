/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finite set of all binary words of length `n`. -/
def allWords (n : ℕ) : Finset (List Bool) :=
  Finset.univ.image (fun f : Fin n → Bool => List.ofFn f)

lemma mem_allWords {n : ℕ} {w : List Bool} : w ∈ allWords n ↔ w.length = n := by
  constructor
  · rintro hw
    simp only [allWords, Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨f, rfl⟩ := hw
    simp
  · intro hw
    subst hw
    simp only [allWords, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => w[i], List.ofFn_getElem w⟩

lemma card_allWords (n : ℕ) : (allWords n).card = 2 ^ n := by
  rw [allWords, Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ]
  simp

/-- Kraft's inequality, in the natural-number form: for a prefix-free set `S` of binary
codewords with maximal length `L`, we have `∑ 2 ^ (L - ℓ i) ≤ 2 ^ L`. -/
lemma kraft_nat (S : Finset (List Bool))
    (hpf : ∀ c ∈ S, ∀ d ∈ S, c <+: d → c = d) :
    ∑ c ∈ S, 2 ^ (S.sup List.length - c.length) ≤ 2 ^ (S.sup List.length) := by
  set L := S.sup List.length with hL
  set f : List Bool → Finset (List Bool) :=
    fun c => (allWords (L - c.length)).image (fun t => c ++ t) with hf
  have hlen : ∀ c ∈ S, c.length ≤ L := fun c hc => Finset.le_sup (f := List.length) hc
  have hcard : ∀ c ∈ S, (f c).card = 2 ^ (L - c.length) := by
    intro c _
    rw [hf]
    simp only
    rw [Finset.card_image_of_injective _ (fun t t' h => by simpa using h), card_allWords]
  have hsub : S.biUnion f ⊆ allWords L := by
    intro w hw
    simp only [Finset.mem_biUnion] at hw
    obtain ⟨c, hc, hwc⟩ := hw
    rw [hf] at hwc
    simp only [Finset.mem_image] at hwc
    obtain ⟨t, ht, rfl⟩ := hwc
    rw [mem_allWords] at ht ⊢
    rw [List.length_append, ht]
    have := hlen c hc
    omega
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (f x) (f y) := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro w hwx hwy
    rw [hf] at hwx hwy
    simp only [Finset.mem_image] at hwx hwy
    obtain ⟨t, _, rfl⟩ := hwx
    obtain ⟨t', _, hw⟩ := hwy
    have hxp : x <+: x ++ t := ⟨t, rfl⟩
    have hyp : y <+: x ++ t := ⟨t', hw⟩
    rcases List.prefix_or_prefix_of_prefix hxp hyp with h | h
    · exact hxy (hpf x hx y hy h)
    · exact hxy (hpf y hy x hx h).symm
  calc ∑ c ∈ S, 2 ^ (L - c.length)
      = ∑ c ∈ S, (f c).card := (Finset.sum_congr rfl hcard).symm
    _ = (S.biUnion f).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (allWords L).card := Finset.card_le_card hsub
    _ = 2 ^ L := card_allWords L

/-- **Kraft's inequality.** Any prefix-free binary code satisfies `∑ 2 ^ (-ℓ i) ≤ 1`,
where the sum runs over the (finitely many) codewords and `ℓ i` is the length of the
`i`-th codeword. Prefix-freeness is expressed as: if a codeword is a prefix of a
codeword, they are equal. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ c ∈ S, ∀ d ∈ S, c <+: d → c = d) :
    ∑ c ∈ S, ((1 : ℝ) / 2) ^ c.length ≤ 1 := by
  set L := S.sup List.length with hL
  have hlen : ∀ c ∈ S, c.length ≤ L := fun c hc => Finset.le_sup (f := List.length) hc
  have hpos : (0 : ℝ) < 2 ^ L := by positivity
  have key : ∀ c ∈ S, ((1 : ℝ) / 2) ^ c.length = (2 : ℝ) ^ (L - c.length) / 2 ^ L := by
    intro c hc
    have h : (2 : ℝ) ^ (L - c.length) * 2 ^ c.length = 2 ^ L := by
      rw [← pow_add, Nat.sub_add_cancel (hlen c hc)]
    have h2 : (2 : ℝ) ^ c.length ≠ 0 := by positivity
    rw [div_pow, one_pow, div_eq_div_iff h2 (ne_of_gt hpos), one_mul, h]
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, div_le_one hpos]
  have := kraft_nat S hpf
  have hcast : ((∑ c ∈ S, 2 ^ (L - c.length) : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at hcast
  exact hcast

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

