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
def words : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => ((words n).image (List.cons false)) ∪ ((words n).image (List.cons true))

@[simp] theorem mem_words {n : ℕ} {l : List Bool} : l ∈ words n ↔ l.length = n := by
  induction n generalizing l with
  | zero =>
      simp [words, List.length_eq_zero_iff]
  | succ n ih =>
      constructor
      · intro hl
        simp only [words, Finset.mem_union, Finset.mem_image] at hl
        rcases hl with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
          simp [ih.mp ht]
      · intro hl
        match l with
        | [] => simp at hl
        | b :: t =>
            have ht : t.length = n := by simpa using hl
            cases b <;>
              simp only [words, Finset.mem_union, Finset.mem_image] <;>
              [left; right] <;> exact ⟨t, ih.mpr ht, rfl⟩

@[simp] theorem card_words (n : ℕ) : (words n).card = 2 ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
      have hdisj :
          Disjoint ((words n).image (List.cons false)) ((words n).image (List.cons true)) := by
        rw [Finset.disjoint_left]
        rintro l hl hl'
        simp only [Finset.mem_image] at hl hl'
        obtain ⟨t, _, rfl⟩ := hl
        obtain ⟨t', _, h⟩ := hl'
        simp at h
      have h1 : ((words n).image (List.cons false)).card = (words n).card :=
        Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)
      have h2 : ((words n).image (List.cons true)).card = (words n).card :=
        Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)
      rw [words, Finset.card_union_of_disjoint hdisj, h1, h2, ih]
      ring

/-- The set of length-`N` extensions of a word `w`. -/
def extensions (N : ℕ) (w : List Bool) : Finset (List Bool) :=
  (words (N - w.length)).image (fun u => w ++ u)

theorem card_extensions (N : ℕ) (w : List Bool) :
    (extensions N w).card = 2 ^ (N - w.length) := by
  rw [extensions, Finset.card_image_of_injective _ (List.append_right_injective w), card_words]

theorem extensions_subset {N : ℕ} {w : List Bool} (hw : w.length ≤ N) :
    extensions N w ⊆ words N := by
  intro l hl
  simp only [extensions, Finset.mem_image, mem_words] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  simp only [mem_words, List.length_append, hu]
  omega

theorem prefix_of_mem_extensions {N : ℕ} {w l : List Bool} (hl : l ∈ extensions N w) :
    w <+: l := by
  simp only [extensions, Finset.mem_image] at hl
  obtain ⟨u, _, rfl⟩ := hl
  exact List.prefix_append w u

/-- **Kraft's inequality.**  For any finite prefix-free binary code `S` (a finite set of
binary words no one of which is a proper prefix of another), the sum of `2 ^ (-ℓ)` over the
codeword lengths `ℓ` is at most `1`. -/
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

