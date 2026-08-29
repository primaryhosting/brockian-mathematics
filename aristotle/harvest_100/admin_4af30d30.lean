import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace CS

/-- The finite set of all binary strings (lists of booleans) of length `n`. -/
def cube : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (cube n).image (List.cons false) ∪ (cube n).image (List.cons true)

@[simp] lemma mem_cube {n : ℕ} {u : List Bool} : u ∈ cube n ↔ u.length = n := by
  induction n generalizing u with
  | zero => simp [cube, List.length_eq_zero_iff]
  | succ n ih =>
      cases u with
      | nil => simp [cube]
      | cons b u =>
          cases b <;> simp [cube, ih]

lemma card_cube (n : ℕ) : (cube n).card = 2 ^ n := by
  induction n with
  | zero => simp [cube]
  | succ n ih =>
      have hinj : ∀ (b : Bool), Set.InjOn (List.cons b) (cube n : Set (List Bool)) := by
        intro b x _ y _ h
        simpa using h
      have hdisj : Disjoint ((cube n).image (List.cons false))
          ((cube n).image (List.cons true)) := by
        rw [Finset.disjoint_left]
        rintro u hu hu'
        simp only [Finset.mem_image] at hu hu'
        obtain ⟨x, _, rfl⟩ := hu
        obtain ⟨y, _, hy⟩ := hu'
        simp at hy
      rw [cube, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injOn (hinj false), Finset.card_image_of_injOn (hinj true), ih]
      ring

/-- **Kraft's inequality.** For any finite prefix-free binary code `S`
(i.e. no codeword is a prefix of another codeword), we have
`∑ w ∈ S, (1/2)^(length w) ≤ 1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b) :
    ∑ w ∈ S, ((1 : ℝ) / 2) ^ w.length ≤ 1 := by
  classical
  set n := S.sup List.length with hn
  have hle : ∀ w ∈ S, w.length ≤ n := fun w hw => Finset.le_sup (f := List.length) hw
  -- the extension sets
  set E : List Bool → Finset (List Bool) :=
    fun w => (cube (n - w.length)).image (fun x => w ++ x) with hE
  have hEcard : ∀ w ∈ S, (E w).card = 2 ^ (n - w.length) := by
    intro w _
    rw [hE]
    rw [Finset.card_image_of_injective _ (fun x y h => List.append_cancel_left h), card_cube]
  have hEsub : ∀ w ∈ S, E w ⊆ cube n := by
    intro w hw u hu
    simp only [hE, Finset.mem_image] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have := hle w hw
    simp only [mem_cube, List.length_append] at hx ⊢
    omega
  have hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (E a) (E b) := by
    intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro u hua hub
    simp only [hE, Finset.mem_image] at hua hub
    obtain ⟨x, _, rfl⟩ := hua
    obtain ⟨y, _, hy⟩ := hub
    have hpa : a <+: a ++ x := ⟨x, rfl⟩
    have hpb : b <+: a ++ x := ⟨y, hy⟩
    rcases List.prefix_or_prefix_of_prefix hpa hpb with h | h
    · exact hab (hpf a ha b hb h)
    · exact hab (hpf b hb a ha h).symm
  -- key counting bound
  have hcount : ∑ w ∈ S, 2 ^ (n - w.length) ≤ 2 ^ n := by
    calc ∑ w ∈ S, 2 ^ (n - w.length) = ∑ w ∈ S, (E w).card :=
          Finset.sum_congr rfl (fun w hw => (hEcard w hw).symm)
      _ = (S.biUnion E).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (cube n).card := Finset.card_le_card (Finset.biUnion_subset.mpr hEsub)
      _ = 2 ^ n := card_cube n
  -- convert to the real inequality
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hkey : ∀ w ∈ S, ((1 : ℝ) / 2) ^ w.length = (2 ^ (n - w.length) : ℕ) / 2 ^ n := by
    intro w hw
    have h1 : w.length ≤ n := hle w hw
    have h2 : ((2 : ℝ) ^ (n - w.length)) * 2 ^ w.length = 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    push_cast
    rw [div_pow, one_pow]
    field_simp
    linarith [h2]
  rw [Finset.sum_congr rfl hkey, ← Finset.sum_div, div_le_one hpow]
  have : ((∑ w ∈ S, 2 ^ (n - w.length) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast hcount
  push_cast at this ⊢
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

