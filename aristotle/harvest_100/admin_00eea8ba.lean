/-
# Singular Series Gaps 14501460 — Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps14501460.lean`.  The target theorem there is
stated in plain core Lean (its file has to start with a fixed header comment, which forbids
`import`s).  Here the same mathematical content is formalized in the idiomatic Mathlib way,
with tuples as `Finset ℤ`, primality as `Nat.Prime`, and residues in `ZMod p`.
-/

import Mathlib

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ H, (a : ZMod p) ≠ r

/-- A set with fewer than `p` elements cannot cover all residues modulo `p`. -/
theorem exists_missing_residue {p : ℕ} (hp : 0 < p) (H : Finset ℤ) (h : H.card < p) :
    ∃ r : ZMod p, ∀ a ∈ H, (a : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.ne'⟩
  by_contra hc
  push_neg at hc
  have himg : (H.image (fun a : ℤ => (a : ZMod p))) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro r
    obtain ⟨a, ha, hae⟩ := hc r
    exact Finset.mem_image.mpr ⟨a, ha, hae⟩
  have hcard := Finset.card_image_le (s := H) (f := fun a : ℤ => (a : ZMod p))
  rw [himg, Finset.card_univ, ZMod.card] at hcard
  omega

/-- The concrete four element tuple inside the gap range `[1450, 1460]`. -/
def gapSet : Finset ℤ := {1450, 1452, 1456, 1458}

theorem gapSet_subset : gapSet ⊆ Finset.Icc (1450 : ℤ) 1460 := by decide

theorem gapSet_card : gapSet.card = 4 := by decide

/-- `{1450, 1452, 1456, 1458}` is admissible: modulo `2` it misses the class of `1`, modulo
`3` it misses the class of `2`, and for every prime `p ≥ 5` it has too few elements to cover
all residues. -/
theorem gapSet_isAdmissible : IsAdmissible gapSet := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact ⟨1, by decide⟩
  by_cases h3 : p = 3
  · subst h3
    exact ⟨2, by decide⟩
  · have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have hp2 := hp.two_le
    refine exists_missing_residue (by omega) gapSet ?_
    rw [gapSet_card]
    omega

/-- Any admissible subset of the window `[1450, 1460]` has at most four elements: modulo `2`
and modulo `3` it must avoid one class each, and the surviving residues modulo `6` occur at
most twice among eleven consecutive integers. -/
theorem card_le_four_of_isAdmissible (H : Finset ℤ) (hsub : H ⊆ Finset.Icc (1450 : ℤ) 1460)
    (hadm : IsAdmissible H) : H.card ≤ 4 := by
  obtain ⟨r2, h2⟩ := hadm 2 Nat.prime_two
  obtain ⟨r3, h3⟩ := hadm 3 Nat.prime_three
  have key : H ⊆ (Finset.Icc (1450 : ℤ) 1460).filter
      (fun a : ℤ => ((a : ZMod 2) ≠ r2 ∧ (a : ZMod 3) ≠ r3)) := fun a ha =>
    Finset.mem_filter.mpr ⟨hsub ha, h2 a ha, h3 a ha⟩
  refine le_trans (Finset.card_le_card key) ?_
  have huniv : ∀ s2 : ZMod 2, ∀ s3 : ZMod 3, ((Finset.Icc (1450 : ℤ) 1460).filter
      (fun a : ℤ => ((a : ZMod 2) ≠ s2 ∧ (a : ZMod 3) ≠ s3))).card ≤ 4 := by decide
  exact huniv r2 r3

/-- **Singular series gaps 14501460 (Mathlib formulation).**

Inside the window `[1450, 1460]` there is an admissible tuple with four elements, and every
admissible tuple contained in that window has at most four elements; so the largest
admissible tuple in this gap range has exactly four elements. -/
theorem singularSeriesGaps14501460_mathlib :
    (∃ H : Finset ℤ, H ⊆ Finset.Icc (1450 : ℤ) 1460 ∧ IsAdmissible H ∧ H.card = 4) ∧
    (∀ H : Finset ℤ, H ⊆ Finset.Icc (1450 : ℤ) 1460 → IsAdmissible H → H.card ≤ 4) :=
  ⟨⟨gapSet, gapSet_subset, gapSet_isAdmissible, gapSet_card⟩, card_le_four_of_isAdmissible⟩

end Brockian

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-! ## Basic notions

Everything below is developed from first principles (no external library is imported, so
that this file can start with the header comment above).
-/

/-- `IsPrime p` says that `p` is a prime natural number. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- A finite tuple `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the members of `H` fail to occupy
every residue class modulo `p`; equivalently, the singular series attached to `H` does not
vanish. -/
def Admissible (H : List Int) : Prop :=
  ∀ p : Nat, IsPrime p → ∃ r : Int, ∀ a ∈ H, a % (p : Int) ≠ r % (p : Int)

/-- The candidate tuple inside the gap range `[1450, 1460]`. -/
def gapTuple : List Int := [1450, 1452, 1456, 1458]

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, fun m hm => ?_⟩
  have h1 : m ≤ 2 := Nat.le_of_dvd (by omega) hm
  have h2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases h2 with rfl | rfl | rfl
  · exact absurd hm (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, fun m hm => ?_⟩
  have h1 : m ≤ 3 := Nat.le_of_dvd (by omega) hm
  have h2 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases h2 with rfl | rfl | rfl | rfl
  · exact absurd hm (by decide)
  · exact Or.inl rfl
  · exact absurd hm (by decide)
  · exact Or.inr rfl

/-- A prime other than `2` and `3` is at least `5`. -/
theorem five_le_of_prime {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  have h4 : p ≠ 4 := by
    intro h
    rcases hp.2 2 (by omega : (2 : Nat) ∣ p) with h' | h' <;> omega
  have := hp.1
  omega

/-! ## The tuple `{1450, 1452, 1456, 1458}` is admissible -/

/-- Among the five values `0, 1, 2, 3, 4` at least one avoids any four prescribed integers. -/
theorem exists_small_avoiding (x1 x2 x3 x4 : Int) :
    ∃ r : Int, 0 ≤ r ∧ r < 5 ∧ x1 ≠ r ∧ x2 ≠ r ∧ x3 ≠ r ∧ x4 ≠ r := by
  by_cases h0 : x1 ≠ 0 ∧ x2 ≠ 0 ∧ x3 ≠ 0 ∧ x4 ≠ 0
  · exact ⟨0, by omega⟩
  by_cases h1 : x1 ≠ 1 ∧ x2 ≠ 1 ∧ x3 ≠ 1 ∧ x4 ≠ 1
  · exact ⟨1, by omega⟩
  by_cases h2 : x1 ≠ 2 ∧ x2 ≠ 2 ∧ x3 ≠ 2 ∧ x4 ≠ 2
  · exact ⟨2, by omega⟩
  by_cases h3 : x1 ≠ 3 ∧ x2 ≠ 3 ∧ x3 ≠ 3 ∧ x4 ≠ 3
  · exact ⟨3, by omega⟩
  by_cases h4 : x1 ≠ 4 ∧ x2 ≠ 4 ∧ x3 ≠ 4 ∧ x4 ≠ 4
  · exact ⟨4, by omega⟩
  · exact ((by omega : False)).elim

/-- Four integers cannot meet every residue class modulo a modulus `p ≥ 5`. -/
theorem exists_residue_of_five_le (p : Int) (hp : 5 ≤ p) (a1 a2 a3 a4 : Int) :
    ∃ r : Int, ∀ a ∈ [a1, a2, a3, a4], a % p ≠ r % p := by
  obtain ⟨r, hr0, hr5, h1, h2, h3, h4⟩ :=
    exists_small_avoiding (a1 % p) (a2 % p) (a3 % p) (a4 % p)
  refine ⟨r, ?_⟩
  have hrp : r % p = r := Int.emod_eq_of_lt hr0 (by omega)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> rw [hrp] <;> assumption

/-- The tuple `{1450, 1452, 1456, 1458}` is admissible: modulo `2` and modulo `3` it misses
the class of `1451`, and for every prime `p ≥ 5` it is too short to cover all classes. -/
theorem gapTuple_admissible : Admissible gapTuple := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact ⟨1451, by decide⟩
  by_cases h3 : p = 3
  · subst h3
    exact ⟨1451, by decide⟩
  · have h5 : (5 : Int) ≤ (p : Int) := by
      have := five_le_of_prime hp h2 h3
      omega
    exact exists_residue_of_five_le (p : Int) h5 1450 1452 1456 1458

theorem gapTuple_length : gapTuple.length = 4 := rfl

theorem gapTuple_mem_range : ∀ a ∈ gapTuple, 1450 ≤ a ∧ a ≤ 1460 := by decide

theorem gapTuple_nodup : gapTuple.Nodup := by decide

/-! ## No admissible five element tuple fits in the range -/

set_option maxHeartbeats 2000000 in
/-- Five distinct integers cannot all lie in a set of four values. -/
theorem five_in_four {a b c d e v1 v2 v3 v4 : Int}
    (ha : a = v1 ∨ a = v2 ∨ a = v3 ∨ a = v4)
    (hb : b = v1 ∨ b = v2 ∨ b = v3 ∨ b = v4)
    (hc : c = v1 ∨ c = v2 ∨ c = v3 ∨ c = v4)
    (hd : d = v1 ∨ d = v2 ∨ d = v3 ∨ d = v4)
    (he : e = v1 ∨ e = v2 ∨ e = v3 ∨ e = v4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : False := by
  omega

theorem win_00 (x : Int) (h1 : 1450 ≤ x) (h2 : x ≤ 1460) (h3 : x % 2 ≠ 0) (h4 : x % 3 ≠ 0) :
    x = 1451 ∨ x = 1453 ∨ x = 1457 ∨ x = 1459 := by omega

theorem win_01 (x : Int) (h1 : 1450 ≤ x) (h2 : x ≤ 1460) (h3 : x % 2 ≠ 0) (h4 : x % 3 ≠ 1) :
    x = 1451 ∨ x = 1455 ∨ x = 1457 ∨ x = 1457 := by omega

theorem win_02 (x : Int) (h1 : 1450 ≤ x) (h2 : x ≤ 1460) (h3 : x % 2 ≠ 0) (h4 : x % 3 ≠ 2) :
    x = 1453 ∨ x = 1455 ∨ x = 1459 ∨ x = 1459 := by omega

theorem win_10 (x : Int) (h1 : 1450 ≤ x) (h2 : x ≤ 1460) (h3 : x % 2 ≠ 1) (h4 : x % 3 ≠ 0) :
    x = 1450 ∨ x = 1454 ∨ x = 1456 ∨ x = 1460 := by omega

theorem win_11 (x : Int) (h1 : 1450 ≤ x) (h2 : x ≤ 1460) (h3 : x % 2 ≠ 1) (h4 : x % 3 ≠ 1) :
    x = 1452 ∨ x = 1454 ∨ x = 1458 ∨ x = 1460 := by omega

theorem win_12 (x : Int) (h1 : 1450 ≤ x) (h2 : x ≤ 1460) (h3 : x % 2 ≠ 1) (h4 : x % 3 ≠ 2) :
    x = 1450 ∨ x = 1452 ∨ x = 1456 ∨ x = 1458 := by omega

/-- No admissible tuple of five distinct integers fits inside the range `[1450, 1460]`. -/
theorem not_admissible_five (a b c d e : Int)
    (ha : 1450 ≤ a ∧ a ≤ 1460) (hb : 1450 ≤ b ∧ b ≤ 1460) (hc : 1450 ≤ c ∧ c ≤ 1460)
    (hd : 1450 ≤ d ∧ d ≤ 1460) (he : 1450 ≤ e ∧ e ≤ 1460)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ¬ Admissible [a, b, c, d, e] := by
  intro hadm
  obtain ⟨r2, h2⟩ := hadm 2 isPrime_two
  obtain ⟨r3, h3⟩ := hadm 3 isPrime_three
  have ha2 : a % (2 : Int) ≠ r2 % (2 : Int) := h2 a (by simp)
  have hb2 : b % (2 : Int) ≠ r2 % (2 : Int) := h2 b (by simp)
  have hc2 : c % (2 : Int) ≠ r2 % (2 : Int) := h2 c (by simp)
  have hd2 : d % (2 : Int) ≠ r2 % (2 : Int) := h2 d (by simp)
  have he2 : e % (2 : Int) ≠ r2 % (2 : Int) := h2 e (by simp)
  have ha3 : a % (3 : Int) ≠ r3 % (3 : Int) := h3 a (by simp)
  have hb3 : b % (3 : Int) ≠ r3 % (3 : Int) := h3 b (by simp)
  have hc3 : c % (3 : Int) ≠ r3 % (3 : Int) := h3 c (by simp)
  have hd3 : d % (3 : Int) ≠ r3 % (3 : Int) := h3 d (by simp)
  have he3 : e % (3 : Int) ≠ r3 % (3 : Int) := h3 e (by simp)
  have hr2 : r2 % (2 : Int) = 0 ∨ r2 % (2 : Int) = 1 := by omega
  have hr3 : r3 % (3 : Int) = 0 ∨ r3 % (3 : Int) = 1 ∨ r3 % (3 : Int) = 2 := by omega
  rcases hr2 with h | h <;> rw [h] at ha2 hb2 hc2 hd2 he2 <;>
    rcases hr3 with h' | h' | h' <;> rw [h'] at ha3 hb3 hc3 hd3 he3
  · exact five_in_four (win_00 a ha.1 ha.2 ha2 ha3) (win_00 b hb.1 hb.2 hb2 hb3)
      (win_00 c hc.1 hc.2 hc2 hc3) (win_00 d hd.1 hd.2 hd2 hd3) (win_00 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_01 a ha.1 ha.2 ha2 ha3) (win_01 b hb.1 hb.2 hb2 hb3)
      (win_01 c hc.1 hc.2 hc2 hc3) (win_01 d hd.1 hd.2 hd2 hd3) (win_01 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_02 a ha.1 ha.2 ha2 ha3) (win_02 b hb.1 hb.2 hb2 hb3)
      (win_02 c hc.1 hc.2 hc2 hc3) (win_02 d hd.1 hd.2 hd2 hd3) (win_02 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_10 a ha.1 ha.2 ha2 ha3) (win_10 b hb.1 hb.2 hb2 hb3)
      (win_10 c hc.1 hc.2 hc2 hc3) (win_10 d hd.1 hd.2 hd2 hd3) (win_10 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_11 a ha.1 ha.2 ha2 ha3) (win_11 b hb.1 hb.2 hb2 hb3)
      (win_11 c hc.1 hc.2 hc2 hc3) (win_11 d hd.1 hd.2 hd2 hd3) (win_11 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_12 a ha.1 ha.2 ha2 ha3) (win_12 b hb.1 hb.2 hb2 hb3)
      (win_12 c hc.1 hc.2 hc2 hc3) (win_12 d hd.1 hd.2 hd2 hd3) (win_12 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde

/-! ## Main result -/

/-- **Singular series gaps 14501460.**

Inside the gap range `[1450, 1460]` the tuple `{1450, 1452, 1456, 1458}` is admissible — it
consists of four distinct integers of the range whose singular series is nonzero — while no
five distinct integers of that range form an admissible tuple.  Hence the maximal size of an
admissible tuple in the window `[1450, 1460]` is exactly `4`. -/
theorem SingularSeriesGaps14501460 :
    (Admissible gapTuple ∧ gapTuple.Nodup ∧ gapTuple.length = 4 ∧
      ∀ a ∈ gapTuple, 1450 ≤ a ∧ a ≤ 1460) ∧
    (∀ a b c d e : Int,
      (1450 ≤ a ∧ a ≤ 1460) → (1450 ≤ b ∧ b ≤ 1460) → (1450 ≤ c ∧ c ≤ 1460) →
      (1450 ≤ d ∧ d ≤ 1460) → (1450 ≤ e ∧ e ≤ 1460) →
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      ¬ Admissible [a, b, c, d, e]) :=
  ⟨⟨gapTuple_admissible, gapTuple_nodup, gapTuple_length, gapTuple_mem_range⟩,
   not_admissible_five⟩

end Brockian

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

