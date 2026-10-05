/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-! ## Admissible tuples and the Hardy–Littlewood singular series

A finite set `H` of nonnegative integers is *admissible* if for every prime `p` the
elements of `H` do not cover all residue classes modulo `p`.  Equivalently, every local
factor of the Hardy–Littlewood singular series attached to `H` is positive.

The main result `Brockian.SingularSeriesGaps16021610` determines exactly which `d` in the
range `1602 ≤ d ≤ 1610` occur as the diameter of a (large) admissible tuple: precisely the
even ones, and for each of those we exhibit an explicit admissible tuple with at least
`145` elements whose smallest element is `0` and whose largest element is `d`.
-/

/-- `H` is an admissible tuple: for each prime `p` some residue class mod `p` is missed. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ x ∈ H, x % p ≠ r

/-- The local factor at `p` of the Hardy–Littlewood singular series of the tuple `H`,
namely `(1 - ν_H(p)/p) * (1 - 1/p)^(-|H|)` where `ν_H(p)` is the number of residue
classes mod `p` occupied by `H`. -/
noncomputable def singularSeriesFactor (H : Finset ℕ) (p : ℕ) : ℝ :=
  (1 - ((H.image (fun x => x % p)).card : ℝ) / (p : ℝ)) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- If `H` has fewer than `p` elements then some residue class mod `p` is missed. -/
lemma exists_missing_residue (H : Finset ℕ) (p : ℕ) (h : H.card < p) :
    ∃ r < p, ∀ x ∈ H, x % p ≠ r := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le _) h
  have hsub : H.image (fun x => x % p) ⊆ Finset.range p := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨x, _, rfl⟩ := hr
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  have hcard : (H.image (fun x => x % p)).card < (Finset.range p).card := by
    have := Finset.card_image_le (s := H) (f := fun x => x % p)
    simpa using lt_of_le_of_lt this h
  obtain ⟨r, hr, hr'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  intro x hx hxr
  exact hr' (Finset.mem_image.mpr ⟨x, hx, hxr⟩)

/-- The number of residues occupied by an admissible tuple mod a prime `p` is `< p`. -/
lemma card_image_mod_lt (H : Finset ℕ) (hH : Admissible H) (p : ℕ) (hp : p.Prime) :
    (H.image (fun x => x % p)).card < p := by
  obtain ⟨r, hrp, hr⟩ := hH p hp
  have hsub : H.image (fun x => x % p) ⊆ (Finset.range p).erase r := by
    intro s hs
    simp only [Finset.mem_image] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact Finset.mem_erase.mpr ⟨hr x hx, Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)⟩
  calc (H.image (fun x => x % p)).card ≤ ((Finset.range p).erase r).card :=
        Finset.card_le_card hsub
    _ < (Finset.range p).card := Finset.card_erase_lt_of_mem (Finset.mem_range.mpr hrp)
    _ = p := Finset.card_range p

/-- Every local factor of the singular series of an admissible tuple is positive. -/
theorem singularSeriesFactor_pos (H : Finset ℕ) (hH : Admissible H) (p : ℕ) (hp : p.Prime) :
    0 < singularSeriesFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : 0 < 1 - ((H.image (fun x => x % p)).card : ℝ) / (p : ℝ) := by
    have := card_image_mod_lt H hH p hp
    have : ((H.image (fun x => x % p)).card : ℝ) < (p : ℝ) := by exact_mod_cast this
    rw [sub_pos, div_lt_one hppos]
    exact this
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one hppos]
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-! ### An explicit family of admissible tuples -/

/-- The odd primes below `212`, used as sieving primes. -/
def sievePrimes : List ℕ := (List.range 212).filter (fun p => Nat.Prime p ∧ p % 2 = 1)

/-- The residue class mod `p` that the tuple of diameter `d` avoids; it is chosen to be
different from both `0` and `d % p`. -/
def avoid (d p : ℕ) : ℕ := if d % p = 1 then 2 else 1

/-- The explicit tuple of diameter `d`: the even numbers in `[0, d]` avoiding the residue
class `avoid d p` for every odd sieving prime `p`. -/
def tuple (d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun x => x % 2 = 0 ∧ ∀ p ∈ sievePrimes, x % p ≠ avoid d p)

lemma mem_tuple_iff (d x : ℕ) :
    x ∈ tuple d ↔ x < d + 1 ∧ x % 2 = 0 ∧ ∀ p ∈ sievePrimes, x % p ≠ avoid d p := by
  simp [tuple, Finset.mem_filter, Finset.mem_range]

lemma avoid_pos (d p : ℕ) : 0 < avoid d p := by
  unfold avoid; split <;> norm_num

lemma avoid_le_two (d p : ℕ) : avoid d p ≤ 2 := by
  unfold avoid; split <;> norm_num

lemma avoid_ne_self (d p : ℕ) : d % p ≠ avoid d p := by
  unfold avoid; split <;> omega

lemma mem_sievePrimes_iff (p : ℕ) : p ∈ sievePrimes ↔ p < 212 ∧ p.Prime ∧ p % 2 = 1 := by
  simp [sievePrimes, List.mem_filter, List.mem_range]

lemma zero_mem_tuple (d : ℕ) : 0 ∈ tuple d := by
  refine (mem_tuple_iff d 0).mpr ⟨by omega, by norm_num, ?_⟩
  intro p _
  simpa using (avoid_pos d p).ne

lemma self_mem_tuple (d : ℕ) (hd : d % 2 = 0) : d ∈ tuple d := by
  exact (mem_tuple_iff d d).mpr ⟨by omega, hd, fun p _ => avoid_ne_self d p⟩

lemma tuple_le (d x : ℕ) (hx : x ∈ tuple d) : x ≤ d := by
  have := (mem_tuple_iff d x).mp hx
  omega

/-- The explicit tuple is admissible as soon as it has at most `211` elements. -/
lemma tuple_admissible (d : ℕ) (hcard : (tuple d).card ≤ 211) : Admissible (tuple d) := by
  intro p hp
  rcases hp.eq_two_or_odd with hp2 | hodd
  · subst hp2
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    have := (mem_tuple_iff d x).mp hx
    omega
  · by_cases hlt : p < 212
    · have hmem : p ∈ sievePrimes := (mem_sievePrimes_iff p).mpr ⟨hlt, hp, hodd⟩
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      refine ⟨avoid d p, by have := avoid_le_two d p; omega, ?_⟩
      intro x hx
      exact ((mem_tuple_iff d x).mp hx).2.2 p hmem
    · exact exists_missing_residue _ _ (by omega)

/-! ### The main theorem -/

/-- **Admissible gap range `1602–1610`.**  For `1602 ≤ d ≤ 1610`, there is an admissible
tuple with at least `145` elements, smallest element `0` and largest element `d` (so of
diameter exactly `d`), all of whose singular series local factors are positive, **iff**
`d` is even.  In particular each of `d = 1602, 1604, 1606, 1608, 1610` is realised as the
diameter of such a tuple, and no odd `d` in this range is. -/
theorem SingularSeriesGaps16021610 (d : ℕ) (hd₁ : 1602 ≤ d) (hd₂ : d ≤ 1610) :
    (∃ H : Finset ℕ, Admissible H ∧ 145 ≤ H.card ∧ 0 ∈ H ∧ d ∈ H ∧ (∀ x ∈ H, x ≤ d) ∧
      ∀ p : ℕ, p.Prime → 0 < singularSeriesFactor H p) ↔ Even d := by
  constructor
  · rintro ⟨H, hadm, -, h0, hd, -, -⟩
    obtain ⟨r, hr2, hr⟩ := hadm 2 Nat.prime_two
    have h0' := hr 0 h0
    have hd' := hr d hd
    have hdd : d % 2 = 0 := by omega
    exact Nat.even_iff.mpr hdd
  · intro heven
    have hd2 : d % 2 = 0 := Nat.even_iff.mp heven
    have key : ∀ e : ℕ, 145 ≤ (tuple e).card → (tuple e).card ≤ 211 → e % 2 = 0 →
        (∃ H : Finset ℕ, Admissible H ∧ 145 ≤ H.card ∧ 0 ∈ H ∧ e ∈ H ∧ (∀ x ∈ H, x ≤ e) ∧
          ∀ p : ℕ, p.Prime → 0 < singularSeriesFactor H p) := by
      intro e h1 h2 h3
      have hadm := tuple_admissible e h2
      exact ⟨tuple e, hadm, h1, zero_mem_tuple e, self_mem_tuple e h3,
        tuple_le e, fun p hp => singularSeriesFactor_pos _ hadm p hp⟩
    interval_cases d
    · exact key 1602 (by decide) (by decide) (by norm_num)
    · omega
    · exact key 1604 (by decide) (by decide) (by norm_num)
    · omega
    · exact key 1606 (by decide) (by decide) (by norm_num)
    · omega
    · exact key 1608 (by decide) (by decide) (by norm_num)
    · omega
    · exact key 1610 (by decide) (by decide) (by norm_num)

end Brockian

