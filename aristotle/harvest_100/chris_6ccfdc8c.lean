/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of natural numbers `H` is *admissible* if for every prime `p` it misses at
least one residue class modulo `p`.  Equivalently (see `admissible_iff_localFactor_pos`), all
local factors of the associated singular series are strictly positive. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- The local factor `1 - |H mod p| / p` of the singular series attached to `H`. -/
def localFactor (H : Finset ℕ) (p : ℕ) : ℚ :=
  1 - ((H.image (· % p)).card : ℚ) / p

/-- A residue class modulo `p` is missed as soon as `H` has fewer than `p` elements. -/
lemma exists_missed_residue_of_card_lt {H : Finset ℕ} {p : ℕ} (h : H.card < p) :
    ∃ r < p, ∀ h' ∈ H, h' % p ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsub : Finset.range p ⊆ H.image (fun x => x % p) := by
    intro r hr
    simp only [Finset.mem_range] at hr
    obtain ⟨h', hh', he⟩ := hcon r hr
    exact Finset.mem_image.2 ⟨h', hh', he⟩
  have h1 : p ≤ (H.image (fun x => x % p)).card := by
    simpa using Finset.card_le_card hsub
  have h2 : (H.image (fun x => x % p)).card ≤ H.card := Finset.card_image_le
  omega

/-- Admissibility is exactly the positivity of all local factors of the singular series. -/
lemma admissible_iff_localFactor_pos (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → 0 < localFactor H p := by
  constructor
  · intro hH p hp
    obtain ⟨r, hrp, hr⟩ := hH p hp
    have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
    have hne : H.image (fun x => x % p) ≠ Finset.range p := by
      intro hEq
      have : r ∈ H.image (fun x => x % p) := by
        rw [hEq]; exact Finset.mem_range.2 hrp
      obtain ⟨h', hh', he⟩ := Finset.mem_image.1 this
      exact hr h' hh' he
    have hsub : H.image (fun x => x % p) ⊆ Finset.range p := by
      intro y hy
      obtain ⟨h', _, he⟩ := Finset.mem_image.1 hy
      exact Finset.mem_range.2 (he ▸ Nat.mod_lt _ hp.pos)
    have hlt : (H.image (fun x => x % p)).card < p := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
      simpa using this
    have : ((H.image (fun x => x % p)).card : ℚ) < p := by exact_mod_cast hlt
    have : ((H.image (fun x => x % p)).card : ℚ) / p < 1 := by
      rw [div_lt_one hppos]; exact this
    simp only [localFactor]
    linarith
  · intro hH p hp
    have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
    have := hH p hp
    simp only [localFactor] at this
    have hlt : ((H.image (fun x => x % p)).card : ℚ) < p := by
      have h1 : ((H.image (fun x => x % p)).card : ℚ) / p < 1 := by linarith
      rwa [div_lt_one hppos] at h1
    have hlt' : (H.image (fun x => x % p)).card < p := by exact_mod_cast hlt
    have hne : ¬ (Finset.range p ⊆ H.image (fun x => x % p)) := by
      intro hsub
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    rw [Finset.subset_iff] at hne
    push_neg at hne
    obtain ⟨r, hr, hr'⟩ := hne
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro h' hh' he
    exact hr' (Finset.mem_image.2 ⟨h', hh', he⟩)

/-- An explicit family of admissible triples `{0, a, d}`: only the primes `2` and `3` need to
be inspected, the remaining ones are handled by the pigeonhole principle. -/
lemma admissible_triple {a d r : ℕ} (ha2 : a % 2 = 0) (hd2 : d % 2 = 0)
    (hr : r < 3) (hr0 : 0 % 3 ≠ r) (hra : a % 3 ≠ r) (hrd : d % 3 ≠ r) :
    Admissible ({0, a, d} : Finset ℕ) := by
  have hcard : ({0, a, d} : Finset ℕ).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := Finset.card_insert_le a ({d} : Finset ℕ)
    simp at this ⊢
    omega
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1, by norm_num, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl <;> omega
  · by_cases hp3 : p = 3
    · subst hp3
      refine ⟨r, hr, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> assumption
    · have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
      have hp5 : 5 ≤ p := by
        have := hp.two_le
        omega
      exact exists_missed_residue_of_card_lt (lt_of_le_of_lt hcard (by omega))

/-- **Singular series gaps 1450–1460.**  For every gap length `d` in the range `1450 ≤ d ≤ 1460`
there is an admissible set of at least three elements contained in `[0, d]` with endpoints `0`
and `d` (i.e. of diameter exactly `d`) if and only if `d` is even.  The even gaps in this range
are therefore exactly `1450, 1452, 1454, 1456, 1458, 1460`. -/
theorem SingularSeriesGaps14501460 (d : ℕ) (hd : d ∈ Finset.Icc 1450 1460) :
    (∃ H : Finset ℕ, 0 ∈ H ∧ d ∈ H ∧ (∀ h ∈ H, h ≤ d) ∧ 3 ≤ H.card ∧ Admissible H) ↔ Even d := by
  simp only [Finset.mem_Icc] at hd
  constructor
  · rintro ⟨H, h0, hdH, -, -, hadm⟩
    obtain ⟨r, hr2, hr⟩ := hadm 2 Nat.prime_two
    have hr0 : r ≠ 0 := by
      intro h
      exact hr 0 h0 (by simp [h])
    have hr1 : r = 1 := by omega
    subst hr1
    have := hr d hdH
    exact Nat.even_iff.2 (by omega)
  · intro hev
    have hd2 : d % 2 = 0 := Nat.even_iff.1 hev
    -- choose `a = 4` when `d ≡ 1 [MOD 3]`, and `a = 2` otherwise
    by_cases h3 : d % 3 = 1
    · refine ⟨{0, 4, d}, by simp, by simp, ?_, ?_, ?_⟩
      · intro h hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with rfl | rfl | rfl <;> omega
      · have h1 : (0 : ℕ) ≠ 4 := by norm_num
        have h2 : (0 : ℕ) ≠ d := by omega
        have h3' : (4 : ℕ) ≠ d := by omega
        rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
          Finset.card_insert_of_notMem (by simp [h3']), Finset.card_singleton]
      · exact admissible_triple (a := 4) (r := 2) (by norm_num) hd2 (by norm_num)
          (by norm_num) (by norm_num) (by omega)
    · refine ⟨{0, 2, d}, by simp, by simp, ?_, ?_, ?_⟩
      · intro h hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with rfl | rfl | rfl <;> omega
      · have h1 : (0 : ℕ) ≠ 2 := by norm_num
        have h2 : (0 : ℕ) ≠ d := by omega
        have h3' : (2 : ℕ) ≠ d := by omega
        rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
          Finset.card_insert_of_notMem (by simp [h3']), Finset.card_singleton]
      · exact admissible_triple (a := 2) (r := 1) (by norm_num) hd2 (by norm_num)
          (by norm_num) (by norm_num) (by omega)

end Brockian

