import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
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

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the reductions of the
elements of `H` modulo `p` do not cover all residue classes mod `p`.  This is exactly the
condition under which the singular series of the tuple `H` is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- `nu H p` is the number of residue classes mod `p` occupied by `H`. -/
def nu (H : Finset ℤ) (p : ℕ) : ℕ := (H.image (fun h : ℤ => (h : ZMod p))).card

/-- The local factor at `p` of the singular series of the tuple `H`, namely
`(1 - ν_p(H)/p) / (1 - 1/p)^{|H|}`. -/
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (nu H p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

/-- Admissibility is equivalent to `ν_p(H) < p` for every prime `p`. -/
theorem admissible_iff_nu_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → nu H p < p := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hrmem : r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
      simp only [Finset.mem_image, not_exists]
      rintro h ⟨hh, rfl⟩
      exact hr h hh rfl
    have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < Fintype.card (ZMod p) := by
      refine Finset.card_lt_card ?_
      refine ⟨Finset.subset_univ _, ?_⟩
      intro hsub
      exact hrmem (hsub (Finset.mem_univ r))
    simpa [nu, ZMod.card] using hlt
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < Fintype.card (ZMod p) := by
      simpa [nu, ZMod.card] using hH p hp
    have : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
      by_contra hcon
      push_neg at hcon
      have : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) :=
        fun r _ => hcon r
      have := Finset.card_le_card this
      simp only [Finset.card_univ] at this
      omega
    obtain ⟨r, hr⟩ := this
    refine ⟨r, ?_⟩
    intro h hh hcast
    exact hr (Finset.mem_image.2 ⟨h, hh, hcast⟩)

/-- Only the primes `p ≤ |H|` need to be checked for admissibility: a set can never cover all
residues modulo a prime larger than its cardinality. -/
theorem admissible_of_small_primes (H : Finset ℤ)
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r) :
    Admissible H := by
  intro p hp
  rcases le_or_gt p H.card with hle | hgt
  · exact h p hp hle
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
      have h1 : (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      have : Fintype.card (ZMod p) = p := ZMod.card p
      omega
    have : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) :=
        fun r _ => hcon r
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ] at this
      omega
    obtain ⟨r, hr⟩ := this
    exact ⟨r, fun x hx hcast => hr (Finset.mem_image.2 ⟨x, hx, hcast⟩)⟩

/-- Admissibility is invariant under translation of the tuple. -/
theorem Admissible.translate {H : Finset ℤ} (hH : Admissible H) (c : ℤ) :
    Admissible (H.image (fun x => x + c)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + (c : ZMod p), ?_⟩
  intro h hh
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
  intro hcast
  refine hr x hx ?_
  have : ((x : ZMod p)) + (c : ZMod p) = r + (c : ZMod p) := by
    simpa using hcast
  exact add_right_cancel this

/-- Every local factor of the singular series of an admissible tuple is strictly positive. -/
theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hnu : nu H p < p := (admissible_iff_nu_lt H).1 hH p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < p := by linarith
  have hnum : 0 < 1 - (nu H p : ℝ) / p := by
    have : (nu H p : ℝ) < p := by exact_mod_cast hnu
    have := (div_lt_one hppos).2 this
    linarith
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hppos]; linarith
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- The gap tuple based at `7280`: the shift by `7280` of the admissible pattern
`{0, 2, 6, 8, 12}`. -/
def gapSet7280 : Finset ℤ := {7280, 7282, 7286, 7288, 7292}

lemma card_gapSet7280 : gapSet7280.card = 5 := by decide

/-!
The main result: the gap range `{7280, 7282, 7286, 7288, 7292}` is an admissible `5`-tuple,
and consequently every local factor of its singular series is strictly positive (so the
singular series does not vanish, and the Hardy–Littlewood prime `k`-tuple conjecture predicts
infinitely many prime constellations with these gaps).
-/
theorem SingularSeriesGaps7280 :
    Admissible gapSet7280 ∧ ∀ p : ℕ, p.Prime → 0 < localFactor gapSet7280 p := by
  have hadm : Admissible gapSet7280 := by
    refine admissible_of_small_primes _ ?_
    intro p hp hple
    rw [card_gapSet7280] at hple
    interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨4, by decide⟩
  exact ⟨hadm, fun p hp => localFactor_pos hadm hp⟩

end Brockian

