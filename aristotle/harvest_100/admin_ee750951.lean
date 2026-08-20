/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture: its singular series is nonzero) when,
for every prime `p`, the elements of the set miss at least one residue class mod `p`. -/
def Admissible (B : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ b ∈ B, b % p ≠ r

/-- A set of size smaller than `p` cannot cover all residue classes mod `p`. -/
theorem exists_missing_residue_of_card_lt (B : Finset ℕ) (p : ℕ) (h : B.card < p) :
    ∃ r : ℕ, r < p ∧ ∀ b ∈ B, b % p ≠ r := by
  by_contra hcon
  push_neg at hcon
  -- every residue in `Finset.range p` is attained by `B`
  have hsub : Finset.range p ⊆ B.image (· % p) := by
    intro r hr
    rw [Finset.mem_range] at hr
    obtain ⟨b, hb, hbr⟩ := hcon r hr
    exact Finset.mem_image.mpr ⟨b, hb, hbr⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact absurd (this.trans (Finset.card_image_le)) (by omega)

/-- Admissibility is invariant under translation. -/
theorem admissible_image_add {B : Finset ℕ} (hB : Admissible B) (t : ℕ) :
    Admissible (B.image (· + t)) := by
  intro p hp
  obtain ⟨r, hrp, hr⟩ := hB p hp
  refine ⟨(r + t) % p, Nat.mod_lt _ hp.pos, ?_⟩
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
  intro hEq
  have hcr : c % p = r % p := Nat.ModEq.add_right_cancel' t hEq
  exact hr c hc (by rw [hcr, Nat.mod_eq_of_lt hrp])

/-- The dense `9`-tuple pattern `{0, 2, 6, 8, 12, 18, 20, 26, 30}`: nine offsets of
diameter `30`. -/
def pattern9098 : Finset ℕ := {0, 2, 6, 8, 12, 18, 20, 26, 30}

theorem card_pattern9098 : pattern9098.card = 9 := by decide

theorem admissible_pattern9098 : Admissible pattern9098 := by
  intro p hp
  by_cases hbig : 9 < p
  · exact exists_missing_residue_of_card_lt _ _ (by rw [card_pattern9098]; omega)
  · push_neg at hbig
    have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, by norm_num, by decide⟩
    · exact ⟨1, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨4, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨3, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)

/-- **Singular Series Gaps 9098.**  Every translate `{t, t+2, t+6, t+8, t+12, t+18,
t+20, t+26, t+30}` of the nine-element gap pattern of diameter `30` is admissible:
for every prime `p` some residue class mod `p` is missed.  Consequently the
associated singular series is nonzero, so this whole family of gap ranges is
conjecturally realised by infinitely many prime constellations. -/
theorem SingularSeriesGaps9098 (t : ℕ) : Admissible (pattern9098.image (· + t)) :=
  admissible_image_add admissible_pattern9098 t

/-- Admissibility is a *finite* condition: only the primes `p ≤ |B|` need to be checked. -/
theorem admissible_iff_small_primes (B : Finset ℕ) :
    Admissible B ↔ ∀ p : ℕ, p.Prime → p ≤ B.card → ∃ r : ℕ, r < p ∧ ∀ b ∈ B, b % p ≠ r := by
  refine ⟨fun h p hp _ => h p hp, fun h p hp => ?_⟩
  by_cases hle : p ≤ B.card
  · exact h p hp hle
  · exact exists_missing_residue_of_card_lt B p (by omega)

/-- Admissibility passes to subsets. -/
theorem admissible_subset {B C : Finset ℕ} (hB : Admissible B) (hCB : C ⊆ B) :
    Admissible C := by
  intro p hp
  obtain ⟨r, hrp, hr⟩ := hB p hp
  exact ⟨r, hrp, fun b hb => hr b (hCB hb)⟩

/-- Not every gap range is admissible: `{0, 2, 4}` covers all residues mod `3`. -/
theorem not_admissible_zero_two_four : ¬ Admissible ({0, 2, 4} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr3, hr⟩ := h 3 (by norm_num)
  interval_cases r
  · exact hr 0 (by decide) rfl
  · exact hr 4 (by decide) rfl
  · exact hr 2 (by decide) rfl

/-- Extending the family: the ten-element pattern `{0, 2, 6, 8, 12, 18, 20, 26, 30, 32}`
of diameter `32`. -/
def pattern9098ext : Finset ℕ := {0, 2, 6, 8, 12, 18, 20, 26, 30, 32}

theorem card_pattern9098ext : pattern9098ext.card = 10 := by decide

theorem admissible_pattern9098ext : Admissible pattern9098ext := by
  intro p hp
  by_cases hbig : 10 < p
  · exact exists_missing_residue_of_card_lt _ _ (by rw [card_pattern9098ext]; omega)
  · push_neg at hbig
    have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, by norm_num, by decide⟩
    · exact ⟨1, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨4, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨3, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)

/-- **Singular Series Gaps 9098, extended family.**  Every translate of the ten-element
gap pattern of diameter `32` is admissible, and it contains the nine-element pattern,
so the whole family of gap ranges obtained by translating either pattern has nonzero
singular series. -/
theorem SingularSeriesGaps9098_family (t : ℕ) :
    Admissible (pattern9098ext.image (· + t)) ∧
      pattern9098 ⊆ pattern9098ext ∧
      Admissible (pattern9098.image (· + t)) :=
  ⟨admissible_image_add admissible_pattern9098ext t, by decide,
    SingularSeriesGaps9098 t⟩

end Brockian

