/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when for every prime `p` the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- A set with fewer than `p` elements can never cover all residues modulo `p`.
(Pigeonhole, via `Finset.card_image_le` and `ZMod.card`.) -/
theorem exists_missed_residue_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (h : H.card < p) : ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
    calc (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := h
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
  have hne : (H.image (fun x : ℤ => (x : ZMod p))) ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  rw [Ne, Finset.eq_univ_iff_forall] at hne
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  exact ⟨r, fun x hx hxr => hr (Finset.mem_image.mpr ⟨x, hx, hxr⟩)⟩

/-- An even integer reduces to `0` modulo `2`
(`ZMod.intCast_zmod_eq_zero_iff_dvd`). -/
theorem intCast_zmod_two_eq_zero_of_even {d : ℤ} (hd : Even d) : ((d : ℤ) : ZMod 2) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast hd.two_dvd

/-- Every even gap gives an admissible pair `{0, d}`. -/
theorem admissible_pair_of_even {d : ℤ} (hd : Even d) : Admissible {0, d} := by
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · decide
    · rw [intCast_zmod_two_eq_zero_of_even hd]
      decide
  · refine exists_missed_residue_of_card_lt hp ?_
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hc : ({0, d} : Finset ℤ).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega

/-- The triple `{0, 1350, 1360}` is admissible: modulo `2` all three entries are even
(so the class `1` is missed), modulo `3` the entries occupy the classes `{0, 1}`
(so the class `2` is missed), and for every prime `p ≥ 5` the triple is too small to
cover all residues. -/
theorem admissible_triple_1350_1360 : Admissible {0, 1350, 1360} := by
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl <;> decide
  · rcases eq_or_ne p 3 with rfl | hp3
    · refine ⟨2, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> decide
    · refine exists_missed_residue_of_card_lt hp ?_
      have h5 : 5 ≤ p := by
        have h2 := hp.two_le
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p
          · omega
          · omega
          · exact absurd hp (by norm_num)
        · exact h
      have hc : ({0, 1350, 1360} : Finset ℤ).card ≤ 3 := by
        refine (Finset.card_insert_le _ _).trans ?_
        have h1 := Finset.card_insert_le (1350 : ℤ) ({1360} : Finset ℤ)
        simp only [Finset.card_singleton] at h1
        omega
      omega

/-- **Singular Series Gaps 13501360.**

New admissible gap ranges extending the `SingularSeriesGaps` family: every even gap `d`
in the range `1350 ≤ d ≤ 1360` yields an admissible pair `{0, d}`, and moreover the
triple `{0, 1350, 1360}` spanning the whole range is itself admissible.  Consequently
each of these configurations has nonvanishing singular series, so none is excluded by a
local (congruence) obstruction. -/
theorem SingularSeriesGaps13501360 :
    (∀ d : ℤ, 1350 ≤ d → d ≤ 1360 → Even d → Admissible {0, d}) ∧
      Admissible {0, 1350, 1360} :=
  ⟨fun _ _ _ hd => admissible_pair_of_even hd, admissible_triple_1350_1360⟩

end Brockian


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

