/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

/-- A finite set of natural numbers is *admissible* when, for every prime `p`, its elements
omit at least one residue class modulo `p`.  This is exactly the classical condition under
which the singular series attached to the tuple is non-zero. -/
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- The *gap* (diameter) of a non-empty finite set of natural numbers. -/
def gap (H : Finset ℕ) (hne : H.Nonempty) : ℕ := H.max' hne - H.min' hne

/-- Any set with at most two elements omits a residue class modulo a prime `p ≥ 3`. -/
lemma exists_avoided_residue_of_two_lt {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (x y : ℕ) :
    ∃ a : ZMod p, (x : ZMod p) ≠ a ∧ (y : ZMod p) ≠ a := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hcard : ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)).card < Finset.univ.card := by
    have h1 : ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have h2 : (Finset.univ : Finset (ZMod p)).card = p := by
      simp [ZMod.card]
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨a, ?_, ?_⟩ <;> intro h <;> apply ha <;> simp [← h]

/-- Elements of an admissible set all have the same parity. -/
lemma modEq_two_of_admissible {H : Finset ℕ} (hH : IsAdmissible H) {x y : ℕ}
    (hx : x ∈ H) (hy : y ∈ H) : x ≡ y [MOD 2] := by
  obtain ⟨a, ha⟩ := hH 2 Nat.prime_two
  have key : ∀ a x y : ZMod 2, x ≠ a → y ≠ a → x = y := by decide
  have : (x : ZMod 2) = (y : ZMod 2) := key a _ _ (ha x hx) (ha y hy)
  exact (ZMod.natCast_eq_natCast_iff x y 2).mp this

/-- The two-element set `{0, d}` is admissible whenever `d` is even. -/
lemma isAdmissible_pair_of_even {d : ℕ} (hd : Even d) : IsAdmissible {0, d} := by
  intro p hp
  rcases eq_or_lt_of_le hp.two_le with h2 | h2
  · -- `p = 2`: both elements are even, so the residue `1` is omitted.
    subst h2
    refine ⟨1, ?_⟩
    intro h hh
    have hh2 : (2 : ℕ) ∣ h := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · exact dvd_zero 2
      · exact hd.two_dvd
    have : (h : ZMod 2) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd h 2).mpr hh2
    rw [this]
    decide
  · obtain ⟨a, ha0, had⟩ := exists_avoided_residue_of_two_lt hp h2 0 d
    refine ⟨a, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact ha0
    · exact had

/--
**Singular Series Gaps 1240–1250.**

For every gap value `d` in the range `1240 ≤ d ≤ 1250`, there exists an admissible tuple of
natural numbers of diameter exactly `d` — equivalently, a tuple whose singular series is
non-vanishing — if and only if `d` is even.  Thus the admissible gaps in this range are
exactly `1240, 1242, 1244, 1246, 1248, 1250`.
-/
theorem SingularSeriesGaps12401250 (d : ℕ) (hd : d ∈ Finset.Icc 1240 1250) :
    (∃ (H : Finset ℕ) (hne : H.Nonempty), IsAdmissible H ∧ gap H hne = d) ↔ Even d := by
  simp only [Finset.mem_Icc] at hd
  constructor
  · rintro ⟨H, hne, hH, hgap⟩
    have hmin : H.min' hne ∈ H := H.min'_mem hne
    have hmax : H.max' hne ∈ H := H.max'_mem hne
    have hle : H.min' hne ≤ H.max' hne := H.min'_le _ hmax
    have hmod : H.min' hne ≡ H.max' hne [MOD 2] := modEq_two_of_admissible hH hmin hmax
    have hdvd : 2 ∣ (H.max' hne - H.min' hne) := (Nat.modEq_iff_dvd' hle).mp hmod
    rw [gap] at hgap
    rw [← hgap]
    exact (even_iff_two_dvd).mpr hdvd
  · intro hde
    have hd0 : d ≠ 0 := by omega
    refine ⟨{0, d}, ⟨0, by simp⟩, isAdmissible_pair_of_even hde, ?_⟩
    have hmax : ({0, d} : Finset ℕ).max' ⟨0, by simp⟩ = d := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · omega
        · exact le_rfl
      · exact Finset.le_max' _ d (by simp)
    have hmin : ({0, d} : Finset ℕ).min' ⟨0, by simp⟩ = 0 := by
      apply le_antisymm
      · exact Finset.min'_le _ 0 (by simp)
      · exact Nat.zero_le _
    rw [gap, hmax, hmin]

end Brockian

