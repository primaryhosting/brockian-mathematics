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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of integer offsets `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the reductions
of the elements of `H` modulo `p` miss at least one residue class.  This is exactly
the condition under which the singular series `𝔖(H)` is nonzero. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- If a set of offsets has fewer elements than `p`, it cannot cover all residues mod `p`. -/
theorem exists_missed_residue_of_card_lt {H : Finset ℤ} {p : ℕ} [NeZero p]
    (h : H.card < p) : ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  classical
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hc r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have hcard : (Finset.univ : Finset (ZMod p)).card ≤ H.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  rw [Finset.card_univ, ZMod.card p] at hcard
  omega

/-- A pair `{0, g}` with `g` even is admissible. -/
theorem isAdmissible_pair_of_even {g : ℤ} (hg : Even g) : IsAdmissible {0, g} := by
  classical
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    have hg2 : (g : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd g 2).mpr (by exact_mod_cast hg.two_dvd)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · simp
    · rw [hg2]
      exact zero_ne_one
  · haveI : Fact p.Prime := ⟨hp⟩
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hcard : ({0, g} : Finset ℤ).card < p :=
      lt_of_le_of_lt (Finset.card_insert_le _ _) (by
        simpa using lt_of_le_of_lt (by simp : (Finset.card {g} : ℕ) + 1 ≤ 2) (by omega))
    exact exists_missed_residue_of_card_lt hcard

/-- A pair `{0, g}` with `g` odd is not admissible: modulo `2` the two offsets already
cover both residue classes. -/
theorem not_isAdmissible_pair_of_odd {g : ℤ} (hg : Odd g) : ¬ IsAdmissible {0, g} := by
  intro h
  obtain ⟨r, hr⟩ := h 2 Nat.prime_two
  have h0 : (0 : ZMod 2) ≠ r := hr 0 (by simp)
  have hg2 : (g : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hg
    subst hk
    have h2 : (2 : ZMod 2) = 0 := by decide
    push_cast
    rw [h2]
    ring
  have h1 : (1 : ZMod 2) ≠ r := by
    have := hr g (by simp)
    rwa [hg2] at this
  have key : ∀ s : ZMod 2, (0 : ZMod 2) ≠ s → (1 : ZMod 2) ≠ s → False := by decide
  exact key r h0 h1

/-- **Singular series gaps in the range `[1450, 1460]`.**
For every integer gap `g` with `1450 ≤ g ≤ 1460`, the pair of offsets `{0, g}` is
admissible — equivalently, the singular series for this pair is nonzero — precisely
when `g` is even.  Thus the admissible gaps in this range are exactly
`1450, 1452, 1454, 1456, 1458, 1460`.

The bounds `1450 ≤ g ≤ 1460` are stated as requested; the equivalence in fact holds for
every integer gap `g`, as the proof (via `isAdmissible_pair_of_even` and
`not_isAdmissible_pair_of_odd`) shows. -/
theorem SingularSeriesGaps14501460 :
    ∀ g : ℤ, 1450 ≤ g → g ≤ 1460 → (IsAdmissible {0, g} ↔ Even g) := by
  intro g _ _
  constructor
  · intro h
    rcases Int.even_or_odd g with he | ho
    · exact he
    · exact absurd h (not_isAdmissible_pair_of_odd ho)
  · exact isAdmissible_pair_of_even

end Brockian

