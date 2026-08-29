/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of integers `H` (a *pattern*, or *gap tuple*) is **admissible** when for every
prime `p` the reductions of the elements of `H` modulo `p` miss at least one residue class.
This is exactly the condition under which every local factor `1 - ν_p(H)/p` of the
Hardy–Littlewood singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` is nonzero. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- Pigeonhole: at a prime larger than the size of the pattern some residue class is missed. -/
theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hhr⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
  rw [Finset.card_univ, ZMod.card] at h1
  omega

/-- The local condition at `p = 2` for a pair `{0, g}`: the pair misses a residue class
modulo `2` exactly when the gap `g` is even. -/
theorem pair_local_two (g : ℤ) :
    (∃ r : ZMod 2, ∀ h ∈ ({0, g} : Finset ℤ), (h : ZMod 2) ≠ r) ↔ Even g := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hcast : ((g : ℤ) : ZMod 2) = 0 ↔ Even g := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.even_iff]
    push_cast
    omega
  constructor
  · rintro ⟨r, hr⟩
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
    have h1 : ((g : ℤ) : ZMod 2) ≠ r := hr g (by simp)
    rw [Int.cast_zero] at h0
    rcases hz r with rfl | rfl
    · exact absurd rfl h0
    · rcases hz ((g : ℤ) : ZMod 2) with h | h
      · exact hcast.1 h
      · exact absurd h h1
  · intro hg
    refine ⟨1, ?_⟩
    intro h hh
    rcases Finset.mem_insert.1 hh with rfl | h'
    · rw [Int.cast_zero]; decide
    · rw [Finset.mem_singleton.1 h', hcast.2 hg]; decide

/-- Characterization of admissibility for the two element pattern `{0, g}`: it is admissible
exactly when the gap `g` is even. -/
theorem admissible_pair_iff_even (g : ℤ) : Admissible ({0, g} : Finset ℤ) ↔ Even g := by
  constructor
  · intro h
    exact (pair_local_two g).1 (h 2 Nat.prime_two)
  · intro hg p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · exact (pair_local_two g).2 hg
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      refine exists_missed_residue_of_card_lt _ p hp ?_
      have hc : ({0, g} : Finset ℤ).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      omega

/-- **Singular Series Gaps 1240–1250.**
For every gap `g` with `1240 ≤ g ≤ 1250`, the pattern `{0, g}` is admissible — i.e. every local
factor of the Hardy–Littlewood singular series is nonzero — if and only if `g` is even.
In particular the admissible gaps in this range are exactly `1240, 1242, 1244, 1246, 1248,
1250`, and the odd values `1241, 1243, 1245, 1247, 1249` are inadmissible. -/
theorem SingularSeriesGaps12401250 :
    (∀ g : ℤ, 1240 ≤ g → g ≤ 1250 → (Admissible ({0, g} : Finset ℤ) ↔ Even g)) ∧
      (∀ g ∈ ({1240, 1242, 1244, 1246, 1248, 1250} : Finset ℤ),
        Admissible ({0, g} : Finset ℤ)) ∧
      (∀ g ∈ ({1241, 1243, 1245, 1247, 1249} : Finset ℤ),
        ¬ Admissible ({0, g} : Finset ℤ)) := by
  refine ⟨fun g _ _ => admissible_pair_iff_even g, ?_, ?_⟩
  · intro g hg
    refine (admissible_pair_iff_even g).2 ?_
    fin_cases hg <;> decide
  · intro g hg hA
    have hev := (admissible_pair_iff_even g).1 hA
    fin_cases hg <;> revert hev <;> decide

/-- An admissible triple of gaps inside the range: `{0, 1242, 1250}` misses a residue class
modulo every prime. -/
theorem admissible_triple_1242_1250 : Admissible ({0, 1242, 1250} : Finset ℤ) := by
  intro p hp
  have hple := hp.two_le
  by_cases h5 : 5 ≤ p
  · refine exists_missed_residue_of_card_lt _ p hp ?_
    have hc : ({0, 1242, 1250} : Finset ℤ).card ≤ 3 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have h2 : ({1250} : Finset ℤ).card ≤ 1 := by simp
      have h3 : ({1242, 1250} : Finset ℤ).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      omega
    omega
  · push_neg at h5
    interval_cases p
    · refine ⟨1, ?_⟩
      intro h hh
      fin_cases hh <;> · push_cast; decide
    · refine ⟨1, ?_⟩
      intro h hh
      fin_cases hh <;> · push_cast; decide
    · exact absurd hp (by norm_num)

end Brockian

