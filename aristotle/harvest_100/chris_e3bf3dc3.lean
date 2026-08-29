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

/-- A finite set of integers `H` (a "gap pattern") is *admissible* when, for every prime `p`,
the elements of `H` do not cover all residue classes modulo `p`.  This is exactly the condition
under which the associated singular series is nonzero, i.e. the Hardy–Littlewood prime tuple
conjecture predicts infinitely many translates of `H` consisting entirely of primes. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r

/-- Pigeonhole: a set of integers with fewer than `p` elements misses a residue class mod `p`. -/
theorem exists_missing_residue (H : Finset ℤ) (p : ℕ) [NeZero p] (hcard : H.card < p) :
    ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have h1 : Fintype.card (ZMod p) ≤ (H.image (fun x : ℤ => (x : ZMod p))).card := by
    simpa [Finset.card_univ] using Finset.card_le_card hsub
  have h2 : (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
  rw [ZMod.card p] at h1
  omega

/-- Admissibility only needs to be checked at primes `p ≤ H.card`. -/
theorem admissible_of_small_primes (H : Finset ℤ)
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r) :
    Admissible H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    exact exists_missing_residue H p (by omega)

/-- Admissibility is invariant under translation of the gap pattern. -/
theorem admissible_translate {H : Finset ℤ} (hH : Admissible H) (m : ℤ) :
    Admissible (H.image (fun x => x + m)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + (m : ZMod p), ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have := hr y hy
  push_cast
  intro hcon
  exact this (by linear_combination hcon)

/-- The `k`-element pattern `{0, k!, 2·k!, …, (k-1)·k!}` is admissible for every `k`. -/
theorem admissible_factorial_ladder (k : ℕ) :
    Admissible ((Finset.range k).image (fun i : ℕ => (i : ℤ) * (k ! : ℤ))) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hle : p ≤ k
  · -- every element is divisible by `p`, so the residue `1` is missed
    refine ⟨1, ?_⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hdvd : (p : ℤ) ∣ (i : ℤ) * (k ! : ℤ) :=
      Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hp.pos hle)) _
    have hzero : (((i : ℤ) * (k ! : ℤ) : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hdvd
    rw [hzero]
    exact zero_ne_one
  · have hcard : ((Finset.range k).image (fun i : ℕ => (i : ℤ) * (k ! : ℤ))).card < p := by
      have h1 : ((Finset.range k).image (fun i : ℕ => (i : ℤ) * (k ! : ℤ))).card ≤ k :=
        le_trans Finset.card_image_le (le_of_eq (Finset.card_range k))
      omega
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact exists_missing_residue _ p hcard

/-- The classical admissible octuple of gaps `0, 2, 6, 8, 12, 18, 20, 26`. -/
theorem admissible_octuple :
    Admissible ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℤ) := by
  apply admissible_of_small_primes
  intro p hp hle
  have hcard : ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℤ).card = 8 := by decide
  rw [hcard] at hle
  have hp2 := hp.two_le
  interval_cases p
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨4, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨3, by decide⟩
  · exact absurd hp (by decide)

/-- **Singular Series Gaps 9098.**  New admissible gap ranges: the factorial ladder patterns
`{0, k!, 2·k!, …, (k-1)·k!}` are admissible for every `k`, and every translate of the classical
octuple `{0, 2, 6, 8, 12, 18, 20, 26}` is admissible as well. -/
theorem SingularSeriesGaps9098 :
    (∀ k : ℕ, Admissible ((Finset.range k).image (fun i : ℕ => (i : ℤ) * (k ! : ℤ)))) ∧
      (∀ m : ℤ, Admissible (({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℤ).image (fun x => x + m))) :=
  ⟨admissible_factorial_ladder, fun m => admissible_translate admissible_octuple m⟩

end Brockian

