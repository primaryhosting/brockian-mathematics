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

/-- A finite set of integer shifts `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture: the associated singular series is
nonzero) when for every prime `p` the shifts miss at least one residue class
modulo `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- If a prime `p` exceeds the size of `H`, then `H` automatically misses a
residue class modulo `p`, simply because it has too few elements to cover all
`p` classes. -/
theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have hsurj : Set.SurjOn (fun h : ℤ => (h : ZMod p)) (H : Set ℤ)
      ((Finset.univ : Finset (ZMod p)) : Set (ZMod p)) := by
    intro r _
    obtain ⟨h, hH, hr⟩ := hcon r
    exact ⟨h, hH, hr⟩
  have hle := Finset.card_le_card_of_surjOn (fun h : ℤ => (h : ZMod p)) hsurj
  simp only [Finset.card_univ, ZMod.card] at hle
  omega

/-- Admissibility only has to be checked at the primes `p ≤ |H|`: this turns the
definition into a finite (decidable) verification. -/
theorem admissible_iff_small_primes (H : Finset ℤ) :
    Admissible H ↔
      ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hH p hp _
    exact hH p hp
  · intro hH p hp
    by_cases hle : p ≤ H.card
    · exact hH p hp hle
    · exact exists_missed_residue_of_card_lt H p hp (by omega)

/-- The `5`-tuple of gaps `{0, 2, 6, 8, 12}` is admissible. -/
theorem admissible_zero_two_six_eight_twelve :
    Admissible ({0, 2, 6, 8, 12} : Finset ℤ) := by
  rw [admissible_iff_small_primes]
  intro p hp hple
  have hcard : ({0, 2, 6, 8, 12} : Finset ℤ).card = 5 := by decide
  rw [hcard] at hple
  have hp2 := hp.two_le
  interval_cases p
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨4, by decide⟩

/-- Translates of an admissible set are admissible: admissibility depends only
on the pattern of gaps, not on where the range sits. -/
theorem admissible_map_add (H : Finset ℤ) (hH : Admissible H) (c : ℤ) :
    Admissible (H.image (fun h => h + c)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + (c : ZMod p), ?_⟩
  intro h hh
  simp only [Finset.mem_image] at hh
  obtain ⟨h₀, hh₀, rfl⟩ := hh
  have := hr h₀ hh₀
  push_cast
  exact fun hc => this (add_right_cancel hc)

/--
**Singular Series Gaps 9098.**

Admissibility of a finite set of integer shifts (nonvanishing of the associated
singular series in the Hardy–Littlewood prime `k`-tuples conjecture) needs to be
tested only at the primes `p ≤ |H|`, since larger primes are automatically
missed for cardinality reasons.  Consequently the gap pattern `{0, 2, 6, 8, 12}`
is admissible, and so is every translate of it, giving admissible ranges
`{c, c+2, c+6, c+8, c+12}` of diameter `12` at every starting point `c`.
-/
theorem SingularSeriesGaps9098 :
    (∀ H : Finset ℤ, Admissible H ↔
        ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) ∧
      ∀ c : ℤ, Admissible ({c, c + 2, c + 6, c + 8, c + 12} : Finset ℤ) := by
  refine ⟨admissible_iff_small_primes, fun c => ?_⟩
  have h := admissible_map_add _ admissible_zero_two_six_eight_twelve c
  have himg : (({0, 2, 6, 8, 12} : Finset ℤ).image (fun h => h + c))
      = ({c, c + 2, c + 6, c + 8, c + 12} : Finset ℤ) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [add_comm]
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨2, by norm_num [add_comm]⟩, ⟨6, by norm_num [add_comm]⟩,
        ⟨8, by norm_num [add_comm]⟩, ⟨12, by norm_num [add_comm]⟩]
  rwa [himg] at h

end Brockian

