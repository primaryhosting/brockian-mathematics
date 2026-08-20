/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: the requested header is reproduced verbatim above, but as an ordinary block comment
`/- ... -/` rather than a module docstring `/-! ... -/`, since Lean 4 does not allow a module
docstring to precede the `import` commands.)
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

set_option grind.warning false

namespace Brockian

/-- A finite set of nonnegative integers `H` (a *gap range*, or prime tuple pattern) is
*admissible* when, for every prime `p`, the reductions of the elements of `H` modulo `p`
do not cover all of `ZMod p`.  Equivalently the local factor
`1 - ν_H(p)/p` of the Hardy–Littlewood singular series is strictly positive at every prime,
which is exactly the condition for the singular series `𝔖(H)` to be nonzero. -/
def AdmissibleTuple (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The number of residue classes modulo `p` occupied by `H`; this is `ν_H(p)`, the quantity
appearing in the local factor `1 - ν_H(p)/p` of the singular series. -/
noncomputable def residueCount (H : Finset ℕ) (p : ℕ) : ℕ :=
  (Finset.image (fun h : ℕ => (h : ZMod p)) H).card

/-- Admissibility is exactly the statement that every local factor of the singular series is
positive, i.e. `ν_H(p) < p` for all primes `p`. -/
theorem admissibleTuple_iff_residueCount_lt (H : Finset ℕ) :
    AdmissibleTuple H ↔ ∀ p : ℕ, p.Prime → residueCount H p < p := by
  constructor
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : Finset.image (fun h : ℕ => (h : ZMod p)) H ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr ?_
      intro hcon
      have : r ∈ Finset.image (fun h : ℕ => (h : ZMod p)) H := by rw [hcon]; exact Finset.mem_univ r
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp this
      exact hr h hh rfl
    have := Finset.card_lt_card hsub
    simpa [residueCount, ZMod.card] using this
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt : (Finset.image (fun h : ℕ => (h : ZMod p)) H).card < Fintype.card (ZMod p) := by
      simpa [residueCount, ZMod.card] using hH p hp
    have : ∃ r : ZMod p, r ∉ Finset.image (fun h : ℕ => (h : ZMod p)) H := by
      by_contra hcon
      push_neg at hcon
      have : Finset.univ ⊆ Finset.image (fun h : ℕ => (h : ZMod p)) H := fun r _ => hcon r
      exact absurd (Finset.card_le_card this) (by simpa using hlt)
    obtain ⟨r, hr⟩ := this
    exact ⟨r, fun h hh hcon => hr (Finset.mem_image.mpr ⟨h, hh, hcon⟩)⟩

/-- **Singular Series Gaps 9098.**
Any finite set `H` of primes, each of which exceeds the cardinality of `H`, is an admissible
tuple: no prime `p` has all its residue classes occupied by `H`.

Proof idea: for small primes `p ≤ #H` no element of `H` is divisible by `p` (the elements are
primes larger than `p`), so the class `0` is missed; for large primes `p > #H` there are simply
too few elements to cover the `p` classes. -/
theorem SingularSeriesGaps9098 (H : Finset ℕ) (hprime : ∀ h ∈ H, Nat.Prime h)
    (hbig : ∀ h ∈ H, H.card < h) : AdmissibleTuple H := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hcase : p ≤ H.card
  · -- small primes: `0` is not a residue of any element of `H`
    refine ⟨0, ?_⟩
    intro h hh hcon
    have hdvd : p ∣ h := (ZMod.natCast_eq_zero_iff h p).mp hcon
    have hhp : Nat.Prime h := hprime h hh
    have : p = h := ((Nat.prime_dvd_prime_iff_eq hp hhp).mp hdvd)
    have := hbig h hh
    omega
  · -- large primes: too few elements to cover all classes
    push_neg at hcase
    have hlt : (Finset.image (fun h : ℕ => (h : ZMod p)) H).card < Fintype.card (ZMod p) := by
      have h1 : (Finset.image (fun h : ℕ => (h : ZMod p)) H).card ≤ H.card := Finset.card_image_le
      have : Fintype.card (ZMod p) = p := ZMod.card p
      omega
    have hex : ∃ r : ZMod p, r ∉ Finset.image (fun h : ℕ => (h : ZMod p)) H := by
      by_contra hcon
      push_neg at hcon
      have hsub : Finset.univ ⊆ Finset.image (fun h : ℕ => (h : ZMod p)) H := fun r _ => hcon r
      exact absurd (Finset.card_le_card hsub) (by simpa using hlt)
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, fun h hh hcon => hr (Finset.mem_image.mpr ⟨h, hh, hcon⟩)⟩

/-- Admissibility only depends on the *gap pattern*: translating a tuple by a fixed shift `c`
preserves admissibility, in both directions. -/
theorem admissibleTuple_image_add_iff (H : Finset ℕ) (c : ℕ) :
    AdmissibleTuple (H.image (fun h => h + c)) ↔ AdmissibleTuple H := by
  constructor
  · intro hH p hp
    obtain ⟨r, hr⟩ := hH p hp
    refine ⟨r - (c : ZMod p), ?_⟩
    intro h hh hcon
    refine hr (h + c) (Finset.mem_image.mpr ⟨h, hh, rfl⟩) ?_
    push_cast
    rw [hcon]
    ring
  · intro hH p hp
    obtain ⟨r, hr⟩ := hH p hp
    refine ⟨r + (c : ZMod p), ?_⟩
    intro h hh hcon
    obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_image.mp hh
    refine hr h₀ hh₀ ?_
    push_cast at hcon
    exact add_right_cancel hcon

/-- A concrete new admissible gap range of length 7 coming from the prime block
`{11, 13, 17, 19, 23, 29, 31}`. -/
theorem admissible_primeBlock_11_31 :
    AdmissibleTuple ({11, 13, 17, 19, 23, 29, 31} : Finset ℕ) := by
  refine SingularSeriesGaps9098 _ ?_ ?_ <;> decide

/-- The corresponding gap range `{0, 2, 6, 8, 12, 18, 20}` (the pattern of
`{11, 13, 17, 19, 23, 29, 31}` normalised to start at `0`) is admissible. -/
theorem admissible_gapRange_0_20 :
    AdmissibleTuple ({0, 2, 6, 8, 12, 18, 20} : Finset ℕ) := by
  rw [← admissibleTuple_image_add_iff _ 11]
  have hset : (({0, 2, 6, 8, 12, 18, 20} : Finset ℕ).image (fun h => h + 11))
      = ({11, 13, 17, 19, 23, 29, 31} : Finset ℕ) := by decide
  rw [hset]
  exact admissible_primeBlock_11_31

end Brockian

