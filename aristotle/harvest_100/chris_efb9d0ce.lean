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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when, for every prime `p`, the elements of `H` do not cover
all residue classes modulo `p`; equivalently the local factor of the singular series
`𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` is nonzero at every prime. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℤ, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (h - r))

/-- For a prime `p` larger than the size of `H`, the admissibility condition at `p` is
automatic: `H` has too few elements to meet every residue class mod `p`. -/
theorem admissible_at_large_prime (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ℤ, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (h - r)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- the image of `H` in `ZMod p` is too small to be everything
  have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < Fintype.card (ZMod p) := by
    have h1 : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
    have h2 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  have hne : (H.image (fun h : ℤ => (h : ZMod p))) ≠ Finset.univ := by
    intro hcon
    rw [hcon, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finset.eq_univ_iff_forall.mpr hcon)
  refine ⟨(r.val : ℤ), ?_⟩
  intro h hh hdvd
  apply hr
  refine Finset.mem_image.mpr ⟨h, hh, ?_⟩
  have : ((h - (r.val : ℤ) : ℤ) : ZMod p) = 0 := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  have hv : ((r.val : ℕ) : ZMod p) = r := by
    simp [ZMod.natCast_val, ZMod.cast_id]
  push_cast at this
  rw [hv] at this
  exact sub_eq_zero.mp this

/-- Admissibility only needs to be checked at the primes `p ≤ |H|`. -/
theorem admissible_iff_small_primes (H : Finset ℤ) :
    Admissible H ↔
      ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ℤ, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (h - r)) := by
  constructor
  · intro hH p hp _
    exact hH p hp
  · intro hH p hp
    by_cases hle : p ≤ H.card
    · exact hH p hp hle
    · exact admissible_at_large_prime H p hp (by omega)

/-- Admissibility is invariant under translation of the gap pattern. -/
theorem admissible_translate (H : Finset ℤ) (t : ℤ) (hH : Admissible H) :
    Admissible (H.image (fun h => h + t)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + t, ?_⟩
  intro h hh hdvd
  obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_image.mp hh
  have hrw : h₀ + t - (r + t) = h₀ - r := by ring
  rw [hrw] at hdvd
  exact hr h₀ hh₀ hdvd

/-- The explicit `8`-tuple `{0, 2, 6, 8, 12, 18, 20, 26}` of diameter `26`. -/
def gapPattern7280 : Finset ℤ := {0, 2, 6, 8, 12, 18, 20, 26}

theorem gapPattern7280_card : gapPattern7280.card = 8 := by decide

theorem gapPattern7280_admissible : Admissible gapPattern7280 := by
  rw [admissible_iff_small_primes, gapPattern7280_card]
  intro p hp hple
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨4, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨3, by decide⟩
  · exact absurd hp (by decide)

/--
**Singular Series Gaps 7280.**

A packaged admissibility ("nonvanishing singular series") statement for prime gap ranges:

1. the admissibility condition at a prime `p` is automatic once `p` exceeds `|H|`, so
   admissibility is decided by the finitely many primes `p ≤ |H|`;
2. admissibility is a translation-invariant property of the gap pattern, so each admissible
   pattern yields a whole family of admissible gap ranges `[t, t + diam]`;
3. the explicit pattern `{0, 2, 6, 8, 12, 18, 20, 26}` — eight points inside a range of
   length `26` — is admissible, and hence so is every translate of it.
-/
theorem SingularSeriesGaps7280 :
    (∀ (H : Finset ℤ), Admissible H ↔
        ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ℤ, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (h - r))) ∧
    (∀ (H : Finset ℤ) (t : ℤ), Admissible H → Admissible (H.image (fun h => h + t))) ∧
    (gapPattern7280.card = 8 ∧
      gapPattern7280.max' (by decide) - gapPattern7280.min' (by decide) = 26 ∧
      ∀ t : ℤ, Admissible (gapPattern7280.image (fun h => h + t))) := by
  refine ⟨admissible_iff_small_primes, admissible_translate, gapPattern7280_card, by decide,
    fun t => admissible_translate _ t gapPattern7280_admissible⟩

end Brockian

