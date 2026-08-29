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
