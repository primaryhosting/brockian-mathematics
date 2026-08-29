/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
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
prime `k`-tuples conjecture) if for every prime `p` the elements of `H` do not cover all
residue classes modulo `p`; equivalently the singular series attached to `H` is nonzero. -/

lemma primeBlock_admissible (k : ℕ) : Admissible (primeBlock k) := by
  intro p hp
  by_cases hpk : p ≤ k
  · -- small primes: no element of the block is divisible by `p`, so the class `0` is missed
    refine ⟨0, ?_⟩
    intro h hh hdvd
    obtain ⟨q, hq, rfl⟩ := primeBlock_prime hh
    rw [sub_zero] at hdvd
    have hdvd' : p ∣ q := by exact_mod_cast hdvd
    have : p = q := ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd')
    have hlt : (k : ℤ) < (q : ℤ) := primeBlock_lt hh
    have : (k : ℤ) < (p : ℤ) := by rw [this]; exact hlt
    have : k < p := by exact_mod_cast this
    omega
  · -- large primes: the block has fewer than `p` elements
    push_neg at hpk
    haveI : Fact p.Prime := ⟨hp⟩
    have hcard : ((primeBlock k).image (fun h : ℤ => (h : ZMod p))).card
        < Fintype.card (ZMod p) := by
      have h1 := Finset.card_image_le (s := primeBlock k) (f := fun h : ℤ => (h : ZMod p))
      rw [primeBlock_card] at h1
      simpa [ZMod.card] using lt_of_le_of_lt h1 hpk
    obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ (primeBlock k).image (fun h : ℤ => (h : ZMod p)) := by
      by_contra hcon
      push_neg at hcon
      rw [Finset.eq_univ_iff_forall.mpr hcon, Finset.card_univ] at hcard
      exact lt_irrefl _ hcard
    refine ⟨(r.val : ℤ), ?_⟩
    intro h hh hdvd
    have h0 : ((h - (r.val : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    have hval : ((h : ℤ) : ZMod p) = r := by
      push_cast at h0
      have h1 : ((h : ℤ) : ZMod p) - ((r.val : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_val, ZMod.cast_id] at h1
      exact sub_eq_zero.mp h1
    exact hr (Finset.mem_image.mpr ⟨h, hh, hval⟩)

/-- **Singular Series Gaps 16021610.**
For every `k` there is an admissible `k`-tuple of integers (so its singular series is
nonzero, and the Hardy–Littlewood conjecture predicts infinitely many prime constellations
of this shape), lying entirely inside the gap range `[p_k, p_{2k}]`, where `p_n` denotes the
`n`-th prime. -/
