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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian

/-- A finite set of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture / singular series) if for every prime `p` it fails to
cover all residue classes modulo `p`. -/

lemma isAdmissible_arithmeticProgression (t d : ℤ) (k : ℕ)
    (hd : ∀ p : ℕ, p.Prime → p ≤ k → (p : ℤ) ∣ d) :
    IsAdmissible ((Finset.range k).image (fun i : ℕ => t + d * (i : ℤ))) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpk : p ≤ k
  · refine ⟨(t : ZMod p) + 1, ?_⟩
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    have hd0 : ((d : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr (hd p hp hpk)
    have : ((t + d * (i : ℤ) : ℤ) : ZMod p) = (t : ZMod p) := by
      push_cast [hd0]
      ring
    rw [this]
    intro hcontra
    have : (0 : ZMod p) = 1 := by linear_combination hcontra
    exact zero_ne_one this
  · refine exists_residue_not_covered hp ?_
    have h1 : ((Finset.range k).image (fun i : ℕ => t + d * (i : ℤ))).card ≤ k := by
      calc ((Finset.range k).image (fun i : ℕ => t + d * (i : ℤ))).card
          ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
    omega

/-- The primorial-style modulus: the product of all primes below `n`. -/
