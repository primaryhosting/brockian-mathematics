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
