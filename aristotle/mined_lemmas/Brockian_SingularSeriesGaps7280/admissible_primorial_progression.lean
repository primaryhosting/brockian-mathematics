/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A finite set `H` of integers is *admissible* if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series `𝔖(H)` of the tuple `H` is nonzero. -/

theorem admissible_primorial_progression (k : ℕ) (a : ℤ)
    (ha : ∀ p : ℕ, p.Prime → p ≤ k → ¬ ((p : ℤ) ∣ a)) :
    Admissible ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))) := by
  intro p hp
  by_cases hpk : p ≤ k
  · -- small primes: every element is `≡ a (mod p)`, and `p ∤ a`
    refine exists_missing_residue_of_not_dvd _ p ?_
    intro h hh
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
    have hdvd : (p : ℤ) ∣ (primorial k : ℤ) := by
      have : p ∣ primorial k := by
        refine Finset.dvd_prod_of_mem (fun q => q) ?_
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp⟩
      exact_mod_cast Int.natCast_dvd_natCast.mpr this
    intro hcon
    exact ha p hp hpk (by
      have : (p : ℤ) ∣ (i : ℤ) * (primorial k : ℤ) := hdvd.mul_left _
      simpa using (dvd_sub hcon this))
  · -- large primes: the tuple has fewer than `p` elements
    refine exists_missing_residue_of_card_lt _ p ?_
    have : ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * (primorial k : ℤ))).card ≤ k :=
      le_trans Finset.card_image_le (le_of_eq (Finset.card_range k))
    omega

/-- The progression really has `k` distinct terms (the common difference `k#` is positive). -/
