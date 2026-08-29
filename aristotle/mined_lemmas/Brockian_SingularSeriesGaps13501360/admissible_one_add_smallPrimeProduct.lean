/-
/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
(Lean requires the `import` command to be the very first command of a file, so
the header above is reproduced verbatim inside this comment and again as the
module docstring below.)
-/
import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- The set of residue classes modulo `p` that are occupied by the shift set `H`. -/

theorem admissible_one_add_smallPrimeProduct (k : ℕ) :
    Admissible ((Finset.range k).image (fun i : ℕ => 1 + (i : ℤ) * (smallPrimeProduct k : ℤ))) := by
  refine SingularSeriesGaps13501360 k 1 (smallPrimeProduct k : ℤ) ?_ ?_
  · intro p hp hpk
    have : p ∣ smallPrimeProduct k := by
      refine Finset.dvd_prod_of_mem _ ?_
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    exact_mod_cast Int.natCast_dvd_natCast.mpr this
  · intro p hp _ hdvd
    have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega

/-- The local factor of the Hardy–Littlewood singular series at the prime `p`:
`(1 - ν_H(p)/p) / (1 - 1/p)^{|H|}` where `ν_H(p)` is the number of occupied residue classes. -/
