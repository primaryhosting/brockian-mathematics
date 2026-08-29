import Mathlib
import RequestProject.Main

/-!
# Admissibility of 4-tuples, `ZMod` formulation

Companion to `RequestProject.Main`.  The main file is developed without `import`s (its header
comment must be the very first thing in the file, which rules out importing Mathlib), so the
notions used there — primality and "the tuple avoids a residue class mod `p`" — are spelled out
from first principles.  Here we check, using Mathlib, that those notions agree with the
standard ones (`Nat.Prime` and non-surjectivity into `ZMod p`), and restate the main theorem
`Brockian.AdmissibilityKTupleK4` in that language.
-/

namespace Brockian

/-- The primality notion of `RequestProject.Main` is Mathlib's `Nat.Prime`. -/

theorem admissible_iff_zmod {k : ℕ} (h : Fin k → ℤ) :
    Admissible h ↔ ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i, ((h i : ZMod p)) ≠ r := by
  constructor
  · intro H p hp
    obtain ⟨r, hr⟩ := H p ((isPrime_iff_nat_prime p).mpr hp)
    exact ⟨(r : ZMod p), fun i => (not_dvd_sub_iff_zmod_ne p (h i) r).mp (hr i)⟩
  · intro H p hp
    obtain ⟨r, hr⟩ := H p ((isPrime_iff_nat_prime p).mp hp)
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective (n := p) r
    exact ⟨z, fun i => (not_dvd_sub_iff_zmod_ne p (h i) z).mpr (hr i)⟩

/-- **Admissibility of 4-tuples, `ZMod` form.**  A 4-tuple of integers is admissible
(no prime `p` has all of `ZMod p` covered by its residues) if and only if this already holds
for the two primes `p = 2` and `p = 3`. -/
