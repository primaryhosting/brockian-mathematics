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

theorem admissibility_kTuple_k4_zmod (h : Fin 4 → ℤ) :
    (∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i, ((h i : ZMod p)) ≠ r) ↔
      ((∃ r : ZMod 2, ∀ i, ((h i : ZMod 2)) ≠ r) ∧
       (∃ r : ZMod 3, ∀ i, ((h i : ZMod 3)) ≠ r)) := by
  rw [← admissible_iff_zmod, AdmissibilityKTupleK4]
  constructor
  · rintro ⟨⟨r2, hr2⟩, ⟨r3, hr3⟩⟩
    refine ⟨⟨(r2 : ZMod 2), fun i => ?_⟩, ⟨(r3 : ZMod 3), fun i => ?_⟩⟩
    · simpa using (not_dvd_sub_iff_zmod_ne 2 (h i) r2).mp (by simpa using hr2 i)
    · simpa using (not_dvd_sub_iff_zmod_ne 3 (h i) r3).mp (by simpa using hr3 i)
  · rintro ⟨⟨r2, hr2⟩, ⟨r3, hr3⟩⟩
    obtain ⟨z2, rfl⟩ := ZMod.intCast_surjective (n := 2) r2
    obtain ⟨z3, rfl⟩ := ZMod.intCast_surjective (n := 3) r3
    refine ⟨⟨z2, fun i => ?_⟩, ⟨z3, fun i => ?_⟩⟩
    · simpa using (not_dvd_sub_iff_zmod_ne 2 (h i) z2).mpr (hr2 i)
    · simpa using (not_dvd_sub_iff_zmod_ne 3 (h i) z3).mpr (hr3 i)

end Brockian

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import`s): Lean requires every `import`
command to precede all other syntax, so keeping the header comment above at the very top
of the file rules out importing Mathlib.  Everything below is therefore developed from
first principles using only the Lean 4 core library.
-/

namespace Brockian

/-- Primality of a natural number, in the usual sense: `p ≥ 2` and every divisor of `p`
is either `1` or `p`. -/
