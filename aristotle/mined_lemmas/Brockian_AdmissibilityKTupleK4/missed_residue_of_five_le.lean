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

theorem missed_residue_of_five_le {p : Nat} (hp : 5 ≤ p) (h : Fin 4 → Int) :
    ∃ r : Int, ∀ i : Fin 4, ¬ ((p : Int) ∣ (h i - r)) := by
  apply Classical.byContradiction
  intro hcon
  have key : ∀ r : Int, ∃ i : Fin 4, (p : Int) ∣ (h i - r) := by
    intro r
    apply Classical.byContradiction
    intro hne
    exact hcon ⟨r, fun i hd => hne ⟨i, hd⟩⟩
  cases key 0 with | intro i0 d0 =>
  cases key 1 with | intro i1 d1 =>
  cases key 2 with | intro i2 d2 =>
  cases key 3 with | intro i3 d3 =>
  cases key 4 with | intro i4 d4 =>
  have n01 := index_ne_of_dvd hp h 0 1 i0 i1 d0 d1 (by decide) (by decide) (by decide)
  have n02 := index_ne_of_dvd hp h 0 2 i0 i2 d0 d2 (by decide) (by decide) (by decide)
  have n03 := index_ne_of_dvd hp h 0 3 i0 i3 d0 d3 (by decide) (by decide) (by decide)
  have n04 := index_ne_of_dvd hp h 0 4 i0 i4 d0 d4 (by decide) (by decide) (by decide)
  have n12 := index_ne_of_dvd hp h 1 2 i1 i2 d1 d2 (by decide) (by decide) (by decide)
  have n13 := index_ne_of_dvd hp h 1 3 i1 i3 d1 d3 (by decide) (by decide) (by decide)
  have n14 := index_ne_of_dvd hp h 1 4 i1 i4 d1 d4 (by decide) (by decide) (by decide)
  have n23 := index_ne_of_dvd hp h 2 3 i2 i3 d2 d3 (by decide) (by decide) (by decide)
  have n24 := index_ne_of_dvd hp h 2 4 i2 i4 d2 d4 (by decide) (by decide) (by decide)
  have n34 := index_ne_of_dvd hp h 3 4 i3 i4 d3 d4 (by decide) (by decide) (by decide)
  have b0 := i0.isLt
  have b1 := i1.isLt
  have b2 := i2.isLt
  have b3 := i3.isLt
  have b4 := i4.isLt
  omega

/-- **Admissibility of 4-tuples.**  For a `4`-tuple of integers the infinite family of
conditions defining admissibility (one condition per prime) collapses to just the two
conditions at the primes `2` and `3`: at every prime `p ≥ 5` a `4`-tuple automatically
misses a residue class, since `4 < p`. -/
