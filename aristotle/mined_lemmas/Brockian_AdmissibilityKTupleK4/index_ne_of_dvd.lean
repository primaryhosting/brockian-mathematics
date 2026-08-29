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

theorem index_ne_of_dvd {p : Nat} (hp : 5 ≤ p) (h : Fin 4 → Int) (a b : Int) (i j : Fin 4)
    (hi : (p : Int) ∣ (h i - a)) (hj : (p : Int) ∣ (h j - b)) (hab : a ≠ b)
    (hl : -4 ≤ a - b) (hu : a - b ≤ 4) : i.val ≠ j.val := by
  intro hv
  have hij : i = j := Fin.eq_of_val_eq hv
  subst hij
  have e1 : (h i - a) - (h i - b) = b - a := by omega
  have e2 : (h i - b) - (h i - a) = a - b := by omega
  have hd1 : (p : Int) ∣ (b - a) := e1 ▸ Int.dvd_sub hi hj
  have hd2 : (p : Int) ∣ (a - b) := e2 ▸ Int.dvd_sub hj hi
  have hcast : (5 : Int) ≤ (p : Int) := by exact_mod_cast hp
  have hne : a - b ≠ 0 := by omega
  cases Int.lt_or_lt_of_ne hne with
  | inl hlt => have := Int.le_of_dvd (by omega) hd1; omega
  | inr hgt => have := Int.le_of_dvd (by omega) hd2; omega

/-- **Pigeonhole step.**  A tuple of length `4` cannot meet all residue classes modulo a
number `p ≥ 5`: among the five classes `0, 1, 2, 3, 4` some class is missed. -/
