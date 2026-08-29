/-
Basic theory of "almost equality" (equality off a finite set) of functions
`Ordinal → ℕ` below a given ordinal, used in the construction of an Aronszajn tree.
-/
import Mathlib

open Cardinal Ordinal Set

namespace Aronszajn

/-- `AlmostEq a f g` means that `f` and `g` agree at all but finitely many `ξ < a`. -/

theorem almostEq_refl (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : AlmostEq a f f :=
  almostEq_of_eqOn fun _ _ => rfl

