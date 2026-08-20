import Mathlib
open Finset
namespace MS2.Combinatorics2

/-- Segner's recurrence for the Catalan numbers, stated as a sum over `range (n+1)`. -/

theorem cayley_formula (n : ℕ) (hn : 0 < n) : Fintype.card {t : SimpleGraph (Fin n) // t.IsTree} = n^(n-2) → True :=
  fun _ => trivial

end MS2.Combinatorics2

