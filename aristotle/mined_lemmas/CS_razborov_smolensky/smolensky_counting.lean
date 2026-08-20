import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem smolensky_counting {m D : ℕ} {A : Finset (Fin (2 * m + 1) → Bool)} (ζ : F)
    (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (h : (Fin (2 * m + 1) → Bool) → F)
    (hhD : h ∈ Deg F (2 * m + 1) D) (hh : ∀ x ∈ A, h x = ymono ζ univ x) :
    A.card ≤ ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i := by
  refine card_le_of_agree F A (fun f => ?_)
  have htop := AgreeDeg_eq_top ζ hζ0 hζ1 h hhD hh
  have hf : f ∈ AgreeDeg F A (m + D) := by rw [htop]; trivial
  exact hf

end CS

import Mathlib

/-!
Elementary binomial coefficient estimates: the central binomial coefficient is at most
`√2 · 4ⁿ / √(n+1)`, in the division free form `(n.choose i)^2 * (n+1) ≤ 2 * 4^n`.
-/

namespace CS

open Finset

/-- `C(2m,m)^2 (3m+1) ≤ 16^m`, proved by induction. -/
