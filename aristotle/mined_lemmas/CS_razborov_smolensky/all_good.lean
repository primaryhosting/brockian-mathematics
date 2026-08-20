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


theorem all_good (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (x : Fin n → Bool) (h : ∀ i, LocalGood F C q t ρ x i) : ∀ i, Good F C q t ρ x i := by
  have H : ∀ N : ℕ, ∀ i : Fin C.size, i.val < N → Good F C q t ρ x i := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ N ih =>
      intro i hi
      refine h i (fun j => ih (C.up i j) ?_)
      have := j.isLt
      simp only [Circuit.up]
      omega
  exact fun i => H (i.val + 1) i (Nat.lt_succ_self _)

/-- The dichotomy at an `OR` gate. -/
