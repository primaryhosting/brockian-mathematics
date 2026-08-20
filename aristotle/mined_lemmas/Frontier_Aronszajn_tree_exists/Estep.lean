/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

noncomputable def Estep (a : Ordinal) (ih : ∀ b, b < a → Ordinal → ℕ) : Ordinal → ℕ :=
  if h0 : a = 0 then fun _ => 0
  else if hs : ∃ b, a = b + 1 then
    fun x => if x < hs.choose then
        ih hs.choose
          (lt_of_lt_of_eq (ord_lt_add_one hs.choose) hs.choose_spec.symm) x else 0
  else
    fun x =>
      if hx : ∃ n, x < cseq a n then
        (Nat.rec (motive := fun _ => Ordinal → ℕ) (fun _ => 0)
          (fun m fm y => if y < cseq a m then fm y
            else max (ih (cseq a (m + 1))
              (cseq_lt_of_limit (limit_props h0 hs).1 (limit_props h0 hs).2 (m + 1)) y) m)
          (Nat.find hx)) x
      else 0

/-- The coherent, finite-to-one family `E a : Iio a → ℕ` for `a < ω₁`. -/
