/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits

We use a term representation of Boolean circuits, but we measure their size in the
*DAG* sense: the size of a circuit is the number of distinct subcircuits occurring in
it (equivalently, the number of gates when identical subcircuits are shared). -/

/-- Boolean circuits on `n` input variables. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | and : Circ n → Circ n → Circ n
  | or : Circ n → Circ n → Circ n
  deriving DecidableEq

namespace Circ

/-- The Boolean function computed by a circuit. -/

lemma nw_pair_identity (A0 A1 r fx neg : Bool) :
    agree (xor neg ((cond r A1 A0) == r)) fx
        + agree (xor neg ((cond (!r) A1 A0) == (!r))) fx
      = 1 + (if neg then (-1 : ℝ) else 1) *
          ((b2r (cond fx A1 A0) - b2r (cond r A1 A0))
            + (b2r (cond fx A1 A0) - b2r (cond (!r) A1 A0))) := by
  cases A0 <;> cases A1 <;> cases r <;> cases fx <;> cases neg <;>
    norm_num [agree, b2r]

/-! ## Blocks of the seed -/

/-- Overwrite the coordinates of `z` lying in the image of `e` according to `x`. -/
