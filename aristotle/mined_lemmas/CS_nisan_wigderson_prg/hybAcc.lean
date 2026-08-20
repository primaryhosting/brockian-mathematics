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

noncomputable def hybAcc {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) (i : ℕ) : ℝ :=
  (∑ z : Fin d → Bool, ∑ y : Fin m → Bool,
      b2r (D.eval (fun j => if (j : ℕ) < i then f (z ∘ e j) else y j))) / (2 ^ d * 2 ^ m)

