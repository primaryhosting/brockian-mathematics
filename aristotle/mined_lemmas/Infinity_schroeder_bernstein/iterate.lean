/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (only Lean's prelude is available), because a
module doc comment such as the header above cannot legally precede an `import` line.
Everything below is therefore developed from scratch: the Cantor–Schröder–Bernstein
back-and-forth construction and its correctness proof.  The only classical ingredient
used is `Classical.choice`.

A Mathlib-flavoured restatement, phrased with `Equiv` (`X ≃ Y`), is derived from the
main theorem in `RequestProject/SchroederBernsteinEquiv.lean`.
-/

namespace Infinity

universe u v

section
variable {X : Type u} {Y : Type v}

/-- `iterate F n x` is the `n`-fold application `F (F (… (F x)))`. -/

def iterate (F : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => F (iterate F n x)

/-- `Reach f g x` says that `x : X` is obtained from some element outside the range of
`g` by finitely many applications of `g ∘ f`.  These are exactly the points where the
Cantor–Schröder–Bernstein bijection is defined to be `f`. -/
