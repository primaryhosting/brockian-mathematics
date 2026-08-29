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

noncomputable def bij (f : X → Y) (g : Y → X) (x : X) : Y :=
  @dite _ (Reach f g x) (Classical.propDecidable _) (fun _ => f x)
    (fun hx => Classical.choose (exists_preimage hx))

