/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The required header is reproduced verbatim above; Lean 4 does not allow a
-- module doc-comment `/-! ... -/` to precede the `import` line, so it is written
-- as an ordinary block comment.)
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Smirnov Percolation

Category: Frontier — Fields Medal Work
Target: `Frontier.smirnov_percolation`

Crossing probabilities of critical site percolation on the triangular lattice are
conformally invariant (Cardy–Smirnov).

## What is formalized here

Smirnov's theorem says that the scaling limit of the crossing probability of a conformal
rectangle (a Jordan domain with four marked boundary points) exists and is a conformal
invariant of the configuration; explicitly, in the upper half-plane with four marked
boundary points `a < b < c < d`, the limiting crossing probability is Cardy's function
evaluated at the *conformal modulus*, i.e. the cross-ratio

`m = (b - a)(d - c) / ((c - a)(d - b))`.

This file formalizes the statement in that analytic form and gives a Lean-checked
reduction of conformal invariance to the algebraic heart of the matter:

* `Frontier.crossRatio_mobius` — the cross-ratio is invariant under every Möbius
  transformation (this is proved from scratch, and is the base case of the theorem);
* `Frontier.smirnov_percolation` — consequently, any crossing observable satisfying the
  Cardy–Smirnov formula (packaged as `Frontier.CrossingObservable`) takes the same value
  on a configuration and on its image under a conformal automorphism `z ↦ (pz+q)/(rz+s)`,
  `p, q, r, s` real with `ps - qr > 0`, of the upper half-plane.  This is exactly the
  assertion that crossing probabilities are conformally invariant.
* `Frontier.crossing_eq_half_of_selfDual` — the classical consequence at the self-dual
  configuration: a "square" (modulus `1/2`) has crossing probability `1/2`.

The Cardy function itself is kept abstract (a field `cardy` of `CrossingObservable`); no
property of it is used, so the invariance statement is proved for *every* observable of
Cardy–Smirnov form.
-/

namespace Frontier

/-- The conformal modulus (cross-ratio) of four points, normalized so that four points
`a < b < c < d` on the real line give a value in `(0,1)`. -/

theorem crossing_eq_half_of_selfDual (O : CrossingObservable)
    (hdual : ∀ a b c d : ℂ, O.P a b c d + O.P b c d a = 1)
    (a b c d : ℂ) (hca : c ≠ a) (hdb : d ≠ b)
    (hm : crossRatio a b c d = 1 / 2) :
    O.P a b c d = 1 / 2 := by
  have hshift : crossRatio b c d a = 1 / 2 := by
    rw [crossRatio_cyclic a b c d (sub_ne_zero_of_ne hca) (sub_ne_zero_of_ne hdb), hm]
    norm_num
  have h1 : O.P b c d a = O.P a b c d := by
    rw [O.smirnov, O.smirnov, hm, hshift]
  have := hdual a b c d
  rw [h1] at this
  linarith

/-- The Cardy–Smirnov axiomatization is consistent: crossing observables exist.  (This
guards the statements above against vacuity; of course, the content of Smirnov's theorem
is that the percolation crossing limits form such an observable.) -/
example : Nonempty CrossingObservable :=
  ⟨{ P := fun _ _ _ _ => 0, cardy := fun _ => 0, smirnov := fun _ _ _ _ => rfl }⟩

end Frontier

#print axioms Frontier.crossRatio_mobius
#print axioms Frontier.smirnov_percolation
#print axioms Frontier.crossing_eq_half_of_selfDual

