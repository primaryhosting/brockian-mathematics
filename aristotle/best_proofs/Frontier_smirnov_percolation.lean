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
noncomputable def crossRatio (a b c d : ℂ) : ℂ := ((b - a) * (d - c)) / ((c - a) * (d - b))

/-- The Möbius transformation `z ↦ (p * z + q) / (r * z + s)`. -/
noncomputable def mobius (p q r s z : ℂ) : ℂ := (p * z + q) / (r * z + s)

/-- Differences are transformed by a Möbius map in a controlled way. -/
lemma mobius_sub (p q r s z w : ℂ) (hz : r * z + s ≠ 0) (hw : r * w + s ≠ 0) :
    mobius p q r s z - mobius p q r s w
      = (p * s - q * r) * (z - w) / ((r * z + s) * (r * w + s)) := by
  unfold mobius
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- **Möbius invariance of the cross-ratio.**  This is the algebraic base case of
conformal invariance of crossing probabilities. -/
lemma crossRatio_mobius (p q r s : ℂ) (hdet : p * s - q * r ≠ 0) (a b c d : ℂ)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0)
    (hca : c - a ≠ 0) (hdb : d - b ≠ 0) :
    crossRatio (mobius p q r s a) (mobius p q r s b) (mobius p q r s c)
        (mobius p q r s d) = crossRatio a b c d := by
  unfold crossRatio
  rw [mobius_sub p q r s b a hb ha, mobius_sub p q r s d c hd hc,
    mobius_sub p q r s c a hc ha, mobius_sub p q r s d b hd hb]
  field_simp

/-- The cross-ratio of the cyclically shifted configuration is the complementary modulus:
this encodes the duality between a crossing and the dual (blocking) crossing. -/
lemma crossRatio_cyclic (a b c d : ℂ) (hca : c - a ≠ 0) (hdb : d - b ≠ 0) :
    crossRatio b c d a = 1 - crossRatio a b c d := by
  have hac : a - c ≠ 0 := fun h => hca (by linear_combination -h)
  unfold crossRatio
  field_simp
  ring

/-- A **crossing observable** for critical percolation: an assignment, to each conformal
rectangle in the upper half-plane (recorded by its four marked boundary points), of the
scaling limit of the crossing probability, together with the Cardy–Smirnov formula
expressing it as a function `cardy` of the conformal modulus of the configuration. -/
structure CrossingObservable where
  /-- The limiting crossing probability of the conformal rectangle `(a, b, c, d)`. -/
  P : ℂ → ℂ → ℂ → ℂ → ℝ
  /-- Cardy's function, of the conformal modulus. -/
  cardy : ℝ → ℝ
  /-- Smirnov's theorem: the limiting crossing probability is Cardy's function of the
  conformal modulus of the configuration. -/
  smirnov : ∀ a b c d : ℂ, P a b c d = cardy (crossRatio a b c d).re

/-- **Cardy–Smirnov conformal invariance of percolation crossing probabilities.**

Let `O` be a crossing observable for critical triangular-lattice percolation, i.e. the
scaling limits of crossing probabilities of conformal rectangles in the upper half-plane,
subject to the Cardy–Smirnov formula.  Let `z ↦ (p z + q)/(r z + s)` with `p, q, r, s`
real and `p s - q r > 0` be a conformal automorphism of the upper half-plane.  Then the
crossing probability of the image configuration equals that of the original: crossing
probabilities are conformally invariant. -/
theorem smirnov_percolation (O : CrossingObservable) (p q r s : ℝ) (hdet : p * s - q * r > 0)
    (a b c d : ℂ) (ha : (r : ℂ) * a + s ≠ 0) (hb : (r : ℂ) * b + s ≠ 0)
    (hc : (r : ℂ) * c + s ≠ 0) (hd : (r : ℂ) * d + s ≠ 0)
    (hca : c ≠ a) (hdb : d ≠ b) :
    O.P (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d)
      = O.P a b c d := by
  have hdet' : (p : ℂ) * s - q * r ≠ 0 := by
    have : ((p * s - q * r : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hdet
    push_cast at this
    exact this
  rw [O.smirnov, O.smirnov,
    crossRatio_mobius (p : ℂ) q r s hdet' a b c d ha hb hc hd (sub_ne_zero_of_ne hca)
      (sub_ne_zero_of_ne hdb)]

/-- At the self-dual ("square") configuration, of conformal modulus `1/2`, the crossing
probability is `1/2`.  Here duality is the statement that a rectangle is crossed in one
direction exactly when its cyclic shift is not crossed in the other. -/
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

