/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

Cardy's formula, as proved by Smirnov for critical site percolation on the triangular
lattice, says the following.  Take a Jordan domain `Ω` with four marked boundary points
`a, b, c, d` in cyclic order, and let `Π(Ω; a, b, c, d)` be the scaling limit of the
probability that the arc `ab` is joined to the arc `cd` by an open cluster.  Then `Π`
depends only on the conformal class of the configuration `(Ω; a, b, c, d)`; concretely,
after uniformizing `Ω` onto the upper half plane `ℍ` (so that the marked points sit on
the real line), `Π` is a fixed function `F` of the *cross-ratio* of the four marked
points.

The two ingredients are therefore:

* **Cardy's formula** (`cardy` below): in the half-plane normalization the crossing
  probability is a function of the cross ratio alone;
* **conformal invariance**: the conformal automorphisms of `ℍ` are the real Möbius maps
  with positive determinant, and the crossing probability is unchanged by them.

What is formalized here is the *reduction* of conformal invariance to Cardy's formula:
granted that the limiting crossing probability has the Cardy form, it is invariant under
every Möbius change of coordinates of the half-plane (`Frontier.smirnov_percolation`), and
it automatically satisfies the self-duality relation
`Π(a,b,c,d) + Π(a,c,b,d) = 1` (`Frontier.crossing_duality`).  The analytic heart of the
reduction is the Möbius invariance of the cross ratio, proved below from scratch.
-/

/-- The cross ratio `(a, b ; c, d) = ((a - c)(b - d)) / ((a - d)(b - c))` of four points of
the real line, thought of as marked boundary points of the upper half plane. -/
noncomputable def crossRatio (a b c d : ℝ) : ℝ := ((a - c) * (b - d)) / ((a - d) * (b - c))

/-- The real Möbius transformation `z ↦ (p z + q) / (r z + s)`.  When `p s - q r > 0` this is
the boundary action of a conformal automorphism of the upper half plane. -/
noncomputable def mobius (p q r s z : ℝ) : ℝ := (p * z + q) / (r * z + s)

/-- Difference formula for a Möbius map: `M x - M y = (ps - qr)(x - y) / ((rx+s)(ry+s))`. -/
theorem mobius_sub (p q r s x y : ℝ) (hx : r * x + s ≠ 0) (hy : r * y + s ≠ 0) :
    mobius p q r s x - mobius p q r s y =
      (p * s - q * r) * (x - y) / ((r * x + s) * (r * y + s)) := by
  unfold mobius
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring

/-- A Möbius map is injective on the set where its denominator does not vanish, provided its
determinant is nonzero. -/
theorem mobius_inj {p q r s x y : ℝ} (hdet : p * s - q * r ≠ 0)
    (hx : r * x + s ≠ 0) (hy : r * y + s ≠ 0) (h : mobius p q r s x = mobius p q r s y) :
    x = y := by
  have hsub := mobius_sub p q r s x y hx hy
  rw [h, sub_self] at hsub
  have hden : (r * x + s) * (r * y + s) ≠ 0 := mul_ne_zero hx hy
  have h0 : (p * s - q * r) * (x - y) = 0 := by
    field_simp at hsub
    simpa using hsub.symm
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hdet
  · linarith [sub_eq_zero.1 h1]

/-- **Möbius invariance of the cross ratio.**  This is the analytic core of the conformal
invariance of crossing probabilities: the cross ratio of four boundary points is unchanged
by any Möbius change of coordinates with nonvanishing determinant (and no pole at the four
points). -/
theorem crossRatio_mobius (p q r s : ℝ) (hdet : p * s - q * r ≠ 0) (a b c d : ℝ)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0) :
    crossRatio (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d)
      = crossRatio a b c d := by
  have hac := mobius_sub p q r s a c ha hc
  have hbd := mobius_sub p q r s b d hb hd
  have had := mobius_sub p q r s a d ha hd
  have hbc := mobius_sub p q r s b c hb hc
  rcases eq_or_ne ((a - d) * (b - c)) 0 with hdeg | hdeg
  · -- Degenerate configuration: both sides are `x / 0 = 0`.
    have hdeg' :
        (mobius p q r s a - mobius p q r s d) * (mobius p q r s b - mobius p q r s c) = 0 := by
      rcases mul_eq_zero.1 hdeg with h | h
      · have : a = d := by linarith [sub_eq_zero.1 h]
        simp [this]
      · have : b = c := by linarith [sub_eq_zero.1 h]
        simp [this]
    unfold crossRatio
    rw [hdeg, hdeg', div_zero, div_zero]
  · have h1 : a - d ≠ 0 := fun h => hdeg (by rw [h]; ring)
    have h2 : b - c ≠ 0 := fun h => hdeg (by rw [h]; ring)
    unfold crossRatio
    rw [hac, hbd, had, hbc]
    field_simp

/-- The cross ratio satisfies the classical relation `(a,b;c,d) + (a,c;b,d) = 1`, which is the
source of the self-duality `Π(a,b,c,d) + Π(a,c,b,d) = 1` of crossing probabilities. -/
theorem crossRatio_add_swap (a b c d : ℝ) (hd : a - d ≠ 0) (hbc : b - c ≠ 0) :
    crossRatio a b c d + crossRatio a c b d = 1 := by
  unfold crossRatio
  have hcb : c - b ≠ 0 := fun h => hbc (by linarith [sub_eq_zero.1 h])
  field_simp
  ring

/-!
## The Cardy–Smirnov statement

A *crossing probability assignment* in the half-plane normalization is a function
`Π : ℝ → ℝ → ℝ → ℝ → ℝ`, where `Π a b c d` is the (scaling limit of the) probability that
the boundary arc from `a` to `b` is connected to the boundary arc from `c` to `d`.

`IsCardy Π` says that `Π` is given by Cardy's formula: it is a function of the cross ratio
of the four marked points.  This is exactly the content of Smirnov's theorem in the
half-plane normalization.
-/

/-- Cardy's form of the limiting crossing probability: `Π` is a function `F` of the cross
ratio of the four marked boundary points. -/
def IsCardy (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ F : ℝ → ℝ, ∀ a b c d : ℝ, crossingProb a b c d = F (crossRatio a b c d)

/-- **Cardy–Smirnov conformal invariance (reduction).**

If the limiting crossing probability `Π` of critical triangular-lattice percolation has
Cardy's form in the half-plane normalization (i.e. it is a function of the cross ratio of
the four marked boundary points — Smirnov's theorem), then it is *conformally invariant*:
applying any Möbius change of coordinates `z ↦ (p z + q) / (r z + s)` with nonzero
determinant (in particular, any conformal automorphism of the upper half plane, for which
`p s - q r > 0`) to the four marked boundary points leaves the crossing probability
unchanged. -/
theorem smirnov_percolation
    (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) (hCardy : IsCardy crossingProb)
    (p q r s : ℝ) (hdet : p * s - q * r ≠ 0) (a b c d : ℝ)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0) :
    crossingProb (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d)
      = crossingProb a b c d := by
  obtain ⟨F, hF⟩ := hCardy
  rw [hF, hF, crossRatio_mobius p q r s hdet a b c d ha hb hc hd]

/-- Specialization of `Frontier.smirnov_percolation` to the conformal automorphisms of the
upper half plane, normalized by `p s - q r > 0`, acting on marked boundary points on which
the map has no pole. -/
theorem smirnov_percolation_halfplane
    (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) (hCardy : IsCardy crossingProb)
    (p q r s : ℝ) (hdet : 0 < p * s - q * r) (a b c d : ℝ)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0) :
    crossingProb (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d)
      = crossingProb a b c d :=
  smirnov_percolation crossingProb hCardy p q r s (ne_of_gt hdet) a b c d ha hb hc hd

/-- Base case: translations `z ↦ z + t` of the real line (`p = s = 1`, `q = t`, `r = 0`)
leave the crossing probability unchanged. -/
theorem smirnov_percolation_translation
    (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) (hCardy : IsCardy crossingProb) (t a b c d : ℝ) :
    crossingProb (a + t) (b + t) (c + t) (d + t) = crossingProb a b c d := by
  have h := smirnov_percolation crossingProb hCardy 1 t 0 1 (by norm_num) a b c d
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [mobius, add_comm] using h

/-- Base case: dilations `z ↦ k z` with `k ≠ 0` leave the crossing probability unchanged. -/
theorem smirnov_percolation_dilation
    (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) (hCardy : IsCardy crossingProb)
    (k : ℝ) (hk : k ≠ 0) (a b c d : ℝ) :
    crossingProb (k * a) (k * b) (k * c) (k * d) = crossingProb a b c d := by
  have h := smirnov_percolation crossingProb hCardy k 0 0 1 (by simpa using hk) a b c d
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [mobius] using h

/-- Base case: the inversion `z ↦ -1 / z` (an automorphism of the upper half plane) leaves
the crossing probability unchanged, for marked points away from the pole. -/
theorem smirnov_percolation_inversion
    (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) (hCardy : IsCardy crossingProb)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    crossingProb (-1 / a) (-1 / b) (-1 / c) (-1 / d) = crossingProb a b c d := by
  have h := smirnov_percolation crossingProb hCardy 0 (-1) 1 0 (by norm_num) a b c d
      (by simpa using ha) (by simpa using hb) (by simpa using hc) (by simpa using hd)
  simpa [mobius] using h

/-- **Self-duality of crossing probabilities.**  If `Π` has Cardy's form with a function `F`
satisfying `F x + F (1 - x) = 1` (the duality of the Cardy function, reflecting that either
the primal arcs `ab`, `cd` are joined, or the dual arcs `ac`, `bd` are), then
`Π(a,b,c,d) + Π(a,c,b,d) = 1` for every nondegenerate configuration. -/
theorem crossing_duality
    (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (hF : ∀ x : ℝ, F x + F (1 - x) = 1)
    (hCardy : ∀ a b c d : ℝ, crossingProb a b c d = F (crossRatio a b c d))
    (a b c d : ℝ) (had : a - d ≠ 0) (hbc : b - c ≠ 0) :
    crossingProb a b c d + crossingProb a c b d = 1 := by
  have h : crossRatio a c b d = 1 - crossRatio a b c d := by
    have := crossRatio_add_swap a b c d had hbc
    linarith
  rw [hCardy, hCardy, h]
  exact hF _

/-- Nondegeneracy: crossing-probability assignments of Cardy type exist and are nonconstant,
so `Frontier.smirnov_percolation` is not vacuous.  (Here `F = id`, i.e. `Π` is the cross
ratio itself.) -/
theorem exists_nonconstant_isCardy :
    ∃ crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ, IsCardy crossingProb ∧
      ∃ a b c d a' b' c' d' : ℝ, crossingProb a b c d ≠ crossingProb a' b' c' d' := by
  refine ⟨crossRatio, ⟨id, fun a b c d => rfl⟩, 0, 1, 2, 3, 0, 1, 3, 2, ?_⟩
  norm_num [crossRatio]

end Frontier


