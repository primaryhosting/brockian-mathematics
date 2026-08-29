import Mathlib
/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` lines to precede every other command in a file,
-- including module doc comments, so the single `import Mathlib` line above is the
-- only thing preceding the requested header comment.

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- The Bekenstein entropy bound `2 π k R E / (ℏ c)` for a system of radius `R`
and total energy `E`, with Boltzmann constant `k`, reduced Planck constant `ℏ`
and speed of light `c`. -/
noncomputable def bekensteinBound (k hbar c R E : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Bekenstein–Hawking entropy `k c³ A / (4 G ℏ)` of a black-hole horizon of
area `A`. -/
noncomputable def bekensteinHawkingEntropy (k hbar c G A : ℝ) : ℝ :=
  k * c ^ 3 * A / (4 * G * hbar)

/--
**Bekenstein bound.**  `S ≤ 2 π k R E / (ℏ c)`.

This is Bekenstein's original gedanken-experiment derivation, formalized with its
physical inputs as explicit hypotheses:

* a system of entropy `S`, energy `E` and radius `R` is dropped into a black hole
  whose horizon area is `A₀`, leaving the exterior world;
* the resulting horizon area is `A₁ = A₀ + 8 π G E R / c⁴`, the (minimal) area
  increase caused by absorbing energy `E` carried by a body of radius `R`
  (hypothesis `harea`);
* the generalized second law says that the black-hole entropy gain is at least the
  entropy `S` removed from the exterior world (hypothesis `hGSL`), black-hole
  entropy being the Bekenstein–Hawking entropy `k c³ A / (4 G ℏ)`.

Evaluating the entropy difference gives exactly the Bekenstein bound
`S ≤ 2 π k R E / (ℏ c)`.
-/
theorem bekenstein_bound
    (k hbar c G S R E A₀ A₁ : ℝ)
    (hhbar : 0 < hbar) (hc : 0 < c) (hG : 0 < G)
    (harea : A₁ = A₀ + 8 * Real.pi * G * E * R / c ^ 4)
    (hGSL : S + bekensteinHawkingEntropy k hbar c G A₀
              ≤ bekensteinHawkingEntropy k hbar c G A₁) :
    S ≤ bekensteinBound k hbar c R E := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hG0 : G ≠ 0 := ne_of_gt hG
  have hh0 : hbar ≠ 0 := ne_of_gt hhbar
  have hkey : bekensteinHawkingEntropy k hbar c G A₁
      - bekensteinHawkingEntropy k hbar c G A₀ = bekensteinBound k hbar c R E := by
    subst harea
    unfold bekensteinHawkingEntropy bekensteinBound
    field_simp
    ring
  linarith [hkey]

/-- Unfolded form of the Bekenstein bound: the conclusion written out explicitly
as `S ≤ 2 π k R E / (ℏ c)`. -/
theorem bekenstein_bound' (k hbar c G S R E A₀ A₁ : ℝ)
    (hhbar : 0 < hbar) (hc : 0 < c) (hG : 0 < G)
    (harea : A₁ = A₀ + 8 * Real.pi * G * E * R / c ^ 4)
    (hGSL : S + k * c ^ 3 * A₀ / (4 * G * hbar) ≤ k * c ^ 3 * A₁ / (4 * G * hbar)) :
    S ≤ 2 * Real.pi * k * R * E / (hbar * c) :=
  bekenstein_bound k hbar c G S R E A₀ A₁ hhbar hc hG harea hGSL

end Phys

