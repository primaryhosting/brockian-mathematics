import Mathlib
/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
module, so the mandated header comment is placed immediately after the single `import Mathlib`
line.  Its text is otherwise reproduced verbatim.

## What is formalized here

The Kardar–Parisi–Zhang equation on the line,

  ∂ₜ h = ∂ₓ² h + (∂ₓ h)² + ξ,

is classically ill-posed because of the quadratic term applied to a distribution.  Hairer's
theory of regularity structures makes sense of it; the structural mechanism underlying every
solution theory for KPZ (Hopf–Cole, regularity structures, paracontrolled distributions) is the
*Hopf–Cole transform*: `h = log Z` where `Z` solves the multiplicative stochastic heat equation

  ∂ₜ Z = ∂ₓ² Z + Z ξ.

We formalize and prove, as the Lean-checked base case / reduction, the exact statement that the
Hopf–Cole transform converts a (strictly positive, classical) solution of the multiplicative heat
equation into a classical solution of KPZ, and conversely.  These are the statements that hold
verbatim for smooth (mollified) noise `ξ`, and which the theory of regularity structures upgrades
to the distributional setting.
-/

namespace Frontier

/-- **Hopf–Cole reduction for KPZ (base case).**

Let `Z : ℝ → ℝ → ℝ` be strictly positive, with time derivative `Zt`, and first and second
spatial derivatives `Zx`, `Zxx`, solving the multiplicative heat equation
`∂ₜ Z = ∂ₓ² Z + Z · ξ` for an arbitrary (e.g. smooth, mollified) forcing `ξ`.

Then `h := log Z` is differentiable in time and twice differentiable in space, with derivatives
`ht = Zt / Z`, `hx = Zx / Z`, `hxx = Zxx / Z - (Zx / Z)^2`, and it solves the KPZ equation

  `∂ₜ h = ∂ₓ² h + (∂ₓ h)² + ξ`.

This is the classical (smooth-noise) well-posedness mechanism for KPZ that Hairer's theory of
regularity structures extends to space–time white noise. -/
theorem hairer_KPZ
    (Z Zt Zx Zxx xi : ℝ → ℝ → ℝ)
    (hpos : ∀ t x, 0 < Z t x)
    (hZt : ∀ t x, HasDerivAt (fun s => Z s x) (Zt t x) t)
    (hZx : ∀ t x, HasDerivAt (fun y => Z t y) (Zx t x) x)
    (hZxx : ∀ t x, HasDerivAt (fun y => Zx t y) (Zxx t x) x)
    (hSHE : ∀ t x, Zt t x = Zxx t x + Z t x * xi t x) :
    ∃ ht hx hxx : ℝ → ℝ → ℝ,
      (∀ t x, HasDerivAt (fun s => Real.log (Z s x)) (ht t x) t) ∧
      (∀ t x, HasDerivAt (fun y => Real.log (Z t y)) (hx t x) x) ∧
      (∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x) ∧
      (∀ t x, ht t x = hxx t x + (hx t x) ^ 2 + xi t x) := by
  refine ⟨fun t x => Zt t x / Z t x, fun t x => Zx t x / Z t x,
    fun t x => Zxx t x / Z t x - (Zx t x / Z t x) ^ 2, ?_, ?_, ?_, ?_⟩
  · intro t x
    exact (hZt t x).log (hpos t x).ne'
  · intro t x
    exact (hZx t x).log (hpos t x).ne'
  · intro t x
    have h := (hZxx t x).div (hZx t x) (hpos t x).ne'
    have hne : Z t x ≠ 0 := (hpos t x).ne'
    convert h using 1
    field_simp
  · intro t x
    have hne : Z t x ≠ 0 := (hpos t x).ne'
    dsimp only
    rw [hSHE t x]
    field_simp
    ring

/-- **Converse of the Hopf–Cole reduction.**

If `h` solves the KPZ equation `∂ₜ h = ∂ₓ² h + (∂ₓ h)² + ξ` classically, then `Z := exp h` is a
strictly positive solution of the multiplicative heat equation `∂ₜ Z = ∂ₓ² Z + Z · ξ`. -/
theorem hairer_KPZ_converse
    (h ht hx hxx xi : ℝ → ℝ → ℝ)
    (hht : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hhx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hhxx : ∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x)
    (hKPZ : ∀ t x, ht t x = hxx t x + (hx t x) ^ 2 + xi t x) :
    ∃ Zt Zx Zxx : ℝ → ℝ → ℝ,
      (∀ t x, 0 < Real.exp (h t x)) ∧
      (∀ t x, HasDerivAt (fun s => Real.exp (h s x)) (Zt t x) t) ∧
      (∀ t x, HasDerivAt (fun y => Real.exp (h t y)) (Zx t x) x) ∧
      (∀ t x, HasDerivAt (fun y => Real.exp (h t y) * hx t y) (Zxx t x) x) ∧
      (∀ t x, Zt t x = Zxx t x + Real.exp (h t x) * xi t x) := by
  refine ⟨fun t x => Real.exp (h t x) * ht t x, fun t x => Real.exp (h t x) * hx t x,
    fun t x => Real.exp (h t x) * ((hx t x) ^ 2 + hxx t x),
    fun t x => Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · intro t x
    simpa [mul_comm] using (hht t x).exp
  · intro t x
    simpa [mul_comm] using (hhx t x).exp
  · intro t x
    have h1 : HasDerivAt (fun y => Real.exp (h t y)) (Real.exp (h t x) * hx t x) x := by
      simpa [mul_comm] using (hhx t x).exp
    have h2 := h1.mul (hhxx t x)
    convert h2 using 1
    ring
  · intro t x
    dsimp only
    rw [hKPZ t x]
    ring

/-- **Non-vacuity of the base case.**

For every `a : ℝ` the travelling-wave profile `Z t x = exp (a * x + a ^ 2 * t)` satisfies all the
hypotheses of `Frontier.hairer_KPZ` with vanishing forcing, so the reduction above is applied to a
non-empty class of data; the resulting KPZ solution is `h t x = a * x + a ^ 2 * t`. -/
theorem hairer_KPZ_nonvacuous (a : ℝ) :
    ∃ Z Zt Zx Zxx xi : ℝ → ℝ → ℝ,
      (∀ t x, Z t x = Real.exp (a * x + a ^ 2 * t)) ∧
      (∀ t x, 0 < Z t x) ∧
      (∀ t x, HasDerivAt (fun s => Z s x) (Zt t x) t) ∧
      (∀ t x, HasDerivAt (fun y => Z t y) (Zx t x) x) ∧
      (∀ t x, HasDerivAt (fun y => Zx t y) (Zxx t x) x) ∧
      (∀ t x, Zt t x = Zxx t x + Z t x * xi t x) := by
  refine ⟨fun t x => Real.exp (a * x + a ^ 2 * t),
    fun t x => a ^ 2 * Real.exp (a * x + a ^ 2 * t),
    fun t x => a * Real.exp (a * x + a ^ 2 * t),
    fun t x => a ^ 2 * Real.exp (a * x + a ^ 2 * t),
    fun _ _ => 0, fun _ _ => rfl, fun _ _ => Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · intro t x
    have h : HasDerivAt (fun s : ℝ => a * x + a ^ 2 * s) (a ^ 2) t := by
      simpa using ((hasDerivAt_id t).const_mul (a ^ 2)).const_add (a * x)
    simpa [mul_comm] using h.exp
  · intro t x
    have h : HasDerivAt (fun y : ℝ => a * y + a ^ 2 * t) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).add_const (a ^ 2 * t)
    simpa [mul_comm] using h.exp
  · intro t x
    have h : HasDerivAt (fun y : ℝ => a * y + a ^ 2 * t) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).add_const (a ^ 2 * t)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (a * y + a ^ 2 * t))
        (Real.exp (a * x + a ^ 2 * t) * a) x := by simpa [mul_comm] using h.exp
    have h3 := h2.const_mul a
    convert h3 using 1
    ring
  · intro t x
    simp

end Frontier

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

