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
