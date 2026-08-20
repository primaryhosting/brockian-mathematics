import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

theorem integral_quadrant_mirzKernel (t : ℝ) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), x * y * mirzKernel (x + y) t) = F3 t / 6 := by
  have hmeas : Measurable (fun s => mirzKernel s t) := by
    have : Continuous (fun s => mirzKernel s t) := by
      unfold mirzKernel
      exact (continuous_fd.comp (continuous_id.add continuous_const)).add
        (continuous_fd.comp (continuous_id.sub continuous_const))
    exact this.measurable
  rw [integral_quadrant hmeas (C := Real.exp (-(t/2)) + Real.exp (t/2))
    (fun s => abs_mirzKernel_le t s), F3]
  ring

end Frontier

/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is written as an ordinary block comment.)

import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim
import RequestProject.Volumes

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open MeasureTheory Set Real

/-!
## Overview

Mirzakhani's recursion expresses the Weil–Petersson volume `V_{g,n}(L₁,…,L_n)` of the
moduli space of genus `g` hyperbolic surfaces with `n` geodesic boundary components of
lengths `L₁,…,L_n` through volumes of smaller complexity:

```
∂/∂L₁ (L₁ · V_{g,n}(L))
  = ½ ∫₀^∞ ∫₀^∞ x y H(x+y, L₁) V_{g-1,n+1}(x, y, L̂) dx dy          (non-separating)
  + ½ Σ_{stable splittings} ∫₀^∞ ∫₀^∞ x y H(x+y, L₁) V₁(x,·) V₂(y,·) dx dy  (separating)
  + ½ Σ_{j=2}^{n} ∫₀^∞ x (H(x, L₁+L_j) + H(x, L₁-L_j)) V_{g,n-1}(x, L̂_j) dx  (`B`-term)
```

where the kernel is `H(x,t) = 1/(1+e^{(x+t)/2}) + 1/(1+e^{(x-t)/2})`.

The analytic input is developed in `RequestProject.Kernel` and `RequestProject.TwoDim`:

* the moment transforms `F₁(t) = ∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3` and
  `F₃(t) = ∫₀^∞ x³ H(x,t) dx = t⁴/4 + 2π²t² + 28π⁴/15`;
* the two-dimensional identity `∫₀^∞ ∫₀^∞ x y H(x+y,t) dx dy = F₃(t)/6`.

`RequestProject.Volumes` then records the volume polynomials in low complexity and
verifies Mirzakhani's recursion in the first two nontrivial cases:

* the base case `V_{0,3} = 1`;
* the recursion for `(g,n) = (0,4)`, where the separating and non-separating terms are
  vacuous since no stable splitting exists, with
  `V_{0,4}(L) = 2π² + ½ Σ L_i²`;
* the recursion for `(g,n) = (0,5)`, where the separating term is present — a sum over the
  six ordered splittings of the remaining four boundary components into two pairs, each
  contributing a product `V_{0,3}·V_{0,3}` — and the `B`-term involves `V_{0,4}`, with
  `V_{0,5}(L) = ¼(Σ L_i²)² − ⅛ Σ L_i⁴ + 3π² Σ L_i² + 10π⁴`;
* the converse in each case: the recursion *determines* the volume polynomial (for
  `L₁ ≠ 0`; the value at `L₁ = 0` is not pinned down pointwise by the recursion, though
  it is by continuity).

Mathlib contains no Weil–Petersson theory, so no existing lemma closes the statement; the
Mathlib results carrying the analytic work here are `integrable_of_isBigO_exp_neg` and
`Real.pow_div_factorial_le_exp` (convergence of the moment integrals),
`hasSum_zeta_two` / `hasSum_zeta_four` (the values `η(2) = π²/12` and
`η(4) = 7π⁴/720` of the alternating zeta values produced by the Fermi–Dirac expansion of
the kernel), `measurePreserving_prod_add` together with
`MeasureTheory.integral_integral_swap` (Fubini for the shear `(x,y) ↦ (x, x+y)`, giving the
two-dimensional term), and `is_const_of_deriv_eq_zero` (the uniqueness statements).
-/

/-- **Mirzakhani's recursion for Weil–Petersson volumes, verified in the first two
nontrivial complexities.**

* The base case: the volume of the moduli space of pairs of pants is `V_{0,3} = 1`.
* Mirzakhani's recursion
  `∂/∂L₁ (L₁ V_{g,n}(L)) = ½ Σ_{stable splittings} ∫∫ x y H(x+y,L₁) V₁(x,·) V₂(y,·) dx dy
     + ½ Σ_{j≥2} ∫₀^∞ x (H(x,L₁+L_j)+H(x,L₁-L_j)) V_{g,n-1}(x, L̂) dx`
  holds for `(g,n) = (0,4)` with `V_{0,4}(L) = 2π² + ½ Σ L_i²` (where the separating and
  non-separating terms are vacuous), and for `(g,n) = (0,5)` with
  `V_{0,5}(L) = ¼(Σ L_i²)² − ⅛ Σ L_i⁴ + 3π² Σ L_i² + 10π⁴` (where the separating term
  contributes through the two-dimensional integral `∫∫ x y H(x+y,L₁) dx dy = F₃(L₁)/6`).
* Conversely, the recursion together with the base case *determines* these volumes:
  any function satisfying it agrees with `V_{0,4}` resp. `V_{0,5}` whenever `L₁ ≠ 0`.
-/
