/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

set_option grind.warning false

namespace Frontier

open MeasureTheory Set Real

/-! ## Mirzakhani's integration kernel

Mirzakhani's recursion for Weil–Petersson volumes of moduli spaces of bordered
hyperbolic surfaces is driven by the kernel

`H (x, t) = 1 / (1 + exp ((x + t) / 2)) + 1 / (1 + exp ((x - t) / 2))`.

We write `wpPhi u = 1 / (1 + exp (u / 2))`, so that `H (x, t) = wpPhi (x+t) + wpPhi (x-t)`.
-/

/-- The basic Fermi–Dirac type profile `u ↦ 1 / (1 + e^{u/2})` out of which Mirzakhani's
integration kernel is built. -/

theorem int_id_mul_mirzakhaniH_pair (a b c d : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (mirzakhaniH x a + mirzakhaniH x b) * wpV03 x c d)
      = (a ^ 2 / 2 + 2 * Real.pi ^ 2 / 3) + (b ^ 2 / 2 + 2 * Real.pi ^ 2 / 3) := by
  have hcongr : (∫ x in Ioi (0:ℝ), x * (mirzakhaniH x a + mirzakhaniH x b) * wpV03 x c d)
      = ∫ x in Ioi (0:ℝ), (x * mirzakhaniH x a + x * mirzakhaniH x b) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    show x * (mirzakhaniH x a + mirzakhaniH x b) * wpV03 x c d
      = x * mirzakhaniH x a + x * mirzakhaniH x b
    unfold wpV03
    ring
  rw [hcongr, integral_add (integrableOn_id_mul_H a) (integrableOn_id_mul_H b),
    int_id_mul_mirzakhaniH, int_id_mul_mirzakhaniH]

/-! ## The main statement -/

/-- **Mirzakhani's recursion for Weil–Petersson volumes: base case and low-complexity
reductions.**

Mirzakhani's recursion computes the Weil–Petersson volume `V_{g,n}(L₁,…,L_n)` of the moduli
space of bordered hyperbolic surfaces of genus `g` with `n` geodesic boundary components of
lengths `L₁,…,L_n` by integrating the kernel
`H (x, t) = 1/(1 + e^{(x+t)/2}) + 1/(1 + e^{(x-t)/2})`
against volumes of lower complexity.  The four conjuncts below are:

1. the base case `V_{0,3} ≡ 1` (a pair of pants is rigid, so its moduli space is a point);

2. the fundamental kernel integral `∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3`, which is the
   `k = 0` case of Mirzakhani's formula for `F_{2k+1}` and the analytic engine of the whole
   recursion;

3. the `(g,n) = (1,1)` instance of the recursion,
   `∂_L (L · V_{1,1}(L)) = (1/4) ∫₀^∞ x H(x,L) dx`,
   for `V_{1,1}(L) = L²/24 + π²/6`.  Here the coefficient `1/4` is the overall factor `1/2`
   of the recursion times the symmetry factor `1/2` coming from the two ends of the pair of
   pants being glued to each other.  (Both `L²/24 + π²/6` and its half `L²/48 + π²/12` occur
   in the literature, according to whether the elliptic involution of the one-holed torus is
   quotiented out; the two conventions differ by the constant factor `2`, which is absorbed
   into the coefficient of the recursion.)

4. the `(g,n) = (0,4)` instance of the recursion,
   `∂_{L₁}(L₁ · V_{0,4}(L)) = (1/2) Σ_{k=2}^{4} ∫₀^∞ x (H(x, L₁+L_k) + H(x, L₁-L_k)) V_{0,3} dx`,
   for `V_{0,4}(L) = 2π² + (L₁² + L₂² + L₃² + L₄²)/2`.  For `(0,4)` no non-separating or
   separating term occurs (the corresponding surfaces are unstable), so the displayed sum is
   the complete right-hand side of Mirzakhani's recursion in this case. -/
