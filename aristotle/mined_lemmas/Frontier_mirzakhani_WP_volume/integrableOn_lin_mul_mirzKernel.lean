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

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

lemma integrableOn_lin_mul_mirzKernel (s : ℝ) :
    IntegrableOn (fun x => x * mirzKernel x s) (Ioi 0) volume := by
  have iA : IntegrableOn (fun x => x * logistic (x + s)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 s
  have iB : IntegrableOn (fun x => x * logistic (x + -s)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 (-s)
  have iAB : IntegrableOn (fun x => x * logistic (x + s) + x * logistic (x + -s))
      (Ioi 0) volume := iA.add iB
  refine iAB.congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [mirzKernel_eq, sub_eq_add_neg]
  ring

/-! ## The main statement -/

/--
**Mirzakhani's recursion for Weil–Petersson volumes: base cases and reduction.**

With `H` Mirzakhani's integration kernel, the recursion reads
`∂_{L₁} (L₁ V_{g,n}(L)) = (1/2) ∫∫ x y H(x+y, L₁) P(x,y,L̂) dx dy
   + Σ_{k≥2} (1/2) ∫ x (H(x, L₁+L_k) + H(x, L₁-L_k)) V_{g,n-1}(x, L̂) dx`.

We verify:
* the base case `V_{0,3} = 1`;
* the `(g,n) = (1,1)` instance of the recursion: here the pair of pants obtained by cutting a
  one-holed torus has its two remaining boundary components glued to each other, and the term
  carries the factor `1/4 = (1/2)·(1/2)` coming from the elliptic involution and from the
  interchangeability of the two ends of the cut curve, so the recursion reads
  `∂_L (L V_{1,1}(L)) = (1/2) · (1/4) · ∫₀^∞ x H(x, L) dx`, for `V_{1,1}(L) = (L² + 4π²)/48`;
* the `(g,n) = (0,4)` instance of the recursion (here the `P`-term vanishes, since no
  stable splitting exists), for `V_{0,4}(L) = 2π² + (Σ L_i²)/2`;
* a Lean-checked reduction: the `(1,1)` recursion together with the kernel integral
  *determines* `V_{1,1}` uniquely.
-/
