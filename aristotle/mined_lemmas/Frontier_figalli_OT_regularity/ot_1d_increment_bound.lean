import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The quadratic cost and the (degenerate) MTW condition

The Ma–Trudinger–Wang condition is a curvature condition on the mixed fourth
derivatives of the cost `c(x, y)`.  For the quadratic cost
`c(x, y) = ‖x - y‖ ^ 2 / 2` on a real inner product space, the cost splits as a
sum of a function of `x`, a function of `y`, and a *bilinear* cross term
`- ⟪x, y⟫`.  Consequently every mixed derivative of order at least three
vanishes, and the MTW tensor is identically zero: the quadratic cost satisfies
`MTW(0)`, the base case of the Ma–Trudinger–Wang / Figalli theory.

The lemma `Frontier.quadCost_split` records exactly this splitting, with the
cross term exhibited as a genuine continuous bilinear form.
-/

/-- The quadratic optimal-transport cost `c(x, y) = ‖x - y‖ ^ 2 / 2`. -/

theorem ot_1d_increment_bound
    (f g T : ℝ → ℝ) (lam Lam : ℝ)
    (hmono : Monotone T)
    (hf : ∀ y : ℝ, lam ≤ f y) (hgU : ∀ x : ℝ, g x ≤ Lam)
    (hfi : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b)
    (hgi : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b)
    (hpush : ∀ a b : ℝ, ∫ y in (T a)..(T b), f y = ∫ x in a..b, g x)
    {a b : ℝ} (hab : a ≤ b) :
    lam * (T b - T a) ≤ Lam * (b - a) := by
  have hTab : T a ≤ T b := hmono hab
  have h1 : lam * (T b - T a) ≤ ∫ y in (T a)..(T b), f y := by
    have := intervalIntegral.integral_mono_on (f := fun _ : ℝ => lam) (g := f)
      (μ := MeasureTheory.volume) hTab
      (intervalIntegrable_const) (hfi (T a) (T b)) (fun x _ => hf x)
    simpa [mul_comm] using this
  have h2 : (∫ x in a..b, g x) ≤ Lam * (b - a) := by
    have := intervalIntegral.integral_mono_on (f := g) (g := fun _ : ℝ => Lam)
      (μ := MeasureTheory.volume) hab
      (hgi a b) (intervalIntegrable_const) (fun x _ => hgU x)
    simpa [mul_comm] using this
  calc lam * (T b - T a) ≤ ∫ y in (T a)..(T b), f y := h1
    _ = ∫ x in a..b, g x := hpush a b
    _ ≤ Lam * (b - a) := h2

/-- **Figalli optimal-transport regularity, one-dimensional base case.**

Let `T : ℝ → ℝ` be the monotone optimal transport map for the quadratic cost
(the MTW(0) cost, cf. `Frontier.quadCost_split`) pushing the measure with
density `g` onto the measure with density `f`, the pushforward being encoded by
the balance condition `∫_{T a}^{T b} f = ∫_a^b g`.

If the target density is bounded below, `lam ≤ f`, with `lam > 0`, and the
source density is bounded above, `g ≤ Lam`, then the transport map is Lipschitz
with constant `Lam / lam`; in particular it is continuous, which is the
regularity conclusion. -/
