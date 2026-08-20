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
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-! ### The Ma–Trudinger–Wang condition (Loeper's form) -/

section MTW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem figalli_OT_regularity_ae_differentiable
    {f g : ℝ → ℝ≥0∞} {lam Lam : ℝ≥0} (hlam : 0 < lam)
    (hfub : ∀ x, f x ≤ Lam) (hglb : ∀ y, (lam : ℝ≥0∞) ≤ g y)
    {T : ℝ → ℝ}
    (hopt : ∀ x y : ℝ,
      quadCost x (T x) + quadCost y (T y) ≤ quadCost x (T y) + quadCost y (T x))
    (hpush : Measure.map T (volume.withDensity f) = volume.withDensity g) :
    (∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ T x) ∧
      ∀ x, |deriv T x| ≤ ((Lam / lam : ℝ≥0) : ℝ) := by
  have hL : LipschitzWith (Lam / lam) T := figalli_OT_regularity hlam hfub hglb hopt hpush
  refine ⟨hL.ae_differentiableAt, fun x => ?_⟩
  simpa using norm_deriv_le_of_lipschitz hL (x₀ := x)

/-- The hypotheses of `Frontier.figalli_OT_regularity` are non-vacuous: the identity map is
the optimal map from Lebesgue measure to itself, and the theorem returns the sharp
Lipschitz constant `1`. -/
example : LipschitzWith ((1 : ℝ≥0) / 1) (id : ℝ → ℝ) :=
  figalli_OT_regularity (f := fun _ => 1) (g := fun _ => 1) (lam := 1) (Lam := 1)
    one_pos (fun _ => le_rfl) (fun _ => le_rfl)
    (fun x y => by simp only [quadCost, id, sub_self, norm_zero]; norm_num; positivity)
    (by rw [Measure.map_id])

end Frontier

