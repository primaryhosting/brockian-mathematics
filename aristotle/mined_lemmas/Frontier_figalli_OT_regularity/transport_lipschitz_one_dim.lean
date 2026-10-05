/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-! ## The cost function and the Ma–Trudinger–Wang condition -/

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖² / 2` on a real inner product
space. -/

theorem transport_lipschitz_one_dim {F G T : ℝ → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hFmono : Monotone F)
    (hFup : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Lam * (y - x))
    (hGlow : ∀ y y' : ℝ, y ≤ y' → lam * (y' - y) ≤ G y' - G y)
    (hT : ∀ x : ℝ, G (T x) = F x) :
    ∀ x y : ℝ, |T x - T y| ≤ (Lam / lam) * |x - y| := by
  intro x y
  rcases le_total (T x) (T y) with h | h
  · have := transport_one_dim_aux hlam hFmono hFup hGlow hT x y h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this
  · have := transport_one_dim_aux hlam hFmono hFup hGlow hT y x h
    rw [abs_of_nonneg (show (0:ℝ) ≤ T x - T y by linarith), abs_sub_comm x y]
    exact this

/-! ## Induction on the dimension -/

/-- Auxiliary induction on the dimension: a pointwise Lipschitz bound on the coordinates
gives a bound on the sums of squares.  Proved by induction on `n`. -/
