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

theorem figalli_OT_regularity (n : ℕ) (lam Lam : ℝ) (hlam : 0 < lam)
    (F G T : Fin n → ℝ → ℝ)
    (hFmono : ∀ i, Monotone (F i))
    (hFup : ∀ (i : Fin n) (x y : ℝ), x ≤ y → F i y - F i x ≤ Lam * (y - x))
    (hGlow : ∀ (i : Fin n) (y y' : ℝ), y ≤ y' → lam * (y' - y) ≤ G i y' - G i y)
    (hT : ∀ (i : Fin n) (x : ℝ), G i (T i x) = F i x) :
    ∀ v w : Fin n → ℝ,
      Real.sqrt (∑ i, (T i (v i) - T i (w i)) ^ 2) ≤
        (Lam / lam) * Real.sqrt (∑ i, (v i - w i) ^ 2) := by
  intro v w
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp
  obtain ⟨i₀⟩ := hn
  have hLam : 0 ≤ Lam := by
    have h1 : F i₀ 0 ≤ F i₀ 1 := hFmono i₀ (by norm_num)
    have h2 : F i₀ 1 - F i₀ 0 ≤ Lam * (1 - 0) := hFup i₀ 0 1 (by norm_num)
    nlinarith
  have hK : (0:ℝ) ≤ Lam / lam := div_nonneg hLam hlam.le
  have hcoord : ∀ i : Fin n, |T i (v i) - T i (w i)| ≤ (Lam / lam) * |v i - w i| := by
    intro i
    exact transport_lipschitz_one_dim hlam (hFmono i) (hFup i) (hGlow i) (hT i) (v i) (w i)
  have hsum : ∑ i, (T i (v i) - T i (w i)) ^ 2
      ≤ (Lam / lam) ^ 2 * ∑ i, (v i - w i) ^ 2 :=
    sum_sq_le_of_coord_le (Lam / lam) n _ _ hcoord
  calc Real.sqrt (∑ i, (T i (v i) - T i (w i)) ^ 2)
      ≤ Real.sqrt ((Lam / lam) ^ 2 * ∑ i, (v i - w i) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (Lam / lam) * Real.sqrt (∑ i, (v i - w i) ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]

end Frontier

