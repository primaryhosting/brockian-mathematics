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

theorem transport_one_dim_aux {F G T : ℝ → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hFmono : Monotone F)
    (hFup : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Lam * (y - x))
    (hGlow : ∀ y y' : ℝ, y ≤ y' → lam * (y' - y) ≤ G y' - G y)
    (hT : ∀ x : ℝ, G (T x) = F x) :
    ∀ x y : ℝ, T x ≤ T y → T y - T x ≤ (Lam / lam) * |x - y| := by
  have hLam0 : 0 ≤ Lam := by
    have h1 : F 0 ≤ F 1 := hFmono (by norm_num)
    have h2 : F 1 - F 0 ≤ Lam * (1 - 0) := hFup 0 1 (by norm_num)
    nlinarith
  intro x y hxy
  have h1 : lam * (T y - T x) ≤ F y - F x := by
    have := hGlow (T x) (T y) hxy
    rwa [hT, hT] at this
  rcases le_total x y with hle | hle
  · have h2 : F y - F x ≤ Lam * (y - x) := hFup x y hle
    have habs : |x - y| = y - x := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs]
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith
  · -- if `y ≤ x` then `F y ≤ F x`, forcing `T x = T y`
    have h2 : F y ≤ F x := hFmono hle
    have h3 : T y - T x ≤ 0 := by nlinarith
    have h4 : T y - T x = 0 := le_antisymm h3 (by linarith)
    rw [h4]
    exact mul_nonneg (div_nonneg hLam0 hlam.le) (abs_nonneg _)

/-- **One-dimensional regularity of the optimal transport map (base case).**
If the source measure has density bounded above by `Lam` (`hFup`) and the target measure has
density bounded below by `lam > 0` (`hGlow`), then the monotone transport map `T`,
characterised by `G ∘ T = F`, is Lipschitz with constant `Lam / lam`. -/
