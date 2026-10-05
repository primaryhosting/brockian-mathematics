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

import Mathlib
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem isPoly_majorant {γ : Type} {p : (γ → ℕ) → ℤ} (hp : IsPoly p) :
    ∃ q : (γ → ℕ) → ℤ, IsPoly q ∧ (∀ v, |p v| ≤ q v) ∧
      (∀ v w : γ → ℕ, (∀ i, v i ≤ w i) → q v ≤ q w) := by
  induction hp with
  | proj i => exact ⟨_, IsPoly.proj i, fun v => by simp, fun v w h => by exact_mod_cast h i⟩
  | const n => exact ⟨_, IsPoly.const |n|, fun _ => le_refl _, fun _ _ _ => le_refl _⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hb1, hm1⟩ := ih1; obtain ⟨q2, hq2, hb2, hm2⟩ := ih2
      refine ⟨fun x => q1 x + q2 x, hq1.add hq2, fun v => ?_, fun v w h => ?_⟩
      · exact le_trans (abs_sub _ _) (add_le_add (hb1 v) (hb2 v))
      · exact add_le_add (hm1 v w h) (hm2 v w h)
  | mul _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hb1, hm1⟩ := ih1; obtain ⟨q2, hq2, hb2, hm2⟩ := ih2
      refine ⟨fun x => q1 x * q2 x, hq1.mul hq2, fun v => ?_, fun v w h => ?_⟩
      · rw [abs_mul]
        exact mul_le_mul (hb1 v) (hb2 v) (abs_nonneg _) (le_trans (abs_nonneg _) (hb1 v))
      · exact mul_le_mul (hm1 v w h) (hm2 v w h) (le_trans (abs_nonneg _) (hb2 v))
          (le_trans (le_trans (abs_nonneg _) (hb1 v)) (hm1 v w h))

/-- Polynomials respect congruences. -/
