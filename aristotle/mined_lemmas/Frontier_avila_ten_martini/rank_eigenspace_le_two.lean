/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ, ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev H2 := ℓ²(ℤ, ℂ)

instance : Nontrivial H2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have : (lp.single 2 (0 : ℤ) (1 : ℂ) : ℤ → ℂ) 0 = (0 : H2) 0 := by rw [h]
  simp [lp.single_apply] at this

/-! ## Shift operators -/


theorem rank_eigenspace_le_two (lam alpha theta : ℝ) (E : ℂ) :
    Module.rank ℂ
        (LinearMap.ker (almostMathieu lam alpha theta - E • (1 : H2 →L[ℂ] H2) :
          H2 →L[ℂ] H2).toLinearMap) ≤ 2 := by
  set A := almostMathieu lam alpha theta
  set K := LinearMap.ker (A - E • (1 : H2 →L[ℂ] H2) : H2 →L[ℂ] H2).toLinearMap
  have hmem : ∀ u : H2, u ∈ K → A u = E • u := by
    intro u hu
    have : (A - E • (1 : H2 →L[ℂ] H2)) u = 0 := hu
    simpa [sub_eq_zero] using this
  let ev : K →ₗ[ℂ] ℂ × ℂ :=
    { toFun := fun u => (((u : H2) : ℤ → ℂ) 0, ((u : H2) : ℤ → ℂ) 1)
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hinj : Function.Injective ev := by
    intro a b hab
    have h0 : ((a : H2) : ℤ → ℂ) 0 = ((b : H2) : ℤ → ℂ) 0 := congrArg Prod.fst hab
    have h1 : ((a : H2) : ℤ → ℂ) 1 = ((b : H2) : ℤ → ℂ) 1 := congrArg Prod.snd hab
    exact Subtype.ext
      (eigenvector_eq_of_eq_at_zero_one (hmem _ a.2) (hmem _ b.2) h0 h1)
  have h := LinearMap.rank_le_of_injective ev hinj
  have h2 : Module.rank ℂ (ℂ × ℂ) = 2 := by simpa using one_add_one_eq_two
  rwa [h2] at h

/-! ## The real spectrum of the almost Mathieu operator -/

/-- The (real) spectrum of the almost Mathieu operator. -/
