import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem gPerm_bijective :
    Function.Bijective
      (fun x : Σ τ : Equiv.Perm (Fin n), ∀ i, Fin (W i (τ i)) =>
        (⟨gPerm W x.1 x.2, gPerm_witness W x.1 x.2⟩ :
          {σ : Equiv.Perm (Vtx W) // ∀ v, gadget W v (σ v) = 1})) := by
  classical
  constructor
  · rintro ⟨τ, c⟩ ⟨τ', c'⟩ h
    simp only [Subtype.mk.injEq] at h
    have hval : ∀ i, gIdx W τ c i = gIdx W τ' c' i := by
      intro i
      have h2 := congrArg (fun e : Equiv.Perm (Vtx W) => e (Sum.inl i)) h
      simp only [gPerm_apply, gFun, Sum.elim_inl] at h2
      exact Sum.inr_injective h2
    have hτ : τ = τ' := by
      refine Equiv.ext (fun i => ?_)
      have h2 := congrArg (fun z : Idx W => (Sigma.fst z).2) (hval i)
      simpa [gIdx] using h2
    subst hτ
    have hc : c = c' := by
      funext i
      have h2 := hval i
      simpa [gIdx] using h2
    rw [hc]
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, c, hτc⟩ := exists_gFun W σ hσ
    exact ⟨⟨τ, c⟩, Subtype.ext (Equiv.ext (fun v => (gPerm_apply W τ c v).trans (hτc v)))⟩

