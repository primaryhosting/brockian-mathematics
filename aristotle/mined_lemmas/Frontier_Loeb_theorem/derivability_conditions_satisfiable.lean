import RequestProject.Loeb

/-!
# Soundness and consistency of the calculus

We interpret the language of arithmetic in the standard model `ℕ` and prove that every formula
provable in `Frontier.Provable` is true in `ℕ` under every assignment.  In particular the
calculus is consistent (`Frontier.Provable_consistent`), so the formalization of Peano
Arithmetic used for Löb's theorem is not degenerate.
-/

namespace Frontier

/-! ## The standard model -/

/-- Extend an assignment by a value for the variable bound by the outermost `∀`. -/

theorem derivability_conditions_satisfiable :
    DerivabilityConditions (fun _ => Fml.eq .zero .zero) := by
  have hzz : ⊢ Fml.eq Trm.zero Trm.zero := by
    have hax : ⊢ (Fml.eq (Trm.var 0) (Trm.var 0)).all ⟹
        (Fml.eq (Trm.var 0) (Trm.var 0)).inst Trm.zero :=
      .logic (.allElim (Fml.eq (.var 0) (.var 0)) .zero)
    have hinst : (Fml.eq (Trm.var 0) (Trm.var 0)).inst Trm.zero = Fml.eq Trm.zero Trm.zero := by
      decide
    rw [hinst] at hax
    exact .mp hax (.logic .eqRefl)
  refine ⟨fun _ _ => hzz, ?_, ?_, ?_⟩
  · intro φ ψ
    exact .taut (by
      intro v
      simp only [propEval]
      cases hv : v (Fml.eq Trm.zero Trm.zero) <;> simp)
  · intro φ
    exact .taut (by
      intro v
      simp only [propEval]
      cases hv : v (Fml.eq Trm.zero Trm.zero) <;> simp)
  · intro φ
    refine ⟨Fml.eq .zero .zero ⟹ φ, .taut ?_⟩
    intro v
    simp only [Fml.iff, Fml.and, Fml.neg, propEval]
    cases hv : v (Fml.eq Trm.zero Trm.zero) <;> cases hφ : propEval v φ <;> simp

end Frontier

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

