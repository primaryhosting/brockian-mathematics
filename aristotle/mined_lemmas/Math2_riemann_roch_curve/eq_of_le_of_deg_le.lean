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

/-
General linear algebra helpers: quotients `b / a` of nested submodules and additivity
of their dimensions along chains.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open Submodule

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The quotient `b / a` of two submodules (interesting when `a ≤ b`). -/
abbrev Qt (a b : Submodule k M) : Type _ := b ⧸ a.submoduleOf b

/-- `b / ⊥ ≃ b`. -/

lemma eq_of_le_of_deg_le (hfin : ∀ P : Place, Module.Finite k (Qt (V.Kge P 1) (V.Kge P 0)))
    {D E : Divisor Place} (h : D ≤ E) (hd : V.deg E ≤ V.deg D) : D = E := by
  classical
  by_contra hne
  obtain ⟨Q, hQ⟩ : ∃ Q, D Q ≠ E Q := by
    by_contra hc
    push_neg at hc
    exact hne (Finsupp.ext hc)
  have hQlt : D Q < E Q := lt_of_le_of_ne (h Q) hQ
  set F : Divisor Place := E - D with hF
  have hF0 : 0 ≤ F := by intro P; simpa [hF] using h P
  have hFQ : 0 < F Q := by simp [hF]; omega
  have hdegF : V.deg F ≤ 0 := by
    rw [deg_sub]; omega
  have hQmem : Q ∈ F.support := by
    simp only [Finsupp.mem_support_iff]
    omega
  have hpos : 0 < F Q * (V.degP Q : ℤ) := by
    have := V.one_le_degP hfin Q
    have h1 : (1 : ℤ) ≤ (V.degP Q : ℤ) := by exact_mod_cast this
    nlinarith
  have hsum : 0 < V.deg F := by
    rw [deg, Finsupp.sum, ← Finset.sum_erase_add _ _ hQmem]
    have hrest : 0 ≤ ∑ P ∈ F.support.erase Q, F P * (V.degP P : ℤ) := by
      refine Finset.sum_nonneg ?_
      intro P _
      have : 0 ≤ F P := by simpa using hF0 P
      positivity
    omega
  omega

/-! ### Riemann-Roch spaces -/

/-- The Riemann-Roch space `L(D) = {x : div x + D ≥ 0}`. -/
