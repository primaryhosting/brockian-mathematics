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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

The first part of this file develops the abstract von Neumann / Weyl deficiency criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space.

The second part constructs the minimal Schrödinger operator `-d²/dx² + V` on `L²(ℝ)`, with domain
the smooth compactly supported functions, and shows that it is essentially self-adjoint as soon as
the differential equation `-u'' + V u = ± i u` has no nonzero solution in `L²(ℝ)` (understood in
the distributional sense).
-/

namespace Brockian.Weyl

open LinearPMap Complex

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A partially defined operator `T` on a complex inner product space is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in its domain. -/

theorem isSelfAdjoint_closure_of_deficiency {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hs : IsSymmetricPMap T)
    (hpos : ∀ u : T.adjoint.domain, T.adjoint u = Complex.I • (u : E) → (u : E) = 0)
    (hneg : ∀ u : T.adjoint.domain, T.adjoint u = -Complex.I • (u : E) → (u : E) = 0) :
    IsSelfAdjoint T.closure := by
  have hAsym : IsSymmetricPMap T.closure := isSymmetric_closure hT hs
  have hAdense : Dense (T.closure.domain : Set E) := dense_closure_domain hT
  have hAclosed : T.closure.IsClosed := (isClosable_of_isSymmetric hT hs).closure_isClosed
  have hAle : T.closure ≤ T.adjoint := closure_le_adjoint hT hs
  -- surjectivity of `closure - i`
  have hrangetop : LinearMap.range (shiftMap T.closure (-1 : ℝ)) = ⊤ := by
    have hclosed := isClosed_range_shiftMap hAclosed hAsym (c := (-1 : ℝ)) (by norm_num)
    haveI : CompleteSpace (LinearMap.range (shiftMap T.closure (-1 : ℝ))) :=
      hclosed.completeSpace_coe
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro w hw
    have hw' : ∀ x : T.domain,
        ⟪w, T x + (((-1 : ℝ) : ℂ) * Complex.I) • (x : E)⟫ = 0 := by
      intro x
      have hx : (x : E) ∈ T.closure.domain := T.le_closure.1 x.2
      have hTx : T x = T.closure ⟨(x : E), hx⟩ := T.le_closure.2 rfl
      have hmem : T.closure ⟨(x : E), hx⟩ + (((-1 : ℝ) : ℂ) * Complex.I) • (x : E) ∈
          LinearMap.range (shiftMap T.closure (-1 : ℝ)) := ⟨⟨(x : E), hx⟩, rfl⟩
      have h0 := (Submodule.mem_orthogonal _ _).mp hw _ hmem
      rw [hTx]
      exact inner_eq_zero_symm.mp h0
    obtain ⟨hw2, hval⟩ := adjoint_apply_of_mem_orthogonal hT (-1 : ℝ) hw'
    refine hneg ⟨w, hw2⟩ ?_
    rw [hval]
    push_cast
    module
  -- the adjoint is contained in the closure
  have hkey : T.adjoint ≤ T.closure := by
    have hdom : ∀ u : T.adjoint.domain, ∃ x : T.closure.domain, (u : E) = (x : E) := by
      intro u
      have hex : T.adjoint u + (((-1 : ℝ) : ℂ) * Complex.I) • (u : E) ∈
          LinearMap.range (shiftMap T.closure (-1 : ℝ)) := by rw [hrangetop]; trivial
      obtain ⟨x, hx⟩ := hex
      have hxdom : (x : E) ∈ T.adjoint.domain := hAle.1 x.2
      have hxval : T.closure x = T.adjoint ⟨(x : E), hxdom⟩ := hAle.2 rfl
      have hsub : (u : E) - (x : E) ∈ T.adjoint.domain :=
        Submodule.sub_mem _ u.2 hxdom
      have hval : T.adjoint ⟨(u : E) - (x : E), hsub⟩ = Complex.I • ((u : E) - (x : E)) := by
        have hsplit : (⟨(u : E) - (x : E), hsub⟩ : T.adjoint.domain)
            = u - ⟨(x : E), hxdom⟩ := by
          apply Subtype.ext; simp
        rw [hsplit, LinearPMap.map_sub, ← hxval]
        rw [shiftMap_apply] at hx
        push_cast at hx ⊢
        linear_combination (norm := module) -hx
      have hzero := hpos ⟨(u : E) - (x : E), hsub⟩ hval
      exact ⟨x, by simpa [sub_eq_zero] using hzero⟩
    constructor
    · intro u hu
      obtain ⟨x, hx⟩ := hdom ⟨u, hu⟩
      simpa [← hx] using x.2
    · rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
      have huv' : u = v := huv
      subst huv'
      exact (hAle.2 (x := ⟨u, hv⟩) (y := ⟨u, hu⟩) rfl).symm
  have hAeq : T.adjoint = T.closure := le_antisymm hkey hAle
  rw [LinearPMap.isSelfAdjoint_def]
  have h1 : T.closure.adjoint ≤ T.adjoint :=
    adjoint_le_adjoint_of_le hT hAdense T.le_closure
  have h2 : T.closure ≤ T.closure.adjoint := hAsym.le_adjoint hAdense
  exact le_antisymm (hAeq ▸ h1) h2

end Hilbert

end Brockian.Weyl

namespace Brockian.Weyl.SchrodingerMinimal

open MeasureTheory Complex LinearPMap
open scoped ContDiff

local notation "L2" => MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A test function: a smooth, compactly supported function `ℝ → ℂ`. -/
