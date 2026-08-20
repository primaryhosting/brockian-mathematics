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

theorem isSymmetric_closure {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hs : IsSymmetricPMap T) : IsSymmetricPMap T.closure := by
  intro x y
  have hcl : T.IsClosable := isClosable_of_isSymmetric hT hs
  have hle : T.closure ≤ T.adjoint := closure_le_adjoint hT hs
  set w : E := T.adjoint ⟨(y : E), hle.1 y.2⟩ with hwdef
  have hyw : T.closure y = w := hle.2 rfl
  have hclosed : IsClosed {p : E × E | ⟪p.2, (y : E)⟫ = ⟪p.1, w⟫} := by
    apply isClosed_eq <;> fun_prop
  have hsub : (T.graph : Set (E × E)) ⊆ {p : E × E | ⟪p.2, (y : E)⟫ = ⟪p.1, w⟫} := by
    rintro ⟨a, b⟩ hab
    obtain ⟨z, hz⟩ := (T.mem_graph_iff).mp hab
    have h1 : a = (z : E) := hz.1.symm
    have h2 : b = T z := hz.2.symm
    subst h1; subst h2
    show ⟪T z, (y : E)⟫ = ⟪(z : E), w⟫
    have h5 := LinearPMap.adjoint_isFormalAdjoint hT ⟨(y : E), hle.1 y.2⟩ z
    rw [← inner_conj_symm (T z) ((y : E)), ← inner_conj_symm ((z : E)) w]
    exact congrArg _ h5.symm
  have hmem : ((x : E), T.closure x) ∈ (T.graph.topologicalClosure : Set (E × E)) := by
    rw [hcl.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  have hfin : ((x : E), T.closure x) ∈ {p : E × E | ⟪p.2, (y : E)⟫ = ⟪p.1, w⟫} := by
    rw [Submodule.topologicalClosure_coe] at hmem
    exact closure_minimal hsub hclosed hmem
  simpa [hyw] using hfin

set_option maxHeartbeats 1000000 in
/-- The range of `A + c i` is closed when `A` is closed and symmetric and `c ≠ 0`. -/
