import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

set_option grind.warning false

open scoped InnerProductSpace
open scoped NNReal

namespace Brockian.Weyl.DeficiencyODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An (in general unbounded) linear operator on a Hilbert space `H` is encoded by its graph,
a linear subspace of `H × H`. -/
abbrev OperatorGraph (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Submodule ℂ (H × H)

/-- The graph of the adjoint of the operator with graph `G`:
`(u, v)` belongs to it iff `⟪T x, u⟫ = ⟪x, v⟫` for all `(x, T x) ∈ G`. -/

lemma dense_defRange_perturbGraph {G : OperatorGraph H} {V : H →L[ℂ] H} {c : ℂ}
    (htop : defRange c (perturbGraph V G.topologicalClosure) = ⊤) :
    Dense ((defRange c (perturbGraph V G) : Submodule ℂ H) : Set H) := by
  set psi : (H × H) →L[ℂ] H := (shiftMap c).comp (perturbMap V) with hpsi
  have hpsiApply : ∀ q : H × H, psi q = (q.2 + V q.1) + c • q.1 := fun _ => rfl
  have himage : psi '' (G : Set (H × H)) ⊆ ((defRange c (perturbGraph V G) : Submodule ℂ H) : Set H) := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_defRange_iff.mpr ⟨(r.1, r.2 + V r.1), mem_perturbGraph_iff.mpr ⟨r, hr, rfl⟩, rfl⟩
  intro x
  have hx : x ∈ defRange c (perturbGraph V G.topologicalClosure) := by rw [htop]; trivial
  obtain ⟨pp, hpp, rfl⟩ := mem_defRange_iff.mp hx
  obtain ⟨q, hq, rfl⟩ := mem_perturbGraph_iff.mp hpp
  have hqmem : q ∈ closure (G : Set (H × H)) := by
    simpa [Submodule.topologicalClosure_coe] using hq
  have hmem : psi q ∈ closure (psi '' (G : Set (H × H))) :=
    image_closure_subset_closure_image psi.continuous ⟨q, hqmem, rfl⟩
  exact closure_mono himage hmem

/-- **Kato–Rellich (bounded perturbation).** If a symmetric operator `T` is essentially
self-adjoint and `V` is a bounded symmetric operator, then `T + V` is essentially self-adjoint
on the same domain. -/
