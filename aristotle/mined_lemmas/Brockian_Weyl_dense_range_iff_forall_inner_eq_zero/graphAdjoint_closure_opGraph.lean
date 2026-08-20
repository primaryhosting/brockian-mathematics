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

/-!
# Symmetric operators, deficiency spaces and the basic criterion of essential self-adjointness

This file develops the small amount of unbounded-operator theory that is needed to state and
prove that a Schrödinger operator is essentially self-adjoint.

An *operator with domain `D`* on a complex Hilbert space `H` is encoded here as a pair of
linear maps `ι T : D →ₗ[ℂ] H`, where `ι` describes how the (abstract) domain `D` sits inside
`H` and `T` is the action of the operator.  (Taking `D` to be a submodule of `H` and `ι` its
inclusion recovers the usual picture; the extra generality is convenient because the natural
domain of a Schrödinger operator is a space of Schwartz functions.)

The main definition is `Brockian.Weyl.IsEssentiallySelfAdjoint`, which is the classical *basic
criterion* of von Neumann (see e.g. Reed–Simon, *Methods of Modern Mathematical Physics I*,
Theorem VIII.3): a densely defined symmetric operator is essentially self-adjoint if and only
if the ranges of `T + i` and `T - i` are dense.  The theorem
`Brockian.Weyl.dense_range_smul_sub_iff_deficiency` records the equivalent formulation in terms
of the *deficiency spaces*: no nonzero `v ∈ H` solves the weak (adjoint) equation `T* v = ∓ i v`.

The remaining results are the analytic tools used later:

* `Brockian.Weyl.norm_add_I_smul_lower_bound`: the basic lower bound `‖T x + i b ι x‖ ≥ |b| ‖ι x‖`
  for a symmetric operator;
* `Brockian.Weyl.dense_range_add_of_relatively_bounded`: a small perturbation lemma, which is the
  engine both of the Kato–Rellich argument and of the transfer of density in the spectral
  parameter;
* `Brockian.Weyl.dense_range_shift_of_dense_range_shift`: density of the range of `T + i b'`
  follows from density of the range of `T + i b` whenever `|b' - b| < b`.
-/

noncomputable section

open scoped ComplexInnerProductSpace

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- An operator `T` with domain described by `ι` is *symmetric* if `⟪T x, ι y⟫ = ⟪ι x, T y⟫`. -/

theorem graphAdjoint_closure_opGraph (h : IsEssentiallySelfAdjoint ι T) :
    (graphAdjoint (closure (opGraph ι T : Set (H × H))) : Set (H × H))
      = closure (opGraph ι T : Set (H × H)) := by
  rw [graphAdjoint_closure]
  refine le_antisymm ?_ ?_
  · -- the hard inclusion: the adjoint is contained in the closure of the graph
    intro p hp
    obtain ⟨p₀, hp₀mem, hp₀⟩ := exists_mem_closure_opGraph h (p.2 - Complex.I • p.1)
    have hp₀adj : p₀ ∈ graphAdjoint (opGraph ι T : Set (H × H)) := by
      have hsub : closure (opGraph ι T : Set (H × H))
          ⊆ (graphAdjoint (opGraph ι T : Set (H × H)) : Set (H × H)) :=
        (isClosed_graphAdjoint _).closure_subset_iff.2 (opGraph_le_graphAdjoint h.symmetric)
      exact hsub hp₀mem
    set u : H := p.1 - p₀.1 with hu
    have hw : p.2 - p₀.2 = Complex.I • u := by
      have := hp₀
      rw [hu, smul_sub]
      linear_combination (norm := module) -this
    have hudef : ∀ x, ⟪T x, u⟫ = Complex.I * ⟪ι x, u⟫ := by
      intro x
      have h1 : ⟪T x, p.1⟫ = ⟪ι x, p.2⟫ := hp (ι x, T x) ⟨x, rfl⟩
      have h2 : ⟪T x, p₀.1⟫ = ⟪ι x, p₀.2⟫ := hp₀adj (ι x, T x) ⟨x, rfl⟩
      have h3 : ⟪T x, u⟫ = ⟪ι x, p.2 - p₀.2⟫ := by
        rw [hu, inner_sub_right, inner_sub_right, h1, h2]
      rw [h3, hw, inner_smul_right]
    have hu0 : u = 0 := by
      have hkey := (dense_range_iff_forall_inner_eq_zero (T + Complex.I • ι)).1 ?_ u ?_
      · exact hkey
      · have := h.dense_range_add_I
        simpa [show (fun x => T x + Complex.I • ι x) = ⇑(T + Complex.I • ι) from rfl] using this
      · intro x
        simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
          hudef x]
        simp [Complex.conj_I]
    have hp1 : p.1 = p₀.1 := by
      rw [hu] at hu0
      exact sub_eq_zero.mp hu0
    have hp2 : p.2 = p₀.2 := by
      have hz : p.2 - p₀.2 = 0 := by rw [hw, hu0, smul_zero]
      exact sub_eq_zero.mp hz
    have hpp : p = p₀ := Prod.ext hp1 hp2
    rw [hpp]
    exact hp₀mem
  · exact (isClosed_graphAdjoint _).closure_subset_iff.2 (opGraph_le_graphAdjoint h.symmetric)

end GraphClosure

end Brockian.Weyl

import Brockian.Weyl.FreeSchrodinger

/-!
# Essential self-adjointness of one-dimensional Schrödinger operators

Let `V : ℝ → ℝ` be a potential which is only assumed to be *weakly regular*, i.e. measurable and
essentially bounded (`MemLp V ⊤`); no continuity or differentiability is assumed.  The associated
Schrödinger operator

`H u = - u'' + V u`

with domain the Schwartz space `𝓢(ℝ, ℂ) ⊆ L²(ℝ)` is then essentially self-adjoint, in the sense
of `Brockian.Weyl.IsEssentiallySelfAdjoint` (von Neumann's basic criterion: `H` is symmetric,
densely defined, and the ranges of `H ± i` are dense).

The proof combines two ingredients:

* the Fourier-analytic solution of the free deficiency ODE `-u'' + i b u = f`
  (`Brockian.Weyl.dense_range_freeOp_shift`), which shows that the free operator `-d²/dx²`
  has trivial deficiency spaces;
* the Kato–Rellich perturbation argument (`Brockian.Weyl.dense_range_add_of_relatively_bounded`):
  for `|b|` larger than the essential supremum of `|V|`, the multiplication operator `V` is a
  relatively bounded perturbation of `-d²/dx² + i b` with relative bound `< 1`, and density of
  the range is then transported back to the spectral parameters `± i`.

Main result: `Brockian.Weyl.schrodinger_essentiallySelfAdjoint_of_weakRegularity`.
-/

noncomputable section

open MeasureTheory SchwartzMap Complex Real
open scoped FourierTransform ComplexInnerProductSpace ContDiff

namespace Brockian.Weyl

/-! ### The potential as a bounded multiplication operator on `L²` -/

/-- A real-valued potential, complexified. -/
abbrev cx (V : ℝ → ℝ) : ℝ → ℂ := fun x => (V x : ℂ)

/-- Multiplication by an essentially bounded potential, as an operator on `L²(ℝ)`. -/
