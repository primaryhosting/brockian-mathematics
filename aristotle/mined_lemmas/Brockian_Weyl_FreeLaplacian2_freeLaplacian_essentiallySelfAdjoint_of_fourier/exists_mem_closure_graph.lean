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
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- Note: Lean requires `import` commands to come before any module docstring `/-! ... -/`, so the
-- required header appears verbatim at the very top of the file as a block comment and is repeated
-- here, after the import, as the module docstring.

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
The free Laplacian `-Δ`, defined on the Schwartz space `𝓢(ℝ^d, ℂ)` regarded as a dense
subspace of `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

The proof follows the classical "basic criterion" of von Neumann/Weyl:

* an abstract criterion (`essentiallySelfAdjoint_of_dense_shift_ranges`): a densely defined
  symmetric operator whose deficiency ranges `Ran (T ± i)` are dense is essentially
  self-adjoint;
* the Fourier transform turns `-Δ` on Schwartz space into multiplication by
  `ξ ↦ 4π²‖ξ‖²` (`fourier_negLaplacianS`), and dividing a smooth compactly supported
  function by `4π²‖ξ‖² ± i` (which never vanishes) produces again a smooth compactly
  supported function.  Since smooth compactly supported functions are dense in `L²` and
  the Fourier transform is unitary on `L²` (Plancherel), the deficiency ranges are dense.
-/

open MeasureTheory SchwartzMap Filter LinearPMap
open scoped FourierTransform ComplexInnerProductSpace LinearPMap Laplacian LineDeriv Topology
  ContDiff

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The operator `T + c` on the domain of the partially defined operator `T`. -/

theorem exists_mem_closure_graph {T : E →ₗ.[ℂ] E} (hsym : T.IsFormalAdjoint T) {c : ℂ}
    (hc : c.re = 0) (hc1 : ‖c‖ = 1)
    (hd : Dense ((LinearMap.range (shiftMap T c) : Submodule ℂ E) : Set E)) (u : E) :
    ∃ p : E × E, p ∈ closure (T.graph : Set (E × E)) ∧ p.2 + c • p.1 = u := by
  have hbound : ∀ a b : T.domain, ‖(a : E) - (b : E)‖ ≤ ‖shiftMap T c a - shiftMap T c b‖ ∧
      ‖T a - T b‖ ≤ ‖shiftMap T c a - shiftMap T c b‖ := by
    intro a b
    have hkey : ‖shiftMap T c (a - b)‖ ^ 2
        = ‖T (a - b)‖ ^ 2 + ‖c‖ ^ 2 * ‖((a - b : T.domain) : E)‖ ^ 2 := norm_shift_sq hsym hc _
    rw [hc1] at hkey
    have h1 : ((a - b : T.domain) : E) = (a : E) - b := rfl
    have h2 : T (a - b) = T a - T b := LinearPMap.map_sub T a b
    have h3 : shiftMap T c (a - b) = shiftMap T c a - shiftMap T c b := map_sub _ a b
    rw [h1, h2, h3] at hkey
    constructor
    · nlinarith [norm_nonneg (T a - T b), norm_nonneg ((a : E) - b),
        norm_nonneg (shiftMap T c a - shiftMap T c b)]
    · nlinarith [norm_nonneg (T a - T b), norm_nonneg ((a : E) - b),
        norm_nonneg (shiftMap T c a - shiftMap T c b)]
  have hu : u ∈ closure (Set.range (shiftMap T c)) := by
    have := hd u
    rwa [LinearMap.coe_range] at this
  rw [mem_closure_iff_seq_limit] at hu
  obtain ⟨g, hg, hgu⟩ := hu
  choose x hx using hg
  have hgc : CauchySeq g := hgu.cauchySeq
  have hxc : CauchySeq (fun n => ((x n : E))) := by
    refine cauchySeq_of_dist_le (g := g) (fun m n => ?_) hgc
    rw [dist_eq_norm, dist_eq_norm, ← hx m, ← hx n]
    exact (hbound (x m) (x n)).1
  have hTxc : CauchySeq (fun n => (T (x n))) := by
    refine cauchySeq_of_dist_le (g := g) (fun m n => ?_) hgc
    rw [dist_eq_norm, dist_eq_norm, ← hx m, ← hx n]
    exact (hbound (x m) (x n)).2
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hxc
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hTxc
  refine ⟨(a, v), ?_, ?_⟩
  · refine mem_closure_of_tendsto (ha.prodMk_nhds hv) ?_
    filter_upwards with n
    exact T.mem_graph (x n)
  · have hlim : Tendsto (fun n => T (x n) + c • ((x n : E))) atTop (𝓝 (v + c • a)) :=
      hv.add (ha.const_smul c)
    have h2 : (fun n => T (x n) + c • ((x n : E))) = g := funext fun n => hx n
    rw [h2] at hlim
    exact tendsto_nhds_unique hlim hgu

/-- **Basic criterion for essential self-adjointness.**  A densely defined symmetric operator
on a complex Hilbert space whose deficiency ranges `Ran (T + i)` and `Ran (T - i)` are dense
is essentially self-adjoint. -/
