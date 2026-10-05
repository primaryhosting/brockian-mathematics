import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.SchrodingerMinimal

open LinearPMap

open scoped LinearPMap ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A densely defined operator `T` on a complex Hilbert space is *essentially self-adjoint* if
its adjoint is self-adjoint; equivalently, `T` has a unique self-adjoint extension, namely the
closure `T†† = T̄` of `T`. -/

theorem surjective_shift_of_isClosed {A : H →ₗ.[ℂ] H} (hclosed : A.IsClosed)
    (hsymm : A.IsFormalAdjoint A) {z : ℂ} (hz : conj z = -z) (hz1 : ‖z‖ = 1)
    (hdense : Dense (Set.range fun x : A.domain => A x + z • (x : H))) (y : H) :
    ∃ x : A.domain, A x + z • (x : H) = y := by
  haveI : _root_.IsClosed (A.graph : Set (H × H)) := hclosed
  haveI : CompleteSpace (A.graph : Set (H × H)) := IsClosed.completeSpace_coe
  -- the continuous linear map `(x, w) ↦ w + z • x` restricted to the graph of `A`
  set F : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) + z • (ContinuousLinearMap.fst ℂ H H) with hF
  set f : (A.graph : Submodule ℂ (H × H)) →L[ℂ] H := F.comp (A.graph.subtypeL) with hf
  have hrange : Set.range f = Set.range fun x : A.domain => A x + z • (x : H) := by
    ext w
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := (A.mem_graph_iff).mp p.2
      refine ⟨x, ?_⟩
      simp only [hf, hF, ContinuousLinearMap.coe_comp', Function.comp_apply,
        Submodule.coe_subtypeL', Submodule.coe_subtype, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [hx1, hx2]
    · rintro ⟨x, rfl⟩
      refine ⟨⟨((x : H), A x), A.mem_graph x⟩, ?_⟩
      simp [hf, hF]
  have hanti : AntilipschitzWith 1 f := by
    refine AddMonoidHomClass.antilipschitz_of_bound f fun p => ?_
    obtain ⟨x, hx1, hx2⟩ := (A.mem_graph_iff).mp p.2
    have hfp : f p = A x + z • (x : H) := by
      simp only [hf, hF, ContinuousLinearMap.coe_comp', Function.comp_apply,
        Submodule.coe_subtypeL', Submodule.coe_subtype, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [hx1, hx2]
    have hkey : ‖A x + z • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
      rw [norm_shift_sq hsymm hz x, norm_smul, hz1]
      ring
    have hpnorm : ‖(p : H × H)‖ = max ‖(x : H)‖ ‖A x‖ := by
      rw [← hx1, ← hx2]
      simp [Prod.norm_def]
    have hp : ‖p‖ = max ‖(x : H)‖ ‖A x‖ := hpnorm
    rw [hp, hfp]
    have h1 : (0 : ℝ) ≤ ‖A x + z • (x : H)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖(x : H)‖ := norm_nonneg _
    have h3 : (0 : ℝ) ≤ ‖A x‖ := norm_nonneg _
    have hx : ‖(x : H)‖ ≤ ‖A x + z • (x : H)‖ := by nlinarith
    have hax : ‖A x‖ ≤ ‖A x + z • (x : H)‖ := by nlinarith
    simp only [NNReal.coe_one, one_mul]
    exact max_le hx hax
  have hclosedRange : _root_.IsClosed (Set.range f) :=
    hanti.isClosed_range (ContinuousLinearMap.uniformContinuous f)
  have : Set.range f = Set.univ := by
    have hd : Dense (Set.range f) := by rw [hrange]; exact hdense
    rw [← hclosedRange.closure_eq, hd.closure_eq]
  rw [hrange] at this
  have hy : y ∈ Set.range fun x : A.domain => A x + z • (x : H) := by
    rw [this]; trivial
  exact hy

/-- **Basic criterion for essential self-adjointness.**  A densely defined symmetric operator
whose deficiency equations `T† u = ± i u` have no nonzero solutions is essentially
self-adjoint. -/
