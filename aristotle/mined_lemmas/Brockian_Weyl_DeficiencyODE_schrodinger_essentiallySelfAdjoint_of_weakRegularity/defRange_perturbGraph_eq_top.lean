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

lemma defRange_perturbGraph_eq_top [CompleteSpace H] {K : OperatorGraph H}
    (hK : IsSelfAdjointGraph K) {V : H →L[ℂ] H}
    {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) (hlt : ‖V‖ < ‖c‖) :
    defRange c (perturbGraph V K) = ⊤ := by
  classical
  have hsym : IsSymmetricGraph K := hK.isSymmetric
  have hKclosed : IsClosed ((K : OperatorGraph H) : Set (H × H)) := hK.isClosed
  haveI : CompleteSpace K := hKclosed.completeSpace_coe
  have hcpos : 0 < ‖c‖ := lt_of_le_of_lt (norm_nonneg V) hlt
  set Phi : K →L[ℂ] H := (shiftMap c).comp K.subtypeL with hPhi
  have hPhiApply : ∀ p : K, Phi p = ((p : H × H)).2 + c • ((p : H × H)).1 := fun _ => rfl
  have hlower : ∀ p : K, ‖c‖ * ‖((p : H × H)).1‖ ≤ ‖Phi p‖ := by
    intro p
    have h := norm_shift_sq hsym p.2 (c := c) hc
    rw [hPhiApply p]
    nlinarith [norm_nonneg ((p : H × H)).1, norm_nonneg ((p : H × H)).2,
      norm_nonneg (((p : H × H)).2 + c • ((p : H × H)).1), hcpos]
  have hker : LinearMap.ker (Phi : K →ₗ[ℂ] H) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have h := norm_shift_sq hsym p.2 (c := c) hc
    have hp' : ((p : H × H)).2 + c • ((p : H × H)).1 = 0 := hp
    rw [hp'] at h
    simp only [norm_zero] at h
    have hcsq : 0 < ‖c‖ ^ 2 := by positivity
    have hsum : ‖((p : H × H)).2‖ ^ 2 + ‖c‖ ^ 2 * ‖((p : H × H)).1‖ ^ 2 = 0 := by
      rw [← h]; ring
    have ha2 : ‖((p : H × H)).1‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖((p : H × H)).2‖, sq_nonneg ‖((p : H × H)).1‖]
    have hb2 : ‖((p : H × H)).2‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖((p : H × H)).2‖, sq_nonneg ‖((p : H × H)).1‖]
    have h1 : ‖((p : H × H)).1‖ = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha2
    have h2 : ‖((p : H × H)).2‖ = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb2
    apply Subtype.ext
    exact Prod.ext (norm_eq_zero.mp h1) (norm_eq_zero.mp h2)
  have hran : LinearMap.range (Phi : K →ₗ[ℂ] H) = ⊤ := by
    refine eq_top_iff.mpr ?_
    intro z _
    have hz : z ∈ defRange c K := by
      rw [defRange_eq_top_of_isSelfAdjointGraph hK hc hc0]; trivial
    obtain ⟨p, hp, hpz⟩ := mem_defRange_iff.mp hz
    exact ⟨⟨p, hp⟩, hpz⟩
  let e : K ≃L[ℂ] H := ContinuousLinearEquiv.ofBijective Phi hker hran
  have he : ∀ p : K, e p = Phi p := fun _ => rfl
  have hesymm : ∀ w : H, Phi (e.symm w) = w := by
    intro w
    rw [← he]
    exact e.apply_symm_apply w
  set R : H →L[ℂ] H :=
    (ContinuousLinearMap.fst ℂ H H).comp (K.subtypeL.comp (e.symm : H →L[ℂ] K)) with hR
  have hRapp : ∀ w : H, R w = ((e.symm w : K) : H × H).1 := fun _ => rfl
  have hRnorm : ∀ w : H, ‖R w‖ ≤ ‖c‖⁻¹ * ‖w‖ := by
    intro w
    have h1 := hlower (e.symm w)
    rw [hesymm w] at h1
    rw [hRapp w, inv_mul_eq_div, le_div_iff₀ hcpos]
    linarith [h1, mul_comm ‖c‖ ‖((e.symm w : K) : H × H).1‖]
  have hRop : ‖R‖ ≤ ‖c‖⁻¹ := R.opNorm_le_bound (by positivity) hRnorm
  set B : H →L[ℂ] H := V.comp R with hB
  have hBnorm : ‖B‖ < 1 := by
    have h1 : ‖B‖ ≤ ‖V‖ * ‖R‖ := V.opNorm_comp_le R
    have h2 : ‖V‖ * ‖R‖ ≤ ‖V‖ * ‖c‖⁻¹ := by
      exact mul_le_mul_of_nonneg_left hRop (norm_nonneg V)
    have h3 : ‖V‖ * ‖c‖⁻¹ < 1 := by
      rw [inv_eq_one_div, mul_one_div, div_lt_one hcpos]
      exact hlt
    linarith
  obtain ⟨u, hu⟩ : ∃ u : (H →L[ℂ] H)ˣ, (u : H →L[ℂ] H) = 1 + B := by
    refine ⟨Units.oneSub (-B) (by simpa using hBnorm), ?_⟩
    simp
  refine eq_top_iff.mpr ?_
  intro w _
  set z : H := ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) w with hz
  have hzw : z + B z = w := by
    have hmul : ((u : H →L[ℂ] H) * ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)) = 1 := u.mul_inv
    have happ := congrArg (fun f : H →L[ℂ] H => f w) hmul
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hu,
      ContinuousLinearMap.add_apply] at happ
    simpa [hz] using happ
  set p : H × H := ((e.symm z : K) : H × H) with hp
  have hpK : p ∈ K := (e.symm z).2
  have hpz : p.2 + c • p.1 = z := hesymm z
  refine mem_defRange_iff.mpr ⟨(p.1, p.2 + V p.1), mem_perturbGraph_iff.mpr ⟨p, hpK, rfl⟩, ?_⟩
  have hBz : B z = V p.1 := by
    rw [hB]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [hRapp z]
  calc (p.2 + V p.1) + c • p.1 = (p.2 + c • p.1) + V p.1 := by abel
    _ = z + B z := by rw [hpz, hBz]
    _ = w := hzw

