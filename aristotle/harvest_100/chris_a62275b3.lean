/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Frontier

/-- The `n`-dimensional torus `𝕋ⁿ = (ℝ/ℤ)ⁿ`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- `W` parametrizes an invariant torus of the map `f` on which the dynamics is
conjugate to the rigid rotation by the frequency vector `ω`:
`f (W θ) = W (θ + ω)` for all angles `θ ∈ 𝕋ⁿ`. -/
def IsInvariantTorus {n : ℕ} {M : Type*} (f : M → M) (ω : Torus n) (W : Torus n → M) : Prop :=
  ∀ θ : Torus n, f (W θ) = W (θ + ω)

/-! ## Base case: the integrable system

An integrable system in action–angle variables on `ℝⁿ × 𝕋ⁿ` has time-one map
`(I, θ) ↦ (I, θ + freq I)`.  Every level set of the action `I` is an invariant torus
carrying a rigid rotation with frequency `freq I`. -/

/-- Time-one map of an integrable system in action–angle coordinates. -/
noncomputable def integrableMap {n : ℕ} (freq : (Fin n → ℝ) → Torus n) :
    ((Fin n → ℝ) × Torus n) → ((Fin n → ℝ) × Torus n) :=
  fun p => (p.1, p.2 + freq p.1)

/-- **Base case of KAM.** For an integrable system, each action level set
`{I₀} × 𝕋ⁿ` is an invariant torus, on which the dynamics is the rotation by `freq I₀`. -/
theorem kam_integrable_torus {n : ℕ} (freq : (Fin n → ℝ) → Torus n) (I₀ : Fin n → ℝ) :
    IsInvariantTorus (integrableMap freq) (freq I₀) (fun θ => (I₀, θ)) := by
  intro θ
  rfl

/-! ## Persistence of invariant tori under perturbation

The analytic heart of KAM theory (small divisors, the homological equation and the
quadratically convergent Newton scheme) is encapsulated in the existence of a *KAM
operator* `Φ` whose fixed points are exactly the invariant tori of the corresponding
map, which is a contraction, and which depends on the vector field in a Lipschitz way.
Given these ingredients, the theorem below shows that the invariant torus `W₀` of the
integrable system persists under an `ε`-small perturbation, and that the perturbed torus
is `O(ε)`-close to the unperturbed one. -/

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]

/-- **KAM theorem (persistence of invariant tori).**

Let `f 0` be an (integrable) map with an invariant torus `W₀` carrying the rotation by
frequency `ω`, and let `f ε` be a perturbation of size at most `ε`.  Assume the standard
KAM Newton scheme is available in the form of an operator `Φ` such that

* `Φ ε' W = W` holds exactly when `W` parametrizes an invariant torus of `f ε'`
  (for `ε' = 0` and for `ε' = ε`),
* `Φ ε` is a contraction with rate `k < 1`,
* `Φ` depends on the map in a Lipschitz way, with constant `C`.

Then the invariant torus persists: the perturbed map `f ε` has an invariant torus `W`,
carrying the *same* rotation frequency `ω`, at distance at most `C * ε / (1 - k)` from the
unperturbed torus `W₀`. -/
theorem kam_theorem
    (f : ℝ → V → V) (ω : Torus n) (W₀ : C(Torus n, V))
    (Φ : ℝ → C(Torus n, V) → C(Torus n, V))
    (k C ε : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    -- the unperturbed system is integrable: it has the invariant torus `W₀`
    (hW₀ : IsInvariantTorus (f 0) ω W₀)
    -- `f ε` is a perturbation of `f 0` of size at most `ε`
    (hpert : ∀ x : V, ‖f ε x - f 0 x‖ ≤ ε)
    -- fixed points of the KAM operator are exactly the invariant tori
    (hfix0 : ∀ W : C(Torus n, V), Φ 0 W = W ↔ IsInvariantTorus (f 0) ω W)
    (hfixε : ∀ W : C(Torus n, V), Φ ε W = W ↔ IsInvariantTorus (f ε) ω W)
    -- the KAM operator is a contraction
    (hlip : LipschitzWith ⟨k, hk0⟩ (Φ ε))
    -- the KAM operator depends on the underlying map in a Lipschitz way
    (hstab : ∀ (W : C(Torus n, V)) (θ : Torus n),
      dist (Φ ε W θ) (Φ 0 W θ) ≤ C * ‖f ε (W θ) - f 0 (W θ)‖) :
    ∃ W : C(Torus n, V), IsInvariantTorus (f ε) ω W ∧ dist W W₀ ≤ C * ε / (1 - k) := by
  have hcontr : ContractingWith ⟨k, hk0⟩ (Φ ε) := ⟨by exact_mod_cast hk1, hlip⟩
  set W : C(Torus n, V) := ContractingWith.fixedPoint (Φ ε) hcontr with hWdef
  have hWfix : Φ ε W = W := hcontr.fixedPoint_isFixedPt
  refine ⟨W, (hfixε W).1 hWfix, ?_⟩
  -- `W₀` is a fixed point of `Φ 0`
  have hΦ0 : Φ 0 W₀ = W₀ := (hfix0 W₀).2 hW₀
  -- hence `Φ ε W₀` is `C * ε`-close to `W₀`
  have hclose : dist W₀ (Φ ε W₀) ≤ C * ε := by
    rw [dist_comm]
    refine (ContinuousMap.dist_le (by positivity)).2 ?_
    intro θ
    have h1 : dist (Φ ε W₀ θ) (W₀ θ) = dist (Φ ε W₀ θ) (Φ 0 W₀ θ) := by rw [hΦ0]
    calc dist (Φ ε W₀ θ) (W₀ θ) = dist (Φ ε W₀ θ) (Φ 0 W₀ θ) := h1
      _ ≤ C * ‖f ε (W₀ θ) - f 0 (W₀ θ)‖ := hstab W₀ θ
      _ ≤ C * ε := by
          exact mul_le_mul_of_nonneg_left (hpert (W₀ θ)) hC
  have key : dist W₀ W ≤ dist W₀ (Φ ε W₀) / (1 - k) := by
    simpa [hWdef] using hcontr.dist_fixedPoint_le W₀
  have h1k : (0:ℝ) < 1 - k := by linarith
  rw [dist_comm]
  exact key.trans (by gcongr)

/-! ## The hypotheses of `kam_theorem` are satisfiable

To confirm that the statement above is not vacuous we exhibit an explicit family of
dynamical systems, together with an explicit KAM operator, satisfying all of its
hypotheses; the conclusion then produces an honest invariant torus of the perturbed
system. -/

/-- An explicit one–parameter family on `V = ℝ`: `f ε x = x / 2 + ε`. -/
noncomputable def exFam : ℝ → ℝ → ℝ := fun ε x => x / 2 + ε

/-- The associated explicit KAM operator on loops. -/
noncomputable def exOp (ω : Torus 1) : ℝ → C(Torus 1, ℝ) → C(Torus 1, ℝ) :=
  fun ε W => ⟨fun θ => (W (θ - ω)) / 2 + ε, by fun_prop⟩

private theorem exOp_fix (ω : Torus 1) (ε : ℝ) (W : C(Torus 1, ℝ)) :
    exOp ω ε W = W ↔ IsInvariantTorus (exFam ε) ω W := by
  constructor
  · intro h θ
    have := congrArg (fun (g : C(Torus 1, ℝ)) => g (θ + ω)) h
    simpa [exOp, exFam, add_sub_cancel_right, div_eq_mul_inv] using this
  · intro h
    ext θ
    have := h (θ - ω)
    simpa [exOp, exFam, sub_add_cancel, div_eq_mul_inv] using this

private theorem exOp_lipschitz (ω : Torus 1) (ε : ℝ) :
    LipschitzWith ⟨1/2, by norm_num⟩ (exOp ω ε) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro W W'
  refine (ContinuousMap.dist_le (by positivity)).2 ?_
  intro θ
  have h : dist (W (θ - ω)) (W' (θ - ω)) ≤ dist W W' :=
    ContinuousMap.dist_apply_le_dist _
  simp only [exOp, ContinuousMap.coe_mk, Real.dist_eq]
  have : (W (θ - ω) / 2 + ε) - (W' (θ - ω) / 2 + ε) = (W (θ - ω) - W' (θ - ω)) / 2 := by ring
  rw [this, abs_div]
  rw [Real.dist_eq] at h
  simp only [NNReal.coe_mk]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

/-- The hypotheses of `kam_theorem` are satisfiable: for the explicit family
`f ε x = x / 2 + ε` on `ℝ` and any frequency `ω`, the invariant torus of the unperturbed
system persists under the `ε`-perturbation and stays `2 * ε`-close to it. -/
theorem kam_theorem_nonvacuous (ω : Torus 1) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ W : C(Torus 1, ℝ), IsInvariantTorus (exFam ε) ω W ∧ dist W 0 ≤ 2 * ε := by
  have hW₀ : IsInvariantTorus (exFam 0) ω (0 : C(Torus 1, ℝ)) := by
    intro θ; simp [exFam]
  have hmain := kam_theorem (V := ℝ) exFam ω 0 (exOp ω) (1/2) 1 ε
    (by norm_num) (by norm_num) (by norm_num) hε hW₀
    (fun x => by simp [exFam, abs_of_nonneg hε])
    (fun W => exOp_fix ω 0 W) (fun W => exOp_fix ω ε W)
    (exOp_lipschitz ω ε)
    (fun W θ => by
      simp only [exOp, exFam, ContinuousMap.coe_mk, Real.dist_eq, Real.norm_eq_abs]
      have h1 : (W (θ - ω) / 2 + ε) - (W (θ - ω) / 2 + 0) = ε := by ring
      have h2 : (W θ / 2 + ε) - (W θ / 2 + 0) = ε := by ring
      rw [h1, h2, one_mul])
  obtain ⟨W, hW, hd⟩ := hmain
  exact ⟨W, hW, by
    refine hd.trans ?_
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 1/2)]
    linarith⟩

end Frontier

