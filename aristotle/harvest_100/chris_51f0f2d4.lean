/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Real Finset RealInnerProductSpace

namespace Frontier

/-- One factor of phase space, `ℝⁿ`.  It is used both for the action variables `p`
and for the angle variables `q`; the angles are understood modulo the lattice `2π ℤⁿ`. -/
abbrev Phase (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The Fourier mode `k ∈ ℤⁿ`, viewed as a vector of `ℝⁿ`. -/
noncomputable def mode (k : Fin n → ℤ) : Phase n := WithLp.toLp 2 fun i => (k i : ℝ)

/-- The angle-dependent perturbation, a trigonometric polynomial with modes in `K`. -/
noncomputable def pert (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ) (θ : Phase n) : ℝ :=
  ∑ k ∈ K, (a k * cos ⟪mode k, θ⟫ + b k * sin ⟪mode k, θ⟫)

/-- The gradient of `pert` (proved to be the gradient in `hasGradientAt_pert`). -/
noncomputable def gradPert (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (θ : Phase n) : Phase n :=
  ∑ k ∈ K, (-(a k) * sin ⟪mode k, θ⟫ + b k * cos ⟪mode k, θ⟫) • mode k

/-- The nearly integrable Hamiltonian `H_ε(p,q) = ⟪ω,p⟫ + ε f(q)`. -/
noncomputable def ham (ω : Phase n) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ) (ε : ℝ)
    (p q : Phase n) : ℝ := ⟪ω, p⟫ + ε * pert K a b q

/-- The solution `U` of the homological equation `D_ω U = ∇f`, obtained by dividing the
Fourier coefficients by the small divisors `⟪k, ω⟫`. -/
noncomputable def kamCorr (ω : Phase n) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (θ : Phase n) : Phase n :=
  ∑ k ∈ K, ((a k * cos ⟪mode k, θ⟫ + b k * sin ⟪mode k, θ⟫) / ⟪mode k, ω⟫) • mode k

section Basic

variable {K : Finset (Fin n → ℤ)} {a b : (Fin n → ℤ) → ℝ} {ω θ : Phase n}

lemma inner_mode_add_smul (k : Fin n → ℤ) (t : ℝ) :
    ⟪mode k, θ + t • ω⟫ = ⟪mode k, θ⟫ + t * ⟪mode k, ω⟫ := by
  simp [inner_add_right, real_inner_smul_right]

lemma hasGradientAt_inner_left (v x : Phase n) : HasGradientAt (fun y => ⟪v, y⟫) v x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using (innerSL ℝ v).hasFDerivAt

lemma hasGradientAt_cos_inner (v x : Phase n) :
    HasGradientAt (fun y => cos ⟪v, y⟫) ((-sin ⟪v, x⟫) • v) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y => ⟪v, y⟫) (innerSL ℝ v) x := by
    simpa using (innerSL ℝ v).hasFDerivAt
  have h2 := (Real.hasDerivAt_cos ⟪v, x⟫).comp_hasFDerivAt x h1
  convert h2 using 1
  ext y; simp

lemma hasGradientAt_sin_inner (v x : Phase n) :
    HasGradientAt (fun y => sin ⟪v, y⟫) ((cos ⟪v, x⟫) • v) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y => ⟪v, y⟫) (innerSL ℝ v) x := by
    simpa using (innerSL ℝ v).hasFDerivAt
  have h2 := (Real.hasDerivAt_sin ⟪v, x⟫).comp_hasFDerivAt x h1
  convert h2 using 1
  ext y; simp

/-- `gradPert` really is the gradient of the perturbation. -/
lemma hasGradientAt_pert (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ) (θ : Phase n) :
    HasGradientAt (pert K a b) (gradPert K a b θ) θ := by
  classical
  rw [hasGradientAt_iff_hasFDerivAt]
  have : ∀ k ∈ K, HasFDerivAt (fun y : Phase n => a k * cos ⟪mode k, y⟫ + b k * sin ⟪mode k, y⟫)
      ((InnerProductSpace.toDual ℝ (Phase n))
        ((-(a k) * sin ⟪mode k, θ⟫ + b k * cos ⟪mode k, θ⟫) • mode k)) θ := by
    intro k _
    have hc := ((hasGradientAt_cos_inner (mode k) θ).hasFDerivAt).const_mul (a k)
    have hs := ((hasGradientAt_sin_inner (mode k) θ).hasFDerivAt).const_mul (b k)
    have := hc.add hs
    convert this using 1
    ext y
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_smul_left, smul_eq_mul]
    ring
  have hsum := HasFDerivAt.fun_sum this
  simp only [gradPert]
  convert hsum using 1
  simp

end Basic

section Homological

variable (ω : Phase n) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)

/-- **The homological equation.**  Along the linear flow `t ↦ θ + t ω` on the torus, the
derivative of the correction `U` is exactly the gradient of the perturbation. -/
lemma hasDerivAt_kamCorr (hnr : ∀ k ∈ K, ⟪mode k, ω⟫ ≠ 0) (θ : Phase n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kamCorr ω K a b (θ + s • ω))
      (gradPert K a b (θ + t • ω)) t := by
  classical
  have key : ∀ k ∈ K, HasDerivAt
      (fun s : ℝ => ((a k * cos ⟪mode k, θ + s • ω⟫ + b k * sin ⟪mode k, θ + s • ω⟫)
        / ⟪mode k, ω⟫) • mode k)
      ((-(a k) * sin ⟪mode k, θ + t • ω⟫ + b k * cos ⟪mode k, θ + t • ω⟫) • mode k) t := by
    intro k hk
    set d : ℝ := ⟪mode k, ω⟫ with hd
    set s0 : ℝ := ⟪mode k, θ⟫ with hs0
    have hdne : d ≠ 0 := hnr k hk
    have hlin : HasDerivAt (fun s : ℝ => s0 + s * d) d t := by
      simpa using ((hasDerivAt_id t).mul_const d).const_add s0
    have hc : HasDerivAt (fun s : ℝ => cos (s0 + s * d)) (-sin (s0 + t * d) * d) t :=
      (Real.hasDerivAt_cos _).comp t hlin
    have hs : HasDerivAt (fun s : ℝ => sin (s0 + s * d)) (cos (s0 + t * d) * d) t :=
      (Real.hasDerivAt_sin _).comp t hlin
    have hf : HasDerivAt (fun s : ℝ => (a k * cos (s0 + s * d) + b k * sin (s0 + s * d)) / d)
        ((-(a k) * sin (s0 + t * d) + b k * cos (s0 + t * d))) t := by
      have := ((hc.const_mul (a k)).add (hs.const_mul (b k))).div_const d
      convert this using 1
      field_simp
    have := hf.smul_const (mode k)
    simpa only [inner_mode_add_smul] using this
  have hsum := HasDerivAt.fun_sum key
  simpa only [kamCorr, gradPert] using hsum

/-- The correction `U` is `2π`-periodic in each angle, i.e. it is a function on the torus. -/
lemma kamCorr_periodic (θ : Phase n) (m : Fin n → ℤ) :
    kamCorr ω K a b (θ + (2 * π) • mode m) = kamCorr ω K a b θ := by
  classical
  refine Finset.sum_congr rfl ?_
  intro k _
  have hint : ⟪mode k, mode m⟫ = ((∑ i, k i * m i : ℤ) : ℝ) := by
    simp [mode, PiLp.inner_apply, mul_comm]
  have : ⟪mode k, θ + (2 * π) • mode m⟫
      = ⟪mode k, θ⟫ + ((∑ i, k i * m i : ℤ) : ℝ) * (2 * π) := by
    rw [inner_add_right, real_inner_smul_right, hint]; ring
  rw [this, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- A uniform bound for the correction: the perturbed torus is `O(ε)`-close to the
unperturbed one. -/
lemma norm_kamCorr_le (θ : Phase n) :
    ‖kamCorr ω K a b θ‖ ≤ ∑ k ∈ K, ((|a k| + |b k|) / |⟪mode k, ω⟫|) * ‖mode k‖ := by
  classical
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k _
  rw [norm_smul, Real.norm_eq_abs, abs_div]
  have h2 : |a k * cos ⟪mode k, θ⟫| ≤ |a k| := by
    rw [abs_mul]
    nlinarith [abs_cos_le_one ⟪mode k, θ⟫, abs_nonneg (a k), abs_nonneg (cos ⟪mode k, θ⟫)]
  have h3 : |b k * sin ⟪mode k, θ⟫| ≤ |b k| := by
    rw [abs_mul]
    nlinarith [abs_sin_le_one ⟪mode k, θ⟫, abs_nonneg (b k), abs_nonneg (sin ⟪mode k, θ⟫)]
  have h1 : |a k * cos ⟪mode k, θ⟫ + b k * sin ⟪mode k, θ⟫| ≤ |a k| + |b k| :=
    (abs_add_le _ _).trans (by linarith)
  gcongr

end Homological

section Hamilton

variable (ω : Phase n) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ) (ε : ℝ)

lemma hasGradientAt_ham_p (q p : Phase n) :
    HasGradientAt (fun x => ham ω K a b ε x q) ω p := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt (fun x : Phase n => ⟪ω, x⟫)
      ((InnerProductSpace.toDual ℝ (Phase n)) ω) p :=
    (hasGradientAt_inner_left ω p).hasFDerivAt
  simpa [ham] using h.add_const (ε * pert K a b q)

lemma hasGradientAt_ham_q (p q : Phase n) :
    HasGradientAt (fun y => ham ω K a b ε p y) (ε • gradPert K a b q) q := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (pert K a b)
      ((InnerProductSpace.toDual ℝ (Phase n)) (gradPert K a b q)) q :=
    (hasGradientAt_pert K a b q).hasFDerivAt
  have h2 := (h1.const_mul ε).const_add ⟪ω, p⟫
  have : HasFDerivAt (fun y => ham ω K a b ε p y)
      (ε • (InnerProductSpace.toDual ℝ (Phase n)) (gradPert K a b q)) q := by
    simpa [ham] using h2
  convert this using 1
  ext y
  simp

lemma gradient_ham_p (q p : Phase n) :
    gradient (fun x => ham ω K a b ε x q) p = ω :=
  (hasGradientAt_ham_p ω K a b ε q p).gradient

lemma gradient_ham_q (p q : Phase n) :
    gradient (fun y => ham ω K a b ε p y) q = ε • gradPert K a b q :=
  (hasGradientAt_ham_q ω K a b ε p q).gradient

/-- **Base case (`ε = 0`, the integrable system).**  For `H_0(p,q) = ⟪ω,p⟫` every torus
`{p = p₀}` is invariant and carries the linear flow `θ ↦ θ + t ω`. -/
theorem kam_base_case (p₀ θ : Phase n) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => θ + s • ω)
      (gradient (fun x => ham ω K a b 0 x (θ + t • ω)) p₀) t) ∧
    (∀ t : ℝ, HasDerivAt (fun _ : ℝ => p₀)
      (-gradient (fun y => ham ω K a b 0 p₀ y) (θ + t • ω)) t) := by
  constructor
  · intro t
    rw [gradient_ham_p]
    simpa using ((hasDerivAt_id t).smul_const ω).const_add θ
  · intro t
    rw [gradient_ham_q]
    simpa using hasDerivAt_const t p₀

end Hamilton

/-- **KAM theorem (persistence of invariant tori), exactly solvable case.**

For the nearly integrable Hamiltonian `H_ε(p,q) = ⟪ω,p⟫ + ε f(q)` on `ℝⁿ × 𝕋ⁿ`, where the
perturbation `f` is a trigonometric polynomial with modes in a finite set `K` and the frequency
vector `ω` is nonresonant on `K` (`⟪k,ω⟫ ≠ 0` for every mode `k ∈ K`), every unperturbed
invariant torus `{p = p₀}` persists:  there is a `2π`-periodic correction `U`, bounded by a
constant `C` independent of `ε`, such that for every `ε` the deformed torus

  `𝕋_ε = { (p₀ - ε U θ, θ) : θ ∈ 𝕋ⁿ }`

is invariant under the Hamiltonian flow of `H_ε`, and the motion on it is the linear flow
`θ ↦ θ + t ω` with the *same* frequency vector `ω`.  For `ε = 0` this is the unperturbed torus,
and `𝕋_ε` is `C|ε|`-close to it. -/
theorem kam_theorem {n : ℕ} (ω : Phase n) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (hnr : ∀ k ∈ K, ⟪mode k, ω⟫ ≠ 0) (p₀ : Phase n) :
    ∃ (U : Phase n → Phase n) (C : ℝ), 0 ≤ C ∧
      (∀ θ, ‖U θ‖ ≤ C) ∧
      (∀ (θ : Phase n) (m : Fin n → ℤ), U (θ + (2 * π) • mode m) = U θ) ∧
      ∀ (ε : ℝ) (θ : Phase n),
        ∃ p q : ℝ → Phase n,
          -- the orbit starts on the deformed torus at the angle `θ`
          p 0 = p₀ - ε • U θ ∧ q 0 = θ ∧
          -- the motion of the angles is the linear flow with frequency `ω`
          (∀ t, q t = θ + t • ω) ∧
          -- the orbit stays on the deformed torus: it is an invariant set
          (∀ t, (p t, q t) ∈ Set.range (fun ϑ : Phase n => (p₀ - ε • U ϑ, ϑ))) ∧
          -- Hamilton's equations for `H_ε`
          (∀ t, HasDerivAt q (gradient (fun x => ham ω K a b ε x (q t)) (p t)) t) ∧
          (∀ t, HasDerivAt p (-gradient (fun y => ham ω K a b ε (p t) y) (q t)) t) := by
  classical
  refine ⟨kamCorr ω K a b, ∑ k ∈ K, ((|a k| + |b k|) / |⟪mode k, ω⟫|) * ‖mode k‖, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => by positivity
  · exact fun θ => norm_kamCorr_le ω K a b θ
  · exact fun θ m => kamCorr_periodic ω K a b θ m
  · intro ε θ
    refine ⟨fun t => p₀ - ε • kamCorr ω K a b (θ + t • ω), fun t => θ + t • ω, by simp, by simp,
      fun t => rfl, fun t => ⟨θ + t • ω, rfl⟩, ?_, ?_⟩
    · intro t
      rw [gradient_ham_p]
      simpa using (hasDerivAt_id t).smul_const ω |>.const_add θ
    · intro t
      rw [gradient_ham_q]
      have h := (hasDerivAt_kamCorr ω K a b hnr θ t).const_smul ε
      have := h.const_sub p₀
      simpa using this

section Nontrivial

/-- The hypotheses of `kam_theorem` are satisfied by a genuinely perturbed system: with two
degrees of freedom, frequency vector `ω = (1, √2)` and the single Fourier mode `k = (1,-1)`,
the small divisor `⟪k, ω⟫ = 1 - √2` is nonzero. -/
lemma kam_example_nonresonant :
    ∀ k ∈ ({![1, -1]} : Finset (Fin 2 → ℤ)),
      ⟪mode k, (WithLp.toLp 2 ![(1 : ℝ), Real.sqrt 2] : Phase 2)⟫ ≠ 0 := by
  intro k hk
  simp only [Finset.mem_singleton] at hk
  subst hk
  simp [mode, PiLp.inner_apply, Fin.sum_univ_two]
  intro h
  have h2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  nlinarith [Real.sqrt_nonneg 2]

/-- ... and the corresponding perturbation is not the zero function. -/
lemma kam_example_pert_ne_zero :
    pert ({![1, -1]} : Finset (Fin 2 → ℤ)) (fun _ => 1) (fun _ => 0) 0 = 1 := by
  simp [pert]

end Nontrivial

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

