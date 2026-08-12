import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

namespace Frontier

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/
noncomputable def dotIR (k : Fin n → ℤ) (x : Fin n → ℝ) : ℝ := ∑ i, (k i : ℝ) * x i

/-- The `j`-th partial derivative of `f : ℝⁿ → ℝ` at `x`. -/
noncomputable def partialDeriv (f : (Fin n → ℝ) → ℝ) (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => f (Function.update x j s)) (x j)

/-- A trigonometric polynomial on the torus `𝕋ⁿ = ℝⁿ / ℤⁿ`, with modes in the finite set `K`
and Fourier coefficients `a`, `b`. -/
noncomputable def trigPoly (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (θ : Fin n → ℝ) : ℝ :=
  ∑ k ∈ K, (a k * Real.cos (2 * π * dotIR k θ) + b k * Real.sin (2 * π * dotIR k θ))

/-- The nearly integrable Hamiltonian `H_ε(θ, I) = ⟪ω, I⟫ + ε P(θ)` on `𝕋ⁿ × ℝⁿ`,
whose unperturbed part `⟪ω, I⟫` is integrable with all tori `{I = const}` invariant and
carrying the linear flow of frequency `ω`. -/
noncomputable def kamHam (ω : Fin n → ℝ) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (ε : ℝ) (θ I : Fin n → ℝ) : ℝ :=
  (∑ i, ω i * I i) + ε * trigPoly K a b θ

/-- The curve `t ↦ (θ t, I t)` solves Hamilton's equations
`θ̇ = ∂H/∂I`, `İ = -∂H/∂θ` for the Hamiltonian `H`. -/
def IsHamiltonianSolution (H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (θ I : ℝ → (Fin n → ℝ)) : Prop :=
  ∀ t : ℝ,
    (∀ j, HasDerivAt (fun s => θ s j) (partialDeriv (fun y => H (θ t) y) j (I t)) t) ∧
    (∀ j, HasDerivAt (fun s => I s j) (-(partialDeriv (fun x => H x (I t)) j (θ t))) t)

/-! ### Auxiliary computations -/

lemma dotIR_add_smul (k : Fin n → ℤ) (θ ω : Fin n → ℝ) (t : ℝ) :
    dotIR k (θ + t • ω) = dotIR k θ + t * dotIR k ω := by
  simp only [dotIR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma dotIR_add_intVec (k m : Fin n → ℤ) (θ : Fin n → ℝ) :
    dotIR k (θ + fun i => (m i : ℝ)) = dotIR k θ + ((∑ i, k i * m i : ℤ) : ℝ) := by
  simp only [dotIR, Pi.add_apply]
  push_cast
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma dotIR_update (k : Fin n → ℤ) (θ : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    dotIR k (Function.update θ j s) =
      (k j : ℝ) * s + ∑ i ∈ Finset.univ.erase j, (k i : ℝ) * θ i := by
  simp only [dotIR]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  rw [Function.update_self, add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

lemma hasDerivAt_dotIR_update (k : Fin n → ℤ) (θ : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    HasDerivAt (fun s => dotIR k (Function.update θ j s)) (k j : ℝ) s := by
  have : (fun s => dotIR k (Function.update θ j s)) =
      fun s => (k j : ℝ) * s + ∑ i ∈ Finset.univ.erase j, (k i : ℝ) * θ i := by
    funext s; exact dotIR_update k θ j s
  rw [this]
  simpa using ((hasDerivAt_id s).const_mul ((k j : ℝ))).add_const
    (∑ i ∈ Finset.univ.erase j, (k i : ℝ) * θ i)

lemma hasDerivAt_cos_affine (c d : ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.cos (2 * π * (c + s * d)))
      (-(2 * π * d) * Real.sin (2 * π * (c + t * d))) t := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * π * (c + s * d)) (2 * π * d) t := by
    have := (((hasDerivAt_id t).mul_const d).const_add c).const_mul (2 * π)
    simpa using this
  have := (Real.hasDerivAt_cos (2 * π * (c + t * d))).comp t h1
  simpa [mul_comm] using this

lemma hasDerivAt_sin_affine (c d : ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.sin (2 * π * (c + s * d)))
      ((2 * π * d) * Real.cos (2 * π * (c + t * d))) t := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * π * (c + s * d)) (2 * π * d) t := by
    have := (((hasDerivAt_id t).mul_const d).const_add c).const_mul (2 * π)
    simpa using this
  have := (Real.hasDerivAt_sin (2 * π * (c + t * d))).comp t h1
  simpa [mul_comm] using this

/-- The `j`-th partial derivative of a trigonometric polynomial. -/
lemma partialDeriv_trigPoly (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (j : Fin n) (θ : Fin n → ℝ) :
    partialDeriv (trigPoly K a b) j θ =
      ∑ k ∈ K, 2 * π * (k j : ℝ) *
        (-(a k) * Real.sin (2 * π * dotIR k θ) + b k * Real.cos (2 * π * dotIR k θ)) := by
  have key : HasDerivAt (fun s => trigPoly K a b (Function.update θ j s))
      (∑ k ∈ K, 2 * π * (k j : ℝ) *
        (-(a k) * Real.sin (2 * π * dotIR k θ) + b k * Real.cos (2 * π * dotIR k θ))) (θ j) := by
    have hupd : Function.update θ j (θ j) = θ := Function.update_eq_self j θ
    simp only [trigPoly]
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have hd : HasDerivAt (fun s => 2 * π * dotIR k (Function.update θ j s))
        (2 * π * (k j : ℝ)) (θ j) := by
      simpa using (hasDerivAt_dotIR_update k θ j (θ j)).const_mul (2 * π)
    have hc : HasDerivAt (fun s => Real.cos (2 * π * dotIR k (Function.update θ j s)))
        (-Real.sin (2 * π * dotIR k θ) * (2 * π * (k j : ℝ))) (θ j) := by
      have := (Real.hasDerivAt_cos (2 * π * dotIR k (Function.update θ j (θ j)))).comp (θ j) hd
      rw [hupd] at this
      exact this
    have hs : HasDerivAt (fun s => Real.sin (2 * π * dotIR k (Function.update θ j s)))
        (Real.cos (2 * π * dotIR k θ) * (2 * π * (k j : ℝ))) (θ j) := by
      have := (Real.hasDerivAt_sin (2 * π * dotIR k (Function.update θ j (θ j)))).comp (θ j) hd
      rw [hupd] at this
      exact this
    have := (hc.const_mul (a k)).add (hs.const_mul (b k))
    convert this using 1
    ring
  rw [partialDeriv, key.deriv]

lemma partialDeriv_linear (ω : Fin n → ℝ) (j : Fin n) (I : Fin n → ℝ) (c : ℝ) :
    partialDeriv (fun y => (∑ i, ω i * y i) + c) j I = ω j := by
  have h : HasDerivAt (fun s => (∑ i, ω i * (Function.update I j s) i) + c) (ω j) (I j) := by
    have h0 : (fun s => (∑ i, ω i * (Function.update I j s) i) + c) =
        fun s => ω j * s + ((∑ i ∈ Finset.univ.erase j, ω i * I i) + c) := by
      funext s
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Function.update_self]
      have : ∑ i ∈ Finset.univ.erase j, ω i * (Function.update I j s) i =
          ∑ i ∈ Finset.univ.erase j, ω i * I i :=
        Finset.sum_congr rfl (fun i hi => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
      rw [this]; ring
    rw [h0]
    simpa using ((hasDerivAt_id (I j)).const_mul (ω j)).add_const
      ((∑ i ∈ Finset.univ.erase j, ω i * I i) + c)
  rw [partialDeriv, h.deriv]

lemma partialDeriv_const_add (f : (Fin n → ℝ) → ℝ) (c : ℝ) (j : Fin n) (x : Fin n → ℝ) :
    partialDeriv (fun y => c + f y) j x = partialDeriv f j x := by
  simp only [partialDeriv]
  exact congrFun (deriv_const_add' c) (x j)

lemma partialDeriv_const_mul (f : (Fin n → ℝ) → ℝ) (c : ℝ) (j : Fin n) (x : Fin n → ℝ) :
    partialDeriv (fun y => c * f y) j x = c * partialDeriv f j x := by
  simp only [partialDeriv]
  exact deriv_const_mul_field c

lemma abs_trig_comb_le (A B x : ℝ) :
    |A * Real.cos x + B * Real.sin x| ≤ |A| + |B| := by
  have h1 : |A * Real.cos x| ≤ |A| := by
    rw [abs_mul]
    nlinarith [Real.abs_cos_le_one x, abs_nonneg A, abs_nonneg (Real.cos x)]
  have h2 : |B * Real.sin x| ≤ |B| := by
    rw [abs_mul]
    nlinarith [Real.abs_sin_le_one x, abs_nonneg B, abs_nonneg (Real.sin x)]
  have := abs_add_le (A * Real.cos x) (B * Real.sin x)
  linarith

/-! ### The main theorem -/

/--
**KAM theorem (persistence of invariant tori), exact version for an isochronous
integrable Hamiltonian with trigonometric-polynomial perturbation.**

Let `ω ∈ ℝⁿ` be a Diophantine frequency vector: `|⟪k, ω⟫| ≥ γ / ‖k‖^τ` for all nonzero integer
vectors `k`. Consider the nearly integrable Hamiltonian
`H_ε(θ, I) = ⟪ω, I⟫ + ε P(θ)` on `𝕋ⁿ × ℝⁿ`, where `P` is a mean-zero trigonometric polynomial
(finite mode set `K` not containing `0`). For `ε = 0` the torus `{I = 0}` is invariant and
carries the quasi-periodic flow `θ(t) = θ₀ + tω`.

Then for **every** `ε` the invariant torus persists: there is a family of embeddings
`θ ↦ (θ, G ε θ)` of `𝕋ⁿ` (i.e. `G ε` is `ℤⁿ`-periodic) which is `O(ε)`-close to the
unperturbed torus `{I = 0}`, uniformly in `ε` and `θ`, and which is invariant under the flow of
`H_ε` with the *same* quasi-periodic dynamics `θ(t) = θ₀ + tω` on it.

The Diophantine hypothesis enters through the small divisors `⟪k, ω⟫` used to solve the
homological equation `∂_ω u = P`.
-/
theorem kam_theorem {n : ℕ} (ω : Fin n → ℝ) (γ τ : ℝ) (hγ : 0 < γ)
    (hdio : ∀ k : Fin n → ℤ, k ≠ 0 → γ / (‖k‖ : ℝ) ^ τ ≤ |dotIR k ω|)
    (K : Finset (Fin n → ℤ)) (hK : (0 : Fin n → ℤ) ∉ K) (a b : (Fin n → ℤ) → ℝ) :
    ∃ G : ℝ → (Fin n → ℝ) → (Fin n → ℝ), ∃ C : ℝ, 0 ≤ C ∧
      -- the torus is `O(ε)`-close to the unperturbed invariant torus `{I = 0}`
      (∀ ε θ, ‖G ε θ‖ ≤ |ε| * C) ∧
      -- `G ε` descends to the torus `𝕋ⁿ = ℝⁿ/ℤⁿ`
      (∀ ε (m : Fin n → ℤ) (θ : Fin n → ℝ), G ε (θ + fun i => (m i : ℝ)) = G ε θ) ∧
      -- invariance: the graph of `G ε` is filled by solutions with linear flow `θ₀ + tω`
      (∀ ε θ₀, IsHamiltonianSolution (kamHam ω K a b ε)
          (fun t => θ₀ + t • ω) (fun t => G ε (θ₀ + t • ω))) := by
  -- nonresonance of the modes occurring in `P`
  have hres : ∀ k ∈ K, dotIR k ω ≠ 0 := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => hK (h ▸ hk)
    have hnorm : (0 : ℝ) < ‖k‖ := norm_pos_iff.mpr hk0
    have : 0 < γ / (‖k‖ : ℝ) ^ τ := div_pos hγ (Real.rpow_pos_of_pos hnorm τ)
    have := lt_of_lt_of_le this (hdio k hk0)
    exact fun h => by simp [h] at this
  refine ⟨fun ε θ j => -ε * ∑ k ∈ K, (k j : ℝ) *
      (a k * Real.cos (2 * π * dotIR k θ) + b k * Real.sin (2 * π * dotIR k θ)) / dotIR k ω,
    ∑ k ∈ K, ‖k‖ * (|a k| + |b k|) / |dotIR k ω|, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun k _ => by positivity)
  · -- closeness estimate
    intro ε θ
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    simp only [Real.norm_eq_abs, abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
    calc |∑ k ∈ K, (k j : ℝ) *
            (a k * Real.cos (2 * π * dotIR k θ) + b k * Real.sin (2 * π * dotIR k θ))
              / dotIR k ω|
        ≤ ∑ k ∈ K, |(k j : ℝ) *
            (a k * Real.cos (2 * π * dotIR k θ) + b k * Real.sin (2 * π * dotIR k θ))
              / dotIR k ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ K, ‖k‖ * (|a k| + |b k|) / |dotIR k ω| := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hd : 0 < |dotIR k ω| := abs_pos.mpr (hres k hk)
          have hkj : |((k j : ℤ) : ℝ)| ≤ ‖k‖ := by
            have h1 : ‖(k j : ℤ)‖ ≤ ‖k‖ := norm_le_pi_norm k j
            simpa [Int.norm_eq_abs] using h1
          rw [abs_div, abs_mul]
          gcongr
          exact abs_trig_comb_le (a k) (b k) (2 * π * dotIR k θ)
  · -- periodicity
    intro ε m θ
    funext j
    simp only
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [dotIR_add_intVec]
    have hc : Real.cos (2 * π * (dotIR k θ + ((∑ i, k i * m i : ℤ) : ℝ))) =
        Real.cos (2 * π * dotIR k θ) := by
      have : 2 * π * (dotIR k θ + ((∑ i, k i * m i : ℤ) : ℝ)) =
          2 * π * dotIR k θ + ((∑ i, k i * m i : ℤ) : ℝ) * (2 * π) := by ring
      rw [this, Real.cos_add_int_mul_two_pi]
    have hs : Real.sin (2 * π * (dotIR k θ + ((∑ i, k i * m i : ℤ) : ℝ))) =
        Real.sin (2 * π * dotIR k θ) := by
      have : 2 * π * (dotIR k θ + ((∑ i, k i * m i : ℤ) : ℝ)) =
          2 * π * dotIR k θ + ((∑ i, k i * m i : ℤ) : ℝ) * (2 * π) := by ring
      rw [this, Real.sin_add_int_mul_two_pi]
    rw [hc, hs]
  · -- invariance
    intro ε θ₀ t
    set θc : Fin n → ℝ := θ₀ + t • ω with hθc
    constructor
    · -- `θ̇ = ∂H/∂I = ω`
      intro j
      have hpd : partialDeriv (fun y => kamHam ω K a b ε θc y) j (fun j => -ε * ∑ k ∈ K,
          (k j : ℝ) * (a k * Real.cos (2 * π * dotIR k θc) +
            b k * Real.sin (2 * π * dotIR k θc)) / dotIR k ω) = ω j := by
        simp only [kamHam]
        exact partialDeriv_linear ω j _ (ε * trigPoly K a b θc)
      rw [hpd]
      have : (fun s : ℝ => (θ₀ + s • ω) j) = fun s : ℝ => ω j * s + θ₀ j := by
        funext s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      simpa using ((hasDerivAt_id t).const_mul (ω j)).add_const (θ₀ j)
    · -- `İ = -∂H/∂θ`
      intro j
      have hpd : partialDeriv (fun x => kamHam ω K a b ε x (fun j => -ε * ∑ k ∈ K,
            (k j : ℝ) * (a k * Real.cos (2 * π * dotIR k θc) +
              b k * Real.sin (2 * π * dotIR k θc)) / dotIR k ω)) j θc
          = ε * ∑ k ∈ K, 2 * π * (k j : ℝ) *
              (-(a k) * Real.sin (2 * π * dotIR k θc) + b k * Real.cos (2 * π * dotIR k θc)) := by
        simp only [kamHam]
        rw [partialDeriv_const_add (fun x => ε * trigPoly K a b x) _ j θc,
          partialDeriv_const_mul (trigPoly K a b) ε j θc, partialDeriv_trigPoly]
      rw [hpd]
      -- the derivative of the parameterization along the linear flow
      have hfun : (fun s : ℝ => -ε * ∑ k ∈ K, (k j : ℝ) *
            (a k * Real.cos (2 * π * dotIR k (θ₀ + s • ω)) +
              b k * Real.sin (2 * π * dotIR k (θ₀ + s • ω))) / dotIR k ω) =
          fun s : ℝ => -ε * ∑ k ∈ K, (k j : ℝ) *
            (a k * Real.cos (2 * π * (dotIR k θ₀ + s * dotIR k ω)) +
              b k * Real.sin (2 * π * (dotIR k θ₀ + s * dotIR k ω))) / dotIR k ω := by
        funext s
        simp only [dotIR_add_smul]
      have hderiv : HasDerivAt (fun s : ℝ => -ε * ∑ k ∈ K, (k j : ℝ) *
            (a k * Real.cos (2 * π * (dotIR k θ₀ + s * dotIR k ω)) +
              b k * Real.sin (2 * π * (dotIR k θ₀ + s * dotIR k ω))) / dotIR k ω)
          (-ε * ∑ k ∈ K, (k j : ℝ) * 2 * π *
            (-(a k) * Real.sin (2 * π * (dotIR k θ₀ + t * dotIR k ω)) +
              b k * Real.cos (2 * π * (dotIR k θ₀ + t * dotIR k ω)))) t := by
        refine HasDerivAt.const_mul (-ε) (HasDerivAt.fun_sum (fun k hk => ?_))
        have hdne : dotIR k ω ≠ 0 := hres k hk
        have hc := hasDerivAt_cos_affine (dotIR k θ₀) (dotIR k ω) t
        have hs := hasDerivAt_sin_affine (dotIR k θ₀) (dotIR k ω) t
        have h := (((hc.const_mul (a k)).add (hs.const_mul (b k))).const_mul
          ((k j : ℝ))).div_const (dotIR k ω)
        convert h using 1
        field_simp
      have heq : (fun s : ℝ => (fun j => -ε * ∑ k ∈ K, (k j : ℝ) *
            (a k * Real.cos (2 * π * dotIR k (θ₀ + s • ω)) +
              b k * Real.sin (2 * π * dotIR k (θ₀ + s • ω))) / dotIR k ω) j) =
          fun s : ℝ => -ε * ∑ k ∈ K, (k j : ℝ) *
            (a k * Real.cos (2 * π * (dotIR k θ₀ + s * dotIR k ω)) +
              b k * Real.sin (2 * π * (dotIR k θ₀ + s * dotIR k ω))) / dotIR k ω := hfun
      rw [heq]
      convert hderiv using 1
      have hdc : ∀ k, dotIR k θc = dotIR k θ₀ + t * dotIR k ω := by
        intro k; rw [hθc, dotIR_add_smul]
      simp only [hdc]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ### Base case and non-vacuity of the hypotheses -/

/-- **Base case (`ε = 0`).** For the unperturbed integrable Hamiltonian `H₀(θ, I) = ⟪ω, I⟫`
the flat torus `{I = 0}` is invariant and carries the quasi-periodic flow `θ(t) = θ₀ + tω`. -/
theorem kam_base_case {n : ℕ} (ω : Fin n → ℝ) (K : Finset (Fin n → ℤ))
    (a b : (Fin n → ℤ) → ℝ) (θ₀ : Fin n → ℝ) :
    IsHamiltonianSolution (kamHam ω K a b 0) (fun t => θ₀ + t • ω) (fun _ => 0) := by
  intro t
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hpd : partialDeriv (fun y => kamHam ω K a b 0 (θ₀ + t • ω) y) j 0 = ω j := by
      simp only [kamHam]
      exact partialDeriv_linear ω j 0 (0 * trigPoly K a b (θ₀ + t • ω))
    rw [hpd]
    have hlin : (fun s : ℝ => (θ₀ + s • ω) j) = fun s : ℝ => ω j * s + θ₀ j := by
      funext s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hlin]
    simpa using ((hasDerivAt_id t).const_mul (ω j)).add_const (θ₀ j)
  · have hpd : partialDeriv (fun x => kamHam ω K a b 0 x 0) j (θ₀ + t • ω) = 0 := by
      simp only [kamHam]
      rw [partialDeriv_const_add (fun x => (0 : ℝ) * trigPoly K a b x) _ j (θ₀ + t • ω),
        partialDeriv_const_mul (trigPoly K a b) 0 j (θ₀ + t • ω), zero_mul]
    rw [hpd, neg_zero]
    simpa using (hasDerivAt_const t (0 : ℝ))

/-- The Diophantine hypothesis of `kam_theorem` is non-vacuous: in dimension one every nonzero
frequency `ω` satisfies it with `γ = |ω 0|` and `τ = 1`. -/
theorem diophantine_nonvacuous (ω : Fin 1 → ℝ) (hω : ω 0 ≠ 0) :
    0 < |ω 0| ∧ ∀ k : Fin 1 → ℤ, k ≠ 0 → |ω 0| / (‖k‖ : ℝ) ^ (1 : ℝ) ≤ |dotIR k ω| := by
  refine ⟨abs_pos.mpr hω, fun k hk => ?_⟩
  have hk0 : k 0 ≠ 0 := by
    intro h
    exact hk (funext fun i => by fin_cases i; simpa using h)
  have hnorm : ‖k‖ = |((k 0 : ℤ) : ℝ)| := by
    have h1 : ‖(k 0 : ℤ)‖ ≤ ‖k‖ := norm_le_pi_norm k 0
    have h2 : ‖k‖ ≤ ‖(k 0 : ℤ)‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => ?_)
      fin_cases i; exact le_refl _
    have : ‖k‖ = ‖(k 0 : ℤ)‖ := le_antisymm h2 h1
    simpa [Int.norm_eq_abs] using this
  have hone : (1 : ℝ) ≤ |((k 0 : ℤ) : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |k 0| := Int.one_le_abs (by simpa using hk0)
    have h2 : (1 : ℝ) ≤ ((|k 0| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [Int.cast_abs] using h2
  have hpos : (0 : ℝ) < |((k 0 : ℤ) : ℝ)| := lt_of_lt_of_le one_pos hone
  have hdot : |dotIR k ω| = |((k 0 : ℤ) : ℝ)| * |ω 0| := by
    simp [dotIR, abs_mul]
  rw [hnorm, Real.rpow_one, hdot, div_le_iff₀ hpos]
  have h4 : |ω 0| ≤ |((k 0 : ℤ) : ℝ)| * |ω 0| :=
    le_mul_of_one_le_left (abs_nonneg _) hone
  have h5 : |((k 0 : ℤ) : ℝ)| * |ω 0| ≤ |((k 0 : ℤ) : ℝ)| * |ω 0| * |((k 0 : ℤ) : ℝ)| :=
    le_mul_of_one_le_right (by positivity) hone
  linarith

end Frontier

