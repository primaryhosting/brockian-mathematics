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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/
def dotRR (c x : Fin n → ℝ) : ℝ := ∑ j, c j * x j

/-- Pairing of an integer Fourier mode `k ∈ ℤⁿ` with an angle vector `x`. -/
def dotZR (k : Fin n → ℤ) (x : Fin n → ℝ) : ℝ := dotRR (fun j => (k j : ℝ)) x

/-- The `ℓ¹` norm `|k|₁ = ∑ⱼ |kⱼ|` of an integer Fourier mode. -/
def l1Norm (k : Fin n → ℤ) : ℝ := ∑ j, |(k j : ℝ)|

/-- The Diophantine (small divisor) condition on a frequency vector `ω`:
`|⟨k, ω⟩| ≥ γ / |k|₁ ^ τ` for every nonzero integer mode `k`. -/
def Diophantine (ω : Fin n → ℝ) (γ τ : ℝ) : Prop :=
  ∀ k : Fin n → ℤ, k ≠ 0 → γ / (l1Norm k) ^ τ ≤ |dotZR k ω|

/-- A trigonometric-polynomial perturbation of the angles,
`f(x) = ∑_{k ∈ s} a k * cos (2π ⟨k, x⟩)`. -/
noncomputable def pert (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ k ∈ s, a k * Real.cos (2 * Real.pi * dotZR k x)

/-- The deformation of the invariant torus produced by the perturbation:
the perturbed torus is the graph `I = I₀ + W(x)` over the angles. -/
noncomputable def torusDeformation (ω : Fin n → ℝ) (ε : ℝ) (s : Finset (Fin n → ℤ))
    (a : (Fin n → ℤ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => -ε * ∑ k ∈ s, a k * (k j : ℝ) * Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω

/-- The `j`-th partial derivative of a function of several real variables. -/
noncomputable def partialDeriv (F : (Fin n → ℝ) → ℝ) (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t : ℝ => F (Function.update x j t)) (x j)

/-- The near-integrable Hamiltonian `H(I, x) = ⟨ω, I⟩ + ε f(x)` in action–angle variables. -/
noncomputable def ham (ω : Fin n → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => dotRR ω p.1 + ε * f p.2

/-- Hamilton's equations `İ = -∂H/∂x`, `ẋ = ∂H/∂I` for a curve `t ↦ (I t, Θ t)`. -/
def IsHamiltonianSolution (H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (I Θ : ℝ → (Fin n → ℝ)) : Prop :=
  ∀ t : ℝ, ∀ j : Fin n,
    HasDerivAt (fun u : ℝ => I u j) (-partialDeriv (fun y => H (I t, y)) j (Θ t)) t ∧
    HasDerivAt (fun u : ℝ => Θ u j) (partialDeriv (fun z => H (z, Θ t)) j (I t)) t

/-! ### Basic algebra of the pairings -/

lemma dotRR_update (c x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    dotRR c (Function.update x j t) = dotRR c x + c j * (t - x j) := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      c i * Function.update x j t i = c i * x i + (if i = j then c j * (t - x j) else 0) := by
    intro i _
    by_cases h : i = j
    · subst h; simp [Function.update_self]; ring
    · simp [h]
  rw [dotRR, dotRR, Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma dotZR_update (k : Fin n → ℤ) (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    dotZR k (Function.update x j t) = dotZR k x + (k j : ℝ) * (t - x j) :=
  dotRR_update _ x j t

lemma dotZR_linear (k : Fin n → ℤ) (θ₀ ω : Fin n → ℝ) (t : ℝ) :
    dotZR k (fun j => θ₀ j + t * ω j) = dotZR k θ₀ + t * dotZR k ω := by
  simp only [dotZR, dotRR, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma dotZR_add_int (k m : Fin n → ℤ) (x : Fin n → ℝ) :
    dotZR k (fun j => x j + (m j : ℝ)) = dotZR k x + ((∑ j, k j * m j : ℤ) : ℝ) := by
  simp only [dotZR, dotRR, Int.cast_sum, Int.cast_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma l1Norm_nonneg (k : Fin n → ℤ) : 0 ≤ l1Norm k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma abs_le_l1Norm (k : Fin n → ℤ) (j : Fin n) : |(k j : ℝ)| ≤ l1Norm k :=
  Finset.single_le_sum (f := fun i => |(k i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

lemma l1Norm_pos {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < l1Norm k := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext fun j => h j)
  have h1 : (0 : ℝ) < |(k j : ℝ)| := by
    simpa [abs_pos] using (Int.cast_ne_zero (α := ℝ)).2 hj
  exact lt_of_lt_of_le h1 (abs_le_l1Norm k j)

/-! ### Small divisor estimates -/

lemma abs_dotZR_pos {ω : Fin n → ℝ} {γ τ : ℝ} (hγ : 0 < γ) (hω : Diophantine ω γ τ)
    {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < |dotZR k ω| := by
  have hp : (0 : ℝ) < (l1Norm k) ^ τ := Real.rpow_pos_of_pos (l1Norm_pos hk) τ
  exact lt_of_lt_of_le (div_pos hγ hp) (hω k hk)

lemma dotZR_ne_zero {ω : Fin n → ℝ} {γ τ : ℝ} (hγ : 0 < γ) (hω : Diophantine ω γ τ)
    {k : Fin n → ℤ} (hk : k ≠ 0) : dotZR k ω ≠ 0 := by
  intro h
  have := abs_dotZR_pos hγ hω hk
  rw [h] at this
  simp at this

lemma inv_abs_dotZR_le {ω : Fin n → ℝ} {γ τ : ℝ} (hγ : 0 < γ) (hω : Diophantine ω γ τ)
    {k : Fin n → ℤ} (hk : k ≠ 0) : 1 / |dotZR k ω| ≤ (l1Norm k) ^ τ / γ := by
  have hp : (0 : ℝ) < (l1Norm k) ^ τ := Real.rpow_pos_of_pos (l1Norm_pos hk) τ
  have h0 : (0 : ℝ) < γ / (l1Norm k) ^ τ := div_pos hγ hp
  have := one_div_le_one_div_of_le h0 (hω k hk)
  rwa [one_div_div] at this

/-! ### Derivatives -/

lemma hasDerivAt_pert_slice (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℝ)
    (j : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => pert s a (Function.update x j t))
      (-(2 * Real.pi) * ∑ k ∈ s, a k * (k j : ℝ) * Real.sin (2 * Real.pi * dotZR k x)) (x j) := by
  have key : ∀ k ∈ s, HasDerivAt
      (fun t : ℝ => a k * Real.cos (2 * Real.pi * dotZR k (Function.update x j t)))
      (-(2 * Real.pi) * (a k * (k j : ℝ) * Real.sin (2 * Real.pi * dotZR k x))) (x j) := by
    intro k _
    have hinner : HasDerivAt
        (fun t : ℝ => 2 * Real.pi * (dotZR k x + (k j : ℝ) * (t - x j)))
        (2 * Real.pi * (k j : ℝ)) (x j) := by
      have h1 : HasDerivAt (fun t : ℝ => dotZR k x + (k j : ℝ) * (t - x j)) ((k j : ℝ)) (x j) := by
        simpa using (((hasDerivAt_id (x j)).sub_const (x j)).const_mul ((k j : ℝ))).const_add
          (dotZR k x)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1.const_mul (2 * Real.pi)
    have hcos := (hinner.cos).const_mul (a k)
    have : (fun t : ℝ => a k * Real.cos (2 * Real.pi * dotZR k (Function.update x j t)))
        = fun t : ℝ => a k * Real.cos (2 * Real.pi * (dotZR k x + (k j : ℝ) * (t - x j))) := by
      funext t; rw [dotZR_update]
    rw [this]
    have hx : 2 * Real.pi * (dotZR k x + (k j : ℝ) * (x j - x j)) = 2 * Real.pi * dotZR k x := by
      ring
    convert hcos using 1
    rw [hx]
    ring
  have h := HasDerivAt.sum key
  have hf : (fun t : ℝ => pert s a (Function.update x j t))
      = ∑ k ∈ s, (fun t : ℝ => a k * Real.cos (2 * Real.pi * dotZR k (Function.update x j t))) := by
    funext t
    simp [pert, Finset.sum_apply]
  rw [hf, Finset.mul_sum]
  exact h

lemma partialDeriv_ham_angle (ω : Fin n → ℝ) (ε : ℝ) (s : Finset (Fin n → ℤ))
    (a : (Fin n → ℤ) → ℝ) (I x : Fin n → ℝ) (j : Fin n) :
    partialDeriv (fun y => ham ω ε (pert s a) (I, y)) j x
      = ε * (-(2 * Real.pi) * ∑ k ∈ s, a k * (k j : ℝ) * Real.sin (2 * Real.pi * dotZR k x)) := by
  have h := ((hasDerivAt_pert_slice s a j x).const_mul ε).const_add (dotRR ω I)
  exact h.deriv

lemma partialDeriv_ham_action (ω : Fin n → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ)
    (I x : Fin n → ℝ) (j : Fin n) :
    partialDeriv (fun z => ham ω ε f (z, x)) j I = ω j := by
  have h1 : HasDerivAt (fun t : ℝ => dotRR ω (Function.update I j t) + ε * f x) (ω j) (I j) := by
    have : (fun t : ℝ => dotRR ω (Function.update I j t) + ε * f x)
        = fun t : ℝ => (dotRR ω I + ω j * (t - I j)) + ε * f x := by
      funext t; rw [dotRR_update]
    rw [this]
    simpa using ((((hasDerivAt_id (I j)).sub_const (I j)).const_mul (ω j)).const_add
      (dotRR ω I)).add_const (ε * f x)
  exact h1.deriv

/-- Derivative along the linear flow of the torus deformation. -/
lemma hasDerivAt_torusDeformation {ω : Fin n → ℝ} {γ τ : ℝ} (hγ : 0 < γ)
    (hω : Diophantine ω γ τ) (ε : ℝ) (s : Finset (Fin n → ℤ)) (hs : (0 : Fin n → ℤ) ∉ s)
    (a : (Fin n → ℤ) → ℝ) (θ₀ : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => torusDeformation ω ε s a (fun i => θ₀ i + u * ω i) j)
      (2 * Real.pi * ε *
        ∑ k ∈ s, a k * (k j : ℝ) *
          Real.sin (2 * Real.pi * dotZR k (fun i => θ₀ i + t * ω i))) t := by
  have key : ∀ k ∈ s, HasDerivAt
      (fun u : ℝ => -ε * (a k * (k j : ℝ) *
          Real.cos (2 * Real.pi * dotZR k (fun i => θ₀ i + u * ω i)) / dotZR k ω))
      (2 * Real.pi * ε * (a k * (k j : ℝ) *
          Real.sin (2 * Real.pi * dotZR k (fun i => θ₀ i + t * ω i)))) t := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => hs (h ▸ hk)
    have hd : dotZR k ω ≠ 0 := dotZR_ne_zero hγ hω hk0
    have hinner : HasDerivAt
        (fun u : ℝ => 2 * Real.pi * (dotZR k θ₀ + u * dotZR k ω))
        (2 * Real.pi * dotZR k ω) t := by
      have h1 : HasDerivAt (fun u : ℝ => dotZR k θ₀ + u * dotZR k ω) (dotZR k ω) t := by
        simpa using ((hasDerivAt_id t).mul_const (dotZR k ω)).const_add (dotZR k θ₀)
      simpa [mul_assoc] using h1.const_mul (2 * Real.pi)
    have hcos := hinner.cos
    have hfun : (fun u : ℝ => -ε * (a k * (k j : ℝ) *
          Real.cos (2 * Real.pi * dotZR k (fun i => θ₀ i + u * ω i)) / dotZR k ω))
        = fun u : ℝ => (-ε * a k * (k j : ℝ) / dotZR k ω) *
          Real.cos (2 * Real.pi * (dotZR k θ₀ + u * dotZR k ω)) := by
      funext u
      rw [dotZR_linear]
      field_simp
    rw [hfun]
    have hd2 := hcos.const_mul (-ε * a k * (k j : ℝ) / dotZR k ω)
    convert hd2 using 1
    rw [dotZR_linear]
    field_simp
  have hsum := HasDerivAt.sum key
  have hfun2 : (fun u : ℝ => torusDeformation ω ε s a (fun i => θ₀ i + u * ω i) j)
      = ∑ k ∈ s, (fun u : ℝ => -ε * (a k * (k j : ℝ) *
          Real.cos (2 * Real.pi * dotZR k (fun i => θ₀ i + u * ω i)) / dotZR k ω)) := by
    funext u
    simp only [torusDeformation, Finset.sum_apply, Finset.mul_sum]
  rw [hfun2, Finset.mul_sum]
  exact hsum

/-! ### The main theorem -/

/--
**KAM theorem (exactly solvable case).**

For a Hamiltonian `H(I, x) = ⟨ω, I⟩ + ε f(x)` in action–angle variables, with `ω` a
Diophantine frequency vector and `f` a zero-mean trigonometric polynomial perturbation of
the angles, the unperturbed invariant torus `{I = I₀}` persists for *every* value of the
perturbation parameter `ε`: it is deformed into the graph `I = I₀ + W(x)`, where the
deformation `W` is obtained by solving the cohomological (homological) equation, the small
divisors `⟨k, ω⟩` being controlled by the Diophantine condition.

The conclusions are:
1. the explicit curve `t ↦ (I₀ + W(x₀ + tω), x₀ + tω)` solves Hamilton's equations for the
   perturbed Hamiltonian;
2. the orbit stays on the deformed torus `𝒯 = {(I, x) | I = I₀ + W x}`, i.e. `𝒯` is invariant;
3. `W` is `ℤⁿ`-periodic, so `𝒯` really is an embedded `n`-torus in action–angle space;
4. the deformed torus is `O(ε/γ)`-close to the unperturbed one, quantitatively;
5. the induced motion on the torus is the quasi-periodic linear flow with the *unperturbed*
   frequency vector `ω`.
-/
theorem kam_theorem {n : ℕ} (ω : Fin n → ℝ) (γ τ : ℝ) (hγ : 0 < γ)
    (hω : Diophantine ω γ τ)
    (s : Finset (Fin n → ℤ)) (hs : (0 : Fin n → ℤ) ∉ s)
    (a : (Fin n → ℤ) → ℝ) (ε : ℝ) (I₀ θ₀ : Fin n → ℝ) :
    let W : (Fin n → ℝ) → (Fin n → ℝ) := torusDeformation ω ε s a
    let Θ : ℝ → (Fin n → ℝ) := fun t j => θ₀ j + t * ω j
    let I : ℝ → (Fin n → ℝ) := fun t j => I₀ j + W (Θ t) j
    let 𝒯 : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {p | p.1 = fun j => I₀ j + W p.2 j}
    IsHamiltonianSolution (ham ω ε (pert s a)) I Θ ∧
    (∀ t : ℝ, (I t, Θ t) ∈ 𝒯) ∧
    (∀ (x : Fin n → ℝ) (m : Fin n → ℤ), W (fun j => x j + (m j : ℝ)) = W x) ∧
    (∀ (x : Fin n → ℝ) (j : Fin n),
      |W x j| ≤ |ε| * (∑ k ∈ s, |a k| * (l1Norm k) ^ (τ + 1)) / γ) ∧
    (∀ (t : ℝ) (j : Fin n), Θ t j = θ₀ j + t * ω j) := by
  intro W Θ I 𝒯
  refine ⟨?_, ?_, ?_, ?_, fun t j => rfl⟩
  · -- Hamilton's equations
    intro t j
    constructor
    · rw [partialDeriv_ham_angle]
      have h := hasDerivAt_torusDeformation hγ hω ε s hs a θ₀ j t
      have : (fun u : ℝ => I u j)
          = fun u : ℝ => I₀ j + torusDeformation ω ε s a (fun i => θ₀ i + u * ω i) j := rfl
      rw [this]
      have h2 := h.const_add (I₀ j)
      convert h2 using 1
      show -(ε * (-(2 * Real.pi) * _)) = _
      ring
    · rw [partialDeriv_ham_action]
      show HasDerivAt (fun u : ℝ => θ₀ j + u * ω j) (ω j) t
      simpa using ((hasDerivAt_id t).mul_const (ω j)).const_add (θ₀ j)
  · intro t
    show (I t) = fun j => I₀ j + W (Θ t) j
    rfl
  · -- ℤⁿ-periodicity of the deformation
    intro x m
    funext j
    show -ε * ∑ k ∈ s, a k * (k j : ℝ) *
        Real.cos (2 * Real.pi * dotZR k (fun i => x i + (m i : ℝ))) / dotZR k ω
      = -ε * ∑ k ∈ s, a k * (k j : ℝ) * Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [dotZR_add_int]
    have : 2 * Real.pi * (dotZR k x + ((∑ i, k i * m i : ℤ) : ℝ))
        = 2 * Real.pi * dotZR k x + ((∑ i, k i * m i : ℤ) : ℝ) * (2 * Real.pi) := by ring
    rw [this, Real.cos_add_int_mul_two_pi]
  · -- quantitative closeness
    intro x j
    have hterm : ∀ k ∈ s,
        |a k * (k j : ℝ) * Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω|
          ≤ |a k| * (l1Norm k) ^ (τ + 1) / γ := by
      intro k hk
      have hk0 : k ≠ 0 := fun h => hs (h ▸ hk)
      have hpos : 0 < |dotZR k ω| := abs_dotZR_pos hγ hω hk0
      have hL : (0:ℝ) < l1Norm k := l1Norm_pos hk0
      have hrpow : (0:ℝ) < (l1Norm k) ^ τ := Real.rpow_pos_of_pos hL τ
      have h1 : |a k * (k j : ℝ) * Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω|
          = |a k| * |(k j : ℝ)| * |Real.cos (2 * Real.pi * dotZR k x)| * (1 / |dotZR k ω|) := by
        rw [abs_div, abs_mul, abs_mul]
        ring
      rw [h1]
      have hcos : |Real.cos (2 * Real.pi * dotZR k x)| ≤ 1 := Real.abs_cos_le_one _
      have hkj : |(k j : ℝ)| ≤ l1Norm k := abs_le_l1Norm k j
      have hinv : 1 / |dotZR k ω| ≤ (l1Norm k) ^ τ / γ := inv_abs_dotZR_le hγ hω hk0
      have step1 : |a k| * |(k j : ℝ)| * |Real.cos (2 * Real.pi * dotZR k x)| * (1 / |dotZR k ω|)
          ≤ |a k| * (l1Norm k) * 1 * ((l1Norm k) ^ τ / γ) := by
        apply mul_le_mul _ hinv (by positivity) (by positivity)
        apply mul_le_mul _ hcos (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hkj (abs_nonneg _)
      refine step1.trans_eq ?_
      rw [Real.rpow_add_one (ne_of_gt hL) τ]
      field_simp
    have hsum := Finset.sum_le_sum hterm
    have habs : |W x j| = |ε| * |∑ k ∈ s, a k * (k j : ℝ) *
        Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω| := by
      show |-ε * ∑ k ∈ s, a k * (k j : ℝ) *
        Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω| = _
      rw [abs_mul, abs_neg]
    rw [habs]
    have h2 : |∑ k ∈ s, a k * (k j : ℝ) * Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω|
        ≤ ∑ k ∈ s, |a k| * (l1Norm k) ^ (τ + 1) / γ :=
      (Finset.abs_sum_le_sum_abs _ _).trans hsum
    calc |ε| * |∑ k ∈ s, a k * (k j : ℝ) * Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω|
        ≤ |ε| * ∑ k ∈ s, |a k| * (l1Norm k) ^ (τ + 1) / γ :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |ε| * (∑ k ∈ s, |a k| * (l1Norm k) ^ (τ + 1)) / γ := by
          rw [← Finset.sum_div, mul_div_assoc]

/-! ### Non-vacuity of the hypotheses -/

/-- The frequency `ω = 1` on a single angle is Diophantine with `γ = 1`, `τ = 0`. -/
lemma diophantine_one : Diophantine (fun _ : Fin 1 => (1 : ℝ)) 1 0 := by
  intro k hk
  have hk0 : k 0 ≠ 0 := by
    intro h
    exact hk (funext fun j => by fin_cases j; exact h)
  have h1 : (1 : ℝ) ≤ |(k 0 : ℝ)| := by
    have : (1 : ℤ) ≤ |k 0| := Int.one_le_abs (by simpa using hk0)
    exact_mod_cast (by exact_mod_cast this : ((1 : ℤ) : ℝ) ≤ ((|k 0| : ℤ) : ℝ))
  simpa [dotZR, dotRR, l1Norm, Real.rpow_zero] using h1

/-- The hypotheses of `kam_theorem` are satisfiable with a genuinely nonzero perturbation:
for `ε ≠ 0` the invariant torus really is deformed. -/
lemma kam_hypotheses_nonvacuous (ε : ℝ) :
    Diophantine (fun _ : Fin 1 => (1 : ℝ)) 1 0 ∧
    (0 : Fin 1 → ℤ) ∉ ({fun _ => 1} : Finset (Fin 1 → ℤ)) ∧
    torusDeformation (fun _ : Fin 1 => (1 : ℝ)) ε ({fun _ => 1} : Finset (Fin 1 → ℤ))
      (fun _ => 1) (fun _ => 0) 0 = -ε := by
  refine ⟨diophantine_one, ?_, ?_⟩
  · simp only [Finset.mem_singleton]
    intro h
    have := congrFun h 0
    simp at this
  · simp [torusDeformation, dotZR, dotRR]

end Frontier

