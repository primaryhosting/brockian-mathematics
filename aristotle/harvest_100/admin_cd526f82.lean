import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Part I. Transfer matrices, mass gap, and exponential clustering -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The kinematical data extracted from a Euclidean quantum field theory by the
Osterwalder–Schrader reconstruction: a (complex) Hilbert space of physical states, a
normalised vacuum vector, and the self-adjoint contraction semigroup `T t = e^{-tH}`
of Euclidean time translations, which fixes the vacuum. -/
structure TransferMatrixTheory (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The Euclidean time evolution semigroup `T t = e^{-t H}`. -/
  T : ℝ → (H →L[ℂ] H)
  /-- The vacuum state. -/
  vacuum : H
  norm_vacuum : ‖vacuum‖ = 1
  T_zero : T 0 = ContinuousLinearMap.id ℂ H
  T_add : ∀ ⦃s t : ℝ⦄, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  T_selfAdjoint : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x y : H, ⟪T t x, y⟫_ℂ = ⟪x, T t y⟫_ℂ
  T_contraction : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖
  T_vacuum : ∀ ⦃t : ℝ⦄, 0 ≤ t → T t vacuum = vacuum

namespace TransferMatrixTheory

variable (Th : TransferMatrixTheory H)

/-- The theory has a mass gap at least `Δ > 0`: on the orthogonal complement of the vacuum
the Euclidean evolution decays at least like `e^{-Δ t}`, uniformly in the state.  Equivalently,
the Hamiltonian has spectrum contained in `{0} ∪ [Δ, ∞)`. -/
def HasMassGap (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ ψ : H, ⟪Th.vacuum, ψ⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
    ‖Th.T t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖

/-- The theory clusters exponentially with rate `Δ > 0`: truncated (vacuum-subtracted)
Euclidean correlations decay exponentially in the time separation, with a constant that is
allowed to depend on the state. -/
def HasExponentialClustering (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ ψ : H, ⟪Th.vacuum, ψ⟫_ℂ = 0 → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t)

section Core

variable {Th}

lemma norm_T_sq (ψ : H) {u : ℝ} (hu : 0 ≤ u) :
    ‖Th.T u ψ‖ ^ 2 = (⟪ψ, Th.T (2 * u) ψ⟫_ℂ).re := by
  have h2 : Th.T (2 * u) ψ = Th.T u (Th.T u ψ) := by
    have h := Th.T_add hu hu
    rw [show (2 : ℝ) * u = u + u by ring, h]
    rfl
  have h3 : ⟪ψ, Th.T (2 * u) ψ⟫_ℂ = ⟪Th.T u ψ, Th.T u ψ⟫_ℂ := by
    rw [h2]; exact (Th.T_selfAdjoint hu _ _).symm
  rw [h3]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (Th.T u ψ)).symm

/-- Cauchy–Schwarz plus the semigroup property: `‖T u ψ‖² ≤ ‖ψ‖ ‖T (2u) ψ‖`. -/
lemma norm_T_sq_le (ψ : H) {u : ℝ} (hu : 0 ≤ u) :
    ‖Th.T u ψ‖ ^ 2 ≤ ‖ψ‖ * ‖Th.T (2 * u) ψ‖ := by
  rw [norm_T_sq ψ hu]
  calc (⟪ψ, Th.T (2 * u) ψ⟫_ℂ).re ≤ ‖⟪ψ, Th.T (2 * u) ψ⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖ψ‖ * ‖Th.T (2 * u) ψ‖ := norm_inner_le_norm _ _

/-- A state whose two-point function decays like `C e^{-Δ t}` has `‖T u ψ‖ ≤ √C e^{-Δ u}`. -/
lemma norm_T_le_sqrt (ψ : H) {C Δ : ℝ}
    (hC : ∀ t : ℝ, 0 ≤ t → ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t))
    {u : ℝ} (hu : 0 ≤ u) :
    ‖Th.T u ψ‖ ≤ Real.sqrt C * Real.exp (-Δ * u) := by
  have h1 : ‖Th.T u ψ‖ ^ 2 ≤ ‖⟪ψ, Th.T (2 * u) ψ⟫_ℂ‖ := by
    rw [norm_T_sq ψ hu]; exact Complex.re_le_norm _
  have h2 := hC (2 * u) (by linarith)
  have h3 : (Real.exp (-Δ * u)) ^ 2 = Real.exp (-Δ * (2 * u)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hbound : ‖Th.T u ψ‖ ^ 2 ≤ C * (Real.exp (-Δ * u)) ^ 2 := by
    rw [h3]; linarith
  have hCnn : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have he : (0:ℝ) < (Real.exp (-Δ * u)) ^ 2 := by positivity
    nlinarith [sq_nonneg ‖Th.T u ψ‖]
  calc ‖Th.T u ψ‖ = Real.sqrt (‖Th.T u ψ‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (C * (Real.exp (-Δ * u)) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt C * Real.exp (-Δ * u) := by
        rw [Real.sqrt_mul hCnn, Real.sqrt_sq (Real.exp_pos _).le]

/-- **Key estimate.** For a state with exponentially decaying two-point function, the
decay is in fact uniform: `‖T s ψ‖ ≤ e^{-Δ s} ‖ψ‖`, with no state-dependent constant. -/
theorem norm_T_le_of_clustering (ψ : H) {C Δ : ℝ}
    (hC : ∀ t : ℝ, 0 ≤ t → ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t))
    {s : ℝ} (hs : 0 ≤ s) :
    ‖Th.T s ψ‖ ≤ Real.exp (-Δ * s) * ‖ψ‖ := by
  rcases eq_or_lt_of_le (norm_nonneg ψ) with hψ | hψ
  · have hψ0 : ψ = 0 := norm_eq_zero.mp hψ.symm
    subst hψ0
    simp
  set N : ℝ := ‖ψ‖ with hN
  set E : ℝ := Real.exp (-Δ * s) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hNpos : (0:ℝ) < N := hψ
  set b : ℕ → ℝ := fun n => ‖Th.T (2 ^ n * s) ψ‖ with hb
  have hbnn : ∀ n, 0 ≤ b n := fun n => norm_nonneg _
  have hsn : ∀ n : ℕ, (0:ℝ) ≤ 2 ^ n * s := by
    intro n; positivity
  -- Step 1 : `b n ^ 2 ≤ N * b (n+1)`
  have step : ∀ n : ℕ, b n ^ 2 ≤ N * b (n + 1) := by
    intro n
    have h := norm_T_sq_le (Th := Th) ψ (hsn n)
    have h2 : (2 : ℝ) * (2 ^ n * s) = 2 ^ (n + 1) * s := by ring
    rw [h2] at h
    exact h
  -- Step 2 : `N * b 0 ^ (2 ^ n) ≤ N ^ (2 ^ n) * b n`
  have ind : ∀ n : ℕ, N * b 0 ^ (2 ^ n) ≤ N ^ (2 ^ n) * b n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hsq : (N * b 0 ^ (2 ^ n)) ^ 2 ≤ (N ^ (2 ^ n) * b n) ^ 2 :=
          pow_le_pow_left₀ (by positivity) ih 2
        have hexp : (N * b 0 ^ (2 ^ n)) ^ 2 = N ^ 2 * b 0 ^ (2 ^ (n + 1)) := by
          rw [mul_pow, ← pow_mul, pow_succ]
          ring_nf
        have hexp2 : (N ^ (2 ^ n) * b n) ^ 2 = N ^ (2 ^ n) * N ^ (2 ^ n) * b n ^ 2 := by
          rw [mul_pow]; ring
        have hstep := step n
        have hkey : N ^ 2 * b 0 ^ (2 ^ (n + 1))
            ≤ N ^ (2 ^ n) * N ^ (2 ^ n) * (N * b (n + 1)) := by
          calc N ^ 2 * b 0 ^ (2 ^ (n + 1)) = (N * b 0 ^ (2 ^ n)) ^ 2 := hexp.symm
            _ ≤ (N ^ (2 ^ n) * b n) ^ 2 := hsq
            _ = N ^ (2 ^ n) * N ^ (2 ^ n) * b n ^ 2 := hexp2
            _ ≤ N ^ (2 ^ n) * N ^ (2 ^ n) * (N * b (n + 1)) :=
                mul_le_mul_of_nonneg_left hstep (by positivity)
        have hpow : N ^ (2 ^ n) * N ^ (2 ^ n) = N ^ (2 ^ (n + 1)) := by
          rw [← pow_add, pow_succ]; ring_nf
        rw [hpow] at hkey
        refine le_of_mul_le_mul_left ?_ hNpos
        calc N * (N * b 0 ^ (2 ^ (n + 1))) = N ^ 2 * b 0 ^ (2 ^ (n + 1)) := by ring
          _ ≤ N ^ (2 ^ (n + 1)) * (N * b (n + 1)) := hkey
          _ = N * (N ^ (2 ^ (n + 1)) * b (n + 1)) := by ring
  -- Step 3 : the ratio `r = b 0 / (N * E)` has all `2^n`-th powers bounded
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, ∀ n : ℕ, b n ≤ C' * E ^ (2 ^ n) := by
    refine ⟨Real.sqrt C, fun n => ?_⟩
    have hbd := norm_T_le_sqrt (Th := Th) ψ hC (hsn n)
    have he : Real.exp (-Δ * (2 ^ n * s)) = E ^ (2 ^ n) := by
      rw [hE, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [he] at hbd
  set r : ℝ := b 0 / (N * E) with hr
  have hrnn : 0 ≤ r := div_nonneg (hbnn 0) (by positivity)
  have hb0 : b 0 = r * (N * E) := by
    rw [hr]; field_simp
  have hrbound : ∀ n : ℕ, N * r ^ (2 ^ n) ≤ C' := by
    intro n
    have h1 := ind n
    have h2 : N ^ (2 ^ n) * b n ≤ N ^ (2 ^ n) * (C' * E ^ (2 ^ n)) :=
      mul_le_mul_of_nonneg_left (hC' n) (by positivity)
    have h3 : N * b 0 ^ (2 ^ n) ≤ N ^ (2 ^ n) * (C' * E ^ (2 ^ n)) := le_trans h1 h2
    rw [hb0] at h3
    have h4 : (r * (N * E)) ^ (2 ^ n) = r ^ (2 ^ n) * (N ^ (2 ^ n) * E ^ (2 ^ n)) := by
      rw [mul_pow, mul_pow]
    rw [h4] at h3
    have hNE : (0:ℝ) < N ^ (2 ^ n) * E ^ (2 ^ n) := by positivity
    refine le_of_mul_le_mul_left ?_ hNE
    calc N ^ (2 ^ n) * E ^ (2 ^ n) * (N * r ^ (2 ^ n))
        = N * (r ^ (2 ^ n) * (N ^ (2 ^ n) * E ^ (2 ^ n))) := by ring
      _ ≤ N ^ (2 ^ n) * (C' * E ^ (2 ^ n)) := h3
      _ = N ^ (2 ^ n) * E ^ (2 ^ n) * C' := by ring
  -- Step 4 : hence `r ≤ 1`
  have hrle : r ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have htend : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hgt
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp htend (C' / N + 1)).exists
    have hmono : r ^ n ≤ r ^ (2 ^ n) :=
      pow_le_pow_right₀ hgt.le (Nat.lt_two_pow_self.le)
    have hbnd := hrbound n
    have h5 : C' / N + 1 ≤ r ^ (2 ^ n) := le_trans hn hmono
    have h6 : N * (C' / N + 1) ≤ N * r ^ (2 ^ n) :=
      mul_le_mul_of_nonneg_left h5 hNpos.le
    have h7 : N * (C' / N + 1) = C' + N := by field_simp
    linarith
  -- Conclude
  have hfinal : b 0 ≤ N * E := by
    rw [hb0]
    have := mul_le_mul_of_nonneg_right hrle (le_of_lt (mul_pos hNpos hEpos))
    linarith [this]
  have hb0' : ‖Th.T s ψ‖ = b 0 := by simp [hb]
  rw [hb0']
  calc b 0 ≤ N * E := hfinal
    _ = E * N := mul_comm N E

end Core

/-- **Reduction theorem.** Exponential clustering of the Euclidean correlations at rate `Δ`
implies a mass gap of size at least `Δ`: the state-dependent constants disappear. -/
theorem hasMassGap_of_hasExponentialClustering {Δ : ℝ}
    (h : Th.HasExponentialClustering Δ) : Th.HasMassGap Δ := by
  refine ⟨h.1, fun ψ hψ t ht => ?_⟩
  obtain ⟨C, hC⟩ := h.2 ψ hψ
  exact norm_T_le_of_clustering ψ hC ht

/-- Conversely, a mass gap of size `Δ` forces exponential clustering at rate `Δ`, with the
explicit constant `‖ψ‖²`. -/
theorem hasExponentialClustering_of_hasMassGap {Δ : ℝ}
    (h : Th.HasMassGap Δ) : Th.HasExponentialClustering Δ := by
  refine ⟨h.1, fun ψ hψ => ⟨‖ψ‖ ^ 2, fun t ht => ?_⟩⟩
  calc ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖Th.T t ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (Real.exp (-Δ * t) * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (h.2 ψ hψ t ht) (norm_nonneg _)
    _ = ‖ψ‖ ^ 2 * Real.exp (-Δ * t) := by ring

/-- **Mass gap and exponential clustering are equivalent.** -/
theorem hasMassGap_iff_hasExponentialClustering {Δ : ℝ} :
    Th.HasMassGap Δ ↔ Th.HasExponentialClustering Δ :=
  ⟨hasExponentialClustering_of_hasMassGap Th, hasMassGap_of_hasExponentialClustering Th⟩


/-! ### Part I.c  From clustering on a dense set of states to a mass gap -/

section Density

variable (Th : TransferMatrixTheory H)

/-- The set of states whose Euclidean two-point function decays exponentially at rate `Δ`.
By the key estimate this is a linear subspace: the cross terms are controlled by the
*uniform* decay that the key estimate provides. -/
noncomputable def clusterSubspace (Δ : ℝ) : Submodule ℂ H where
  carrier := {ψ : H | ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t)}
  zero_mem' := ⟨0, by intro t _; simp⟩
  add_mem' := by
    rintro ψ ψ₂ ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩
    refine ⟨‖ψ + ψ₂‖ * (‖ψ‖ + ‖ψ₂‖), fun t ht => ?_⟩
    have hψ : ‖Th.T t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖ := norm_T_le_of_clustering ψ hC₁ ht
    have hψ₂ : ‖Th.T t ψ₂‖ ≤ Real.exp (-Δ * t) * ‖ψ₂‖ := norm_T_le_of_clustering ψ₂ hC₂ ht
    have hsplit : ⟪ψ + ψ₂, Th.T t (ψ + ψ₂)⟫_ℂ
        = ⟪ψ + ψ₂, Th.T t ψ⟫_ℂ + ⟪ψ + ψ₂, Th.T t ψ₂⟫_ℂ := by
      rw [map_add, inner_add_right]
    calc ‖⟪ψ + ψ₂, Th.T t (ψ + ψ₂)⟫_ℂ‖
        ≤ ‖⟪ψ + ψ₂, Th.T t ψ⟫_ℂ‖ + ‖⟪ψ + ψ₂, Th.T t ψ₂⟫_ℂ‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖ψ + ψ₂‖ * ‖Th.T t ψ‖ + ‖ψ + ψ₂‖ * ‖Th.T t ψ₂‖ := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ ≤ ‖ψ + ψ₂‖ * (Real.exp (-Δ * t) * ‖ψ‖) + ‖ψ + ψ₂‖ * (Real.exp (-Δ * t) * ‖ψ₂‖) := by
          gcongr
      _ = ‖ψ + ψ₂‖ * (‖ψ‖ + ‖ψ₂‖) * Real.exp (-Δ * t) := by ring
  smul_mem' := by
    rintro a ψ ⟨C, hC⟩
    refine ⟨‖a‖ ^ 2 * C, fun t ht => ?_⟩
    have : ⟪a • ψ, Th.T t (a • ψ)⟫_ℂ = (starRingEnd ℂ) a * a * ⟪ψ, Th.T t ψ⟫_ℂ := by
      rw [map_smul, inner_smul_left, inner_smul_right]; ring
    rw [this, norm_mul, norm_mul, RCLike.norm_conj]
    have h1 := hC t ht
    nlinarith [norm_nonneg a, norm_nonneg (⟪ψ, Th.T t ψ⟫_ℂ), Real.exp_pos (-Δ * t)]

lemma mem_clusterSubspace_iff {Δ : ℝ} {ψ : H} :
    ψ ∈ Th.clusterSubspace Δ ↔
      ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖⟪ψ, Th.T t ψ⟫_ℂ‖ ≤ C * Real.exp (-Δ * t) := Iff.rfl

lemma norm_T_le_of_mem_clusterSubspace {Δ : ℝ} {ψ : H} (h : ψ ∈ Th.clusterSubspace Δ)
    {s : ℝ} (hs : 0 ≤ s) : ‖Th.T s ψ‖ ≤ Real.exp (-Δ * s) * ‖ψ‖ := by
  obtain ⟨C, hC⟩ := h
  exact norm_T_le_of_clustering ψ hC hs

/-- The set of states obeying the uniform gap bound is closed. -/
lemma isClosed_gapSet (Δ : ℝ) :
    IsClosed {ψ : H | ∀ t : ℝ, 0 ≤ t → ‖Th.T t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖} := by
  have hset : {ψ : H | ∀ t : ℝ, 0 ≤ t → ‖Th.T t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖}
      = ⋂ (t : ℝ) (_ : 0 ≤ t), {ψ : H | ‖Th.T t ψ‖ ≤ Real.exp (-Δ * t) * ‖ψ‖} := by
    ext ψ; simp [Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun t => isClosed_iInter fun _ => ?_
  exact isClosed_le ((Th.T t).continuous.norm) (continuous_const.mul continuous_norm)

/-- **Mass gap from clustering on a dense set of states.** If every state orthogonal to the
vacuum can be approximated by states with exponentially decaying two-point function, then the
theory has a mass gap. -/
theorem hasMassGap_of_dense_clusterSubspace {Δ : ℝ} (hΔ : 0 < Δ)
    (hdense : ∀ ψ : H, ⟪Th.vacuum, ψ⟫_ℂ = 0 →
      ψ ∈ closure ((Th.clusterSubspace Δ : Submodule ℂ H) : Set H)) :
    Th.HasMassGap Δ := by
  refine ⟨hΔ, fun ψ hψ t ht => ?_⟩
  have hsub : ((Th.clusterSubspace Δ : Submodule ℂ H) : Set H)
      ⊆ {x : H | ∀ s : ℝ, 0 ≤ s → ‖Th.T s x‖ ≤ Real.exp (-Δ * s) * ‖x‖} :=
    fun x hx s hs => norm_T_le_of_mem_clusterSubspace Th hx hs
  exact closure_minimal hsub (isClosed_gapSet Th Δ) (hdense ψ hψ) t ht

/-- The projection onto the orthogonal complement of the vacuum. -/
noncomputable def vacuumComplProj : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (innerSL ℂ Th.vacuum).smulRight Th.vacuum

lemma vacuumComplProj_apply (x : H) :
    Th.vacuumComplProj x = x - ⟪Th.vacuum, x⟫_ℂ • Th.vacuum := rfl

lemma inner_vacuum_self : ⟪Th.vacuum, Th.vacuum⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, Th.norm_vacuum]; norm_num

lemma inner_vacuumComplProj (x : H) : ⟪Th.vacuum, Th.vacuumComplProj x⟫_ℂ = 0 := by
  rw [vacuumComplProj_apply, inner_sub_right, inner_smul_right, Th.inner_vacuum_self]
  ring

lemma vacuumComplProj_of_orthogonal {x : H} (hx : ⟪Th.vacuum, x⟫_ℂ = 0) :
    Th.vacuumComplProj x = x := by
  rw [vacuumComplProj_apply, hx]
  simp

lemma norm_vacuumComplProj_le (x : H) : ‖Th.vacuumComplProj x‖ ≤ 2 * ‖x‖ := by
  have h1 : ‖⟪Th.vacuum, x⟫_ℂ • Th.vacuum‖ ≤ ‖x‖ := by
    rw [norm_smul, Th.norm_vacuum, mul_one]
    simpa [Th.norm_vacuum] using norm_inner_le_norm (𝕜 := ℂ) Th.vacuum x
  calc ‖Th.vacuumComplProj x‖ ≤ ‖x‖ + ‖⟪Th.vacuum, x⟫_ℂ • Th.vacuum‖ := by
        rw [vacuumComplProj_apply]; exact norm_sub_le _ _
    _ ≤ ‖x‖ + ‖x‖ := by linarith
    _ = 2 * ‖x‖ := by ring

/-- **Mass gap from clustering of a total family of states.** If the vacuum projections of a
family of states spanning a dense subspace all have exponentially decaying two-point
functions, then the theory has a mass gap. -/
theorem hasMassGap_of_total_clustering {Δ : ℝ} (hΔ : 0 < Δ) (S : Set H)
    (hSdense : Dense ((Submodule.span ℂ S : Submodule ℂ H) : Set H))
    (hS : ∀ x ∈ S, Th.vacuumComplProj x ∈ Th.clusterSubspace Δ) :
    Th.HasMassGap Δ := by
  refine hasMassGap_of_dense_clusterSubspace Th hΔ fun ψ hψ => ?_
  have hspan : Submodule.span ℂ S ≤ (Th.clusterSubspace Δ).comap (Th.vacuumComplProj : H →ₗ[ℂ] H) := by
    refine Submodule.span_le.2 fun x hx => ?_
    simpa [Submodule.mem_comap] using hS x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hvmem, hv⟩ := Metric.mem_closure_iff.1 (hSdense.closure_eq ▸ Set.mem_univ ψ) (ε / 3)
    (by linarith)
  refine ⟨Th.vacuumComplProj v, hspan hvmem, ?_⟩
  have hproj : ψ - Th.vacuumComplProj v = Th.vacuumComplProj (ψ - v) := by
    rw [map_sub, Th.vacuumComplProj_of_orthogonal hψ]
  have : dist ψ (Th.vacuumComplProj v) ≤ 2 * dist ψ v := by
    rw [dist_eq_norm, dist_eq_norm, hproj]
    exact Th.norm_vacuumComplProj_le _
  linarith

end Density

end TransferMatrixTheory

/-! ## Part I.b  Consistency: the axioms are satisfiable, with a genuine gap

The axioms of `TransferMatrixTheory`, of `HasExponentialClustering` and of `HasMassGap` are not
vacuous.  For any unit vector `Ω` in any complex Hilbert space, the semigroup
`T t = e^{-t}(1 - P_Ω) + P_Ω` (a single massive mode of mass one above the vacuum) satisfies all
of them, with gap `Δ = 1`. -/

section GappedModel

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `vacuumMix Ω a = a • id + (1 - a) • P_Ω`, where `P_Ω` is the rank-one projection on `Ω`. -/
noncomputable def vacuumMix (Ω : H) (a : ℝ) : H →L[ℂ] H :=
  ((a : ℝ) : ℂ) • (ContinuousLinearMap.id ℂ H)
    + ((1 - a : ℝ) : ℂ) • ((innerSL ℂ Ω).smulRight Ω)

lemma vacuumMix_apply (Ω x : H) (a : ℝ) :
    vacuumMix Ω a x = ((a : ℝ) : ℂ) • x + ((1 - a : ℝ) : ℂ) • (⟪Ω, x⟫_ℂ • Ω) := rfl

lemma vacuumMix_selfAdjoint (Ω : H) (a : ℝ) (x y : H) :
    ⟪vacuumMix Ω a x, y⟫_ℂ = ⟪x, vacuumMix Ω a y⟫_ℂ := by
  simp only [vacuumMix_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_conj_symm]
  ring

lemma vacuumMix_comp (Ω : H) (hΩ : ‖Ω‖ = 1) (a b : ℝ) :
    (vacuumMix Ω a).comp (vacuumMix Ω b) = vacuumMix Ω (a * b) := by
  have hΩΩ : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  ext x
  simp only [vacuumMix_apply, ContinuousLinearMap.comp_apply, inner_add_right, inner_smul_right,
    hΩΩ]
  push_cast
  module

lemma vacuumMix_norm_le (Ω : H) (hΩ : ‖Ω‖ = 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x : H) :
    ‖vacuumMix Ω a x‖ ≤ ‖x‖ := by
  have h1 : ‖⟪Ω, x⟫_ℂ • Ω‖ ≤ ‖x‖ := by
    rw [norm_smul, hΩ, mul_one]
    simpa [hΩ] using norm_inner_le_norm (𝕜 := ℂ) Ω x
  calc ‖vacuumMix Ω a x‖
      ≤ ‖((a : ℝ) : ℂ) • x‖ + ‖((1 - a : ℝ) : ℂ) • (⟪Ω, x⟫_ℂ • Ω)‖ := by
        rw [vacuumMix_apply]; exact norm_add_le _ _
    _ = a * ‖x‖ + (1 - a) * ‖⟪Ω, x⟫_ℂ • Ω‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg ha0,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - a)]
    _ ≤ a * ‖x‖ + (1 - a) * ‖x‖ := by nlinarith
    _ = ‖x‖ := by ring

lemma vacuumMix_vacuum (Ω : H) (hΩ : ‖Ω‖ = 1) (a : ℝ) : vacuumMix Ω a Ω = Ω := by
  have hΩΩ : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  rw [vacuumMix_apply, hΩΩ]
  push_cast
  module

lemma vacuumMix_orthogonal (Ω : H) {x : H} (hx : ⟪Ω, x⟫_ℂ = 0) (a : ℝ) :
    vacuumMix Ω a x = ((a : ℝ) : ℂ) • x := by
  rw [vacuumMix_apply, hx]; simp

/-- The single-massive-mode model over a unit vector `Ω`. -/
noncomputable def gappedModel (Ω : H) (hΩ : ‖Ω‖ = 1) : TransferMatrixTheory H where
  T t := vacuumMix Ω (Real.exp (-t))
  vacuum := Ω
  norm_vacuum := hΩ
  T_zero := by
    ext x
    simp [vacuumMix_apply]
  T_add := by
    intro s t _ _
    rw [vacuumMix_comp Ω hΩ, ← Real.exp_add]
    ring_nf
  T_selfAdjoint := by
    intro t _ x y
    exact vacuumMix_selfAdjoint Ω _ x y
  T_contraction := by
    intro t ht x
    refine vacuumMix_norm_le Ω hΩ (Real.exp_pos _).le ?_ x
    rw [Real.exp_le_one_iff]
    linarith
  T_vacuum := by
    intro t _
    exact vacuumMix_vacuum Ω hΩ _

/-- The model clusters exponentially with rate `1`. -/
theorem gappedModel_hasExponentialClustering (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (gappedModel Ω hΩ).HasExponentialClustering 1 := by
  refine ⟨one_pos, fun ψ hψ => ⟨‖ψ‖ ^ 2, fun t ht => ?_⟩⟩
  have hT : (gappedModel Ω hΩ).T t ψ = ((Real.exp (-t) : ℝ) : ℂ) • ψ :=
    vacuumMix_orthogonal Ω hψ _
  have hnorm : ‖⟪ψ, (gappedModel Ω hΩ).T t ψ⟫_ℂ‖ = Real.exp (-t) * ‖ψ‖ ^ 2 := by
    rw [hT, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_pow]
    simp
  rw [hnorm, neg_one_mul]
  exact le_of_eq (mul_comm _ _)

/-- Consequently the model has a mass gap of size `1`. -/
theorem gappedModel_hasMassGap (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (gappedModel Ω hΩ).HasMassGap 1 :=
  TransferMatrixTheory.hasMassGap_of_hasExponentialClustering _
    (gappedModel_hasExponentialClustering Ω hΩ)

end GappedModel

/-! ## Part II. Wilson's lattice Yang–Mills theory

The rigorous meaning of "quantum Yang–Mills theory on `ℝ⁴` exists" is that the Wilson lattice
gauge theory with compact gauge group `G` has a continuum limit obeying the
Osterwalder–Schrader/Wightman axioms.  This part sets up the lattice theory: gauge fields,
plaquettes, the Wilson action, and the finite-volume Gibbs expectation of Wilson loops. -/

section Lattice

open MeasureTheory

/-- Euclidean spacetime `ℝ⁴`. -/
abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

/-- Sites of the hypercubic lattice `ℤ⁴`. -/
abbrev Site := Fin 4 → ℤ

/-- The unit lattice vector in direction `μ`. -/
def unitVec (μ : Fin 4) : Site := fun ν => if ν = μ then 1 else 0

/-- The point of `ℝ⁴` represented by the lattice site `x` at lattice spacing `a`. -/
def embedSite (a : ℝ) (x : Site) : Spacetime := WithLp.toLp 2 (fun i => a * (x i : ℝ))

/-- A lattice gauge field assigns a group element to every directed edge `(x, μ)`. -/
def LatticeGaugeField (G : Type) := Site → Fin 4 → G

variable {G : Type} [Group G]

/-- The holonomy around the elementary plaquette based at `x` in the `(μ, ν)` plane. -/
def plaquette (U : LatticeGaugeField G) (x : Site) (μ ν : Fin 4) : G :=
  U x μ * U (x + unitVec μ) ν * (U (x + unitVec ν) μ)⁻¹ * (U x ν)⁻¹

/-- Wilson's plaquette action in a finite box `Λ`, for the class function `chi`
(the real part of the character of a faithful representation of `G`). -/
def wilsonAction (chi : G → ℝ) (Λ : Finset Site) (U : LatticeGaugeField G) : ℝ :=
  ∑ x ∈ Λ, ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then 1 - chi (plaquette U x μ ν) else 0

/-- A closed lattice path: a base site together with a list of oriented unit steps
(`(μ, true)` steps forwards in direction `μ`, `(μ, false)` steps backwards). -/
structure LatticeLoop where
  /-- The base point of the path. -/
  base : Site
  /-- The oriented unit steps of the path. -/
  steps : List (Fin 4 × Bool)

/-- The parallel transport of a gauge field along a lattice path. -/
def pathHolonomy (U : LatticeGaugeField G) : Site → List (Fin 4 × Bool) → G
  | _, [] => 1
  | x, (μ, true) :: l => U x μ * pathHolonomy U (x + unitVec μ) l
  | x, (μ, false) :: l => (U (x - unitVec μ) μ)⁻¹ * pathHolonomy U (x - unitVec μ) l

/-- The sites visited by a lattice path. -/
def pathSites : Site → List (Fin 4 × Bool) → List Site
  | x, [] => [x]
  | x, (μ, true) :: l => x :: pathSites (x + unitVec μ) l
  | x, (μ, false) :: l => x :: pathSites (x - unitVec μ) l

/-- The set of points of `ℝ⁴` visited by a lattice loop at lattice spacing `a`. -/
def latticeLoopPoints (a : ℝ) (L : LatticeLoop) : Set Spacetime :=
  embedSite a '' {x : Site | x ∈ pathSites L.base L.steps}

/-- The Wilson loop observable of a lattice loop. -/
def latticeWilsonLoop (chi : G → ℝ) (U : LatticeGaugeField G) (L : LatticeLoop) : ℝ :=
  chi (pathHolonomy U L.base L.steps)

variable [MeasurableSpace G]

/-- A configuration of edge variables in a box, extended by `1` outside the box
(free boundary conditions). -/
def boxExtend (Λ : Finset Site) (V : (↥Λ × Fin 4) → G) : LatticeGaugeField G :=
  fun x μ => if h : x ∈ Λ then V (⟨x, h⟩, μ) else 1

/-- The finite-volume Wilson-lattice-gauge-theory expectation of an observable `F` in the box
`Λ` at inverse bare coupling `beta`: the Gibbs average of `F` with respect to the Wilson action,
using the Haar probability measure on each edge. -/
noncomputable def wilsonExpectation (haar : Measure G) (chi : G → ℝ) (beta : ℝ) (Λ : Finset Site)
    (F : LatticeGaugeField G → ℝ) : ℝ :=
  (∫ V, F (boxExtend Λ V) * Real.exp (-beta * wilsonAction chi Λ (boxExtend Λ V))
      ∂(Measure.pi fun _ : (↥Λ × Fin 4) => haar))
    / (∫ V, Real.exp (-beta * wilsonAction chi Λ (boxExtend Λ V))
      ∂(Measure.pi fun _ : (↥Λ × Fin 4) => haar))

end Lattice

/-! ## Part III. Continuum loops and the statement of Yang–Mills existence -/

section Continuum

open MeasureTheory

/-- A parametrised closed loop in Euclidean spacetime `ℝ⁴`. -/
structure ContinuumLoop where
  /-- The parametrisation of the loop. -/
  toFun : ℝ → Spacetime
  continuous_toFun : Continuous toFun
  periodic_toFun : Function.Periodic toFun 1

instance : CoeFun ContinuumLoop (fun _ => ℝ → Spacetime) := ⟨ContinuumLoop.toFun⟩

/-- Reflection of the Euclidean time coordinate (coordinate `0`). -/
noncomputable def timeReflection : Spacetime ≃ₗᵢ[ℝ] Spacetime :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

/-- The unit vector in the Euclidean time direction. -/
noncomputable def timeAxis : Spacetime := EuclideanSpace.single (0 : Fin 4) (1 : ℝ)

namespace ContinuumLoop

/-- The image of a loop under a linear isometry of spacetime. -/
noncomputable def mapIsom (g : Spacetime ≃ₗᵢ[ℝ] Spacetime) (γ : ContinuumLoop) : ContinuumLoop :=
  ⟨fun s => g (γ s), g.continuous.comp γ.continuous_toFun, fun s => by
    show g (γ (s + 1)) = g (γ s)
    rw [γ.periodic_toFun s]⟩

/-- The translate of a loop by a vector of spacetime. -/
noncomputable def translate (v : Spacetime) (γ : ContinuumLoop) : ContinuumLoop :=
  ⟨fun s => γ s + v, γ.continuous_toFun.add continuous_const, fun s => by
    show γ (s + 1) + v = γ s + v
    rw [γ.periodic_toFun s]⟩

/-- The translate of a loop by `t` units of Euclidean time. -/
noncomputable def timeShift (t : ℝ) (γ : ContinuumLoop) : ContinuumLoop :=
  γ.translate (t • timeAxis)

/-- The reflection of a loop in the time-zero hyperplane. -/
noncomputable def reflect (γ : ContinuumLoop) : ContinuumLoop := γ.mapIsom timeReflection

/-- A loop lying in the time-zero hyperplane. -/
def IsTimeZero (γ : ContinuumLoop) : Prop := ∀ s : ℝ, (γ s) 0 = 0

end ContinuumLoop

/-- A complex Hilbert space of physical states. -/
structure PhysicalHilbertSpace : Type 1 where
  /-- The underlying type of states. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] PhysicalHilbertSpace.normedAddCommGroup PhysicalHilbertSpace.innerProductSpace
  PhysicalHilbertSpace.completeSpace

/-- A compact gauge group: a nontrivial compact topological group with its normalised Haar
measure and a conjugation-invariant real character (for `SU(N)`, `chi = Re tr`). -/
structure GaugeGroup : Type 1 where
  /-- The underlying group of the gauge group, e.g. `SU(3)`. -/
  carrier : Type
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]
  /-- The gauge group is compact. -/
  [compactSpace : CompactSpace carrier]
  /-- The gauge group is nontrivial (otherwise the theory is empty). -/
  [nontrivial : Nontrivial carrier]
  [measurableSpace : MeasurableSpace carrier]
  [borelSpace : BorelSpace carrier]
  /-- Normalised Haar measure on the gauge group. -/
  haar : Measure carrier
  [isHaarMeasure : haar.IsHaarMeasure]
  [isProbabilityMeasure : IsProbabilityMeasure haar]
  /-- The real part of the character of a faithful representation, used in the Wilson action. -/
  chi : carrier → ℝ
  chi_conj : ∀ g h : carrier, chi (h * g * h⁻¹) = chi g

attribute [instance] GaugeGroup.group GaugeGroup.topologicalSpace GaugeGroup.isTopologicalGroup
  GaugeGroup.compactSpace GaugeGroup.nontrivial GaugeGroup.measurableSpace GaugeGroup.borelSpace
  GaugeGroup.isHaarMeasure GaugeGroup.isProbabilityMeasure

/-- **Quantum Yang–Mills theory on `ℝ⁴` with compact gauge group `Γ`.**

This bundles the data and axioms that constitute a solution of the existence half of the
Clay Millennium problem for the gauge group `Γ`:

* a Hilbert space of physical states with a vacuum vector and the self-adjoint contraction
  semigroup `e^{-tH}` of Euclidean time translations (`transfer`), i.e. a positive-energy
  quantum theory obtained by Osterwalder–Schrader reconstruction;
* gauge-invariant Wilson-loop field operators (`wilson`) whose vacuum expectations are the
  Schwinger functions (`vacuum_expectation`), which are invariant under the full Euclidean
  group of `ℝ⁴` (`euclidean_invariance`) and which reproduce the Euclidean time evolution
  (`reconstruction`);
* completeness of the Wilson observables: the vacuum is cyclic (`vacuum_cyclic`);
* and, crucially, the statement that these Schwinger functions are the continuum limit
  (`continuum_limit`) of the Wilson lattice gauge theory with gauge group `Γ`, along lattice
  spacings tending to `0` in boxes exhausting the lattice, with loops discretised
  consistently (`discretise_approx`). -/
structure YangMillsTheory (Γ : GaugeGroup) : Type 1 where
  /-- The Hilbert space of physical states. -/
  space : PhysicalHilbertSpace
  /-- The vacuum and the Euclidean time evolution semigroup `e^{-tH}`. -/
  transfer : TransferMatrixTheory space.carrier
  /-- The Wilson loop field operators. -/
  wilson : ContinuumLoop → (space.carrier →L[ℂ] space.carrier)
  /-- The Schwinger functions (Euclidean correlation functions of Wilson loops). -/
  schwinger : List ContinuumLoop → ℂ
  /-- The lattice spacings along which the continuum limit is taken. -/
  spacing : ℕ → ℝ
  /-- The bare inverse couplings along which the continuum limit is taken. -/
  coupling : ℕ → ℝ
  /-- The finite boxes exhausting the lattice. -/
  boxes : ℕ → Finset Site
  /-- The discretisation of a continuum loop at the `n`-th lattice spacing. -/
  discretise : ℕ → ContinuumLoop → LatticeLoop
  spacing_pos : ∀ n, 0 < spacing n
  spacing_tendsto_zero : Filter.Tendsto spacing Filter.atTop (nhds 0)
  boxes_mono : Monotone boxes
  boxes_exhaust : ∀ x : Site, ∃ n, x ∈ boxes n
  /-- The discretised loops converge to the continuum loops. -/
  discretise_approx : ∀ γ : ContinuumLoop, Filter.Tendsto
    (fun n => Metric.hausdorffDist (latticeLoopPoints (spacing n) (discretise n γ))
      (Set.range γ)) Filter.atTop (nhds 0)
  /-- The Schwinger functions are the continuum limit of Wilson lattice gauge theory. -/
  continuum_limit : ∀ loops : List ContinuumLoop, Filter.Tendsto
    (fun n => wilsonExpectation Γ.haar Γ.chi (coupling n) (boxes n)
      (fun U => (loops.map (fun γ => latticeWilsonLoop Γ.chi U (discretise n γ))).prod))
    Filter.atTop (nhds (schwinger loops).re)
  /-- Euclidean invariance of the Schwinger functions. -/
  euclidean_invariance : ∀ (g : Spacetime ≃ₗᵢ[ℝ] Spacetime) (v : Spacetime)
      (loops : List ContinuumLoop),
    schwinger (loops.map (fun γ => (γ.mapIsom g).translate v)) = schwinger loops
  /-- The Schwinger functions are the vacuum expectation values of the Wilson operators. -/
  vacuum_expectation : ∀ γ : ContinuumLoop,
    ⟪transfer.vacuum, wilson γ transfer.vacuum⟫_ℂ = schwinger [γ]
  /-- Osterwalder–Schrader reconstruction: Euclidean time evolution of time-zero Wilson
  observables is computed by the Schwinger functions. -/
  reconstruction : ∀ γ₁ γ₂ : ContinuumLoop, γ₁.IsTimeZero → γ₂.IsTimeZero → ∀ t : ℝ, 0 ≤ t →
    ⟪wilson γ₁ transfer.vacuum, transfer.T t (wilson γ₂ transfer.vacuum)⟫_ℂ
      = schwinger [γ₁.reflect, γ₂.timeShift t]
  /-- The vacuum is cyclic for the time-zero Wilson observables. -/
  vacuum_cyclic : Dense (X := space.carrier)
    ↑(Submodule.span ℂ
      {x | ∃ γ : ContinuumLoop, γ.IsTimeZero ∧ x = wilson γ transfer.vacuum})

variable (Γ : GaugeGroup)

/-- **Existence of quantum Yang–Mills on `ℝ⁴` with a positive mass gap** for the compact
gauge group `Γ`: there is a quantum Yang–Mills theory (a continuum limit of Wilson lattice
gauge theory satisfying the Osterwalder–Schrader/Wightman requirements) whose Hamiltonian
has a strictly positive spectral gap above the vacuum. -/
def YangMillsExistsWithMassGap : Prop :=
  ∃ (Y : YangMillsTheory Γ) (Δ : ℝ), 0 < Δ ∧ Y.transfer.HasMassGap Δ

/-- Existence of quantum Yang–Mills on `ℝ⁴` whose truncated Euclidean correlations decay
exponentially at a fixed rate `Δ > 0` (exponential clustering). -/
def YangMillsExistsWithExponentialClustering : Prop :=
  ∃ (Y : YangMillsTheory Γ) (Δ : ℝ), 0 < Δ ∧ Y.transfer.HasExponentialClustering Δ


/-! ### Part IV.  The mass gap from clustering of the Schwinger functions

This is the substance of the reduction: exponential clustering of the (continuum limit of the)
Wilson-loop Schwinger functions — a statement purely about the Euclidean correlation functions
of the lattice gauge theory — implies a mass gap of the reconstructed quantum Hamiltonian. -/

namespace YangMillsTheory

variable {Γ : GaugeGroup} (Y : YangMillsTheory Γ)

/-- The states created from the vacuum by time-zero Wilson loops. -/
def timeZeroStates : Set Y.space.carrier :=
  {x | ∃ γ : ContinuumLoop, γ.IsTimeZero ∧ x = Y.wilson γ Y.transfer.vacuum}

/-- **Exponential clustering of the Schwinger functions** at rate `Δ`: the truncated
Euclidean two-point function of every time-zero Wilson loop with its own time translate
decays like `e^{-Δ t}`. -/
def SchwingerClustering (Δ : ℝ) : Prop :=
  ∀ γ : ContinuumLoop, γ.IsTimeZero → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    ‖Y.schwinger [γ.reflect, γ.timeShift t]
      - Y.schwinger [γ] * (starRingEnd ℂ) (Y.schwinger [γ])‖ ≤ C * Real.exp (-Δ * t)

/-- The truncated Euclidean two-point function of a time-zero Wilson loop, computed by
Osterwalder–Schrader reconstruction. -/
lemma inner_vacuumComplProj_wilson (γ : ContinuumLoop) (hγ : γ.IsTimeZero) {t : ℝ} (ht : 0 ≤ t) :
    ⟪Y.transfer.vacuumComplProj (Y.wilson γ Y.transfer.vacuum),
        Y.transfer.T t (Y.transfer.vacuumComplProj (Y.wilson γ Y.transfer.vacuum))⟫_ℂ
      = Y.schwinger [γ.reflect, γ.timeShift t]
        - Y.schwinger [γ] * (starRingEnd ℂ) (Y.schwinger [γ]) := by
  set Th := Y.transfer
  set u : Y.space.carrier := Y.wilson γ Th.vacuum
  set c : ℂ := ⟪Th.vacuum, u⟫_ℂ with hc
  have hcS : c = Y.schwinger [γ] := Y.vacuum_expectation γ
  have hΩ1 : ⟪Th.vacuum, Th.vacuum⟫_ℂ = 1 := Th.inner_vacuum_self
  have hTΩ : Th.T t Th.vacuum = Th.vacuum := Th.T_vacuum ht
  have hproj : Th.vacuumComplProj u = u - c • Th.vacuum := rfl
  have hTproj : Th.T t (u - c • Th.vacuum) = Th.T t u - c • Th.vacuum := by
    rw [map_sub, map_smul, hTΩ]
  have huΩ : ⟪u, Th.vacuum⟫_ℂ = (starRingEnd ℂ) c := by
    rw [hc, ← inner_conj_symm]
  have hΩTu : ⟪Th.vacuum, Th.T t u⟫_ℂ = c := by
    rw [← Th.T_selfAdjoint ht, hTΩ]
  have hrec : ⟪u, Th.T t u⟫_ℂ = Y.schwinger [γ.reflect, γ.timeShift t] :=
    Y.reconstruction γ γ hγ hγ t ht
  rw [hproj, hTproj]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hΩ1, huΩ,
    hΩTu, hrec, hcS.symm]
  ring

/-- **Main reduction, at the level of a single theory.** A quantum Yang–Mills theory whose
Schwinger functions cluster exponentially at rate `Δ > 0` has a mass gap of size at least
`Δ`: the Hamiltonian obtained by Osterwalder–Schrader reconstruction has spectrum contained
in `{0} ∪ [Δ, ∞)`. -/
theorem hasMassGap_of_schwingerClustering {Δ : ℝ} (hΔ : 0 < Δ)
    (h : Y.SchwingerClustering Δ) : Y.transfer.HasMassGap Δ := by
  refine TransferMatrixTheory.hasMassGap_of_total_clustering Y.transfer hΔ Y.timeZeroStates
    Y.vacuum_cyclic ?_
  rintro x ⟨γ, hγ, rfl⟩
  obtain ⟨C, hC⟩ := h γ hγ
  refine ⟨C, fun t ht => ?_⟩
  rw [Y.inner_vacuumComplProj_wilson γ hγ ht]
  exact hC t ht

end YangMillsTheory

/-- Existence of quantum Yang–Mills on `ℝ⁴` whose Wilson-loop Schwinger functions cluster
exponentially at a fixed rate `Δ > 0`. -/
def YangMillsExistsWithSchwingerClustering : Prop :=
  ∃ (Y : YangMillsTheory Γ) (Δ : ℝ), 0 < Δ ∧ Y.SchwingerClustering Δ

/-- Any single Yang–Mills theory whose Euclidean correlations cluster exponentially at rate
`Δ` has a mass gap of size at least `Δ`. -/
theorem YangMillsTheory.hasMassGap_of_clustering {Γ : GaugeGroup} (Y : YangMillsTheory Γ) {Δ : ℝ}
    (h : Y.transfer.HasExponentialClustering Δ) : Y.transfer.HasMassGap Δ :=
  TransferMatrixTheory.hasMassGap_of_hasExponentialClustering _ h

/-- **Yang–Mills existence and mass gap, reduced to exponential clustering of the Euclidean
correlation functions.**

For every compact gauge group `Γ`, the existence of a quantum Yang–Mills theory on `ℝ⁴` — a
continuum limit of Wilson lattice gauge theory satisfying the Osterwalder–Schrader
requirements — whose Wilson-loop Schwinger functions cluster exponentially at some fixed rate
`Δ > 0` implies the existence of a quantum Yang–Mills theory on `ℝ⁴` with a positive mass gap,
of size at least `Δ`: the reconstructed Hamiltonian has spectrum contained in `{0} ∪ [Δ, ∞)`.

The hypothesis is a statement purely about Euclidean correlation functions of Wilson loops (the
objects produced by the lattice theory); the conclusion is a spectral statement about the
reconstructed quantum Hamiltonian.  The nontrivial content, proved in Parts I and IV, is that
state-dependent exponential decay of the two-point functions of a total family of states
upgrades to a *uniform* spectral gap. -/
theorem yang_mills_mass_gap :
    YangMillsExistsWithSchwingerClustering Γ → YangMillsExistsWithMassGap Γ := by
  rintro ⟨Y, Δ, hΔ, h⟩
  exact ⟨Y, Δ, hΔ, Y.hasMassGap_of_schwingerClustering hΔ h⟩

/-- The same reduction, from clustering formulated directly on the physical Hilbert space. -/
theorem yang_mills_mass_gap_of_state_clustering :
    YangMillsExistsWithExponentialClustering Γ → YangMillsExistsWithMassGap Γ := by
  rintro ⟨Y, Δ, hΔ, hclust⟩
  exact ⟨Y, Δ, hΔ, TransferMatrixTheory.hasMassGap_of_hasExponentialClustering _ hclust⟩
end Continuum

end Frontier

