import Mathlib
/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ENNReal

/-! ## The Hilbert space `ℓ²(ℤ, ℝ)` -/

/-- The Hilbert space `ℓ²(ℤ)` (real scalars) on which the almost Mathieu operator acts. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℝ) 2

/-! ## Multiplication and shift operators on `ℓ²(ℤ)` -/

theorem memlp_mul {g f : ℤ → ℝ} {C : ℝ} (hg : ∀ n, |g n| ≤ C) (hf : Memℓp f 2) :
    Memℓp (fun n => g n * f n) 2 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hg 0)
  apply memℓp_gen
  have hs := hf.summable (p := 2) (by norm_num)
  have h2 : Summable fun i : ℤ => C ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ≥0∞).toReal := hs.mul_left _
  refine h2.of_nonneg_of_le (fun i => by positivity) ?_
  intro i
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_mul]
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  gcongr
  exact hg i

theorem memlp_shift {f : ℤ → ℝ} (k : ℤ) (hf : Memℓp f 2) : Memℓp (fun n => f (n + k)) 2 := by
  apply memℓp_gen
  exact (Equiv.addRight k).summable_iff.2 (hf.summable (p := 2) (by norm_num))

/-- Multiplication by a bounded sequence `g` (with `|g n| ≤ C`), as a bounded operator
on `ℓ²(ℤ)`. -/
noncomputable def mulOp (g : ℤ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) : L2Z →L[ℝ] L2Z :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => g n * (f : ℤ → ℝ) n, memlp_mul hg (lp.memℓp f)⟩
      map_add' := by intro f h; ext n; simp [mul_add]
      map_smul' := by intro c f; ext n; simp [mul_left_comm] } C
    (by
      intro f
      have hC : 0 ≤ C := le_trans (abs_nonneg _) (hg 0)
      refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
      have hs := (lp.memℓp f).summable (p := 2) (by norm_num)
      have hkey : ∀ i : ℤ, ‖g i * (f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal
          ≤ C ^ (2 : ℝ) * ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal := by
        intro i
        simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_mul]
        rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
        gcongr
        exact hg i
      have hsum : Summable fun i : ℤ => ‖g i * (f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal :=
        (hs.mul_left (C ^ (2 : ℝ))).of_nonneg_of_le (fun i => by positivity) hkey
      calc ∑' i, ‖(⟨fun n => g n * (f : ℤ → ℝ) n, memlp_mul hg (lp.memℓp f)⟩ : L2Z) i‖
              ^ (2 : ℝ≥0∞).toReal
          = ∑' i : ℤ, ‖g i * (f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal := rfl
        _ ≤ ∑' i : ℤ, C ^ (2 : ℝ) * ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal :=
            hsum.tsum_le_tsum hkey (hs.mul_left _)
        _ = C ^ (2 : ℝ) * ‖f‖ ^ (2 : ℝ≥0∞).toReal := by
            rw [tsum_mul_left, lp.norm_rpow_eq_tsum (by norm_num)]
        _ = (C * ‖f‖) ^ (2 : ℝ≥0∞).toReal := by
            rw [Real.mul_rpow hC (norm_nonneg _)]; norm_num)

@[simp]
theorem mulOp_apply (g : ℤ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) (f : L2Z) (n : ℤ) :
    (mulOp g C hg f : ℤ → ℝ) n = g n * (f : ℤ → ℝ) n := rfl

theorem norm_mulOp_le (g : ℤ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) : ‖mulOp g C hg‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (abs_nonneg _) (hg 0)) _

/-- The translation `(S_k u) n = u (n + k)` as a bounded operator on `ℓ²(ℤ)`. -/
noncomputable def shiftOp (k : ℤ) : L2Z →L[ℝ] L2Z :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => (f : ℤ → ℝ) (n + k), memlp_shift k (lp.memℓp f)⟩
      map_add' := by intro f h; ext n; simp
      map_smul' := by intro c f; ext n; simp } 1
    (by
      intro f
      refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
      have hre : ∑' i : ℤ, ‖(f : ℤ → ℝ) (i + k)‖ ^ (2 : ℝ≥0∞).toReal
          = ∑' i : ℤ, ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal :=
        (Equiv.addRight k).tsum_eq fun i => ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal
      calc ∑' i : ℤ, ‖(⟨fun n => (f : ℤ → ℝ) (n + k), memlp_shift k (lp.memℓp f)⟩ : L2Z) i‖
              ^ (2 : ℝ≥0∞).toReal
          = ∑' i : ℤ, ‖(f : ℤ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal := hre
        _ = ‖f‖ ^ (2 : ℝ≥0∞).toReal := (lp.norm_rpow_eq_tsum (by norm_num) f).symm
        _ ≤ (1 * ‖f‖) ^ (2 : ℝ≥0∞).toReal := by rw [one_mul])

@[simp]
theorem shiftOp_apply (k : ℤ) (f : L2Z) (n : ℤ) :
    (shiftOp k f : ℤ → ℝ) n = (f : ℤ → ℝ) (n + k) := rfl

theorem norm_shiftOp_le (k : ℤ) : ‖shiftOp k‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## The almost Mathieu operator -/

/-- The potential of the almost Mathieu operator: `V n = 2 λ cos (2π (θ + n α))`. -/
noncomputable def amoPotential (lam alpha theta : ℝ) : ℤ → ℝ :=
  fun n => 2 * lam * Real.cos (2 * π * (theta + n * alpha))

theorem abs_amoPotential_le (lam alpha theta : ℝ) (n : ℤ) :
    |amoPotential lam alpha theta n| ≤ 2 * |lam| := by
  have h := Real.abs_cos_le_one (2 * π * (theta + n * alpha))
  calc |amoPotential lam alpha theta n|
      = 2 * |lam| * |Real.cos (2 * π * (theta + n * alpha))| := by
        simp [amoPotential, abs_mul]
    _ ≤ 2 * |lam| * 1 := by
        have : (0:ℝ) ≤ 2 * |lam| := by positivity
        exact mul_le_mul_of_nonneg_left h this
    _ = 2 * |lam| := by ring

/-- The **almost Mathieu operator** `H_{λ,α,θ}` acting on `ℓ²(ℤ)`:
`(H u) n = u (n+1) + u (n-1) + 2 λ cos (2π (θ + n α)) u n`. -/
noncomputable def amo (lam alpha theta : ℝ) : L2Z →L[ℝ] L2Z :=
  shiftOp 1 + shiftOp (-1) +
    mulOp (amoPotential lam alpha theta) (2 * |lam|) (abs_amoPotential_le lam alpha theta)

theorem amo_apply (lam alpha theta : ℝ) (f : L2Z) (n : ℤ) :
    (amo lam alpha theta f : ℤ → ℝ) n =
      (f : ℤ → ℝ) (n + 1) + (f : ℤ → ℝ) (n - 1)
        + 2 * lam * Real.cos (2 * π * (theta + n * alpha)) * (f : ℤ → ℝ) n := by
  simp [amo, amoPotential, sub_eq_add_neg]

/-- Two almost Mathieu operators with the same potential coincide. -/
theorem amo_congr {lam₁ alpha₁ theta₁ lam₂ alpha₂ theta₂ : ℝ}
    (h : ∀ n : ℤ, amoPotential lam₁ alpha₁ theta₁ n = amoPotential lam₂ alpha₂ theta₂ n) :
    amo lam₁ alpha₁ theta₁ = amo lam₂ alpha₂ theta₂ := by
  ext f n
  simp only [amo_apply]
  have := h n
  simp only [amoPotential] at this
  rw [this]

/-- The almost Mathieu operator is bounded by `2 + 2|λ|`. -/
theorem norm_amo_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  have h1 := norm_shiftOp_le 1
  have h2 := norm_shiftOp_le (-1)
  have h3 := norm_mulOp_le (amoPotential lam alpha theta) (2 * |lam|)
    (abs_amoPotential_le lam alpha theta)
  calc ‖amo lam alpha theta‖
      ≤ ‖shiftOp 1 + shiftOp (-1)‖
        + ‖mulOp (amoPotential lam alpha theta) (2 * |lam|)
            (abs_amoPotential_le lam alpha theta)‖ := norm_add_le _ _
    _ ≤ (‖shiftOp (1 : ℤ)‖ + ‖shiftOp (-1 : ℤ)‖)
        + ‖mulOp (amoPotential lam alpha theta) (2 * |lam|)
            (abs_amoPotential_le lam alpha theta)‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (1 + 1) + 2 * |lam| := by gcongr
    _ = 2 + 2 * |lam| := by ring

/-- The spectrum of the almost Mathieu operator with coupling `λ`, flux `α` and phase `θ`. -/
noncomputable def amoSpectrum (lam alpha theta : ℝ) : Set ℝ := spectrum ℝ (amo lam alpha theta)

theorem isCompact_amoSpectrum (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) :=
  spectrum.isCompact _

theorem amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  have hne : Nontrivial L2Z := by
    refine ⟨⟨lp.single 2 (0 : ℤ) (1 : ℝ), 0, ?_⟩⟩
    intro h
    have := congrFun (congrArg (fun u : L2Z => (u : ℤ → ℝ)) h) 0
    simp [lp.single_apply] at this
  intro E hE
  have h1 : E ∈ Metric.closedBall (0 : ℝ) ‖amo lam alpha theta‖ :=
    spectrum.subset_closedBall_norm _ hE
  have h2 : |E| ≤ ‖amo lam alpha theta‖ := by
    simpa [Real.norm_eq_abs] using h1
  have h3 : |E| ≤ 2 + 2 * |lam| := le_trans h2 (norm_amo_le lam alpha theta)
  exact Set.mem_Icc.2 ⟨by linarith [(abs_le.1 h3).1], (abs_le.1 h3).2⟩

/-! ## Cantor sets -/

/-- A *Cantor set* (in the sense of Brouwer's characterization): a nonempty compact
perfect totally disconnected subset of `ℝ`. -/
def IsCantorSet (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsCompact S ∧ Perfect S ∧ IsTotallyDisconnected S

/-- A subset of `ℝ` with empty interior is totally disconnected. -/
theorem totallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts htpre
  have key : ∀ a b : ℝ, a ∈ t → b ∈ t → a < b → False := by
    intro a b ha hb hab
    have hord : t.OrdConnected := htpre.ordConnected
    have hsub : Set.Icc a b ⊆ S := (hord.out ha hb).trans hts
    have : Set.Ioo a b ⊆ interior S := by
      rw [← interior_Icc]
      exact interior_mono hsub
    have hx : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have := this hx
    rw [h] at this
    exact this
  intro x hx y hy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd (key x y hx hy hlt) not_false
  · exact heq
  · exact absurd (key y x hy hx hgt) not_false

/-- A totally disconnected subset of `ℝ` has empty interior. -/
theorem interior_eq_empty_of_totallyDisconnected {S : Set ℝ} (h : IsTotallyDisconnected S) :
    interior S = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hsub : Set.Ioo (x - e) (x + e) ⊆ S := by
    rw [← Real.ball_eq_Ioo]
    exact hball.trans interior_subset
  have hss := h _ hsub isPreconnected_Ioo
  have h1 : x ∈ Set.Ioo (x - e) (x + e) := ⟨by linarith, by linarith⟩
  have h2 : x + e / 2 ∈ Set.Ioo (x - e) (x + e) := ⟨by linarith, by linarith⟩
  have := hss h1 h2
  linarith

/-! ## The Ten Martini Problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya): for every nonzero coupling `λ`,
every irrational flux `α` and every phase `θ`, the spectrum of the almost Mathieu
operator is a Cantor set. -/
def TenMartini : Prop :=
  ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha → IsCantorSet (amoSpectrum lam alpha theta)

/-- A reduced form of the Ten Martini Problem: it suffices to consider positive coupling,
flux in `(0,1)` and phase in `[0,1)`, and to show that the spectrum is nonempty, has empty
interior and has no isolated points. -/
def TenMartiniReduced : Prop :=
  ∀ lam alpha theta : ℝ, 0 < lam → Irrational alpha →
    alpha ∈ Set.Ioo (0 : ℝ) 1 → theta ∈ Set.Ico (0 : ℝ) 1 →
      (amoSpectrum lam alpha theta).Nonempty ∧
      interior (amoSpectrum lam alpha theta) = ∅ ∧
      Preperfect (amoSpectrum lam alpha theta)

/-- The potential (hence the operator) is unchanged when `α` and `θ` are shifted by
integers. -/
theorem amo_int_shift (lam alpha theta : ℝ) (k m : ℤ) :
    amo lam (alpha - k) (theta - m) = amo lam alpha theta := by
  refine amo_congr fun n => ?_
  have hcos : Real.cos (2 * π * (theta - m + n * (alpha - k)))
      = Real.cos (2 * π * (theta + n * alpha)) := by
    have : 2 * π * (theta - m + n * (alpha - k))
        = 2 * π * (theta + n * alpha) - ((m + n * k : ℤ) : ℝ) * (2 * π) := by
      push_cast
      ring
    rw [this, Real.cos_sub_int_mul_two_pi]
  simp [amoPotential, hcos]

/-- Flipping the sign of the coupling amounts to a half-period shift of the phase. -/
theorem amo_neg_lam (lam alpha theta : ℝ) :
    amo (-lam) alpha (theta + 1 / 2) = amo lam alpha theta := by
  refine amo_congr fun n => ?_
  have hcos : Real.cos (2 * π * (theta + 1 / 2 + n * alpha))
      = -Real.cos (2 * π * (theta + n * alpha)) := by
    have : 2 * π * (theta + 1 / 2 + n * alpha) = 2 * π * (theta + n * alpha) + π := by ring
    rw [this, Real.cos_add_pi]
  simp only [amoPotential, hcos]
  ring

/-- Normalization: every almost Mathieu operator with nonzero coupling and irrational flux
equals one with positive coupling, flux in `(0,1)` and phase in `[0,1)`. -/
theorem amo_normalize (lam alpha theta : ℝ) (hlam : lam ≠ 0) (hirr : Irrational alpha) :
    ∃ lam' alpha' theta' : ℝ, 0 < lam' ∧ Irrational alpha' ∧
      alpha' ∈ Set.Ioo (0 : ℝ) 1 ∧ theta' ∈ Set.Ico (0 : ℝ) 1 ∧
      amo lam alpha theta = amo lam' alpha' theta' := by
  -- the normalized flux
  set alpha' : ℝ := Int.fract alpha with halpha'
  have hirr' : Irrational alpha' := by
    rw [halpha', Int.fract]
    exact hirr.sub_intCast _
  have halphaIoo : alpha' ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne (Int.fract_nonneg alpha) ?_, Int.fract_lt_one alpha⟩
    intro h0
    exact hirr' (by rw [← h0]; exact ⟨0, by norm_num⟩)
  -- the base phase, adjusted so that the coupling becomes positive
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · refine ⟨-lam, alpha', Int.fract (theta + 1 / 2), by linarith, hirr', halphaIoo,
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    have h1 : amo lam alpha theta = amo (-lam) alpha (theta + 1 / 2) :=
      (amo_neg_lam lam alpha theta).symm
    have h2 : amo (-lam) (alpha - (⌊alpha⌋ : ℤ)) (theta + 1 / 2 - (⌊theta + 1 / 2⌋ : ℤ))
        = amo (-lam) alpha (theta + 1 / 2) := amo_int_shift _ _ _ _ _
    rw [h1, ← h2]
    rfl
  · refine ⟨lam, alpha', Int.fract theta, hpos, hirr', halphaIoo,
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    have h2 : amo lam (alpha - (⌊alpha⌋ : ℤ)) (theta - (⌊theta⌋ : ℤ)) = amo lam alpha theta :=
      amo_int_shift _ _ _ _ _
    rw [← h2]
    rfl

/-- **Ten Martini, Lean-checked reduction.**

The Ten Martini Problem — the spectrum of the almost Mathieu operator
`(H u) n = u (n+1) + u (n-1) + 2λ cos (2π (θ + n α)) u n` on `ℓ²(ℤ)` is a Cantor set for
every `λ ≠ 0` and every irrational `α` — is *equivalent* to the following, formally weaker
looking statement: for positive coupling `λ`, irrational flux `α ∈ (0,1)` and phase
`θ ∈ [0,1)`, the spectrum is nonempty, has empty interior, and has no isolated points.

The reduction uses: compactness of the spectrum of a bounded operator, the invariance of the
operator under integer shifts of `α` and `θ` and under `(λ, θ) ↦ (-λ, θ + 1/2)`, and the fact
that a subset of `ℝ` is totally disconnected exactly when it has empty interior. -/
theorem avila_ten_martini : TenMartini ↔ TenMartiniReduced := by
  constructor
  · intro h lam alpha theta hlam hirr _ _
    obtain ⟨hne, _, hperf, htd⟩ := h lam alpha theta (ne_of_gt hlam) hirr
    exact ⟨hne, interior_eq_empty_of_totallyDisconnected htd, hperf.acc⟩
  · intro h lam alpha theta hlam hirr
    obtain ⟨lam', alpha', theta', hlam', hirr', hIoo, hIco, heq⟩ :=
      amo_normalize lam alpha theta hlam hirr
    have hspec : amoSpectrum lam alpha theta = amoSpectrum lam' alpha' theta' := by
      simp [amoSpectrum, heq]
    obtain ⟨hne, hint, hacc⟩ := h lam' alpha' theta' hlam' hirr' hIoo hIco
    rw [hspec]
    refine ⟨hne, isCompact_amoSpectrum _ _ _,
      ⟨(isCompact_amoSpectrum _ _ _).isClosed, hacc⟩,
      totallyDisconnected_of_interior_eq_empty hint⟩

/-- A subset of `ℝ` of Lebesgue measure zero has empty interior. -/
theorem interior_eq_empty_of_volume_eq_zero {S : Set ℝ}
    (h : MeasureTheory.volume S = 0) : interior S = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hpos : 0 < MeasureTheory.volume (interior S) :=
    isOpen_interior.measure_pos MeasureTheory.volume ⟨x, hx⟩
  have hle : MeasureTheory.volume (interior S) ≤ MeasureTheory.volume S :=
    MeasureTheory.measure_mono interior_subset
  rw [h] at hle
  exact absurd (le_antisymm hle (zero_le _)) hpos.ne'

/-- A second Lean-checked reduction of the Ten Martini Problem: it suffices to prove, for
positive coupling, irrational flux in `(0,1)` and phase in `[0,1)`, that the spectrum is
nonempty, has Lebesgue measure zero, and has no isolated points. -/
theorem tenMartini_of_measure_zero
    (h : ∀ lam alpha theta : ℝ, 0 < lam → Irrational alpha →
        alpha ∈ Set.Ioo (0 : ℝ) 1 → theta ∈ Set.Ico (0 : ℝ) 1 →
        (amoSpectrum lam alpha theta).Nonempty ∧
        MeasureTheory.volume (amoSpectrum lam alpha theta) = 0 ∧
        Preperfect (amoSpectrum lam alpha theta)) :
    TenMartini := by
  refine avila_ten_martini.2 fun lam alpha theta hlam hirr hIoo hIco => ?_
  obtain ⟨hne, hvol, hacc⟩ := h lam alpha theta hlam hirr hIoo hIco
  exact ⟨hne, interior_eq_empty_of_volume_eq_zero hvol, hacc⟩

end Frontier

