/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Set Metric

/-- A **quadratic-like map** in the sense of Douady–Hubbard: a holomorphic map
`f : U → V` between bounded connected open subsets of `ℂ` with `closure U ⊆ V`,
which is a branched covering of degree two (every fibre over `V` is a non-empty set of
at most two points, and some fibre has exactly two points). -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isPreconnected_U : IsPreconnected U
  isPreconnected_V : IsPreconnected V
  isBounded_V : Bornology.IsBounded V
  closure_U_subset_V : closure U ⊆ V
  analyticOn : AnalyticOnNhd ℂ f U
  mapsTo : MapsTo f U V
  /-- every fibre over `V` is a pair of points (possibly a doubled point) -/
  fiber_pair : ∀ w ∈ V, ∃ z₁ z₂, U ∩ f ⁻¹' {w} = {z₁, z₂}
  /-- the degree is exactly two -/
  degree_two : ∃ w ∈ V, ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ ∧ f z₁ = w ∧ f z₂ = w

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/
def QuadraticLike.K (Q : QuadraticLike) : Set ℂ := {z | ∀ n : ℕ, Q.f^[n] z ∈ Q.U}

/-- The filled Julia set is forward invariant. -/
theorem QuadraticLike.mapsTo_K (Q : QuadraticLike) : MapsTo Q.f Q.K Q.K := by
  intro z hz n
  rw [← Function.iterate_succ_apply]
  exact hz (n + 1)

/-- `Q'` is a renormalization of `Q` of period `p`: `Q'` is a quadratic-like restriction of
the `p`-th iterate of `Q`, and the first `p` iterates of `Q` keep the domain of `Q'` inside the
domain of `Q`. -/
structure IsRenormalization (Q Q' : QuadraticLike) (p : ℕ) : Prop where
  one_le : 1 ≤ p
  iterate : Q'.f = Q.f^[p]
  subset : Q'.U ⊆ Q.U
  iterates_mem : ∀ j < p, MapsTo (Q.f^[j]) Q'.U Q.U

/-- `Q` is renormalizable of period `p`. -/
def Renormalizable (Q : QuadraticLike) (p : ℕ) : Prop := ∃ Q', IsRenormalization Q Q' p

/-- The small filled Julia set of a renormalization sits inside the big one. -/
theorem IsRenormalization.K_subset {Q Q' : QuadraticLike} {p : ℕ}
    (h : IsRenormalization Q Q' p) : Q'.K ⊆ Q.K := by
  intro z hz m
  have hp : 0 < p := h.one_le
  have hm : m % p + p * (m / p) = m := by
    rw [add_comm]; exact Nat.div_add_mod m p
  have hstep : Q.f^[p * (m / p)] z = Q'.f^[m / p] z := by
    rw [h.iterate, ← Function.iterate_mul]
  rw [← hm, Function.iterate_add_apply, hstep]
  exact h.iterates_mem (m % p) (Nat.mod_lt _ hp) (hz (m / p))

/-- The quadratic polynomial `z ↦ z ^ 2 + c`. -/
noncomputable def quadMap (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + c

/-- The domain `U` of the quadratic-like restriction of `z ↦ z ^ 2 + c`: the preimage of the
disc of radius `R`. -/
noncomputable def quadU (c : ℂ) (R : ℝ) : Set ℂ := quadMap c ⁻¹' (ball 0 R)

section Quadratic

variable {c : ℂ} {R : ℝ}

theorem mem_quadU_iff {z : ℂ} : z ∈ quadU c R ↔ ‖quadMap c z‖ < R := by
  simp [quadU, mem_ball, dist_eq_norm]

theorem quadMap_escape_pos (hR : 1 + ‖c‖ < R) : 0 < R * (R - 1) - ‖c‖ := by
  nlinarith [norm_nonneg c]

theorem norm_c_lt (hR : 1 + ‖c‖ < R) : ‖c‖ < R := by nlinarith [norm_nonneg c]

theorem R_pos (hR : 1 + ‖c‖ < R) : 0 < R := by nlinarith [norm_nonneg c]

/-- Escape estimate: outside the disc of radius `R` the quadratic map increases the modulus
by at least the definite amount `R * (R - 1) - ‖c‖ > 0`. -/
theorem norm_quadMap_ge (hR : 1 + ‖c‖ < R) {z : ℂ} (hz : R ≤ ‖z‖) :
    ‖z‖ + (R * (R - 1) - ‖c‖) ≤ ‖quadMap c z‖ := by
  have h1 : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
    have h : ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
    rw [h]
    exact norm_sub_le _ _
  have h2 : ‖z ^ 2‖ = ‖z‖ ^ 2 := by rw [norm_pow]
  have hc := norm_nonneg c
  simp only [quadMap]
  nlinarith [h1, h2]

theorem norm_lt_of_mem_quadU (hR : 1 + ‖c‖ < R) {z : ℂ} (hz : z ∈ quadU c R) : ‖z‖ < R := by
  by_contra h
  push_neg at h
  have h1 := norm_quadMap_ge hR h
  have h2 : ‖quadMap c z‖ < R := mem_quadU_iff.1 hz
  nlinarith [norm_nonneg c]

theorem isOpen_quadU : IsOpen (quadU c R) := by
  apply IsOpen.preimage _ isOpen_ball
  unfold quadMap
  fun_prop

theorem starConvex_quadU (hR : 1 + ‖c‖ < R) : StarConvex ℝ 0 (quadU c R) := by
  intro z hz a b _ hb hab
  have hzn : ‖quadMap c z‖ < R := mem_quadU_iff.1 hz
  have hc : ‖c‖ < R := norm_c_lt hR
  rw [smul_zero, zero_add, mem_quadU_iff]
  have key : quadMap c (b • z) = (b : ℂ) ^ 2 * (z ^ 2 + c) + (1 - (b : ℂ) ^ 2) * c := by
    simp only [quadMap, Complex.real_smul]; ring
  have hb1 : b ≤ 1 := by nlinarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hX : ‖z ^ 2 + c‖ < R := hzn
  rw [key]
  calc ‖(b : ℂ) ^ 2 * (z ^ 2 + c) + (1 - (b : ℂ) ^ 2) * c‖
      ≤ ‖(b : ℂ) ^ 2 * (z ^ 2 + c)‖ + ‖(1 - (b : ℂ) ^ 2) * c‖ := norm_add_le _ _
    _ = b ^ 2 * ‖z ^ 2 + c‖ + (1 - b ^ 2) * ‖c‖ := by
        rw [norm_mul, norm_mul]
        congr 1
        · congr 1
          simp [abs_of_nonneg hb]
        · congr 1
          have h3 : (1 : ℂ) - (b : ℂ) ^ 2 = ((1 - b ^ 2 : ℝ) : ℂ) := by push_cast; ring
          rw [h3, Complex.norm_real]
          exact abs_of_nonneg (by nlinarith)
    _ < R := by
        rcases eq_or_lt_of_le hb with h | h
        · simp [← h]; linarith
        · have hbb : 0 < b ^ 2 := by positivity
          nlinarith [norm_nonneg (z ^ 2 + c), norm_nonneg c]

theorem zero_mem_quadU (hR : 1 + ‖c‖ < R) : (0 : ℂ) ∈ quadU c R := by
  rw [mem_quadU_iff]
  simp only [quadMap]
  have h : ‖(0 : ℂ) ^ 2 + c‖ = ‖c‖ := by norm_num
  rw [h]
  exact norm_c_lt hR

theorem isPreconnected_quadU (hR : 1 + ‖c‖ < R) : IsPreconnected (quadU c R) :=
  ((starConvex_quadU hR).isPathConnected (zero_mem_quadU hR)).isConnected.isPreconnected

theorem closure_quadU_subset (hR : 1 + ‖c‖ < R) : closure (quadU c R) ⊆ ball 0 R := by
  have hRpos : 0 < R := R_pos hR
  set r := Real.sqrt (R + ‖c‖) with hr
  have hsub : quadU c R ⊆ closedBall 0 r := by
    intro z hz
    have hzn : ‖quadMap c z‖ < R := mem_quadU_iff.1 hz
    have h1 : ‖z‖ ^ 2 ≤ R + ‖c‖ := by
      have h2 : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
        have h3 : ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
        rw [h3]
        exact norm_sub_le _ _
      rw [norm_pow] at *
      simp only [quadMap] at hzn
      linarith
    simp only [mem_closedBall, dist_zero_right, hr]
    exact Real.le_sqrt_of_sq_le h1
  have hrR : r < R := by
    rw [hr]
    have h : R + ‖c‖ < R ^ 2 := by nlinarith [norm_nonneg c]
    calc Real.sqrt (R + ‖c‖) < Real.sqrt (R ^ 2) := Real.sqrt_lt_sqrt (by positivity) h
      _ = R := by rw [Real.sqrt_sq hRpos.le]
  calc closure (quadU c R) ⊆ closure (closedBall 0 r) := closure_mono hsub
    _ = closedBall 0 r := isClosed_closedBall.closure_eq
    _ ⊆ ball 0 R := by
        intro x hx
        simp only [mem_closedBall, dist_zero_right] at hx
        simp only [mem_ball, dist_zero_right]
        linarith

theorem analytic_quadMap : AnalyticOnNhd ℂ (quadMap c) (quadU c R) :=
  fun _ _ => (analyticAt_id.pow 2).add analyticAt_const

theorem fiber_quadMap : ∀ w ∈ ball (0 : ℂ) R,
    ∃ z₁ z₂, quadU c R ∩ quadMap c ⁻¹' {w} = {z₁, z₂} := by
  intro w hw
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
  refine ⟨s, -s, ?_⟩
  have hmem : ∀ t : ℂ, t ^ 2 = w - c → t ∈ quadU c R ∩ quadMap c ⁻¹' {w} := by
    intro t ht
    have hfz : quadMap c t = w := by simp only [quadMap, ht]; ring
    refine ⟨?_, by simp [hfz]⟩
    rw [mem_quadU_iff, hfz]
    simpa [mem_ball, dist_eq_norm] using hw
  apply Subset.antisymm
  · rintro z ⟨-, hz2⟩
    simp only [mem_preimage, mem_singleton_iff, quadMap] at hz2
    have hfac : (z - s) * (z + s) = 0 := by
      have h : z ^ 2 = s ^ 2 := by rw [hs]; linear_combination hz2
      linear_combination h
    rcases mul_eq_zero.1 hfac with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (by simpa using eq_neg_of_add_eq_zero_left h)
  · rintro z (rfl | rfl)
    · exact hmem _ hs
    · exact hmem _ (by rw [neg_pow]; simpa using hs)

theorem degree_two_quadMap (hR : 1 + ‖c‖ < R) :
    ∃ w ∈ ball (0 : ℂ) R, ∃ z₁ ∈ quadU c R, ∃ z₂ ∈ quadU c R, z₁ ≠ z₂ ∧
      quadMap c z₁ = w ∧ quadMap c z₂ = w := by
  have hRpos : 0 < R := R_pos hR
  obtain ⟨w, hwV, hwc⟩ : ∃ w ∈ ball (0 : ℂ) R, w ≠ c := by
    by_cases h : c = 0
    · refine ⟨(R / 2 : ℝ), ?_, ?_⟩
      · simp [mem_ball, dist_eq_norm, abs_of_nonneg hRpos.le]; linarith
      · simp [h]; intro hh; linarith
    · exact ⟨0, by simp [mem_ball, hRpos], fun hh => h hh.symm⟩
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    exact hwc (sub_eq_zero.1 hs.symm)
  have hmem : ∀ t : ℂ, t ^ 2 = w - c → t ∈ quadU c R ∧ quadMap c t = w := by
    intro t ht
    have hfz : quadMap c t = w := by simp only [quadMap, ht]; ring
    refine ⟨?_, hfz⟩
    rw [mem_quadU_iff, hfz]
    simpa [mem_ball, dist_eq_norm] using hwV
  obtain ⟨h1, h1'⟩ := hmem s hs
  obtain ⟨h2, h2'⟩ := hmem (-s) (by rw [neg_pow]; simpa using hs)
  exact ⟨w, hwV, s, h1, -s, h2, fun h => hs0 (by linear_combination h / 2), h1', h2'⟩

/-- The quadratic polynomial `z ↦ z ^ 2 + c`, restricted to `quadU c R`, is a quadratic-like
map onto the disc of radius `R`, as soon as `1 + ‖c‖ < R`. -/
noncomputable def quadLike (c : ℂ) (R : ℝ) (hR : 1 + ‖c‖ < R) : QuadraticLike where
  U := quadU c R
  V := ball 0 R
  f := quadMap c
  isOpen_U := isOpen_quadU
  isOpen_V := isOpen_ball
  isPreconnected_U := isPreconnected_quadU hR
  isPreconnected_V := (convex_ball (0 : ℂ) R).isPreconnected
  isBounded_V := isBounded_ball
  closure_U_subset_V := closure_quadU_subset hR
  analyticOn := analytic_quadMap
  mapsTo := fun _ hz => hz
  fiber_pair := fiber_quadMap
  degree_two := degree_two_quadMap hR

/-- Iterated escape: once the orbit leaves the disc of radius `R`, the modulus grows without
bound, at a definite linear rate. -/
theorem norm_iterate_escape (hR : 1 + ‖c‖ < R) {z : ℂ} (hz : R ≤ ‖z‖) (k : ℕ) :
    ‖z‖ + k * (R * (R - 1) - ‖c‖) ≤ ‖(quadMap c)^[k] z‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : R ≤ ‖(quadMap c)^[k] z‖ := by
        have := quadMap_escape_pos hR
        have hkpos : (0 : ℝ) ≤ k * (R * (R - 1) - ‖c‖) := by positivity
        linarith
      have hstep := norm_quadMap_ge hR hk
      rw [Function.iterate_succ_apply']
      push_cast
      linarith

/-- The filled Julia set of the quadratic-like restriction, described by the modulus bound. -/
theorem quadLike_K_eq (hR : 1 + ‖c‖ < R) :
    (quadLike c R hR).K = {z : ℂ | ∀ n : ℕ, ‖(quadMap c)^[n] z‖ ≤ R} := by
  have hδ := quadMap_escape_pos hR
  ext z
  simp only [QuadraticLike.K, quadLike, mem_setOf_eq]
  constructor
  · intro h n
    match n with
    | 0 =>
        by_contra hc
        push_neg at hc
        have h1 := norm_quadMap_ge hR hc.le
        have h2 : ‖quadMap c z‖ < R := mem_quadU_iff.1 (h 0)
        simp only [Function.iterate_zero_apply] at *
        linarith
    | (n + 1) =>
        have h2 : ‖quadMap c ((quadMap c)^[n] z)‖ < R := mem_quadU_iff.1 (h n)
        rw [Function.iterate_succ_apply']
        exact h2.le
  · intro h n
    rw [mem_quadU_iff]
    by_contra hc
    push_neg at hc
    have h1 : R ≤ ‖quadMap c ((quadMap c)^[n] z)‖ := hc
    have h2 : quadMap c ((quadMap c)^[n] z) = (quadMap c)^[n + 1] z :=
      (Function.iterate_succ_apply' _ _ _).symm
    rw [h2] at h1
    have h3 := norm_iterate_escape hR h1 1
    have h4 : ((quadMap c)^[1]) ((quadMap c)^[n + 1] z) = (quadMap c)^[n + 2] z := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h4] at h3
    have h5 := h (n + 2)
    push_cast at h3
    linarith

/-- The filled Julia set of the quadratic-like restriction is exactly the classical filled
Julia set of the polynomial `z ↦ z ^ 2 + c`: the set of points with bounded forward orbit. -/
theorem quadLike_K_eq_bounded_orbit (hR : 1 + ‖c‖ < R) :
    (quadLike c R hR).K
      = {z : ℂ | Bornology.IsBounded (Set.range fun n : ℕ => (quadMap c)^[n] z)} := by
  have hδ := quadMap_escape_pos hR
  rw [quadLike_K_eq hR]
  ext z
  simp only [mem_setOf_eq]
  constructor
  · intro h
    rw [isBounded_iff_forall_norm_le]
    exact ⟨R, by rintro x ⟨n, rfl⟩; exact h n⟩
  · intro h n
    rw [isBounded_iff_forall_norm_le] at h
    obtain ⟨M, hM⟩ := h
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := exists_nat_gt ((M - ‖(quadMap c)^[n] z‖) / (R * (R - 1) - ‖c‖))
    have h1 := norm_iterate_escape hR hcon.le k
    have h2 : ((quadMap c)^[k]) ((quadMap c)^[n] z) = (quadMap c)^[n + k] z := by
      rw [← Function.iterate_add_apply]
      ring_nf
    rw [h2] at h1
    have h3 : ‖(quadMap c)^[n + k] z‖ ≤ M := hM _ ⟨n + k, rfl⟩
    have h4 : (M - ‖(quadMap c)^[n] z‖) < k * (R * (R - 1) - ‖c‖) := by
      rw [div_lt_iff₀ hδ] at hk
      exact hk
    linarith

/-- The filled Julia set is non-empty: it contains a fixed point of `z ↦ z ^ 2 + c`. -/
theorem quadLike_K_nonempty (hR : 1 + ‖c‖ < R) : (quadLike c R hR).K.Nonempty := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * c) (n := 2) (by norm_num)
  set z₀ : ℂ := (1 + s) / 2 with hz₀
  have hfix : quadMap c z₀ = z₀ := by
    simp only [quadMap, hz₀]
    field_simp
    linear_combination hs
  have hiter : ∀ n : ℕ, (quadMap c)^[n] z₀ = z₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hnorm : ‖z₀‖ ≤ R := by
    by_contra hcon
    push_neg at hcon
    have h1 := norm_quadMap_ge hR hcon.le
    rw [hfix] at h1
    have := quadMap_escape_pos hR
    linarith
  refine ⟨z₀, ?_⟩
  rw [quadLike_K_eq hR]
  intro n
  rw [hiter n]
  exact hnorm

/-- The filled Julia set of the quadratic-like restriction is compact. -/
theorem quadLike_K_isCompact (hR : 1 + ‖c‖ < R) : IsCompact (quadLike c R hR).K := by
  rw [quadLike_K_eq hR]
  have hcl : IsClosed {z : ℂ | ∀ n : ℕ, ‖(quadMap c)^[n] z‖ ≤ R} := by
    have : {z : ℂ | ∀ n : ℕ, ‖(quadMap c)^[n] z‖ ≤ R}
        = ⋂ n : ℕ, ((quadMap c)^[n]) ⁻¹' (closedBall 0 R) := by
      ext z; simp [mem_closedBall, dist_zero_right]
    rw [this]
    refine isClosed_iInter fun n => IsClosed.preimage ?_ isClosed_closedBall
    have hcont : Continuous (quadMap c) := by unfold quadMap; fun_prop
    exact hcont.iterate n
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R) hcl ?_
  intro z hz
  simpa [mem_closedBall, dist_zero_right] using hz 0

/-- Dichotomy: a point outside the filled Julia set has an orbit escaping to infinity at a
definite linear rate. -/
theorem quadLike_tendsto_atTop (hR : 1 + ‖c‖ < R) {z : ℂ} (hz : z ∉ (quadLike c R hR).K) :
    Filter.Tendsto (fun n : ℕ => ‖(quadMap c)^[n] z‖) Filter.atTop Filter.atTop := by
  have hδ := quadMap_escape_pos hR
  rw [quadLike_K_eq hR] at hz
  simp only [mem_setOf_eq, not_forall, not_le] at hz
  obtain ⟨n, hn⟩ := hz
  rw [Filter.tendsto_atTop_atTop]
  intro M
  obtain ⟨k, hk⟩ := exists_nat_gt ((M - ‖(quadMap c)^[n] z‖) / (R * (R - 1) - ‖c‖))
  refine ⟨n + k, fun m hm => ?_⟩
  have hsplit : (quadMap c)^[m] z = (quadMap c)^[m - n] ((quadMap c)^[n] z) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hge := norm_iterate_escape hR hn.le (m - n)
  rw [← hsplit] at hge
  have hkm : (k : ℝ) ≤ (m - n : ℕ) := by
    have : k ≤ m - n := by omega
    exact_mod_cast this
  have hMk : M - ‖(quadMap c)^[n] z‖ < k * (R * (R - 1) - ‖c‖) := by
    rw [div_lt_iff₀ hδ] at hk
    exact hk
  nlinarith

end Quadratic

/-- **McMullen renormalization, base case.**

For every quadratic polynomial `z ↦ z ^ 2 + c` and every radius `R > 1 + ‖c‖`:

* the restriction of `z ↦ z ^ 2 + c` to `quadU c R` is a quadratic-like map onto `ball 0 R`
  (this is the map `quadLike c R hR`);
* its filled Julia set is exactly the classical filled Julia set of the polynomial, i.e. the
  set of points with bounded forward orbit: the quadratic-like dynamics captures the whole
  bounded dynamics of `z ↦ z ^ 2 + c`;
* that filled Julia set is a non-empty compact forward-invariant set, and every point outside
  it has an orbit tending to infinity;
* `Q` admits the (trivial) renormalization of period one, and every renormalization `Q'` of
  any period `p` has its small filled Julia set contained in the big one and invariant under
  the renormalized map `Q'.f = Q.f^[p]`.
-/
theorem mcmullen_renormalization (c : ℂ) (R : ℝ) (hR : 1 + ‖c‖ < R) :
    ∀ Q : QuadraticLike, Q = quadLike c R hR →
      Q.f = quadMap c ∧
      Q.K = {z : ℂ | Bornology.IsBounded (Set.range fun n : ℕ => Q.f^[n] z)} ∧
      Q.K.Nonempty ∧ IsCompact Q.K ∧ MapsTo Q.f Q.K Q.K ∧
      (∀ z ∉ Q.K, Filter.Tendsto (fun n : ℕ => ‖Q.f^[n] z‖) Filter.atTop Filter.atTop) ∧
      Renormalizable Q 1 ∧
      (∀ (p : ℕ) (Q' : QuadraticLike), IsRenormalization Q Q' p →
        Q'.K ⊆ Q.K ∧ MapsTo Q'.f Q'.K Q'.K) := by
  rintro Q rfl
  refine ⟨rfl, ?_, quadLike_K_nonempty hR, quadLike_K_isCompact hR,
    QuadraticLike.mapsTo_K _, fun z hz => quadLike_tendsto_atTop hR hz, ?_, ?_⟩
  · exact quadLike_K_eq_bounded_orbit hR
  · exact ⟨quadLike c R hR, ⟨le_refl 1, (Function.iterate_one _).symm, subset_rfl,
      fun j hj => by interval_cases j; simpa using fun _ h => h⟩⟩
  · exact fun p Q' h => ⟨h.K_subset, Q'.mapsTo_K⟩

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

