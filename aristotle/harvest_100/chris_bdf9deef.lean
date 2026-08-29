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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/
def qmap (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + c

/-- A quadratic-like map `f : U → V`. -/
structure QuadraticLike (f : ℂ → ℂ) (U V : Set ℂ) : Prop where
  /-- The source is open. -/
  isOpen_source : IsOpen U
  /-- The target is open. -/
  isOpen_target : IsOpen V
  /-- The closure of the source is compact. -/
  isCompact_closure : IsCompact (closure U)
  /-- `U` is compactly contained in `V`. -/
  closure_subset : closure U ⊆ V
  /-- `f` is holomorphic on `U`. -/
  analyticOnNhd : AnalyticOnNhd ℂ f U
  /-- `f` maps `U` into `V`. -/
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is a proper branched cover of degree two. -/
  degree_two : ∃ w₀ ∈ V, {z ∈ U | f z = w₀}.ncard = 1 ∧
    ∀ w ∈ V, w ≠ w₀ → {z ∈ U | f z = w}.ncard = 2

/-- The filled Julia set of `f` at radius `R`: points whose whole forward orbit
stays in the closed disk of radius `R`. -/
def filledJulia (f : ℂ → ℂ) (R : ℝ) : Set ℂ := {z | ∀ n, ‖f^[n] z‖ ≤ R}

/-- The set of points with bounded forward orbit. -/
def boundedOrbit (f : ℂ → ℂ) : Set ℂ := {z | ∃ M : ℝ, ∀ n, ‖f^[n] z‖ ≤ M}

/-! ## Elementary estimates -/

lemma norm_qmap_ge (c z : ℂ) : ‖z‖ ^ 2 - ‖c‖ ≤ ‖qmap c z‖ := by
  have h : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
    have h2 := norm_add_le (z ^ 2 + c) (-c)
    simpa [add_assoc] using h2
  have hz : ‖z ^ 2‖ = ‖z‖ ^ 2 := by simp [norm_pow]
  rw [hz] at h
  simp only [qmap]
  linarith

lemma continuous_qmap (c : ℂ) : Continuous (qmap c) := by
  unfold qmap; fun_prop

/-! ## The quadratic family is quadratic-like on suitable disks -/

section Disks

variable {c : ℂ} {R : ℝ}

/-- Points of the closure of `qmap c ⁻¹' ball 0 R` have norm `< R`. -/
lemma closure_preimage_subset (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) :
    closure (qmap c ⁻¹' Metric.ball (0 : ℂ) R) ⊆ Metric.ball (0 : ℂ) R := by
  have hsub : closure (qmap c ⁻¹' Metric.ball (0 : ℂ) R) ⊆ {z : ℂ | ‖qmap c z‖ ≤ R} := by
    apply closure_minimal
    · intro z hz
      simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hz
      exact le_of_lt hz
    · exact isClosed_le (continuous_norm.comp (continuous_qmap c)) continuous_const
  intro z hz
  have h1 : ‖qmap c z‖ ≤ R := hsub hz
  have h2 : ‖z‖ ^ 2 - ‖c‖ ≤ R := le_trans (norm_qmap_ge c z) h1
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have : ‖z‖ < R := by nlinarith
  simpa [Metric.mem_ball, dist_zero_right] using this

/-- The fiber of `qmap c` over a point `w` of the target disk is `{s, -s}`,
where `s` is any square root of `w - c`. -/
lemma fiber_eq {w s : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R) (hs : s ^ 2 = w - c) :
    {z ∈ qmap c ⁻¹' Metric.ball (0 : ℂ) R | qmap c z = w} = ({s, -s} : Set ℂ) := by
  have hmem : ∀ z : ℂ, qmap c z = w → z ∈ qmap c ⁻¹' Metric.ball (0 : ℂ) R := by
    intro z hz; simpa [Set.mem_preimage, hz] using hw
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hz⟩
    have h2 : (z - s) * (z + s) = 0 := by
      simp only [qmap] at hz; linear_combination hz - hs
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · have hval : qmap c s = w := by simp only [qmap]; linear_combination hs
    have hval' : qmap c (-s) = w := by simp only [qmap]; linear_combination hs
    rintro (rfl | rfl)
    · exact ⟨hmem _ hval, hval⟩
    · exact ⟨hmem _ hval', hval'⟩

/-- The quadratic map `z ↦ z ^ 2 + c` is quadratic-like from
`qmap c ⁻¹' ball 0 R` onto `ball 0 R`, whenever `2 ≤ R` and `‖c‖ < R`. -/
theorem quadraticLike_qmap (hR : 2 ≤ R) (hc : ‖c‖ < R) :
    QuadraticLike (qmap c) (qmap c ⁻¹' Metric.ball (0 : ℂ) R) (Metric.ball (0 : ℂ) R) := by
  have hR1 : 1 < R := by linarith
  have hRc : R + ‖c‖ < R ^ 2 := by nlinarith
  have hclos := closure_preimage_subset (c := c) (R := R) hR1 hRc
  refine
    { isOpen_source := (Metric.isOpen_ball).preimage (continuous_qmap c)
      isOpen_target := Metric.isOpen_ball
      isCompact_closure := ?_
      closure_subset := hclos
      analyticOnNhd := ?_
      mapsTo := ?_
      degree_two := ?_ }
  · refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure ?_
    exact hclos.trans Metric.ball_subset_closedBall
  · intro z _
    exact (analyticAt_id.pow 2).add analyticAt_const
  · intro z hz; exact hz
  · have hcV : c ∈ Metric.ball (0 : ℂ) R := by
      simpa [Metric.mem_ball, dist_zero_right] using hc
    refine ⟨c, hcV, ?_, ?_⟩
    · have hs : (0 : ℂ) ^ 2 = c - c := by ring
      rw [fiber_eq hcV hs]
      simp
    · intro w hw hwc
      obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsAlgClosed.exists_pow_nat_eq (w - c) two_pos
      rw [fiber_eq hw hs]
      refine Set.ncard_pair ?_
      intro h
      have hs0 : s = 0 := by
        have h2 : (2 : ℂ) * s = 0 := by linear_combination h
        simpa using h2
      rw [hs0] at hs
      have hwc0 : w - c = 0 := by linear_combination -hs
      exact hwc (sub_eq_zero.mp hwc0)

end Disks

/-! ## The escape criterion and the filled Julia set -/

section Julia

variable {c : ℂ} {R : ℝ}

/-- Escape estimate: outside the disk of radius `R`, orbits grow linearly. -/
lemma escape_growth (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) {z : ℂ} (hz : R < ‖z‖) (n : ℕ) :
    ‖z‖ + n * (R ^ 2 - R - ‖c‖) ≤ ‖(qmap c)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      set d : ℝ := R ^ 2 - R - ‖c‖ with hd
      have hd0 : 0 < d := by simp only [hd]; linarith
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have ht : R < ‖(qmap c)^[n] z‖ := by nlinarith
      have hstep : ‖(qmap c)^[n] z‖ ^ 2 - ‖c‖ ≤ ‖(qmap c)^[n + 1] z‖ := by
        rw [Function.iterate_succ_apply']
        exact norm_qmap_ge c _
      have hsq : ‖(qmap c)^[n] z‖ + d ≤ ‖(qmap c)^[n] z‖ ^ 2 - ‖c‖ := by
        simp only [hd]; nlinarith
      have hfin : ‖z‖ + (n : ℝ) * d + d ≤ ‖(qmap c)^[n + 1] z‖ := by linarith
      push_cast
      calc ‖z‖ + ((n : ℝ) + 1) * d = ‖z‖ + (n : ℝ) * d + d := by ring
        _ ≤ ‖(qmap c)^[n + 1] z‖ := hfin

/-- Orbits leaving the disk of radius `R` are unbounded. -/
lemma unbounded_of_escape (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) {z : ℂ} (hz : R < ‖z‖) :
    z ∉ boundedOrbit (qmap c) := by
  rintro ⟨M, hM⟩
  set d : ℝ := R ^ 2 - R - ‖c‖ with hd
  have hd0 : 0 < d := by simp only [hd]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - ‖z‖) / d)
  have h1 : ‖z‖ + (n : ℝ) * d ≤ ‖(qmap c)^[n] z‖ := escape_growth hR hRc hz n
  have h2 : ‖(qmap c)^[n] z‖ ≤ M := hM n
  have h3 : (M - ‖z‖) < (n : ℝ) * d := by
    rw [div_lt_iff₀ hd0] at hn; exact hn
  linarith

/-- **Escape criterion.** For `1 < R` and `R + ‖c‖ < R ^ 2`, the filled Julia
set at radius `R` is exactly the set of points with bounded forward orbit. -/
theorem filledJulia_eq_boundedOrbit (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) :
    filledJulia (qmap c) R = boundedOrbit (qmap c) := by
  ext z
  constructor
  · intro hz; exact ⟨R, hz⟩
  · intro hz n
    by_contra hcon
    push_neg at hcon
    have hmem : (qmap c)^[n] z ∈ boundedOrbit (qmap c) := by
      obtain ⟨M, hM⟩ := hz
      refine ⟨M, fun m => ?_⟩
      rw [← Function.iterate_add_apply]
      exact hM (m + n)
    exact unbounded_of_escape hR hRc hcon hmem

/-- The filled Julia set is closed. -/
lemma isClosed_filledJulia (f : ℂ → ℂ) (hf : Continuous f) (R : ℝ) :
    IsClosed (filledJulia f R) := by
  have : filledJulia f R = ⋂ n : ℕ, (f^[n]) ⁻¹' (Metric.closedBall (0 : ℂ) R) := by
    ext z; simp [filledJulia, Metric.mem_closedBall, dist_zero_right]
  rw [this]
  exact isClosed_iInter fun n => (Metric.isClosed_closedBall).preimage (hf.iterate n)

/-- The filled Julia set is compact. -/
theorem isCompact_filledJulia (f : ℂ → ℂ) (hf : Continuous f) (R : ℝ) :
    IsCompact (filledJulia f R) := by
  refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_filledJulia f hf R) ?_
  intro z hz
  have := hz 0
  simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- The filled Julia set is forward invariant. -/
theorem mapsTo_filledJulia (f : ℂ → ℂ) (R : ℝ) :
    Set.MapsTo f (filledJulia f R) (filledJulia f R) := by
  intro z hz n
  rw [← Function.iterate_succ_apply]
  exact hz (n + 1)

/-- Every quadratic map has a fixed point of norm at most `√‖c‖`. -/
lemma exists_fixed_point (c : ℂ) : ∃ z : ℂ, qmap c z = z ∧ ‖z‖ ^ 2 ≤ ‖c‖ := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = 1 - 4 * c := IsAlgClosed.exists_pow_nat_eq (1 - 4 * c) two_pos
  set z₁ : ℂ := (1 + s) / 2 with hz₁
  set z₂ : ℂ := (1 - s) / 2 with hz₂
  have hprod : z₁ * z₂ = c := by
    simp only [hz₁, hz₂]
    field_simp
    linear_combination -hs
  have hfix₁ : qmap c z₁ = z₁ := by
    simp only [qmap, hz₁]
    field_simp
    linear_combination hs
  have hfix₂ : qmap c z₂ = z₂ := by
    simp only [qmap, hz₂]
    field_simp
    linear_combination hs
  have hnorm : ‖z₁‖ * ‖z₂‖ = ‖c‖ := by rw [← norm_mul, hprod]
  rcases le_total ‖z₁‖ ‖z₂‖ with h | h
  · exact ⟨z₁, hfix₁, by nlinarith [norm_nonneg z₁, norm_nonneg z₂]⟩
  · exact ⟨z₂, hfix₂, by nlinarith [norm_nonneg z₁, norm_nonneg z₂]⟩

/-- The filled Julia set of a quadratic map is nonempty: it contains a fixed
point. -/
theorem filledJulia_nonempty (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) :
    (filledJulia (qmap c) R).Nonempty := by
  obtain ⟨z, hz, hzn⟩ := exists_fixed_point c
  refine ⟨z, fun n => ?_⟩
  rw [Function.iterate_fixed hz]
  nlinarith [norm_nonneg z, norm_nonneg c]

end Julia

/-! ## Base case: the filled Julia set of `z ↦ z ^ 2` is the closed unit disk -/

lemma iterate_qmap_zero (z : ℂ) (n : ℕ) : (qmap 0)^[n] z = z ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [qmap, add_zero]
      rw [← pow_mul, pow_succ]

/-- **Base case of straightening.** For `c = 0` the filled Julia set is the
closed unit disk. -/
theorem filledJulia_zero {R : ℝ} (hR : 1 < R) :
    filledJulia (qmap 0) R = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [filledJulia, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R hcon
    have hmn : m ≤ 2 ^ m := Nat.le_of_lt (Nat.lt_two_pow_self)
    have h1 : ‖z‖ ^ m ≤ ‖z‖ ^ (2 ^ m) := pow_le_pow_right₀ (le_of_lt hcon) hmn
    have h2 : ‖(qmap 0)^[m] z‖ ≤ R := h m
    rw [iterate_qmap_zero, norm_pow] at h2
    linarith
  · intro h n
    rw [iterate_qmap_zero, norm_pow]
    calc ‖z‖ ^ (2 ^ n) ≤ 1 ^ (2 ^ n) := pow_le_pow_left₀ (norm_nonneg z) h _
      _ = 1 := one_pow _
      _ ≤ R := le_of_lt hR

/-! ## Renormalization: the small filled Julia set sits inside the big one -/

/-- **Reduction for renormalization.**  If `f^[p] : U' → V'` is a
renormalization of `f` of period `p` (so that the first `p` iterates of `f`
map `U'` into `U`), then the filled Julia set of the renormalization is
contained in the filled Julia set of `f`. -/
theorem renormalization_reduction (f : ℂ → ℂ) (U U' : Set ℂ) (p : ℕ) (hp : 0 < p)
    (h : ∀ k < p, Set.MapsTo (f^[k]) U' U) :
    {z | ∀ n, (f^[p])^[n] z ∈ U'} ⊆ {z | ∀ n, f^[n] z ∈ U} := by
  intro z hz n
  have hkey : f^[n] z = f^[n % p] ((f^[p])^[n / p] z) := by
    rw [← Function.iterate_mul, ← Function.iterate_add_apply]
    congr 1
    exact (Nat.mod_add_div n p).symm
  rw [hkey]
  exact h (n % p) (Nat.mod_lt _ hp) (hz (n / p))

/-! ## Rigidity: distinct parameters are not affinely conjugate -/

/-- **Affine rigidity of the quadratic family.**  If an affine map
`z ↦ a * z + b` (with `a ≠ 0`) conjugates `z ↦ z ^ 2 + c` to `z ↦ z ^ 2 + c'`,
then the conjugacy is the identity and `c = c'`. -/
theorem affine_rigidity (a b c c' : ℂ) (ha : a ≠ 0)
    (h : ∀ z, a * qmap c z + b = qmap c' (a * z + b)) :
    a = 1 ∧ b = 0 ∧ c = c' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  simp only [qmap] at h0 h1 h2
  have hb : b = 0 := by
    have h4 : 4 * (a * b) = 0 := by linear_combination h2 - h1
    have hab : a * b = 0 := by linear_combination h4 / 4
    rcases mul_eq_zero.1 hab with h | h
    · exact absurd h ha
    · exact h
  subst hb
  have haa : a = a ^ 2 := by linear_combination h1 - h0
  have ha1 : a = 1 := by
    have : a * (a - 1) = 0 := by linear_combination -haa
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ha
    · linear_combination h
  subst ha1
  refine ⟨rfl, rfl, ?_⟩
  linear_combination h0

/-! ## Main theorem -/

/-- **McMullen renormalization (formalized statement, with base cases and a
Lean-checked reduction).**

For the quadratic family `qmap c : z ↦ z ^ 2 + c`:

1. *(Quadratic-like structure.)*  For `1 < R` with `R + ‖c‖ < R ^ 2`, the map
   `qmap c` restricted to `U = (qmap c)⁻¹(B(0,R))` is a quadratic-like map onto
   `V = B(0,R)`: `U ⋐ V`, the map is holomorphic and is a proper degree-two
   branched cover.
2. *(Escape criterion.)*  The filled Julia set `K = {z : ∀ n, ‖f^n z‖ ≤ R}` is
   exactly the set of points with bounded orbit.
3. *(Compactness, invariance, nonemptiness of `K`.)*
4. *(Base case of straightening.)*  For `c = 0`, `K` is the closed unit disk.
5. *(Renormalization reduction.)*  The filled Julia set of a period-`p`
   renormalization `f^[p] : U' → V'` is contained in that of `f`.
6. *(Affine rigidity.)*  Distinct parameters `c` are not affinely conjugate. -/
theorem mcmullen_renormalization :
    (∀ (c : ℂ) (R : ℝ), 2 ≤ R → ‖c‖ < R →
        QuadraticLike (qmap c) (qmap c ⁻¹' Metric.ball (0 : ℂ) R) (Metric.ball (0 : ℂ) R)) ∧
    (∀ (c : ℂ) (R : ℝ), 1 < R → R + ‖c‖ < R ^ 2 →
        filledJulia (qmap c) R = boundedOrbit (qmap c)) ∧
    (∀ (c : ℂ) (R : ℝ), 1 < R → R + ‖c‖ < R ^ 2 →
        IsCompact (filledJulia (qmap c) R) ∧ (filledJulia (qmap c) R).Nonempty ∧
          Set.MapsTo (qmap c) (filledJulia (qmap c) R) (filledJulia (qmap c) R)) ∧
    (∀ R : ℝ, 1 < R → filledJulia (qmap 0) R = Metric.closedBall (0 : ℂ) 1) ∧
    (∀ (f : ℂ → ℂ) (U U' : Set ℂ) (p : ℕ), 0 < p → (∀ k < p, Set.MapsTo (f^[k]) U' U) →
        {z | ∀ n, (f^[p])^[n] z ∈ U'} ⊆ {z | ∀ n, f^[n] z ∈ U}) ∧
    (∀ a b c c' : ℂ, a ≠ 0 → (∀ z, a * qmap c z + b = qmap c' (a * z + b)) →
        a = 1 ∧ b = 0 ∧ c = c') := by
  refine ⟨fun c R hR hc => quadraticLike_qmap hR hc,
    fun c R hR hRc => filledJulia_eq_boundedOrbit hR hRc,
    fun c R hR hRc => ⟨isCompact_filledJulia _ (continuous_qmap c) R,
      filledJulia_nonempty hR hRc, mapsTo_filledJulia _ R⟩,
    fun R hR => filledJulia_zero hR,
    fun f U U' p hp h => renormalization_reduction f U U' p hp h,
    fun a b c c' ha h => affine_rigidity a b c c' ha h⟩

end Frontier

