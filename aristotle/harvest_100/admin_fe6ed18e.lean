/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/
noncomputable def ip (v w : n → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (v i) * w i

/-- The outer product `|v⟩⟨v|`. -/
def outer (v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec v (star v)

/-- `P` is an orthogonal projector. -/
structure IsProj (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P

/-- The code with projector `P` is *correctable* for the error set `E` if there is a
recovery quantum channel, given by Kraus operators `R k` with `∑ k, (R k)ᴴ * (R k) = 1`,
whose composition with the error channel `ρ ↦ ∑ i, E i * ρ * (E i)ᴴ` acts as the identity
(up to the trace factor) on every pure state of the code space. -/
def Corrects (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∃ (m : ℕ) (R : Fin m → Matrix n n ℂ),
    (∑ k, (R k)ᴴ * R k = 1) ∧
    ∀ v : n → ℂ, P *ᵥ v = v → ip v v = 1 →
      ∑ k, ∑ i, outer ((R k * E i) *ᵥ v)
        = (∑ i, ip (E i *ᵥ v) (E i *ᵥ v)) • outer v

/-- The Knill–Laflamme conditions. -/
def KLCond (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∃ c : Matrix ι ι ℂ, ∀ i j, P * (E i)ᴴ * E j * P = c i j • P

/-! ## Basic facts about `ip` and `outer` -/

omit [DecidableEq n] in
theorem ip_self_eq (v : n → ℂ) : ip v v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp [ip, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]

omit [DecidableEq n] in
theorem ip_self_nonneg (v : n → ℂ) : 0 ≤ (ip v v).re := by
  rw [ip_self_eq]
  simpa using Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)

omit [DecidableEq n] in
theorem ip_self_im (v : n → ℂ) : (ip v v).im = 0 := by
  rw [ip_self_eq]; simp

omit [DecidableEq n] in
theorem ip_self_eq_zero {v : n → ℂ} (h : ip v v = 0) : v = 0 := by
  rw [ip_self_eq] at h
  have h' : (∑ i, Complex.normSq (v i)) = 0 := by exact_mod_cast h
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (v i))).1 h'
  funext i
  simpa using Complex.normSq_eq_zero.1 (this i (Finset.mem_univ i))

omit [DecidableEq n] in
theorem ip_conj (v w : n → ℂ) : (starRingEnd ℂ) (ip v w) = ip w v := by
  simp [ip, map_sum, mul_comm]

omit [DecidableEq n] in
theorem ip_add_right (u v w : n → ℂ) : ip u (v + w) = ip u v + ip u w := by
  simp [ip, mul_add, Finset.sum_add_distrib]

omit [DecidableEq n] in
theorem ip_add_left (u v w : n → ℂ) : ip (u + v) w = ip u w + ip v w := by
  simp [ip, add_mul, Finset.sum_add_distrib]

omit [DecidableEq n] in
theorem ip_sub_right (u v w : n → ℂ) : ip u (v - w) = ip u v - ip u w := by
  simp [ip, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq n] in
theorem ip_sub_left (u v w : n → ℂ) : ip (u - v) w = ip u w - ip v w := by
  simp [ip, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq n] in
theorem ip_smul_right (c : ℂ) (u v : n → ℂ) : ip u (c • v) = c * ip u v := by
  simp [ip, Finset.mul_sum]; ring_nf
  simp [mul_comm, mul_left_comm]

omit [DecidableEq n] in
theorem ip_smul_left (c : ℂ) (u v : n → ℂ) :
    ip (c • u) v = (starRingEnd ℂ) c * ip u v := by
  simp [ip, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
theorem ip_zero_left (v : n → ℂ) : ip 0 v = 0 := by simp [ip]

omit [DecidableEq n] in
theorem ip_zero_right (v : n → ℂ) : ip v 0 = 0 := by simp [ip]

omit [DecidableEq n] in
theorem ip_sum_right {κ : Type} [Fintype κ] (u : n → ℂ) (f : κ → n → ℂ) :
    ip u (∑ k, f k) = ∑ k, ip u (f k) := by
  simp [ip, Finset.mul_sum, Finset.sum_comm (γ := n)]

omit [DecidableEq n] in
theorem ip_mulVec_right (A : Matrix n n ℂ) (v w : n → ℂ) :
    ip v (A *ᵥ w) = ip (Aᴴ *ᵥ v) w := by
  simp only [ip, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum,
    map_mul, RCLike.star_def, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

omit [DecidableEq n] in
theorem ip_mulVec_left (A : Matrix n n ℂ) (v w : n → ℂ) :
    ip (A *ᵥ v) w = ip v (Aᴴ *ᵥ w) := by
  rw [ip_mulVec_right, Matrix.conjTranspose_conjTranspose]

/-- Two matrices agreeing in all "matrix elements" are equal. -/
theorem matrix_ext_ip {A B : Matrix n n ℂ}
    (h : ∀ v w, ip v (A *ᵥ w) = ip v (B *ᵥ w)) : A = B := by
  ext p q
  have := h (Pi.single p 1) (Pi.single q 1)
  simpa [ip, Matrix.mulVec, dotProduct, Pi.single_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq] using this

omit [Fintype n] [DecidableEq n] in
theorem outer_apply (v : n → ℂ) (p q : n) :
    outer v p q = v p * (starRingEnd ℂ) (v q) := rfl

omit [DecidableEq n] in
theorem outer_mulVec (v w : n → ℂ) : (outer v) *ᵥ w = (ip v w) • v := by
  funext p
  simp only [outer, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, ip,
    Pi.star_apply, RCLike.star_def, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

omit [DecidableEq n] in
theorem outer_smul (c : ℂ) (v : n → ℂ) :
    outer (c • v) = (c * (starRingEnd ℂ) c) • outer v := by
  ext p q
  simp [outer, Matrix.vecMulVec_apply]
  ring

/-! ## The forward direction: correctability implies the Knill–Laflamme conditions -/

theorem eq_zero_of_sum_mul_conj_eq_zero {κ : Type} [Fintype κ] {z : κ → ℂ}
    (h : ∑ k, z k * (starRingEnd ℂ) (z k) = 0) (k : κ) : z k = 0 := by
  have h2 : ((∑ k, Complex.normSq (z k) : ℝ) : ℂ) = 0 := by
    push_cast
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => (Complex.mul_conj (z k)).symm
  have h3 : (∑ k, Complex.normSq (z k)) = 0 := by exact_mod_cast h2
  have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg (z k)).1 h3
  exact Complex.normSq_eq_zero.1 (this k (Finset.mem_univ k))

omit [DecidableEq n] in
/-- If a sum of rank-one positive operators `outer (u m)` is proportional to `outer v`
with `v` a unit vector, then every `u m` is a multiple of `v`. -/
theorem eq_smul_of_sum_outer {κ : Type} [Fintype κ] {u : κ → n → ℂ} {v : n → ℂ}
    {C : ℂ} (hv : ip v v = 1) (h : ∑ k, outer (u k) = C • outer v) (k : κ) :
    u k = (ip v (u k)) • v := by
  set c := ip v (u k) with hc
  set w := u k - c • v with hw
  have hvw : ip v w = 0 := by
    rw [hw, ip_sub_right, ip_smul_right, hv, mul_one, ← hc, sub_self]
  have hq := congrArg (fun M : Matrix n n ℂ => ip w (M *ᵥ w)) h
  simp only [Matrix.sum_mulVec, smul_mulVec, outer_mulVec,
    ip_sum_right, ip_smul_right, hvw, zero_mul, mul_zero] at hq
  have hall : ∀ k', ip (u k') w = 0 := by
    intro k'
    refine eq_zero_of_sum_mul_conj_eq_zero (z := fun k' => ip (u k') w) ?_ k'
    rw [← hq]
    exact Finset.sum_congr rfl fun k' _ => by rw [ip_conj]
  have hww : ip w w = 0 := by
    rw [hw, ip_sub_left, ip_smul_left, hvw, mul_zero, sub_zero]
    exact hall k
  have := ip_self_eq_zero hww
  rw [hw] at this
  have : u k - c • v = 0 := this
  linear_combination (norm := module) this

omit [DecidableEq n] in
theorem ip_self_re (v : n → ℂ) : (((ip v v).re : ℝ) : ℂ) = ip v v := by
  apply Complex.ext <;> simp [ip_self_im]

omit [DecidableEq n] in
/-- Every nonzero vector can be rescaled to a unit vector. -/
theorem exists_unit_smul {v : n → ℂ} (hv : v ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ip (r • v) (r • v) = 1 := by
  have hs0 : 0 < (ip v v).re := by
    rcases lt_or_eq_of_le (ip_self_nonneg v) with h | h
    · exact h
    · exact absurd (ip_self_eq_zero (by rw [← ip_self_re v, ← h]; simp)) hv
  refine ⟨((1 / Real.sqrt (ip v v).re : ℝ) : ℂ), ?_, ?_⟩
  · simp only [ne_eq, Complex.ofReal_eq_zero, one_div, inv_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.2 hs0)
  · rw [ip_smul_left, ip_smul_right, ← ip_self_re v]
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    norm_cast
    field_simp
    rw [Real.sq_sqrt hs0.le]

omit [DecidableEq n] in
theorem scalar_of_unit_scalar {T : Matrix n n ℂ} {v : n → ℂ} {r c : ℂ} (hr : r ≠ 0)
    (h : T *ᵥ (r • v) = c • (r • v)) : T *ᵥ v = c • v := by
  rw [mulVec_smul, smul_comm] at h
  exact smul_right_injective _ hr h

omit [DecidableEq n] in
/-- A matrix which acts as a scalar on every unit vector of the code space acts as a
single scalar on the whole code space. -/
theorem scalar_on_code {P : Matrix n n ℂ} {T : Matrix n n ℂ}
    (h : ∀ v : n → ℂ, P *ᵥ v = v → ip v v = 1 → ∃ c : ℂ, T *ᵥ v = c • v) :
    ∃ c : ℂ, ∀ v : n → ℂ, P *ᵥ v = v → T *ᵥ v = c • v := by
  -- a scalar for every nonzero code vector
  have key : ∀ v : n → ℂ, P *ᵥ v = v → v ≠ 0 → ∃ c : ℂ, T *ᵥ v = c • v := by
    intro v hv hv0
    obtain ⟨r, hr, hru⟩ := exists_unit_smul hv0
    obtain ⟨c, hc⟩ := h (r • v) (by rw [mulVec_smul, hv]) hru
    exact ⟨c, scalar_of_unit_scalar hr hc⟩
  by_cases hex : ∃ v : n → ℂ, P *ᵥ v = v ∧ v ≠ 0
  · obtain ⟨v₀, hv₀, hv₀0⟩ := hex
    obtain ⟨c₀, hc₀⟩ := key v₀ hv₀ hv₀0
    refine ⟨c₀, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · simp [hv0]
    obtain ⟨cv, hcv⟩ := key v hv hv0
    by_cases hsum : v + v₀ = 0
    · have : v = (-1 : ℂ) • v₀ := by
        have : v = -v₀ := by linear_combination (norm := module) hsum
        rw [this]; module
      rw [this, mulVec_smul, hc₀, smul_comm]
    · obtain ⟨cw, hcw⟩ := key (v + v₀) (by rw [mulVec_add, hv, hv₀]) hsum
      rw [mulVec_add, hcv, hc₀] at hcw
      -- (cv - cw) • v = (cw - c₀) • v₀
      have hkey : (cv - cw) • v = (cw - c₀) • v₀ := by
        linear_combination (norm := module) hcw
      by_cases hcc : cv = cw
      · rw [hcc, sub_self, zero_smul] at hkey
        have : cw - c₀ = 0 := by
          by_contra hne
          exact hv₀0 (by
            have := congrArg (fun x => (cw - c₀)⁻¹ • x) hkey.symm
            simpa [smul_smul, inv_mul_cancel₀ hne] using this)
        rw [hcv, hcc, sub_eq_zero.1 this]
      · have hne : cv - cw ≠ 0 := sub_ne_zero.2 hcc
        have hvv : v = ((cw - c₀) / (cv - cw)) • v₀ := by
          have := congrArg (fun x => (cv - cw)⁻¹ • x) hkey
          simpa [smul_smul, inv_mul_cancel₀ hne, div_eq_inv_mul] using this
        rw [hvv, mulVec_smul, hc₀, smul_comm]
  · push_neg at hex
    refine ⟨0, fun v hv => ?_⟩
    rw [hex v hv]
    simp

omit [DecidableEq n] in
/-- Matrix elements of a "sandwiched" product. -/
theorem ip_sandwich {P : Matrix n n ℂ} (hP : IsProj P) {A B : Matrix n n ℂ} (v w : n → ℂ) :
    ip v ((P * Aᴴ * B * P) *ᵥ w) = ip (A *ᵥ (P *ᵥ v)) (B *ᵥ (P *ᵥ w)) := by
  simp only [← mulVec_mulVec]
  rw [ip_mulVec_right P, hP.herm, ip_mulVec_right (Aᴴ), Matrix.conjTranspose_conjTranspose]

omit [DecidableEq ι] in
theorem kl_of_corrects {P : Matrix n n ℂ} (hP : IsProj P) {E : ι → Matrix n n ℂ}
    (h : Corrects P E) : KLCond P E := by
  classical
  obtain ⟨m, R, h1, h2⟩ := h
  -- Each `R k * E i` acts as a scalar on the code space.
  have hscal : ∀ (k : Fin m) (i : ι), ∃ c : ℂ, ∀ v : n → ℂ, P *ᵥ v = v →
      (R k * E i) *ᵥ v = c • v := by
    intro k i
    apply scalar_on_code
    intro v hv hn
    have hsum := h2 v hv hn
    rw [← Fintype.sum_prod_type (fun p : Fin m × ι => outer ((R p.1 * E p.2) *ᵥ v))] at hsum
    exact ⟨_, eq_smul_of_sum_outer (u := fun p : Fin m × ι => (R p.1 * E p.2) *ᵥ v)
      hn hsum (k, i)⟩
  choose lam hlam using hscal
  -- inserting the resolution of the identity given by the Kraus operators
  have hins : ∀ a b : n → ℂ, ip a b = ∑ k, ip (R k *ᵥ a) (R k *ᵥ b) := by
    intro a b
    conv_lhs => rw [show b = (∑ k, (R k)ᴴ * R k) *ᵥ b by rw [h1, one_mulVec]]
    rw [Matrix.sum_mulVec, ip_sum_right]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← mulVec_mulVec, ip_mulVec_right, conjTranspose_conjTranspose]
  refine ⟨Matrix.of fun i j => ∑ k, (starRingEnd ℂ) (lam k i) * lam k j, ?_⟩
  intro i j
  apply matrix_ext_ip
  intro v w
  have hPx : P *ᵥ (P *ᵥ w) = P *ᵥ w := by rw [mulVec_mulVec, hP.idem]
  have hPy : P *ᵥ (P *ᵥ v) = P *ᵥ v := by rw [mulVec_mulVec, hP.idem]
  have hyx : ip (P *ᵥ v) (P *ᵥ w) = ip v (P *ᵥ w) := by
    rw [ip_mulVec_left, hP.herm, hPx]
  rw [ip_sandwich hP, hins]
  have hterm : ∀ k : Fin m, ip (R k *ᵥ (E i *ᵥ (P *ᵥ v))) (R k *ᵥ (E j *ᵥ (P *ᵥ w)))
      = (starRingEnd ℂ) (lam k i) * lam k j * ip v (P *ᵥ w) := by
    intro k
    rw [mulVec_mulVec (P *ᵥ v) (R k) (E i), mulVec_mulVec (P *ᵥ w) (R k) (E j),
      hlam k i _ hPy, hlam k j _ hPx,
      ip_smul_left, ip_smul_right, hyx]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_mul]
  simp [Matrix.of_apply, smul_mulVec, ip_smul_right]

/-! ## The converse: the Knill–Laflamme conditions imply correctability -/

omit [DecidableEq ι] in
/-- Convenience constructor for `Corrects` allowing an arbitrary finite index type. -/
theorem corrects_of {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {κ : Type} [Fintype κ]
    (R : κ → Matrix n n ℂ) (h1 : ∑ k, (R k)ᴴ * R k = 1)
    (h2 : ∀ v : n → ℂ, P *ᵥ v = v → ip v v = 1 →
      ∑ k, ∑ i, outer ((R k * E i) *ᵥ v)
        = (∑ i, ip (E i *ᵥ v) (E i *ᵥ v)) • outer v) : Corrects P E := by
  classical
  refine ⟨Fintype.card κ, fun k => R ((Fintype.equivFin κ).symm k), ?_, ?_⟩
  · rw [Equiv.sum_comp (Fintype.equivFin κ).symm (fun k => (R k)ᴴ * R k)]; exact h1
  · intro v hv hn
    rw [Equiv.sum_comp (Fintype.equivFin κ).symm
      (fun k => ∑ i, outer ((R k * E i) *ᵥ v))]
    exact h2 v hv hn

omit [DecidableEq n] in
theorem ip_self_trace (v : n → ℂ) : ip v v = Matrix.trace (outer v) := by
  simp [ip, Matrix.trace, outer, Matrix.vecMulVec_apply, Matrix.diag, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- Kraus operators may be mixed by a unitary matrix without changing the channel. -/
theorem sum_outer_unitary {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (g : ι → n → ℂ) :
    ∑ a, outer (∑ i, U i a • g i) = ∑ i, outer (g i) := by
  have hd : ∀ i j, ∑ a, U i a * (starRingEnd ℂ) (U j a) = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun hU i) j
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      eq_comm] using h
  ext p q
  simp only [Matrix.sum_apply, outer, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  have step : ∀ a : ι, (∑ i, U i a * g i p) * (∑ j, (starRingEnd ℂ) (U j a) *
      (starRingEnd ℂ) (g j q))
      = ∑ i, ∑ j, (U i a * (starRingEnd ℂ) (U j a)) * (g i p * (starRingEnd ℂ) (g j q)) := by
    intro a
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ j : ι, ∑ a, (U i a * (starRingEnd ℂ) (U j a)) *
      (g i p * (starRingEnd ℂ) (g j q))
      = (if i = j then 1 else 0) * (g i p * (starRingEnd ℂ) (g j q)) := by
    intro j; rw [← Finset.sum_mul, hd i j]
  rw [Finset.sum_congr rfl fun j _ => this j]
  simp

omit [DecidableEq n] in
theorem sum_ip_unitary {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (g : ι → n → ℂ) :
    ∑ a, ip (∑ i, U i a • g i) (∑ i, U i a • g i) = ∑ i, ip (g i) (g i) := by
  simp only [ip_self_trace, ← Matrix.trace_sum, sum_outer_unitary hU]

omit [DecidableEq ι] in
theorem mul_mixed_mulVec {A : Matrix n n ℂ} {E F : ι → Matrix n n ℂ} {U : Matrix ι ι ℂ}
    (hF : ∀ a, F a = ∑ i, U i a • E i) (v : n → ℂ) (a : ι) :
    (A * F a) *ᵥ v = ∑ i, U i a • ((A * E i) *ᵥ v) := by
  rw [hF a, Finset.mul_sum]
  simp [Matrix.sum_mulVec, smul_mulVec]

/-- Mixing the error operators by a unitary matrix does not change correctability. -/
theorem corrects_of_unitary_change {P : Matrix n n ℂ} {E F : ι → Matrix n n ℂ}
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (hF : ∀ a, F a = ∑ i, U i a • E i)
    (h : Corrects P F) : Corrects P E := by
  obtain ⟨m, R, h1, h2⟩ := h
  refine ⟨m, R, h1, fun v hv hn => ?_⟩
  have h3 := h2 v hv hn
  rw [Finset.sum_congr rfl fun k _ =>
      (Finset.sum_congr rfl fun a _ => congrArg outer (mul_mixed_mulVec hF v a) :
        ∑ a, outer ((R k * F a) *ᵥ v) = ∑ a, outer (∑ i, U i a • ((R k * E i) *ᵥ v))),
    Finset.sum_congr rfl fun k _ => sum_outer_unitary hU (fun i => (R k * E i) *ᵥ v)] at h3
  rw [h3]
  congr 1
  have hE1 : ∀ a, F a *ᵥ v = ∑ i, U i a • (E i *ᵥ v) := by
    intro a
    have hone := mul_mixed_mulVec (A := (1 : Matrix n n ℂ)) hF v a
    simpa using hone
  rw [Finset.sum_congr rfl fun a _ => congrArg (fun x => ip x x) (hE1 a),
    sum_ip_unitary hU (fun i => E i *ᵥ v)]

omit [Fintype n] [DecidableEq n] in
theorem outer_zero : outer (0 : n → ℂ) = 0 := by
  ext p q; simp [outer, Matrix.vecMulVec_apply]

/-- The Knill–Laflamme recovery construction, in the case where the error operators have
already been orthogonalised, i.e. `P * (F a)ᴴ * F b * P = δ a b * d a • P`. -/
theorem corrects_of_diag {P : Matrix n n ℂ} (hP : IsProj P) {F : ι → Matrix n n ℂ}
    {d : ι → ℝ} (hd : ∀ a, 0 ≤ d a)
    (hF : ∀ a b, P * (F a)ᴴ * F b * P = (if a = b then ((d a : ℝ) : ℂ) else 0) • P) :
    Corrects P F := by
  classical
  set Q : ι → Matrix n n ℂ :=
    fun a => ((1 / d a : ℝ) : ℂ) • (F a * P * (F a)ᴴ) with hQdef
  set Rk : ι ⊕ Unit → Matrix n n ℂ :=
    Sum.elim (fun a => ((1 / Real.sqrt (d a) : ℝ) : ℂ) • (P * (F a)ᴴ))
      (fun _ => 1 - ∑ a, Q a) with hRdef
  -- `Q a` is a family of mutually orthogonal projectors
  have hQherm : ∀ a, (Q a)ᴴ = Q a := by
    intro a
    simp only [hQdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP.herm, RCLike.star_def, Complex.conj_ofReal,
      mul_assoc]
  have hQmul : ∀ a b, Q a * Q b = if a = b then Q a else 0 := by
    intro a b
    have hmid : F a * P * (F a)ᴴ * (F b * P * (F b)ᴴ)
        = F a * (P * (F a)ᴴ * F b * P) * (F b)ᴴ := by simp only [mul_assoc]
    have expand : Q a * Q b
        = (((1 / d a : ℝ) : ℂ) * ((1 / d b : ℝ) : ℂ) *
            (if a = b then ((d a : ℝ) : ℂ) else 0)) • (F a * P * (F b)ᴴ) := by
      simp only [hQdef]
      rw [smul_mul, Matrix.mul_smul, smul_smul, hmid, hF a b, Matrix.mul_smul, smul_mul,
        smul_smul]
    rw [expand]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
      simp only [hQdef]
      congr 1
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      norm_cast
      rcases eq_or_ne (d a) 0 with h0 | h0
      · simp [h0]
      · field_simp
    · rw [if_neg hab, if_neg hab]
      simp
  have hQsq : (∑ a, Q a) * (∑ a, Q a) = ∑ a, Q a := by
    calc (∑ a, Q a) * (∑ b, Q b) = ∑ a, ∑ b, Q a * Q b := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
      _ = ∑ a, Q a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_congr rfl fun b _ => hQmul a b]
          simp
  have hQsumherm : (∑ a, Q a)ᴴ = ∑ a, Q a := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun a _ => hQherm a
  -- the recovery operators form a channel
  have hsum : ∑ k, (Rk k)ᴴ * Rk k = 1 := by
    have h1 : ∀ a, (Rk (Sum.inl a))ᴴ * Rk (Sum.inl a) = Q a := by
      intro a
      have hpp : (F a * P) * (P * (F a)ᴴ) = F a * P * (F a)ᴴ := by
        rw [← mul_assoc, mul_assoc (F a) P P, hP.idem]
      simp only [hRdef, Sum.elim_inl, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hP.herm, RCLike.star_def, Complex.conj_ofReal,
        smul_mul, Matrix.mul_smul, smul_smul, hpp, hQdef]
      congr 1
      rw [← Complex.ofReal_mul]
      norm_cast
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (hd a)]
    have h2 : (Rk (Sum.inr ()))ᴴ * Rk (Sum.inr ()) = 1 - ∑ a, Q a := by
      have hexp : ((1 : Matrix n n ℂ) - ∑ a, Q a) * (1 - ∑ a, Q a)
          = 1 - (∑ a, Q a) - (∑ a, Q a) + (∑ a, Q a) * (∑ a, Q a) := by
        noncomm_ring
      simp only [hRdef, Sum.elim_inr, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        hQsumherm]
      rw [hexp, hQsq]
      abel
    rw [Fintype.sum_sum_type, Finset.sum_congr rfl fun a _ => h1 a]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [h2]
    abel
  refine corrects_of Rk hsum ?_
  intro v hv hn
  have hipd : ∀ b, ip (F b *ᵥ v) (F b *ᵥ v) = ((d b : ℝ) : ℂ) := by
    intro b
    conv_lhs => rw [← hv]
    rw [← ip_sandwich hP, hF b b, if_pos rfl, smul_mulVec, hv, ip_smul_right, hn, mul_one]
  -- action of `P * (F a)ᴴ` on the errored code states
  have hact : ∀ a b : ι, (P * (F a)ᴴ) *ᵥ (F b *ᵥ v)
      = (if a = b then ((d a : ℝ) : ℂ) else 0) • v := by
    intro a b
    have hstep : (P * (F a)ᴴ) *ᵥ (F b *ᵥ v) = (P * (F a)ᴴ * F b * P) *ᵥ v := by
      conv_lhs => rw [← hv]
      rw [mulVec_mulVec, mulVec_mulVec]
    rw [hstep, hF a b, smul_mulVec, hv]
  have hFv0 : ∀ b, d b = 0 → F b *ᵥ v = 0 := fun b hb =>
    ip_self_eq_zero (by rw [hipd b, hb]; simp)
  have hRinl : ∀ a b : ι, (Rk (Sum.inl a) * F b) *ᵥ v
      = (if a = b then ((Real.sqrt (d a) : ℝ) : ℂ) else 0) • v := by
    intro a b
    rw [← mulVec_mulVec]
    simp only [hRdef, Sum.elim_inl, smul_mulVec, hact a b, smul_smul]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
      congr 1
      rw [← Complex.ofReal_mul]
      norm_cast
      rcases eq_or_lt_of_le (hd a) with h0 | h0
      · simp [← h0]
      · field_simp
        rw [Real.sq_sqrt (hd a)]
    · rw [if_neg hab, if_neg hab]
      simp
  have hQsumact : ∀ b : ι, (∑ a, Q a) *ᵥ (F b *ᵥ v) = F b *ᵥ v := by
    intro b
    rw [Matrix.sum_mulVec]
    have hterm : ∀ a, Q a *ᵥ (F b *ᵥ v) = if a = b then F b *ᵥ v else 0 := by
      intro a
      have hexp : Q a *ᵥ (F b *ᵥ v)
          = (((1 / d a : ℝ) : ℂ) * (if a = b then ((d a : ℝ) : ℂ) else 0)) • (F a *ᵥ v) := by
        simp only [hQdef, smul_mulVec, mul_assoc]
        rw [← mulVec_mulVec, hact a b, mulVec_smul, smul_smul]
      rw [hexp]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos rfl]
        rcases eq_or_ne (d a) 0 with h0 | h0
        · rw [h0]
          simp [hFv0 a h0]
        · rw [← Complex.ofReal_mul, show (1 / d a) * d a = 1 from by field_simp]
          simp
      · rw [if_neg hab, if_neg hab]
        simp
    rw [Finset.sum_congr rfl fun a _ => hterm a]
    simp
  have hRinr : ∀ b : ι, (Rk (Sum.inr ()) * F b) *ᵥ v = 0 := by
    intro b
    rw [← mulVec_mulVec]
    simp only [hRdef, Sum.elim_inr, Matrix.sub_mulVec, Matrix.one_mulVec, hQsumact b]
    simp
  -- assemble
  rw [Fintype.sum_sum_type]
  have hleft : ∀ a : ι, ∑ b, outer ((Rk (Sum.inl a) * F b) *ᵥ v)
      = ((d a : ℝ) : ℂ) • outer v := by
    intro a
    rw [Finset.sum_congr rfl fun b _ => congrArg outer (hRinl a b),
      Finset.sum_eq_single a]
    · rw [if_pos rfl, outer_smul]
      congr 1
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hd a)]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), zero_smul, outer_zero]
    · intro hcon
      exact absurd (Finset.mem_univ a) hcon
  rw [Finset.sum_congr rfl fun a _ => hleft a]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_congr rfl fun b _ => congrArg outer (hRinr b)]
  simp only [outer_zero, Finset.sum_const, smul_zero, add_zero]
  rw [Finset.sum_congr rfl fun b _ => hipd b, ← Finset.sum_smul]

omit [DecidableEq n] [DecidableEq ι] in
theorem sandwich_expand (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) (x y : ι → ℂ) :
    P * (∑ i, x i • E i)ᴴ * (∑ j, y j • E j) * P
      = ∑ i, ∑ j, ((starRingEnd ℂ) (x i) * y j) • (P * (E i)ᴴ * E j * P) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, smul_mul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

omit [DecidableEq ι] in
theorem conj_bilin_apply (U c : Matrix ι ι ℂ) (a b : ι) :
    ∑ i, ∑ j, (starRingEnd ℂ) (U i a) * U j b * c i j = (Uᴴ * c * U) a b := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_unit_code_vector {P : Matrix n n ℂ} (hP : IsProj P) (hP0 : P ≠ 0) :
    ∃ u : n → ℂ, P *ᵥ u = u ∧ ip u u = 1 := by
  have hx : ∃ x : n → ℂ, P *ᵥ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hP0 ?_
    ext p q
    have := congrFun (hcon (Pi.single q 1)) p
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  obtain ⟨x, hxne⟩ := hx
  obtain ⟨r, hr, hru⟩ := exists_unit_smul hxne
  exact ⟨r • (P *ᵥ x), by rw [mulVec_smul, mulVec_mulVec, hP.idem], hru⟩

theorem corrects_of_kl {P : Matrix n n ℂ} (hP : IsProj P) {E : ι → Matrix n n ℂ}
    (h : KLCond P E) : Corrects P E := by
  classical
  obtain ⟨c, hc⟩ := h
  by_cases hP0 : P = 0
  · -- the trivial code: there are no unit code vectors, so any channel works
    refine corrects_of (κ := Unit) (fun _ => 1) (by simp) ?_
    intro v hv hn
    rw [hP0, Matrix.zero_mulVec] at hv
    rw [← hv, ip_zero_left] at hn
    exact absurd hn.symm one_ne_zero
  obtain ⟨u, hu, hun⟩ := exists_unit_code_vector hP hP0
  -- the matrix of Knill–Laflamme coefficients is a Gram matrix, hence Hermitian
  have hcu : ∀ i j, c i j = ip (E i *ᵥ u) (E j *ᵥ u) := by
    intro i j
    conv_rhs => rw [← hu]
    rw [← ip_sandwich hP, hc i j, smul_mulVec, hu, ip_smul_right, hun, mul_one]
  have hch : c.IsHermitian := by
    ext i j
    rw [Matrix.conjTranspose_apply, hcu, hcu, RCLike.star_def]
    exact ip_conj _ _
  set U : Matrix ι ι ℂ := (hch.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set d : ι → ℝ := hch.eigenvalues with hddef
  have hUU : U * Uᴴ = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact (Unitary.mem_iff.1 hch.eigenvectorUnitary.2).2
  have hUsU : Uᴴ * U = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact (Unitary.mem_iff.1 hch.eigenvectorUnitary.2).1
  -- diagonalisation of the coefficient matrix
  have hspec : Uᴴ * c * U = Matrix.diagonal (fun a => ((d a : ℝ) : ℂ)) := by
    have hs := hch.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at hs
    have key : Uᴴ * (U * Matrix.diagonal (RCLike.ofReal ∘ hch.eigenvalues) * star U) * U
        = Matrix.diagonal (fun a => ((d a : ℝ) : ℂ)) := by
      rw [← Matrix.star_eq_conjTranspose]
      rw [← Matrix.star_eq_conjTranspose] at hUsU
      simp only [← mul_assoc, hUsU]
      rw [mul_assoc, mul_assoc, hUsU]
      simp [Function.comp_def, hddef]
    rw [← hs] at key
    exact key
  -- the orthogonalised error operators
  set F : ι → Matrix n n ℂ := fun a => ∑ i, U i a • E i with hFdef
  have hFdiag : ∀ a b, P * (F a)ᴴ * F b * P
      = (if a = b then ((d a : ℝ) : ℂ) else 0) • P := by
    intro a b
    have hentry : (∑ i, ∑ j, (starRingEnd ℂ) (U i a) * U j b * c i j)
        = if a = b then ((d a : ℝ) : ℂ) else 0 := by
      rw [conj_bilin_apply, hspec, Matrix.diagonal_apply]
    rw [hFdef]
    simp only
    rw [sandwich_expand P E (fun i => U i a) (fun j => U j b)]
    simp only [hc, smul_smul, ← Finset.sum_smul]
    rw [hentry]
  have hd : ∀ a, 0 ≤ d a := by
    intro a
    have h1 : ((d a : ℝ) : ℂ) = ip (F a *ᵥ u) (F a *ᵥ u) := by
      conv_rhs => rw [← hu]
      rw [← ip_sandwich hP, hFdiag a a, if_pos rfl, smul_mulVec, hu, ip_smul_right, hun,
        mul_one]
    have h2 := ip_self_nonneg (F a *ᵥ u)
    rw [← h1] at h2
    simpa using h2
  exact corrects_of_unitary_change hUU (fun a => rfl) (corrects_of_diag hP hd hFdiag)

/-- **Knill–Laflamme theorem.**  A quantum code with orthogonal projector `P` corrects
the error set `E` if and only if the Knill–Laflamme conditions hold. -/
theorem knill_laflamme {P : Matrix n n ℂ} (hP : IsProj P) (E : ι → Matrix n n ℂ) :
    Corrects P E ↔ KLCond P E :=
  ⟨kl_of_corrects hP, corrects_of_kl hP⟩

/-! ## Sanity checks

These two examples show that neither side of the equivalence is trivially true or
trivially false. -/

/-- The identity error is corrected by every code. -/
example {P : Matrix n n ℂ} (hP : IsProj P) :
    Corrects P (fun _ : Fin 1 => (1 : Matrix n n ℂ)) :=
  (knill_laflamme hP _).2 ⟨1, by
    intro i j
    rw [Subsingleton.elim i j]
    simp [hP.idem]⟩

/-- A code cannot correct an error which collapses one basis state: here the whole space
is used as the code and the error is the projection onto the first basis vector. -/
example : ¬ Corrects (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (fun _ : Fin 1 => Matrix.diagonal ![1, 0]) := by
  intro hcor
  obtain ⟨c, hc⟩ := (knill_laflamme ⟨by simp, by simp⟩ _).1 hcor
  have h := hc 0 0
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply] at h00 h11
  exact one_ne_zero (h00.trans h11.symm)

end QI

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

