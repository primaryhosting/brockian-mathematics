import Mathlib
/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

namespace QI

open Finset Complex

/-!
## The Shor sampling distribution

We model the period-finding core of Shor's algorithm.  Fix a modulus `N`, a unit
`u : (ZMod N)ˣ` and a power-of-two-sized (any size, really) register `Q`.
The algorithm prepares

  `Q^{-1/2} ∑_{j < Q} |j⟩ |u ^ j⟩`,

applies the quantum Fourier transform modulo `Q` to the first register and
measures.  The probability of observing `c` in the first register and `y` in the
second one is `Q^{-2} ‖∑_{j < Q, u ^ j = y} e^{2πι c j / Q}‖^2`, so the marginal
probability of observing `c` is the following quantity.
-/

/-- Probability that Shor's period-finding circuit, run with modulus `N`, base `u`
and register size `Q`, outputs the value `c`. -/
noncomputable def shorProb (N : ℕ) (u : (ZMod N)ˣ) (Q : ℕ) (c : ℕ) : ℝ :=
  ∑ y ∈ (range Q).image (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N)),
    (1 / (Q : ℝ) ^ 2) *
      ‖∑ j ∈ (range Q).filter (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N) = y),
          Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ ^ 2

/-- The classical post-processing succeeded on the sample `c`: some fraction in
lowest terms with denominator at most `M` approximates `c / Q` to within
`1 / (2 Q)`, and *every* such fraction has denominator exactly `r`.  Thus the
period `r` is unambiguously determined by the measurement outcome `c`. -/
def DeterminesPeriod (Q M r c : ℕ) : Prop :=
  (∃ s : ℕ, Nat.Coprime s r ∧ |(c : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q)) ∧
    (∀ s' r' : ℕ, 0 < r' → r' ≤ M → Nat.Coprime s' r' →
      |(c : ℝ) / Q - (s' : ℝ) / r'| ≤ 1 / (2 * Q) → r' = r)

/-! ### `shorProb` is a probability distribution

The following two lemmas are not needed for the main theorem, but they certify
that `shorProb` really is the distribution of the measurement outcome: it is
nonnegative and its total mass over the `Q` possible outcomes is `1`. -/

lemma shorProb_nonneg (N : ℕ) (u : (ZMod N)ˣ) (Q c : ℕ) : 0 ≤ shorProb N u Q c :=
  Finset.sum_nonneg fun y _ => by positivity

/-- Orthogonality of the characters of `ZMod Q`. -/
lemma sum_exp_orthogonality {Q : ℕ} (hQ : 0 < Q) {j j' : ℕ} (hj : j < Q) (hj' : j' < Q) :
    ∑ c ∈ range Q, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q))
      = if j = j' then (Q : ℂ) else 0 := by
  have hQC : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) - j') / Q) with hx
  have hterm : ∀ c ∈ range Q, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q)) = x ^ c := by
    intro c _
    rw [← Complex.exp_conj, ← Complex.exp_add, hx, ← Complex.exp_nat_mul]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_natCast]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  have hxQ : x ^ Q = 1 := by
    rw [hx, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨(j : ℤ) - j', ?_⟩
    push_cast
    field_simp
  by_cases hjj : j = j'
  · subst hjj
    simp [hx]
  · rw [if_neg hjj]
    have hxne : x ≠ 1 := by
      intro h
      rw [hx, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      field_simp at hn
      have h3 : ((j : ℤ) - j') = (Q : ℤ) * n := by exact_mod_cast hn
      have hdvd : (Q : ℤ) ∣ ((j : ℤ) - j') := ⟨n, h3⟩
      have habs : |((j : ℤ) - j')| < (Q : ℤ) := by
        rw [abs_lt]
        omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      omega
    rw [geom_sum_eq hxne, hxQ]
    simp

/-- Parseval for a single fibre. -/
lemma sum_sq_norm_eq {Q : ℕ} (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ range Q) :
    ∑ c ∈ range Q, ‖∑ j ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ ^ 2
      = (Q : ℝ) * S.card := by
  have hcast : ((∑ c ∈ range Q,
        ‖∑ j ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ ^ 2 : ℝ) : ℂ)
      = ((Q : ℝ) * S.card : ℝ) := by
    push_cast
    have step : ∀ c ∈ range Q,
        (((‖∑ j ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ : ℝ) : ℂ)) ^ 2
        = ∑ j ∈ S, ∑ j' ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
            (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q)) := by
      intro c _
      rw [← Complex.ofReal_pow, Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    have h2 : ∀ j ∈ S, (∑ c ∈ range Q, ∑ j' ∈ S,
        Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
          (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q))) = (Q : ℂ) := by
      intro j hj
      rw [Finset.sum_comm]
      have h3 : ∀ j' ∈ S, (∑ c ∈ range Q,
          Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
            (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q)))
          = if j = j' then (Q : ℂ) else 0 :=
        fun j' hj' => sum_exp_orthogonality hQ (mem_range.mp (hS hj)) (mem_range.mp (hS hj'))
      rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq S j (fun _ => (Q : ℂ))]
      simp [hj]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
    ring
  exact_mod_cast hcast

/-- The Shor measurement outcome distribution has total mass one. -/
lemma shorProb_sum_eq_one {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) {Q : ℕ} (hQ : 0 < Q) :
    ∑ c ∈ range Q, shorProb N u Q c = 1 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  simp only [shorProb]
  rw [Finset.sum_comm]
  have h1 : ∀ y ∈ (range Q).image (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N)),
      (∑ c ∈ range Q, (1 / (Q : ℝ) ^ 2) *
        ‖∑ j ∈ (range Q).filter (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N) = y),
          Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ ^ 2)
      = (1 / (Q : ℝ)) * ((range Q).filter (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N) = y)).card := by
    intro y _
    rw [← Finset.mul_sum, sum_sq_norm_eq hQ _ (Finset.filter_subset _ _)]
    field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hcard : ∑ y ∈ (range Q).image (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N)),
      (((range Q).filter (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N) = y)).card : ℝ) = Q := by
    rw [← Nat.cast_sum, ← card_eq_sum_card_image, Finset.card_range]
  rw [hcard]
  field_simp

/-- Number of `j < Q` with `j ≡ k [MOD r]`, i.e. `⌈(Q - k) / r⌉`. -/
def blockCount (Q r k : ℕ) : ℕ := (Q - k + r - 1) / r

/-! ### Elementary facts about `blockCount` -/

lemma lt_blockCount_iff {Q r k t : ℕ} (hr : 0 < r) (hk : k < Q) :
    t < blockCount Q r k ↔ k + t * r < Q := by
  rw [blockCount, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hr, Nat.succ_mul]
  omega

lemma blockCount_mul_le {Q r k : ℕ} (hr : 0 < r) : blockCount Q r k * r + 1 ≤ Q + r := by
  have := Nat.div_mul_le_self (Q - k + r - 1) r
  simp only [blockCount]
  omega

lemma add_mul_injective {r : ℕ} (hr : 0 < r) (k : ℕ) : Function.Injective (fun t => k + t * r) := by
  intro a b hab
  dsimp only at hab
  exact Nat.eq_of_mul_eq_mul_right hr (Nat.add_left_cancel hab)

lemma fiberNat_eq {Q r k : ℕ} (hr : 0 < r) (hk : k < Q) (hkr : k < r) :
    (range Q).filter (fun j => j % r = k) = (range (blockCount Q r k)).image (fun t => k + t * r) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  have hq : j / r * r + j % r = j := Nat.div_add_mod' j r
  constructor
  · rintro ⟨hjQ, hj⟩
    refine ⟨j / r, ?_, by omega⟩
    rw [lt_blockCount_iff hr hk]
    omega
  · rintro ⟨t, ht, rfl⟩
    rw [lt_blockCount_iff hr hk] at ht
    exact ⟨ht, by simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hkr]⟩

lemma sum_blockCount {Q r : ℕ} (hr : 0 < r) (hrQ : r ≤ Q) :
    ∑ k ∈ range r, blockCount Q r k = Q := by
  have h : (range Q).card = ∑ k ∈ range r, ((range Q).filter (fun j => j % r = k)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x _
    simp [Nat.mod_lt _ hr]
  have h2 : ∑ k ∈ range r, blockCount Q r k
      = ∑ k ∈ range r, ((range Q).filter (fun j => j % r = k)).card := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [fiberNat_eq hr (lt_of_lt_of_le hk hrQ) hk,
      Finset.card_image_of_injective _ (add_mul_injective hr k), Finset.card_range]
  rw [h2, ← h, Finset.card_range]

/-! ### A lower bound for a truncated geometric sum of phases -/

lemma sum_range_cast_sq (A : ℕ) :
    ∑ t ∈ range A, ((t : ℝ)) ^ 2 = (A : ℝ) * ((A : ℝ) - 1) * (2 * (A : ℝ) - 1) / 6 := by
  induction A with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_range_cast (A : ℕ) : ∑ t ∈ range A, ((t : ℝ)) = (A : ℝ) * ((A : ℝ) - 1) / 2 := by
  induction A with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_centered_sq (A : ℕ) :
    ∑ t ∈ range A, ((t : ℝ) - ((A : ℝ) - 1) / 2) ^ 2 = (A : ℝ) * ((A : ℝ) ^ 2 - 1) / 12 := by
  have h : ∀ t : ℕ, ((t : ℝ) - ((A : ℝ) - 1) / 2) ^ 2
      = (t : ℝ) ^ 2 - ((A : ℝ) - 1) * t + (((A : ℝ) - 1) / 2) ^ 2 := by
    intro t; ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, sum_range_cast_sq, sum_range_cast]
  ring

/-- Lower bound for the modulus of a truncated geometric series of phases:
`‖∑_{t<A} e^{ιθt}‖ ≥ A (1 - θ²(A²-1)/24)`. -/
lemma norm_sum_exp_lower (θ : ℝ) (A : ℕ) :
    (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24) ≤
      ‖∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I)‖ := by
  have hw : ‖Complex.exp ((-(θ * (((A : ℝ) - 1) / 2)) : ℝ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  have key : Complex.exp ((-(θ * (((A : ℝ) - 1) / 2)) : ℝ) * Complex.I) *
        (∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I))
      = ∑ t ∈ range A, Complex.exp ((θ * ((t : ℝ) - ((A : ℝ) - 1) / 2) : ℝ) * Complex.I) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsum : ∑ t ∈ range A, (1 - (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) ^ 2 / 2)
      = (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24) := by
    have h1 : (∑ t ∈ range A, (1 - (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) ^ 2 / 2))
        = (∑ _t ∈ range A, (1 : ℝ))
          - θ ^ 2 / 2 * ∑ t ∈ range A, ((t : ℝ) - ((A : ℝ) - 1) / 2) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [h1, sum_centered_sq]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  calc (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24)
      = ∑ t ∈ range A, (1 - (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) ^ 2 / 2) := hsum.symm
    _ ≤ ∑ t ∈ range A, Real.cos (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) :=
        Finset.sum_le_sum fun t _ => Real.one_sub_sq_div_two_le_cos
    _ = (∑ t ∈ range A, Complex.exp ((θ * ((t : ℝ) - ((A : ℝ) - 1) / 2) : ℝ) * Complex.I)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun t _ => (Complex.exp_ofReal_mul_I_re _).symm
    _ ≤ ‖∑ t ∈ range A, Complex.exp ((θ * ((t : ℝ) - ((A : ℝ) - 1) / 2) : ℝ) * Complex.I)‖ :=
        Complex.re_le_norm _
    _ = ‖Complex.exp ((-(θ * (((A : ℝ) - 1) / 2)) : ℝ) * Complex.I) *
          (∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I))‖ := by rw [key]
    _ = ‖∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I)‖ := by rw [norm_mul, hw, one_mul]

/-! ### Rewriting the Shor distribution as a sum over residue classes -/

lemma shorProb_eq {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) {Q : ℕ} (hrQ : orderOf u ≤ Q) (c : ℕ) :
    shorProb N u Q c =
      (1 / (Q : ℝ) ^ 2) * ∑ k ∈ range (orderOf u),
        ‖∑ t ∈ range (blockCount Q (orderOf u) k),
            Complex.exp (2 * Real.pi * Complex.I * (c * (orderOf u * t)) / Q)‖ ^ 2 := by
  set r := orderOf u with hrdef
  have hr : 0 < r := orderOf_pos u
  have hfib : ∀ j k : ℕ, k < r →
      (((u ^ j : (ZMod N)ˣ) : ZMod N) = ((u ^ k : (ZMod N)ˣ) : ZMod N) ↔ j % r = k) := by
    intro j k hk
    rw [Units.val_inj, pow_eq_pow_iff_modEq, Nat.ModEq, Nat.mod_eq_of_lt hk]
  have hinjOn : Set.InjOn (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N))
      ((range r : Finset ℕ) : Set ℕ) := by
    intro k hk k' hk' h
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    rw [hfib k k' hk', Nat.mod_eq_of_lt hk] at h
    exact h
  have himg : (range Q).image (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N))
      = (range r).image (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N)) := by
    apply Finset.Subset.antisymm
    · intro y hy
      simp only [Finset.mem_image, Finset.mem_range] at hy ⊢
      obtain ⟨j, hj, rfl⟩ := hy
      exact ⟨j % r, Nat.mod_lt _ hr, ((hfib j (j % r) (Nat.mod_lt _ hr)).mpr rfl).symm⟩
    · refine Finset.image_subset_image ?_
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
  rw [shorProb, himg, Finset.sum_image hinjOn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hfilter : (range Q).filter
        (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N) = ((u ^ k : (ZMod N)ˣ) : ZMod N))
      = (range (blockCount Q r k)).image (fun t => k + t * r) := by
    rw [← fiberNat_eq hr (lt_of_lt_of_le hk hrQ) hk]
    exact Finset.filter_congr fun j _ => by simpa using hfib j k hk
  rw [hfilter, Finset.sum_image ((add_mul_injective hr k).injOn)]
  congr 1
  have hfactor : (∑ t ∈ range (blockCount Q r k),
        Complex.exp (2 * Real.pi * Complex.I * (c * ((k + t * r : ℕ) : ℂ)) / Q))
      = Complex.exp (((2 * Real.pi * (c * k) / Q : ℝ) : ℂ) * Complex.I) *
        ∑ t ∈ range (blockCount Q r k),
          Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-! ### The probability of a good sample -/

/-- The phase `θ = 2πd/Q` accumulated over a whole block stays below `6π/5`. -/
lemma theta_sq_bound {Q r A : ℕ} {d : ℤ} (hr : 0 < r) (hQ : r ^ 2 < Q) (hQ0 : 0 < Q)
    (hd : 2 * |d| ≤ (r : ℤ)) (hA : A * r + 1 ≤ Q + r) :
    (2 * Real.pi * (d : ℝ) / Q) ^ 2 * (A : ℝ) ^ 2 ≤ 14.4 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hAR : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hQ' : r * r < Q := by nlinarith
  have h5 : 5 * r ≤ Q + 5 := by
    rcases Nat.lt_or_ge r 4 with h | h
    · interval_cases r <;> omega
    · nlinarith
  have h5R : 5 * (r : ℝ) ≤ (Q : ℝ) + 5 := by exact_mod_cast h5
  have hAR' : (A : ℝ) * r ≤ (Q : ℝ) + r - 1 := by
    have h : ((A * r + 1 : ℕ) : ℝ) ≤ ((Q + r : ℕ) : ℝ) := by exact_mod_cast hA
    push_cast at h
    linarith
  have hX : (A : ℝ) * r ≤ (6 / 5) * Q := by linarith
  have hdR : 4 * (d : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by
    have h1 : |(d : ℝ)| * 2 ≤ (r : ℝ) := by
      have h : ((2 * |d| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by exact_mod_cast hd
      push_cast at h
      linarith
    nlinarith [abs_nonneg (d : ℝ), sq_abs (d : ℝ)]
  have hpi : Real.pi ^ 2 ≤ 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have key : (2 * Real.pi * (d : ℝ) / Q) ^ 2 * (A : ℝ) ^ 2
      = Real.pi ^ 2 * (4 * (d : ℝ) ^ 2 * (A : ℝ) ^ 2) / (Q : ℝ) ^ 2 := by
    field_simp
    ring
  rw [key, div_le_iff₀ (by positivity)]
  have step2 : 4 * (d : ℝ) ^ 2 * (A : ℝ) ^ 2 ≤ ((r : ℝ) * A) ^ 2 := by nlinarith [sq_nonneg (A : ℝ)]
  have step3 : ((r : ℝ) * A) ^ 2 ≤ ((6 / 5) * Q) ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hrR) hAR]
  nlinarith [step2, step3, hpi, sq_nonneg ((Q : ℝ))]

/-- If `c / Q` is within `1 / (2Q)` of `s / r`, then `c` is observed with
probability at least `1 / (8 r)`. -/
lemma prob_lower {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) {Q : ℕ} (hQ : (orderOf u) ^ 2 < Q)
    (c : ℕ) (s : ℤ) (hd : 2 * |(c : ℤ) * orderOf u - s * Q| ≤ orderOf u) :
    1 / (8 * (orderOf u : ℝ)) ≤ shorProb N u Q c := by
  set r := orderOf u with hrdef
  have hr : 0 < r := orderOf_pos u
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hrQ : r ≤ Q := le_trans hrr hQ.le
  have hQ0 : 0 < Q := lt_of_lt_of_le hr hrQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set d : ℤ := (c : ℤ) * r - s * Q with hddef
  set θ : ℝ := 2 * Real.pi * (d : ℝ) / Q with hθ
  have hexp : ∀ t : ℕ, Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)
      = Complex.exp ((θ * t : ℝ) * Complex.I) := by
    intro t
    have hc : (2 * (Real.pi : ℂ) * Complex.I * ((c : ℂ) * ((r : ℂ) * (t : ℂ))) / Q)
        = ((θ * t : ℝ) : ℂ) * Complex.I + ((s * t : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
      rw [hθ, hddef]
      push_cast
      field_simp
      ring
    rw [hc, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hkey : ∀ k ∈ range r, (4 / 25 : ℝ) * (blockCount Q r k : ℝ) ^ 2
      ≤ ‖∑ t ∈ range (blockCount Q r k),
            Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)‖ ^ 2 := by
    intro k _
    set A := blockCount Q r k with hA
    have hsimp : (∑ t ∈ range A, Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q))
        = ∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I) :=
      Finset.sum_congr rfl fun t _ => hexp t
    rw [hsimp]
    have hAR : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hθA : θ ^ 2 * (A : ℝ) ^ 2 ≤ 14.4 :=
      theta_sq_bound hr hQ hQ0 (by rw [hddef]; exact hd) (blockCount_mul_le hr)
    have h1 : (2 / 5 : ℝ) * A ≤ (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24) := by
      nlinarith [sq_nonneg θ, hθA, hAR]
    have h3 : (2 / 5 : ℝ) * A ≤ ‖∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I)‖ :=
      le_trans h1 (norm_sum_exp_lower θ A)
    nlinarith [h3, hAR]
  rw [shorProb_eq u hrQ c]
  have hsum : ∑ k ∈ range r, (blockCount Q r k : ℝ) = Q := by
    have h := sum_blockCount (Q := Q) (r := r) hr hrQ
    calc ∑ k ∈ range r, (blockCount Q r k : ℝ) = ((∑ k ∈ range r, blockCount Q r k : ℕ) : ℝ) := by
          push_cast; ring
      _ = Q := by rw [h]
  have hCS : (Q : ℝ) ^ 2 ≤ (r : ℝ) * ∑ k ∈ range r, (blockCount Q r k : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := range r) (f := fun k => (blockCount Q r k : ℝ))
    rw [Finset.card_range, hsum] at h
    exact h
  have hS : (Q : ℝ) ^ 2 / r ≤ ∑ k ∈ range r, (blockCount Q r k : ℝ) ^ 2 := by
    rw [div_le_iff₀ hrR]
    linarith [hCS]
  have hstep : (4 / 25 : ℝ) * ∑ k ∈ range r, (blockCount Q r k : ℝ) ^ 2
      ≤ ∑ k ∈ range r, ‖∑ t ∈ range (blockCount Q r k),
            Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hkey
  have hfinal : 1 / (8 * (r : ℝ)) ≤ (1 / (Q : ℝ) ^ 2) * ((4 / 25 : ℝ) * ((Q : ℝ) ^ 2 / r)) := by
    rw [show (1 / (Q : ℝ) ^ 2) * ((4 / 25 : ℝ) * ((Q : ℝ) ^ 2 / r)) = 4 / (25 * r) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  refine le_trans hfinal ?_
  have hlast : (4 / 25 : ℝ) * ((Q : ℝ) ^ 2 / r)
      ≤ ∑ k ∈ range r, ‖∑ t ∈ range (blockCount Q r k),
            Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)‖ ^ 2 := by
    refine le_trans ?_ hstep
    nlinarith [hS]
  exact mul_le_mul_of_nonneg_left hlast (by positivity)

/-! ### The classical post-processing -/

/-- An integer bound `2|cr - sQ| ≤ r` is exactly the statement that `s/r`
approximates `c/Q` to within `1/(2Q)`. -/
lemma close_of_int_bound {Q r c s : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (h : 2 * |(c : ℤ) * r - s * Q| ≤ r) : |(c : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have key : (c : ℝ) / Q - (s : ℝ) / r = (((c : ℤ) * r - s * Q : ℤ) : ℝ) / (Q * r) := by
    push_cast
    field_simp
  have habs : (|(c : ℤ) * r - s * Q| : ℝ) ≤ (r : ℝ) / 2 := by
    have h2 : ((2 * |(c : ℤ) * r - s * Q| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h2 ⊢
    linarith
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (Q : ℝ) * r)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at habs ⊢
  nlinarith [habs]

/-- Uniqueness of the rational approximation: if `c/Q` is within `1/(2Q)` of `s/r`
in lowest terms with `r ≤ M` and `M ^ 2 < Q`, no other fraction with denominator
at most `M` can be that close. -/
lemma determines_of_close {Q M r s : ℕ} (hr : 0 < r) (hrM : r ≤ M) (hMQ : M ^ 2 < Q)
    (hs : Nat.Coprime s r) {c : ℕ} (hc : |(c : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q)) :
    DeterminesPeriod Q M r c := by
  have hQ : 0 < Q := lt_of_le_of_lt (Nat.zero_le _) hMQ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨⟨s, hs, hc⟩, ?_⟩
  intro s' r' hr' hr'M hs' hc'
  have hr'R : (0 : ℝ) < r' := by exact_mod_cast hr'
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htri : |(s : ℝ) / r - (s' : ℝ) / r'| ≤ 1 / Q := by
    calc |(s : ℝ) / r - (s' : ℝ) / r'|
        = |((c : ℝ) / Q - (s' : ℝ) / r') - ((c : ℝ) / Q - (s : ℝ) / r)| := by ring_nf
      _ ≤ |(c : ℝ) / Q - (s' : ℝ) / r'| + |(c : ℝ) / Q - (s : ℝ) / r| := abs_sub _ _
      _ ≤ 1 / (2 * Q) + 1 / (2 * Q) := by linarith
      _ = 1 / Q := by field_simp; ring
  have hnum : (s : ℤ) * r' = (s' : ℤ) * r := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |((s : ℤ) * r' - (s' : ℤ) * r : ℤ)| := by
      have h1' : (1 : ℤ) ≤ |((s : ℤ) * r' - (s' : ℤ) * r)| := Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast h1'
    have heq : (s : ℝ) / r - (s' : ℝ) / r'
        = (((s : ℤ) * r' - (s' : ℤ) * r : ℤ) : ℝ) / (r * r') := by
      push_cast
      field_simp
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (r : ℝ) * r')] at htri
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at htri
    have hrr : ((r : ℝ) * r') ≤ (M : ℝ) * M := by
      have k1 : (r : ℝ) ≤ M := by exact_mod_cast hrM
      have k2 : (r' : ℝ) ≤ M := by exact_mod_cast hr'M
      nlinarith
    have hMQ' : ((M : ℝ) * M) < Q := by
      have : ((M : ℝ) ^ 2) < Q := by exact_mod_cast hMQ
      nlinarith
    push_cast at htri h1
    nlinarith [htri, h1]
  have h0 : (s * r' : ℕ) = s' * r := by exact_mod_cast hnum
  have hdvd1 : r ∣ r' := by
    have hd : r ∣ s * r' := ⟨s', by rw [h0, mul_comm]⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hd
  have hdvd2 : r' ∣ r := by
    have hd : r' ∣ s' * r := ⟨s, by rw [← h0, mul_comm]⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs') hd
  exact Nat.dvd_antisymm hdvd2 hdvd1

/-- The rounded sample `c_s = round (s Q / r)`. -/
def roundSample (Q r s : ℕ) : ℕ := (2 * s * Q + r) / (2 * r)

lemma roundSample_spec {Q r s : ℕ} (hr : 0 < r) :
    2 * |(roundSample Q r s : ℤ) * r - s * Q| ≤ r := by
  have h2r : 0 < 2 * r := by omega
  have hd := Nat.div_add_mod (2 * s * Q + r) (2 * r)
  have hm := Nat.mod_lt (2 * s * Q + r) h2r
  set q := (2 * s * Q + r) / (2 * r) with hq
  set m := (2 * s * Q + r) % (2 * r) with hmm
  have hd' : (2 : ℤ) * r * q + m = 2 * s * Q + r := by exact_mod_cast hd
  have hm' : (m : ℤ) < 2 * r := by exact_mod_cast hm
  have hm0 : (0 : ℤ) ≤ m := Int.natCast_nonneg m
  have key : |2 * ((q : ℤ) * r - s * Q)| ≤ (r : ℤ) := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  calc 2 * |(q : ℤ) * r - s * Q| = |2 * ((q : ℤ) * r - s * Q)| := by rw [abs_mul]; norm_num
    _ ≤ (r : ℤ) := key

lemma roundSample_bounds {Q r s : ℕ} (hr : 0 < r) :
    -(r : ℤ) ≤ 2 * ((roundSample Q r s : ℤ) * r - s * Q) ∧
      2 * ((roundSample Q r s : ℤ) * r - s * Q) ≤ r := by
  have h := roundSample_spec (Q := Q) (r := r) (s := s) hr
  have h' : |(2 : ℤ) * ((roundSample Q r s : ℤ) * r - s * Q)| ≤ r := by
    rw [abs_mul]; simpa using h
  exact abs_le.mp h'

lemma roundSample_lt {Q r s : ℕ} (hr : 0 < r) (hs : s < r) (hQ : r < Q) :
    roundSample Q r s < Q := by
  obtain ⟨h1, h2⟩ := roundSample_bounds (Q := Q) (r := r) (s := s) hr
  have hs' : (s : ℤ) ≤ (r : ℤ) - 1 := by omega
  have hQ' : (r : ℤ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have hlt : (roundSample Q r s : ℤ) < Q := by nlinarith
  exact_mod_cast hlt

lemma roundSample_inj {Q r : ℕ} (hr : 0 < r) (hQ : r < Q) :
    Function.Injective (roundSample Q r) := by
  intro a b hab
  obtain ⟨ha1, ha2⟩ := roundSample_bounds (Q := Q) (r := r) (s := a) hr
  obtain ⟨hb1, hb2⟩ := roundSample_bounds (Q := Q) (r := r) (s := b) hr
  rw [hab] at ha1 ha2
  have hQ' : (r : ℤ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have k1 : (a : ℤ) ≤ b := by nlinarith
  have k2 : (b : ℤ) ≤ a := by nlinarith
  omega

/-! ### Main theorem -/

/-- **Shor's period finding works with high probability.**

Let `u` be a unit modulo `N` of multiplicative order `r`, and run the quantum
period-finding routine with a register of size `Q`, where `r ≤ M` and `M ^ 2 < Q`
(the usual choice is `M = N` and `Q` a power of two exceeding `N ^ 2`).  Then with
probability at least `φ(r) / (8 r)` the measured value `c` determines the period
`r` unambiguously: some fraction `s'/r'` in lowest terms with `r' ≤ M`
approximates `c / Q` to within `1 / (2 Q)`, and every such fraction has
denominator `r' = r`. -/
theorem shor_period {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (Q M : ℕ)
    (hrM : orderOf u ≤ M) (hMQ : M ^ 2 < Q) :
    (Nat.totient (orderOf u) : ℝ) / (8 * orderOf u) ≤
      ∑ c ∈ (range Q).filter (fun c => DeterminesPeriod Q M (orderOf u) c),
        shorProb N u Q c := by
  set r := orderOf u with hrdef
  have hr : 0 < r := orderOf_pos u
  have hMM : M ≤ M ^ 2 := by nlinarith [hr.trans_le hrM]
  have hrQ : r < Q := lt_of_le_of_lt hrM (lt_of_le_of_lt hMM hMQ)
  have hQ : 0 < Q := hr.trans hrQ
  have hr2Q : r ^ 2 < Q := lt_of_le_of_lt (Nat.pow_le_pow_left hrM 2) hMQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set S : Finset ℕ := (range r).filter (fun s => Nat.Coprime s r) with hS
  have hcard : (S.card : ℝ) = (Nat.totient r : ℝ) := by
    congr 1
    rw [Nat.totient, hS]
    exact congrArg Finset.card (Finset.filter_congr fun s _ => by
      simpa using Nat.coprime_comm)
  have hsub : S.image (roundSample Q r) ⊆
      (range Q).filter (fun c => DeterminesPeriod Q M r c) := by
    intro c hc
    simp only [Finset.mem_image] at hc
    obtain ⟨s, hs, rfl⟩ := hc
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hs
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨roundSample_lt hr hs.1 hrQ,
      determines_of_close hr hrM hMQ hs.2 (close_of_int_bound hr hQ (roundSample_spec hr))⟩
  calc (Nat.totient r : ℝ) / (8 * r)
      = (S.card : ℝ) * (1 / (8 * r)) := by rw [hcard]; ring
    _ ≤ ∑ s ∈ S, shorProb N u Q (roundSample Q r s) := by
        have := Finset.card_nsmul_le_sum S (fun s => shorProb N u Q (roundSample Q r s))
          (1 / (8 * (r : ℝ))) (fun s _ => prob_lower u hr2Q _ (s : ℤ) (roundSample_spec hr))
        simpa [nsmul_eq_mul] using this
    _ = ∑ c ∈ S.image (roundSample Q r), shorProb N u Q c := by
        rw [Finset.sum_image (fun a _ b _ hab => roundSample_inj hr hrQ hab)]
    _ ≤ ∑ c ∈ (range Q).filter (fun c => DeterminesPeriod Q M r c), shorProb N u Q c :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => shorProb_nonneg N u Q i)

end QI

