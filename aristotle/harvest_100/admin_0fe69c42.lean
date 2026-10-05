/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; it is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

/-!
## Li's criterion

Let `Z` be the multiset of (nontrivial) zeros of a completed zeta-type function.  Li's
coefficients are

`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`,

and Li's criterion states that all zeros lie on the critical line `Re ρ = 1/2` if and only if
`λ_n ≥ 0` for every `n ≥ 1`.

The content of the criterion is the Möbius change of variable `z = 1 - 1/ρ`, which maps the
critical line to the unit circle and the functional-equation symmetry `ρ ↦ 1 - ρ` to the
inversion `z ↦ 1/z`.  We prove the criterion for an arbitrary finite multiset of zeros which
avoids `0` and is stable under `ρ ↦ 1 - ρ`; this is the arithmetic-free core of Li's theorem
(the analytic input specific to `ζ`, namely the Hadamard product for the completed zeta
function, is what turns this statement into the statement about `ζ` itself).

The nontrivial direction uses a simultaneous recurrence statement on the unit circle
(`Frontier.exists_large_pow_near_one`): for finitely many unimodular numbers there are
arbitrarily large exponents `n` making all `n`-th powers simultaneously close to `1`.  This is
what forces a zero off the critical line to produce a negative Li coefficient.
-/

/-- The `n`-th Li coefficient attached to a finite multiset `Z` of zeros:
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`. -/
noncomputable def liCoeff (Z : Multiset ℂ) (n : ℕ) : ℂ :=
  (Z.map (fun ρ => 1 - (1 - 1 / ρ) ^ n)).sum

/-- The Riemann hypothesis for a multiset `Z` of zeros: every zero lies on the critical line. -/
def RiemannHypothesisFor (Z : Multiset ℂ) : Prop := ∀ ρ ∈ Z, ρ.re = 1 / 2

/-! ### The Möbius dictionary -/

/-- The basic identity behind Li's criterion: `|1 - 1/ρ|² - 1 = (1 - 2 Re ρ)/|ρ|²`. -/
lemma norm_sq_mobius_sub_one (ρ : ℂ) (h : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ ^ 2 - 1 = (1 - 2 * ρ.re) / ‖ρ‖ ^ 2 := by
  have h1 : ‖1 - 1 / ρ‖ = ‖ρ - 1‖ / ‖ρ‖ := by
    rw [← norm_div]; congr 1; field_simp
  rw [h1, div_pow]
  have hn : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  have h2 : ‖ρ - 1‖ ^ 2 = (ρ.re - 1) ^ 2 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  rw [hn, h2]
  have hp : ρ.re ^ 2 + ρ.im ^ 2 ≠ 0 := by rw [← hn]; positivity
  field_simp
  ring

/-- `ρ` lies on the critical line iff `1 - 1/ρ` lies on the unit circle. -/
lemma norm_mobius_eq_one_iff (ρ : ℂ) (h : ρ ≠ 0) : ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hp : (0 : ℝ) < ‖ρ‖ ^ 2 := by positivity
  have hk := norm_sq_mobius_sub_one ρ h
  constructor
  · intro he
    rw [he] at hk
    have h0 : (1 - 2 * ρ.re) / ‖ρ‖ ^ 2 = 0 := by rw [← hk]; ring
    rcases div_eq_zero_iff.mp h0 with h1 | h1
    · linarith
    · exact absurd h1 hp.ne'
  · intro he
    have hz : (1 : ℝ) - 2 * ρ.re = 0 := by rw [he]; ring
    rw [hz, zero_div] at hk
    nlinarith [norm_nonneg (1 - 1 / ρ)]

/-- `ρ` lies to the left of the critical line iff `1 - 1/ρ` lies outside the unit circle. -/
lemma one_lt_norm_mobius_iff (ρ : ℂ) (h : ρ ≠ 0) : 1 < ‖1 - 1 / ρ‖ ↔ ρ.re < 1 / 2 := by
  have hp : (0 : ℝ) < ‖ρ‖ ^ 2 := by positivity
  have hk := norm_sq_mobius_sub_one ρ h
  constructor
  · intro he
    have hpos : 0 < (1 - 2 * ρ.re) / ‖ρ‖ ^ 2 := by rw [← hk]; nlinarith
    rcases div_pos_iff.mp hpos with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  · intro he
    have h0 : 0 < (1 - 2 * ρ.re) / ‖ρ‖ ^ 2 := by apply div_pos <;> linarith
    rw [← hk] at h0
    nlinarith [norm_nonneg (1 - 1 / ρ)]

/-! ### A simultaneous recurrence lemma -/

/-- Simultaneous recurrence on the unit circle: for finitely many unimodular numbers `u i`
there are arbitrarily large exponents `n` for which all the powers `u i ^ n` are
simultaneously close to `1`. -/
lemma exists_large_pow_near_one {ι : Type} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) : ∃ n, N ≤ n ∧ ∀ i, ‖u i ^ n - 1‖ < ε := by
  set x : ℕ → (ι → ℂ) := fun m i => u i ^ m with hxdef
  have hx : ∀ m, x m ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro m
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_
    intro i
    simp [hxdef, hu i]
  obtain ⟨a, -, ph, hph, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hx
  have hcauchy : CauchySeq (x ∘ ph) := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨M, hM⟩ := hcauchy ε hε
  obtain ⟨p, hp1, hp2⟩ : ∃ p, M ≤ p ∧ N + ph M ≤ ph p :=
    ⟨max M (N + ph M), le_max_left _ _,
      le_trans (le_max_right M (N + ph M)) hph.le_apply⟩
  refine ⟨ph p - ph M, by omega, ?_⟩
  intro i
  have hnorm : ‖u i ^ (ph M)‖ = 1 := by simp [hu i]
  have hsplit : (u i ^ (ph p - ph M) - 1) * u i ^ (ph M) = u i ^ (ph p) - u i ^ (ph M) := by
    rw [sub_mul, one_mul, ← pow_add]
    congr 2
    omega
  have heq : ‖u i ^ (ph p - ph M) - 1‖ = ‖u i ^ (ph p) - u i ^ (ph M)‖ := by
    rw [← hsplit, norm_mul, hnorm, mul_one]
  have hd : dist (x (ph p) i) (x (ph M) i) ≤ dist (x (ph p)) (x (ph M)) := dist_le_pi_dist _ _ i
  have hlt := hM p hp1 M le_rfl
  simp only [Function.comp_apply] at hlt
  rw [heq]
  calc ‖u i ^ (ph p) - u i ^ (ph M)‖ = dist (x (ph p) i) (x (ph M) i) := by
        simp [hxdef, dist_eq_norm]
    _ ≤ dist (x (ph p)) (x (ph M)) := hd
    _ < ε := hlt

/-! ### Two computational lemmas -/

/-- Splitting off the modulus: `Re (z^n) = ‖z‖^n * Re ((z/‖z‖)^n)`. -/
lemma re_pow_eq (z : ℂ) (n : ℕ) : (z ^ n).re = ‖z‖ ^ n * (((z / (‖z‖ : ℂ)) ^ n).re) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rcases n with _ | m <;> simp
  · rw [div_pow, ← Complex.ofReal_pow, Complex.div_ofReal_re]
    have hr : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    field_simp

/-- The real part of a multiset sum is the sum of the real parts. -/
lemma re_multiset_sum (s : Multiset ℂ) : (s.sum).re = (s.map Complex.re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-! ### The two directions -/

/-- Easy direction: if all zeros lie on the critical line then all Li coefficients have
nonnegative real part. -/
lemma liCoeff_nonneg_of_RH (Z : Multiset ℂ) (h0 : ∀ ρ ∈ Z, ρ ≠ 0)
    (hRH : RiemannHypothesisFor Z) (n : ℕ) : 0 ≤ (liCoeff Z n).re := by
  rw [liCoeff, re_multiset_sum, Multiset.map_map]
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hx
  have hz : ‖1 - 1 / ρ‖ = 1 := (norm_mobius_eq_one_iff ρ (h0 ρ hρ)).mpr (hRH ρ hρ)
  have hpow : ‖(1 - 1 / ρ) ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have := Complex.re_le_norm ((1 - 1 / ρ) ^ n)
  rw [hpow] at this
  simp only [Function.comp_apply, Complex.sub_re, Complex.one_re]
  linarith

/-- Hard direction, on the `z`-side: if a finite multiset `W` of nonzero complex numbers
contains an element of modulus `> 1`, then for some `n ≥ 1` the sum `∑_{z ∈ W} (1 - z^n)` has
negative real part. -/
lemma exists_neg_of_one_lt_norm (W : Multiset ℂ) (hW : ∀ z ∈ W, z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ W) (hz₀' : 1 < ‖z₀‖) :
    ∃ n : ℕ, 1 ≤ n ∧ ((W.map (fun z => 1 - z ^ n)).sum).re < 0 := by
  obtain ⟨W', rfl⟩ := Multiset.exists_cons_of_mem hz₀
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (2 * (1 + (Multiset.card W' : ℝ))) hz₀'
  set N := max N₀ 1 with hNdef
  have hNle : ‖z₀‖ ^ N₀ ≤ ‖z₀‖ ^ N := pow_le_pow_right₀ hz₀'.le (le_max_left _ _)
  set u : (↥(z₀ ::ₘ W').toFinset) → ℂ := fun z => (z : ℂ) / (‖(z : ℂ)‖ : ℂ) with hu_def
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    have hi : (i : ℂ) ∈ z₀ ::ₘ W' := Multiset.mem_toFinset.mp i.2
    have hne : (i : ℂ) ≠ 0 := hW _ hi
    simp [hu_def, norm_ne_zero_iff.mpr hne]
  obtain ⟨n, hnN, hn⟩ := exists_large_pow_near_one u hu (ε := 1 / 2) (by norm_num) N
  have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hnN
  refine ⟨n, hn1, ?_⟩
  have hpt : ∀ z ∈ z₀ ::ₘ W', (1 / 2) * ‖z‖ ^ n ≤ (z ^ n).re := by
    intro z hz
    have hmem : z ∈ (z₀ ::ₘ W').toFinset := Multiset.mem_toFinset.mpr hz
    have hclose := hn ⟨z, hmem⟩
    have hre : (1 : ℝ) / 2 < ((z / (‖z‖ : ℂ)) ^ n).re := by
      have h1 : |(1 - (z / (‖z‖ : ℂ)) ^ n).re| ≤ ‖(1 - (z / (‖z‖ : ℂ)) ^ n)‖ :=
        Complex.abs_re_le_norm _
      have h2 : ‖(1 - (z / (‖z‖ : ℂ)) ^ n)‖ < 1 / 2 := by
        rw [show (1 - (z / (‖z‖ : ℂ)) ^ n) = -((z / (‖z‖ : ℂ)) ^ n - 1) by ring, norm_neg]
        exact hclose
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      simp only [Complex.sub_re, Complex.one_re] at h3
      linarith [h3.2]
    rw [re_pow_eq z n]
    have hnn : (0 : ℝ) ≤ ‖z‖ ^ n := by positivity
    nlinarith
  have hbig : 1 + (Multiset.card W' : ℝ) < (1 / 2) * ‖z₀‖ ^ n := by
    have h1 : ‖z₀‖ ^ N ≤ ‖z₀‖ ^ n := pow_le_pow_right₀ hz₀'.le hnN
    linarith
  rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
  have h1 : (1 - z₀ ^ n).re = 1 - (z₀ ^ n).re := by simp
  have h2 : ((W'.map (fun z => 1 - z ^ n)).sum).re ≤ (Multiset.card W' : ℝ) := by
    rw [re_multiset_sum, Multiset.map_map]
    have hb := Multiset.sum_le_card_nsmul (W'.map (Complex.re ∘ fun z => 1 - z ^ n)) (1 : ℝ) ?_
    · simpa using hb
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
      have hzz := hpt z (Multiset.mem_cons_of_mem hz)
      have hnn : (0 : ℝ) ≤ ‖z‖ ^ n := by positivity
      simp only [Function.comp_apply, Complex.sub_re, Complex.one_re]
      nlinarith
  have h3 := hpt z₀ (Multiset.mem_cons_self _ _)
  rw [h1]
  linarith

/-- **Li's criterion** for a finite multiset of zeros.

`Z` is a finite multiset of complex numbers ("the nontrivial zeros"), none of which is `0`,
which is stable under the functional-equation symmetry `ρ ↦ 1 - ρ`.  Then all elements of `Z`
lie on the critical line `Re ρ = 1/2` if and only if all the Li coefficients
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`, `n ≥ 1`, have nonnegative real part. -/
theorem RH_Li_criterion (Z : Multiset ℂ) (h0 : ∀ ρ ∈ Z, ρ ≠ 0)
    (hfe : Z.map (fun ρ => 1 - ρ) = Z) :
    RiemannHypothesisFor Z ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ (liCoeff Z n).re := by
  have hmem : ∀ ρ ∈ Z, 1 - ρ ∈ Z := by
    intro ρ hρ
    have : (1 - ρ) ∈ Z.map (fun ρ => 1 - ρ) := Multiset.mem_map_of_mem _ hρ
    rwa [hfe] at this
  constructor
  · intro hRH n _
    exact liCoeff_nonneg_of_RH Z h0 hRH n
  · intro H
    by_contra hcon
    -- some zero is off the critical line; by symmetry we may take it to the left of it
    rw [RiemannHypothesisFor] at hcon
    push_neg at hcon
    obtain ⟨ρ₁, hρ₁, hne⟩ := hcon
    obtain ⟨ρ, hρ, hlt⟩ : ∃ ρ ∈ Z, ρ.re < 1 / 2 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨ρ₁, hρ₁, h⟩
      · refine ⟨1 - ρ₁, hmem ρ₁ hρ₁, ?_⟩
        simp only [Complex.sub_re, Complex.one_re]
        linarith
    -- pass to the `z`-side
    set W : Multiset ℂ := Z.map (fun ρ => 1 - 1 / ρ) with hWdef
    have hWne : ∀ z ∈ W, z ≠ 0 := by
      intro z hz
      obtain ⟨σ, hσ, rfl⟩ := Multiset.mem_map.mp hz
      intro hzero
      have hσ1 : σ = 1 := by
        have hσ0 : σ ≠ 0 := h0 σ hσ
        have h1 : (1 : ℂ) = 1 / σ := sub_eq_zero.mp hzero
        field_simp at h1
        exact h1
      have : (0 : ℂ) ∈ Z := by
        have := hmem σ hσ
        rwa [hσ1, sub_self] at this
      exact h0 0 this rfl
    have hz₀ : (1 - 1 / ρ) ∈ W := Multiset.mem_map_of_mem _ hρ
    have hz₀' : 1 < ‖1 - 1 / ρ‖ := (one_lt_norm_mobius_iff ρ (h0 ρ hρ)).mpr hlt
    obtain ⟨n, hn1, hneg⟩ := exists_neg_of_one_lt_norm W hWne hz₀ hz₀'
    have : liCoeff Z n = (W.map (fun z => 1 - z ^ n)).sum := by
      rw [hWdef, liCoeff, Multiset.map_map]
      rfl
    have hHn := H n hn1
    rw [this] at hHn
    exact absurd hHn (not_le.mpr hneg)

/-! ### Sanity checks: the hypotheses are satisfiable and the criterion has content -/

/-- A zero multiset on the critical line: `{1/2 + i, 1/2 - i}`.  It avoids `0` and is stable
under `ρ ↦ 1 - ρ`, so Li's criterion gives nonnegativity of all its Li coefficients. -/
example : ∀ n : ℕ, 1 ≤ n →
    0 ≤ (liCoeff {(1 / 2 + Complex.I), (1 / 2 - Complex.I)} n).re := by
  refine (RH_Li_criterion _ ?_ ?_).mp ?_
  · intro ρ hρ
    fin_cases hρ <;> simp [Complex.ext_iff] <;> norm_num
  · show Multiset.map _ ((1 / 2 + Complex.I) ::ₘ (1 / 2 - Complex.I) ::ₘ 0) = _
    rw [Multiset.map_cons, Multiset.map_cons]
    norm_num
    rw [show (1 : ℂ) - (1 / 2 + Complex.I) = 1 / 2 - Complex.I by ring,
        show (1 : ℂ) - (1 / 2 - Complex.I) = 1 / 2 + Complex.I by ring]
    exact Multiset.cons_swap _ _ _
  · intro ρ hρ
    fin_cases hρ <;> simp

/-- A symmetric pair of zeros off the critical line, `{1/4, 3/4}`, has `λ₂ = 2 - (9 + 1/9) < 0`,
so by Li's criterion it does not satisfy the Riemann hypothesis. -/
example : ¬ RiemannHypothesisFor {(1 / 4 : ℂ), (3 / 4 : ℂ)} := by
  have hne : ∀ ρ ∈ ({(1 / 4 : ℂ), (3 / 4 : ℂ)} : Multiset ℂ), ρ ≠ 0 := by
    intro ρ hρ
    fin_cases hρ <;> norm_num
  have hfe : Multiset.map (fun ρ : ℂ => 1 - ρ) {(1 / 4 : ℂ), (3 / 4 : ℂ)}
      = {(1 / 4 : ℂ), (3 / 4 : ℂ)} := by
    show Multiset.map _ ((1 / 4 : ℂ) ::ₘ (3 / 4 : ℂ) ::ₘ 0) = _
    rw [Multiset.map_cons, Multiset.map_cons]
    norm_num
    exact Multiset.cons_swap _ _ _
  have hneg : (liCoeff {(1 / 4 : ℂ), (3 / 4 : ℂ)} 2).re < 0 := by
    have h : ({(1 / 4 : ℂ), (3 / 4 : ℂ)} : Multiset ℂ) = (1 / 4 : ℂ) ::ₘ (3 / 4 : ℂ) ::ₘ 0 := rfl
    rw [liCoeff, h, Multiset.map_cons, Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons,
      Multiset.sum_cons, Multiset.sum_zero]
    norm_num
  intro hRH
  exact absurd ((RH_Li_criterion _ hne hfe).mp hRH 2 (by norm_num)) (not_le.mpr hneg)

end Frontier

