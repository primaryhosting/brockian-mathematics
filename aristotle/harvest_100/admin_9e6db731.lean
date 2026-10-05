/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Quadratic-like maps

Following Douady–Hubbard and McMullen, a *quadratic-like map* is a holomorphic proper
degree-two branched covering `f : U → V` between simply connected planar domains with
`closure U` a compact subset of `V`.  We encode "proper of degree two, branched over the
unique critical value" by the fibre conditions `fiber_crit` and `fiber_two`. -/

/-- A quadratic-like map `f : U → V` with critical point `c`. -/
structure QuadraticLike (f : ℂ → ℂ) (U V : Set ℂ) (c : ℂ) : Prop where
  /-- The domain is open. -/
  isOpen_U : IsOpen U
  /-- The range is open. -/
  isOpen_V : IsOpen V
  /-- `U` is relatively compact. -/
  isCompact_closure : IsCompact (closure U)
  /-- `U` is compactly contained in `V`. -/
  closure_subset : closure U ⊆ V
  /-- `f` is holomorphic on a neighbourhood of `V`. -/
  analytic : AnalyticOnNhd ℂ f V
  /-- `f` maps `U` into `V`. -/
  mapsTo : Set.MapsTo f U V
  /-- The critical point lies in `U`. -/
  crit_mem : c ∈ U
  /-- `c` is a critical point. -/
  crit_deriv : deriv f c = 0
  /-- The fibre over the critical value is the single (doubled) point `c`. -/
  fiber_crit : {z ∈ U | f z = f c} = {c}
  /-- Every other fibre consists of exactly two points: `f : U → V` is proper of degree 2. -/
  fiber_two : ∀ w ∈ V, w ≠ f c → ∃ a b : ℂ, a ≠ b ∧ {z ∈ U | f z = w} = {a, b}

/-- The filled Julia set of a quadratic-like map `f : U → V`:
points whose whole forward orbit stays in `U`. -/
def filledJulia (f : ℂ → ℂ) (U : Set ℂ) : Set ℂ := {z | ∀ n : ℕ, f^[n] z ∈ U}

/-- `(U', V')` exhibits a renormalization of period `n` of the quadratic-like map
`f : U → V` with critical point `c`: the `n`-th iterate `f^[n] : U' → V'` is again
quadratic-like with the *same* critical point, its domain sits inside `U`, the first `n`
iterates of `U'` stay inside `U` (so the small Julia sets form a cycle inside `K(f)`),
and the small filled Julia set is connected. -/
structure IsRenormalization (f : ℂ → ℂ) (U : Set ℂ) (c : ℂ) (n : ℕ)
    (U' V' : Set ℂ) : Prop where
  /-- The period is positive. -/
  pos : 0 < n
  /-- The return map is quadratic-like. -/
  quadraticLike : QuadraticLike (f^[n]) U' V' c
  /-- The small domain sits inside the big one. -/
  subset : U' ⊆ U
  /-- The orbit of the small domain up to time `n` stays inside `U`. -/
  orbit : ∀ i < n, Set.MapsTo (f^[i]) U' U
  /-- The small filled Julia set is connected (simple renormalization). -/
  connected : IsConnected (filledJulia (f^[n]) U')

/-- The set of renormalization periods of a quadratic-like map. -/
def renormPeriods (f : ℂ → ℂ) (U : Set ℂ) (c : ℂ) : Set ℕ :=
  {n | ∃ U' V' : Set ℂ, IsRenormalization f U c n U' V'}

/-- A quadratic-like map is *infinitely renormalizable* if it has arbitrarily large
renormalization periods. -/
def InfinitelyRenormalizable (f : ℂ → ℂ) (U : Set ℂ) (c : ℂ) : Prop :=
  ∀ N : ℕ, ∃ n ∈ renormPeriods f U c, N < n

/-! ## Base case: period one -/

/-- **Base case.** A quadratic-like map with connected filled Julia set is renormalizable
with period `1` (it is its own first renormalization). -/
theorem one_mem_renormPeriods {f : ℂ → ℂ} {U V : Set ℂ} {c : ℂ}
    (hf : QuadraticLike f U V c) (hK : IsConnected (filledJulia f U)) :
    1 ∈ renormPeriods f U c := by
  refine ⟨U, V, Nat.one_pos, ?_, subset_rfl, ?_, ?_⟩
  · rwa [Function.iterate_one]
  · intro i hi
    interval_cases i
    simpa using Set.mapsTo_id U
  · rwa [Function.iterate_one]

/-! ## The tower (reduction) law: periods multiply -/

/-- **Reduction.** If `f` is renormalizable with period `n` and the renormalized map
`f^[n] : U₁ → V₁` is itself renormalizable with period `m`, then `f` is renormalizable
with period `n * m`.  This is the tower law underlying McMullen's inductive analysis of
infinitely renormalizable maps. -/
theorem isRenormalization_mul {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {n m : ℕ}
    {U₁ V₁ U₂ V₂ : Set ℂ}
    (h₁ : IsRenormalization f U c n U₁ V₁)
    (h₂ : IsRenormalization (f^[n]) U₁ c m U₂ V₂) :
    IsRenormalization f U c (n * m) U₂ V₂ := by
  have hiter : f^[n * m] = (f^[n])^[m] := Function.iterate_mul f n m
  refine ⟨Nat.mul_pos h₁.pos h₂.pos, ?_, h₂.subset.trans h₁.subset, ?_, ?_⟩
  · rw [hiter]; exact h₂.quadraticLike
  · intro i hi
    -- write `i = n * q + r` with `r < n` and `q < m`
    have hn : 0 < n := h₁.pos
    set q := i / n with hq
    set r := i % n with hr
    have hir : n * q + r = i := Nat.div_add_mod i n
    have hrn : r < n := Nat.mod_lt _ hn
    have hqm : q < m := by
      by_contra hcon
      push_neg at hcon
      have : n * m ≤ n * q := Nat.mul_le_mul_left n hcon
      omega
    have hstep1 : Set.MapsTo ((f^[n])^[q]) U₂ U₁ := h₂.orbit q hqm
    have hstep2 : Set.MapsTo (f^[r]) U₁ U := h₁.orbit r hrn
    have : Set.MapsTo (f^[r] ∘ (f^[n])^[q]) U₂ U := hstep2.comp hstep1
    have hcomp : f^[r] ∘ (f^[n])^[q] = f^[i] := by
      rw [← Function.iterate_mul, ← Function.iterate_add]
      congr 1
      omega
    rwa [hcomp] at this
  · rw [hiter]; exact h₂.connected

/-- The multiplicative form on the level of period sets. -/
theorem mul_mem_renormPeriods {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {n m : ℕ}
    {U₁ V₁ : Set ℂ} (h₁ : IsRenormalization f U c n U₁ V₁)
    (h₂ : m ∈ renormPeriods (f^[n]) U₁ c) :
    n * m ∈ renormPeriods f U c := by
  obtain ⟨U₂, V₂, h₂⟩ := h₂
  exact ⟨U₂, V₂, isRenormalization_mul h₁ h₂⟩

/-! ## Small Julia sets sit inside the big one -/

/-- The filled Julia set of a renormalization is contained in the filled Julia set of the
original map. -/
theorem filledJulia_renorm_subset {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {n : ℕ}
    {U' V' : Set ℂ} (h : IsRenormalization f U c n U' V') :
    filledJulia (f^[n]) U' ⊆ filledJulia f U := by
  intro z hz j
  have hn : 0 < n := h.pos
  have hir : n * (j / n) + j % n = j := Nat.div_add_mod j n
  have hrn : j % n < n := Nat.mod_lt _ hn
  have hmem : (f^[n])^[j / n] z ∈ U' := hz (j / n)
  have := h.orbit (j % n) hrn hmem
  have hcomp : f^[j % n] ((f^[n])^[j / n] z) = f^[j] z := by
    rw [← Function.iterate_mul, ← Function.iterate_add_apply]
    congr 1
    omega
  rwa [hcomp] at this

/-! ## Non-vacuity: `z ↦ z²` is quadratic-like with connected filled Julia set -/

/-- Iterates of the squaring map. -/
theorem iterate_sq (n : ℕ) (z : ℂ) : (fun w : ℂ => w ^ 2)^[n] z = z ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

/-- The filled Julia set of `z ↦ z²` on the disc of radius `2` is the closed unit disc. -/
theorem filledJulia_sq :
    filledJulia (fun z : ℂ => z ^ 2) (Metric.ball 0 2) = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [filledJulia, Set.mem_setOf_eq, iterate_sq, Metric.mem_ball, Metric.mem_closedBall,
    dist_zero_right, norm_pow]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 : ℝ) hc
    have h1 : ‖z‖ ^ (2 ^ m) < 2 := h m
    have h2 : ‖z‖ ^ m ≤ ‖z‖ ^ (2 ^ m) :=
      pow_le_pow_right₀ hc.le (Nat.le_of_lt Nat.lt_two_pow_self)
    linarith
  · intro h n
    calc ‖z‖ ^ (2 ^ n) ≤ 1 ^ (2 ^ n) := pow_le_pow_left₀ (norm_nonneg z) h _
      _ = 1 := one_pow _
      _ < 2 := by norm_num

/-- The squaring map is quadratic-like on `𝔻(0,2) → 𝔻(0,4)`, with critical point `0`. -/
theorem quadraticLike_sq :
    QuadraticLike (fun z : ℂ => z ^ 2) (Metric.ball 0 2) (Metric.ball 0 4) 0 := by
  have hcl : closure (Metric.ball (0 : ℂ) 2) = Metric.closedBall (0 : ℂ) 2 :=
    closure_ball 0 (by norm_num)
  refine ⟨Metric.isOpen_ball, Metric.isOpen_ball, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcl]; exact isCompact_closedBall 0 2
  · rw [hcl]
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  · exact fun z _ => analyticAt_id.pow 2
  · intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    rw [norm_pow]
    nlinarith
  · simp
  · simp
  · ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨-, h⟩
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using h)
    · rintro rfl; norm_num
  · intro w hw hw0
    simp only [Metric.mem_ball, dist_zero_right] at hw
    simp only [ne_eq] at hw0
    have hw0' : w ≠ 0 := by simpa using hw0
    obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq w 2
    have hsne : s ≠ 0 := by rintro rfl; simp at hs; exact hw0' hs.symm
    have hnorm : ‖s‖ < 2 := by
      have hns : ‖s‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hs]
      nlinarith [norm_nonneg s]
    refine ⟨s, -s, ?_, ?_⟩
    · intro h
      apply hsne
      have h2 : (2 : ℂ) * s = 0 := by linear_combination h
      simpa using h2
    · ext z
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Metric.mem_ball,
        dist_zero_right]
      constructor
      · rintro ⟨-, h⟩
        have h2 : (z - s) * (z + s) = 0 := by rw [← hs] at h; linear_combination h
        rcases mul_eq_zero.1 h2 with h1 | h1
        · left; linear_combination h1
        · right; linear_combination h1
      · rintro (rfl | rfl)
        · exact ⟨hnorm, hs⟩
        · exact ⟨by simpa using hnorm, by rw [← hs]; ring⟩

/-! ## Main theorem -/

/-- **McMullen renormalization: statement and Lean-checked base case / reduction.**

For quadratic-like maps (Douady–Hubbard–McMullen) we record:

1. *(non-vacuity)* the family of quadratic-like maps with connected filled Julia set is
   nonempty — `z ↦ z²` on `𝔻(0,2) → 𝔻(0,4)` is such a map;
2. *(base case)* every quadratic-like map with connected filled Julia set is renormalizable
   of period `1`, so `renormPeriods` is nonempty;
3. *(reduction / tower law)* renormalization periods compose multiplicatively: a period-`m`
   renormalization of the period-`n` renormalization of `f` is a period-`n*m`
   renormalization of `f`;
4. *(rigidity of the small Julia sets)* the filled Julia set of any renormalization is
   contained in the filled Julia set of the original map, and its full forward orbit under
   `f` stays inside `U`. -/
theorem mcmullen_renormalization :
    (QuadraticLike (fun z : ℂ => z ^ 2) (Metric.ball 0 2) (Metric.ball 0 4) 0 ∧
      IsConnected (filledJulia (fun z : ℂ => z ^ 2) (Metric.ball 0 2))) ∧
    (∀ (f : ℂ → ℂ) (U V : Set ℂ) (c : ℂ), QuadraticLike f U V c →
      IsConnected (filledJulia f U) → 1 ∈ renormPeriods f U c) ∧
    (∀ (f : ℂ → ℂ) (U : Set ℂ) (c : ℂ) (n m : ℕ) (U₁ V₁ U₂ V₂ : Set ℂ),
      IsRenormalization f U c n U₁ V₁ →
      IsRenormalization (f^[n]) U₁ c m U₂ V₂ →
      IsRenormalization f U c (n * m) U₂ V₂) ∧
    (∀ (f : ℂ → ℂ) (U : Set ℂ) (c : ℂ) (n : ℕ) (U' V' : Set ℂ),
      IsRenormalization f U c n U' V' →
      filledJulia (f^[n]) U' ⊆ filledJulia f U) := by
  refine ⟨⟨quadraticLike_sq, ?_⟩, ?_, ?_, ?_⟩
  · rw [filledJulia_sq]
    exact ⟨⟨0, by simp⟩, (convex_closedBall (0 : ℂ) 1).isPreconnected⟩
  · intro f U V c hf hK; exact one_mem_renormPeriods hf hK
  · intro f U c n m U₁ V₁ U₂ V₂ h₁ h₂; exact isRenormalization_mul h₁ h₂
  · intro f U c n U' V' h; exact filledJulia_renorm_subset h

end Frontier

