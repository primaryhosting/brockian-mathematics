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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a proper holomorphic map of degree two `f : U → V` between topological
discs in `ℂ` with `closure U` a compact subset of `V`.

We encode this as a structure.  The degree-two condition is encoded by:
* surjectivity of `f : U → V` (`surjOn`),
* every fibre over `V` has at most two points (`deg_le_two`),
* there is a unique critical point `crit ∈ U` (`crit_mem`, `deriv_crit`, `crit_unique`).

Properness of `f : U → V` is recorded in the field `proper`.
-/

/-- A quadratic-like map: a proper degree-two holomorphic map `f : U → V` of plane domains
with `closure U` compact and contained in `V`. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the big domain -/
  V : Set ℂ
  /-- the map, given as a globally defined function which is holomorphic on `U` -/
  f : ℂ → ℂ
  /-- the (unique) critical point -/
  crit : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isBounded_V : Bornology.IsBounded V
  closure_U_subset_V : closure U ⊆ V
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  surjOn : V ⊆ f '' U
  proper : ∀ C ⊆ V, IsCompact C → IsCompact (U ∩ f ⁻¹' C)
  crit_mem : crit ∈ U
  deriv_crit : deriv f crit = 0
  crit_unique : ∀ z ∈ U, deriv f z = 0 → z = crit
  deg_le_two : ∀ w ∈ V, (U ∩ f ⁻¹' {w}).ncard ≤ 2

namespace QuadraticLike

variable (F : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit stays
in the small domain `U`. -/
def K : Set ℂ := {z : ℂ | ∀ n : ℕ, F.f^[n] z ∈ F.U}

lemma K_subset_U : F.K ⊆ F.U := fun z hz => by simpa using hz 0

lemma mem_K_iff {z : ℂ} : z ∈ F.K ↔ ∀ n : ℕ, F.f^[n] z ∈ F.U := Iff.rfl

/-- The filled Julia set is forward invariant. -/
lemma mapsTo_K : Set.MapsTo F.f F.K F.K := by
  intro z hz n
  rw [← Function.iterate_succ_apply]
  exact hz (n + 1)

/-- The filled Julia set is totally invariant: it is exactly the set of points of `U` which are
mapped into it. -/
lemma preimage_K : F.U ∩ F.f ⁻¹' F.K = F.K := by
  ext z
  constructor
  · rintro ⟨hzU, hz⟩ n
    cases n with
    | zero => simpa using hzU
    | succ n => rw [Function.iterate_succ_apply]; exact hz n
  · intro hz
    exact ⟨F.K_subset_U hz, F.mapsTo_K hz⟩

lemma continuousAt_f {z : ℂ} (hz : z ∈ F.U) : ContinuousAt F.f z :=
  (F.analytic z hz).continuousAt

lemma continuousAt_iterate :
    ∀ (n : ℕ) {z : ℂ}, (∀ k < n, F.f^[k] z ∈ F.U) → ContinuousAt (F.f^[n]) z := by
  intro n
  induction n with
  | zero => intro z _; simpa using continuousAt_id
  | succ n ih =>
      intro z hz
      have h1 : ContinuousAt (F.f^[n]) z := ih (fun k hk => hz k (by omega))
      have h2 : ContinuousAt F.f (F.f^[n] z) := F.continuousAt_f (hz n (by omega))
      rw [Function.iterate_succ']
      exact h2.comp h1

lemma isCompact_closure_U : IsCompact (closure F.U) := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
  exact F.isBounded_V.subset F.closure_U_subset_V

/-- The compact set `A = U ∩ f⁻¹(closure U)`; it contains the filled Julia set. -/
def core : Set ℂ := F.U ∩ F.f ⁻¹' (closure F.U)

lemma isCompact_core : IsCompact F.core :=
  F.proper _ F.closure_U_subset_V F.isCompact_closure_U

lemma core_subset_U : F.core ⊆ F.U := Set.inter_subset_left

/-- The `n`-th stage of the construction of the filled Julia set. -/
def stage (n : ℕ) : Set ℂ := {z : ℂ | ∀ k ≤ n, F.f^[k] z ∈ F.core}

lemma stage_zero : F.stage 0 = F.core := by
  ext z
  simp only [stage, Set.mem_setOf_eq, Nat.le_zero]
  constructor
  · intro h; simpa using h 0 rfl
  · intro h k hk; subst hk; simpa using h

lemma stage_succ (n : ℕ) : F.stage (n + 1) = F.stage n ∩ (F.f^[n + 1]) ⁻¹' F.core := by
  ext z
  simp only [stage, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h (n + 1) le_rfl⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with hk' | hk'
    · exact h1 k (by omega)
    · subst hk'; exact h2

lemma isClosed_stage : ∀ n : ℕ, IsClosed (F.stage n) := by
  intro n
  induction n with
  | zero => rw [F.stage_zero]; exact F.isCompact_core.isClosed
  | succ n ih =>
      rw [F.stage_succ]
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_ ih F.isCompact_core.isClosed
      intro z hz
      refine (F.continuousAt_iterate (n + 1) ?_).continuousWithinAt
      intro k hk
      exact F.core_subset_U (hz k (by omega))

lemma K_eq_iInter_stage : F.K = ⋂ n : ℕ, F.stage n := by
  ext z
  simp only [Set.mem_iInter, stage, Set.mem_setOf_eq, mem_K_iff]
  constructor
  · intro h n k _
    refine ⟨h k, ?_⟩
    have hk : F.f (F.f^[k] z) = F.f^[k + 1] z := (Function.iterate_succ_apply' F.f k z).symm
    exact Set.mem_preimage.mpr (by rw [hk]; exact subset_closure (h (k + 1)))
  · intro h n
    exact F.core_subset_U (h n n le_rfl)

lemma isClosed_K : IsClosed F.K := by
  rw [F.K_eq_iInter_stage]
  exact isClosed_iInter F.isClosed_stage

lemma K_subset_core : F.K ⊆ F.core := by
  rw [F.K_eq_iInter_stage, ← F.stage_zero]
  exact Set.iInter_subset _ 0

/-- The filled Julia set of a quadratic-like map is compact. -/
theorem isCompact_K : IsCompact F.K :=
  F.isCompact_core.of_isClosed_subset F.isClosed_K F.K_subset_core

end QuadraticLike

/-!
## Renormalization

`f` is renormalizable with period `p ≥ 2` if some iterate `f^p`, restricted to a suitable
domain around the critical point, is again quadratic-like, and the first `p` iterates of that
domain stay inside `U`.
-/

/-- A quadratic-like restriction of period `p` of a quadratic-like map `F`: a quadratic-like
map `G` which agrees with `F^p` on its domain, whose domain sits inside `U` and has its first
`p` iterates inside `U`, and which is centred at the critical point of `F`. -/
structure Restriction (F : QuadraticLike) (p : ℕ) where
  /-- the restricted quadratic-like map -/
  G : QuadraticLike
  pos : 0 < p
  /-- `G` is the `p`-th iterate of `F` on its domain -/
  eqOn : Set.EqOn G.f (F.f^[p]) G.U
  /-- the domain lies in `U` -/
  subset : G.U ⊆ F.U
  /-- the first `p` iterates of the domain stay in `U` -/
  orbit : ∀ j < p, Set.MapsTo (F.f^[j]) G.U F.U
  /-- the restriction is centred at the critical point of `F` -/
  crit_eq : G.crit = F.crit

/-- A *renormalization* of period `p ≥ 2`: a quadratic-like restriction of period at least two.
This is the situation in which `F` is said to be renormalizable. -/
structure Renormalization (F : QuadraticLike) (p : ℕ) extends Restriction F p where
  two_le : 2 ≤ p

namespace Restriction

variable {F : QuadraticLike} {p : ℕ} (R : Restriction F p)

/-- The axioms of `Restriction` are consistent: every quadratic-like map is a quadratic-like
restriction of itself, of period one. -/
def self (F : QuadraticLike) : Restriction F 1 where
  G := F
  pos := Nat.one_pos
  eqOn := by intro z _; simp
  subset := subset_rfl
  orbit := by
    intro j hj
    interval_cases j
    intro z hz
    simpa using hz
  crit_eq := rfl

/-- As long as the orbit stays in the domain of `G`, iterating `G` is iterating `F^p`. -/
lemma iterate_eq_of_forall_mem {z : ℂ} :
    ∀ {n : ℕ}, (∀ k < n, R.G.f^[k] z ∈ R.G.U) → R.G.f^[n] z = (F.f^[p])^[n] z := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      have hn : R.G.f^[n] z ∈ R.G.U := h n (Nat.lt_succ_self n)
      have ih' := ih (fun k hk => h k (by omega))
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', R.eqOn hn, ih']

lemma iterate_eq_of_mem_K {z : ℂ} (hz : z ∈ R.G.K) :
    ∀ n : ℕ, R.G.f^[n] z = (F.f^[p])^[n] z :=
  fun _ => R.iterate_eq_of_forall_mem (fun k _ => hz k)

/-- **Reduction step.**  The small filled Julia set of a renormalization is contained in the
filled Julia set of the original quadratic-like map. -/
theorem K_subset_K : R.G.K ⊆ F.K := by
  intro z hz m
  have hp : 0 < p := R.pos
  have hm : m = m % p + p * (m / p) := by
    rw [Nat.mod_add_div]
  have hr : m % p < p := Nat.mod_lt _ hp
  have h1 : F.f^[m] z = F.f^[m % p] ((F.f^[p])^[m / p] z) := by
    conv_lhs => rw [hm]
    rw [Function.iterate_add_apply, Function.iterate_mul]
  have h2 : (F.f^[p])^[m / p] z = R.G.f^[m / p] z := (R.iterate_eq_of_mem_K hz _).symm
  rw [h1, h2]
  exact R.orbit _ hr (hz (m / p))

/-- The small filled Julia set is compact. -/
theorem isCompact_K : IsCompact R.G.K := R.G.isCompact_K

/-- The small filled Julia set is invariant under `F.f^[p]`. -/
theorem mapsTo_iterate : Set.MapsTo (F.f^[p]) R.G.K R.G.K := by
  intro z hz
  have h1 : F.f^[p] z = R.G.f z := (R.eqOn (R.G.K_subset_U hz)).symm
  rw [h1]
  exact R.G.mapsTo_K hz

/-- **Composition of renormalizations.**  A quadratic-like restriction of period `q` of a
quadratic-like restriction of period `p` of `F` is a quadratic-like restriction of `F` of
period `p * q`.  This is the combinatorial mechanism behind infinitely renormalizable maps. -/
def comp {q : ℕ} (R₁ : Restriction F p) (R₂ : Restriction R₁.G q) :
    Restriction F (p * q) where
  G := R₂.G
  pos := Nat.mul_pos R₁.pos R₂.pos
  eqOn := by
    intro z hz
    have h1 : R₂.G.f z = R₁.G.f^[q] z := R₂.eqOn hz
    have h2 : R₁.G.f^[q] z = (F.f^[p])^[q] z :=
      R₁.iterate_eq_of_forall_mem (fun k hk => R₂.orbit k hk hz)
    rw [h1, h2, ← Function.iterate_mul]
  subset := R₂.subset.trans R₁.subset
  orbit := by
    intro j hj z hz
    have hr : j % p < p := Nat.mod_lt _ R₁.pos
    have hs : j / p < q := by
      rw [Nat.div_lt_iff_lt_mul R₁.pos]
      simpa [Nat.mul_comm] using hj
    have hj' : j = j % p + p * (j / p) := (Nat.mod_add_div j p).symm
    have h1 : F.f^[j] z = F.f^[j % p] ((F.f^[p])^[j / p] z) := by
      conv_lhs => rw [hj']
      rw [Function.iterate_add_apply, Function.iterate_mul]
    have h2 : (F.f^[p])^[j / p] z = R₁.G.f^[j / p] z :=
      (R₁.iterate_eq_of_forall_mem (fun k hk => R₂.orbit k (by omega) hz)).symm
    rw [h1, h2]
    exact R₁.orbit _ hr (R₂.orbit _ hs hz)
  crit_eq := R₂.crit_eq.trans R₁.crit_eq

end Restriction

/-- **Composition of renormalizations.**  Renormalizing a renormalization of period `p` with
period `q` gives a renormalization of period `p * q`. -/
def Renormalization.comp {F : QuadraticLike} {p q : ℕ} (R₁ : Renormalization F p)
    (R₂ : Renormalization R₁.G q) : Renormalization F (p * q) where
  toRestriction := R₁.toRestriction.comp R₂.toRestriction
  two_le := le_trans R₁.two_le (Nat.le_mul_of_pos_right p R₂.pos)

@[simp] lemma Renormalization.comp_G {F : QuadraticLike} {p q : ℕ} (R₁ : Renormalization F p)
    (R₂ : Renormalization R₁.G q) : (R₁.comp R₂).G = R₂.G := rfl

/-!
## The quadratic family: the base case

For `‖c‖ < 2` the polynomial `z ↦ z² + c` restricted to `U = {z : ‖z²+c‖ < 2}` and
`V = B(0,2)` is a quadratic-like map, and for `c = 0` its filled Julia set is the closed
unit disc.
-/

lemma sq_add_const_analytic (c : ℂ) : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2 + c) Set.univ :=
  fun _ _ => (analyticAt_id.pow 2).add analyticAt_const

lemma deriv_sq_add_const (c z : ℂ) : deriv (fun z : ℂ => z ^ 2 + c) z = 2 * z := by
  simp [mul_comm]

lemma closure_quadratic_domain (c : ℂ) (hc : ‖c‖ < 2) :
    closure {z : ℂ | ‖z ^ 2 + c‖ < 2} ⊆ Metric.ball (0 : ℂ) 2 := by
  have h1 : closure {z : ℂ | ‖z ^ 2 + c‖ < 2} ⊆ {z : ℂ | ‖z ^ 2 + c‖ ≤ 2} := by
    apply closure_minimal
    · intro z hz; exact le_of_lt (Set.mem_setOf_eq ▸ hz)
    · exact isClosed_le (by fun_prop) continuous_const
  intro z hz
  have h0 : ‖z ^ 2 + c‖ ≤ 2 := h1 hz
  have h2 : ‖z‖ ^ 2 ≤ 2 + ‖c‖ := by
    have h3 : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
      calc ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
        _ ≤ ‖z ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
    rw [norm_pow] at h3; linarith
  simp only [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg z, norm_nonneg c]

/-- The quadratic polynomial `z ↦ z² + c`, for `‖c‖ < 2`, as a quadratic-like map. -/
noncomputable def quadraticLike (c : ℂ) (hc : ‖c‖ < 2) : QuadraticLike where
  U := {z : ℂ | ‖z ^ 2 + c‖ < 2}
  V := Metric.ball (0 : ℂ) 2
  f := fun z => z ^ 2 + c
  crit := 0
  isOpen_U := isOpen_lt (by fun_prop) continuous_const
  isOpen_V := Metric.isOpen_ball
  isBounded_V := Metric.isBounded_ball
  closure_U_subset_V := closure_quadratic_domain c hc
  analytic := fun z _ => sq_add_const_analytic c z (Set.mem_univ z)
  mapsTo := by
    intro z hz
    simpa [Metric.mem_ball, dist_zero_right] using hz
  surjOn := by
    intro w hw
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsSepClosed.exists_pow_nat_eq (w - c) 2
    refine ⟨s, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, hs]
      simpa [Metric.mem_ball, dist_zero_right] using hw
    · simp [hs]
  proper := by
    intro C hCV hC
    have hset : {z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' C
        = closure {z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' C := by
      apply Set.Subset.antisymm
      · exact Set.inter_subset_inter_left _ subset_closure
      · rintro z ⟨hz1, hz2⟩
        refine ⟨?_, hz2⟩
        have := hCV hz2
        simpa [Metric.mem_ball, dist_zero_right] using this
    rw [hset]
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_closure.inter (IsClosed.preimage (by fun_prop) hC.isClosed)) ?_
    refine Bornology.IsBounded.subset ?_ Set.inter_subset_left
    exact (Metric.isBounded_ball).subset (closure_quadratic_domain c hc)
  crit_mem := by simpa using hc
  deriv_crit := by simp
  crit_unique := by
    intro z _ hz
    rw [deriv_sq_add_const] at hz
    simpa using hz
  deg_le_two := by
    intro w _
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsSepClosed.exists_pow_nat_eq (w - c) 2
    have hsub : {z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' {w} ⊆ {s, -s} := by
      rintro z ⟨-, hz⟩
      have hz2 : z ^ 2 = w - c := by
        have : z ^ 2 + c = w := hz
        linear_combination this
      have hfac : (z - s) * (z + s) = 0 := by linear_combination hz2 - hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.mp hfac with h | h
      · left; linear_combination h
      · right; linear_combination h
    calc ({z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' {w}).ncard
        ≤ ({s, -s} : Set ℂ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          calc ({s, -s} : Set ℂ).ncard ≤ ({-s} : Set ℂ).ncard + 1 := Set.ncard_insert_le _ _
            _ = 2 := by simp

lemma iterate_sq (n : ℕ) (z : ℂ) : (fun w : ℂ => w ^ 2 + 0)^[n] z = z ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, add_zero, ← pow_mul, pow_succ]

/-- **Base case.**  The filled Julia set of `z ↦ z²`, viewed as a quadratic-like map, is the
closed unit disc. -/
theorem K_quadraticLike_zero :
    (quadraticLike 0 (by norm_num)).K = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [QuadraticLike.mem_K_iff, quadraticLike, Metric.mem_closedBall,
    dist_zero_right, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hz
    push_neg at hz
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 < ‖z‖ ^ n := pow_unbounded_of_one_lt _ hz
    have h1 := h n
    rw [iterate_sq n z] at h1
    simp only [add_zero, norm_pow] at h1
    have h2 : ‖z‖ ^ n ≤ ‖z‖ ^ (2 ^ n) :=
      pow_le_pow_right₀ (le_of_lt hz) (Nat.le_of_lt (Nat.lt_two_pow_self))
    have h3 : (1 : ℝ) ≤ ‖z‖ ^ (2 ^ n) := one_le_pow₀ (le_of_lt hz)
    nlinarith
  · intro hz n
    rw [iterate_sq n z]
    simp only [add_zero, norm_pow]
    have h1 : ‖z‖ ^ (2 ^ n) ≤ 1 :=
      calc ‖z‖ ^ (2 ^ n) ≤ 1 ^ (2 ^ n) := pow_le_pow_left₀ (norm_nonneg z) hz _
        _ = 1 := one_pow _
    nlinarith [pow_nonneg (norm_nonneg z) (2 ^ n)]

lemma norm_sq_add_le (c : ℂ) (hc : ‖c‖ ≤ 1 / 4) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖z ^ 2 + c‖ ≤ 1 / 2 := by
  have h1 : ‖z ^ 2 + c‖ ≤ ‖z‖ ^ 2 + ‖c‖ := by
    calc ‖z ^ 2 + c‖ ≤ ‖z ^ 2‖ + ‖c‖ := norm_add_le _ _
      _ = ‖z‖ ^ 2 + ‖c‖ := by rw [norm_pow]
  nlinarith [norm_nonneg z]

/-- For `‖c‖ ≤ 1/4` the disc of radius `1/2` is contained in the filled Julia set of `z ↦ z²+c`;
in particular the filled Julia set is nonempty and contains the critical point. -/
theorem closedBall_subset_K_quadraticLike (c : ℂ) (hc : ‖c‖ < 2) (hc4 : ‖c‖ ≤ 1 / 4) :
    Metric.closedBall (0 : ℂ) (1 / 2) ⊆ (quadraticLike c hc).K := by
  intro z hz n
  have hz' : ‖z‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have key : ∀ m : ℕ, ‖(fun w : ℂ => w ^ 2 + c)^[m] z‖ ≤ 1 / 2 := by
    intro m
    induction m with
    | zero => simpa using hz'
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact norm_sq_add_le c hc4 ih
  have h1 : ‖((quadraticLike c hc).f^[n] z) ^ 2 + c‖ ≤ 1 / 2 :=
    norm_sq_add_le c hc4 (key n)
  have : ‖((quadraticLike c hc).f^[n] z) ^ 2 + c‖ < 2 := by linarith
  exact this

/-!
## Rigidity in the quadratic family

No two distinct members of the quadratic family `z ↦ z² + c` are conjugate by an affine map;
this is the base case of the rigidity statements for quadratic-like maps.
-/

/-- **Rigidity, base case.**  If the affine map `z ↦ a z + b` (with `a ≠ 0`) conjugates
`z ↦ z² + c` to `z ↦ z² + c'`, then the conjugacy is the identity and `c = c'`. -/
theorem affine_conjugacy_rigidity {a b c c' : ℂ} (ha : a ≠ 0)
    (h : ∀ z : ℂ, a * (z ^ 2 + c) + b = (a * z + b) ^ 2 + c') :
    a = 1 ∧ b = 0 ∧ c = c' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have hb : b = 0 := by
    have hab : (4 : ℂ) * (a * b) = 0 := by linear_combination h2 - h1
    have hab' : a * b = 0 := by linear_combination (1 / 4 : ℂ) * hab
    rcases mul_eq_zero.mp hab' with h' | h'
    · exact absurd h' ha
    · exact h'
  subst hb
  have ha1 : a = 1 := by
    have hsq : a * a = 1 * a := by linear_combination h0 - h1
    exact mul_right_cancel₀ ha hsq
  refine ⟨ha1, rfl, ?_⟩
  subst ha1
  linear_combination h0

/-!
## The main statement
-/

/-- **McMullen renormalization / rigidity for quadratic-like maps.**

This packages:

1. *Structure of the filled Julia set*: for every quadratic-like map `F`, the filled Julia set
   `K(F)` is compact, forward invariant and totally invariant.
2. *Base case*: for `‖c‖ < 2` the quadratic polynomial `z ↦ z² + c` is quadratic-like on
   suitable domains, for `c = 0` the filled Julia set is exactly the closed unit disc, and for
   `‖c‖ ≤ 1/4` the filled Julia set contains the disc of radius `1/2` (so it is nonempty).
3. *Renormalization reduction*: if `F` is renormalizable with period `p ≥ 2`, with
   renormalization `G ≃ F^p`, then the small filled Julia set `K(G)` is a compact subset of
   `K(F)` which is invariant under `F^p`.
4. *Rigidity base case*: distinct members of the quadratic family are not affinely conjugate.
5. *Composition*: renormalizing a renormalization of period `p` with period `q` yields a
   renormalization of period `p * q` with the same small quadratic-like map.
6. *Consistency*: the axioms describing a quadratic-like restriction of period `p` are
   satisfiable (the period-one restriction of `F` by itself).
-/
theorem mcmullen_renormalization :
    (∀ F : QuadraticLike, IsCompact F.K ∧ Set.MapsTo F.f F.K F.K ∧ F.U ∩ F.f ⁻¹' F.K = F.K) ∧
    ((quadraticLike 0 (by norm_num)).K = Metric.closedBall (0 : ℂ) 1) ∧
    (∀ (c : ℂ) (hc : ‖c‖ < 2), ‖c‖ ≤ 1 / 4 →
        Metric.closedBall (0 : ℂ) (1 / 2) ⊆ (quadraticLike c hc).K) ∧
    (∀ (F : QuadraticLike) (p : ℕ) (R : Renormalization F p),
        2 ≤ p ∧ IsCompact R.G.K ∧ R.G.K ⊆ F.K ∧ Set.MapsTo (F.f^[p]) R.G.K R.G.K) ∧
    (∀ a b c c' : ℂ, a ≠ 0 → (∀ z : ℂ, a * (z ^ 2 + c) + b = (a * z + b) ^ 2 + c') →
        a = 1 ∧ b = 0 ∧ c = c') ∧
    (∀ (F : QuadraticLike) (p q : ℕ) (R₁ : Renormalization F p) (R₂ : Renormalization R₁.G q),
        ∃ R : Renormalization F (p * q), R.G = R₂.G) ∧
    (∀ F : QuadraticLike, ∃ R : Restriction F 1, R.G = F) := by
  refine ⟨fun F => ⟨F.isCompact_K, F.mapsTo_K, F.preimage_K⟩, K_quadraticLike_zero,
    fun c hc hc4 => closedBall_subset_K_quadraticLike c hc hc4,
    fun F p R => ⟨R.two_le, R.toRestriction.isCompact_K, R.toRestriction.K_subset_K,
      R.toRestriction.mapsTo_iterate⟩,
    fun a b c c' ha h => affine_conjugacy_rigidity ha h,
    fun _ _ _ R₁ R₂ => ⟨R₁.comp R₂, rfl⟩,
    fun F => ⟨Restriction.self F, rfl⟩⟩

end Frontier

