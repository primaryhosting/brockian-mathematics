/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a module
-- docstring before the `import` line; the same text is reproduced as the module docstring below.)

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

/-! ## Quadratic-like maps (Douady–Hubbard) -/

/-- A *quadratic-like map* in the sense of Douady–Hubbard: a proper degree-two
holomorphic branched covering `f : V → U` between two bounded, connected open subsets of `ℂ`
with `closure V ⊆ U`.

Degree two is encoded concretely: there is a (unique) critical point `c ∈ V` whose fibre is the
singleton `{c}`, and every other fibre over `U` consists of exactly two points. -/
structure QuadraticLike : Type where
  /-- The larger domain. -/
  U : Set ℂ
  /-- The smaller domain, compactly contained in `U`. -/
  V : Set ℂ
  /-- The map (defined on all of `ℂ`, but only its restriction to `V` matters). -/
  f : ℂ → ℂ
  /-- The critical point. -/
  c : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  closure_V_subset : closure V ⊆ U
  isBounded_V : Bornology.IsBounded V
  isPreconnected_U : IsPreconnected U
  isPreconnected_V : IsPreconnected V
  analyticOn : AnalyticOnNhd ℂ f V
  mapsTo : Set.MapsTo f V U
  surjOn : Set.SurjOn f V U
  /-- Properness of `f : V → U`. -/
  proper : ∀ L ⊆ U, IsCompact L → IsCompact (V ∩ f ⁻¹' L)
  crit_mem : c ∈ V
  /-- The critical fibre is a single point. -/
  crit_fiber : V ∩ f ⁻¹' {f c} = {c}
  /-- Every non-critical fibre has exactly two points: `f : V → U` has degree two. -/
  deg_two : ∀ w ∈ U, w ≠ f c → (V ∩ f ⁻¹' {w}).ncard = 2

namespace QuadraticLike

variable (F : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points of `V` whose whole forward
orbit stays in `V`. -/
def filledJulia : Set ℂ := {z : ℂ | ∀ n : ℕ, F.f^[n] z ∈ F.V}

/-- The tower of preimages `closure V ⊇ V ∩ f⁻¹(closure V) ⊇ ⋯` whose intersection is the
filled Julia set. -/
def preimTower : ℕ → Set ℂ
  | 0 => closure F.V
  | (n + 1) => F.V ∩ F.f ⁻¹' preimTower n

lemma nonempty_V : F.V.Nonempty := ⟨F.c, F.crit_mem⟩

lemma isCompact_closure_V : IsCompact (closure F.V) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure F.isBounded_V.closure

lemma V_subset_closure : F.V ⊆ closure F.V := subset_closure

lemma V_subset_U : F.V ⊆ F.U := F.V_subset_closure.trans F.closure_V_subset

lemma preimTower_subset_U : ∀ n : ℕ, F.preimTower n ⊆ F.U
  | 0 => F.closure_V_subset
  | (_ + 1) => (Set.inter_subset_left).trans F.V_subset_U

lemma isCompact_preimTower : ∀ n : ℕ, IsCompact (F.preimTower n) := by
  intro n
  induction n with
  | zero => exact F.isCompact_closure_V
  | succ n ih => exact F.proper _ (F.preimTower_subset_U n) ih

lemma preimTower_antitone : ∀ n : ℕ, F.preimTower (n + 1) ⊆ F.preimTower n := by
  intro n
  induction n with
  | zero => intro z hz; exact F.V_subset_closure hz.1
  | succ n ih => intro z hz; exact ⟨hz.1, ih hz.2⟩

lemma nonempty_preimTower : ∀ n : ℕ, (F.preimTower n).Nonempty := by
  intro n
  induction n with
  | zero => exact F.nonempty_V.mono F.V_subset_closure
  | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨z, hzV, hz⟩ := F.surjOn (F.preimTower_subset_U n hx)
      exact ⟨z, hzV, by simpa [hz] using hx⟩

lemma mem_preimTower : ∀ (n : ℕ) (z : ℂ),
    z ∈ F.preimTower n ↔ ((∀ k < n, F.f^[k] z ∈ F.V) ∧ F.f^[n] z ∈ closure F.V) := by
  intro n
  induction n with
  | zero => intro z; simp [preimTower]
  | succ n ih =>
      intro z
      rw [preimTower, Set.mem_inter_iff, Set.mem_preimage, ih (F.f z)]
      simp only [← Function.iterate_succ_apply]
      constructor
      · rintro ⟨hzV, hall, hlast⟩
        refine ⟨?_, hlast⟩
        intro k hk
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simpa using hzV
        · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          exact hall j (by omega)
      · rintro ⟨hall, hlast⟩
        exact ⟨by simpa using hall 0 (Nat.succ_pos n), fun k hk => hall (k + 1) (by omega), hlast⟩

lemma filledJulia_eq_iInter : F.filledJulia = ⋂ n : ℕ, F.preimTower (n + 1) := by
  ext z
  simp only [Set.mem_iInter, filledJulia, Set.mem_setOf_eq, F.mem_preimTower]
  constructor
  · intro h n
    exact ⟨fun k _ => h k, F.V_subset_closure (h (n + 1))⟩
  · intro h n
    exact (h n).1 n (Nat.lt_succ_self n)

lemma filledJulia_subset_V : F.filledJulia ⊆ F.V := fun _ hz => by simpa using hz 0

/-- The filled Julia set is compact. -/
theorem isCompact_filledJulia : IsCompact F.filledJulia := by
  rw [F.filledJulia_eq_iInter]
  refine IsCompact.of_isClosed_subset (F.isCompact_preimTower 1) ?_ (Set.iInter_subset _ 0)
  exact isClosed_iInter fun n => (F.isCompact_preimTower (n + 1)).isClosed

/-- The filled Julia set is nonempty. -/
theorem nonempty_filledJulia : F.filledJulia.Nonempty := by
  rw [F.filledJulia_eq_iInter]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun i => F.preimTower_antitone (i + 1)) (fun i => F.nonempty_preimTower (i + 1))
    (F.isCompact_preimTower 1) (fun i => (F.isCompact_preimTower (i + 1)).isClosed)

/-- The filled Julia set is completely invariant inside `V`. -/
theorem filledJulia_eq_preimage : F.filledJulia = F.V ∩ F.f ⁻¹' F.filledJulia := by
  ext z
  simp only [filledJulia, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun n => by simpa [Function.iterate_succ_apply] using h (n + 1)⟩
  · rintro ⟨hzV, h⟩ n
    cases n with
    | zero => simpa using hzV
    | succ n => simpa [Function.iterate_succ_apply] using h n

/-- The filled Julia set is forward invariant. -/
theorem mapsTo_filledJulia : Set.MapsTo F.f F.filledJulia F.filledJulia := by
  intro z hz
  have := F.filledJulia_eq_preimage ▸ hz
  exact this.2

end QuadraticLike

/-! ## Renormalization -/

open QuadraticLike

/-- `G` is an *`n`-th renormalization* of `F` (`n ≥ 1`): `G` is a quadratic-like restriction of
`F.f^[n]` around the same critical point, whose domain has its first `n` forward iterates inside
`F.V`, and whose filled Julia set is connected. -/
def IsRenormalization (F : QuadraticLike) (n : ℕ) (G : QuadraticLike) : Prop :=
  1 ≤ n ∧
  G.V ⊆ F.V ∧
  G.c = F.c ∧
  Set.EqOn G.f (F.f^[n]) G.V ∧
  (∀ k < n, Set.MapsTo (F.f^[k]) G.V F.V) ∧
  IsConnected G.filledJulia

/-- `F` is `n`-renormalizable. -/
def Renormalizable (F : QuadraticLike) (n : ℕ) : Prop := ∃ G : QuadraticLike, IsRenormalization F n G

/-- `F` is infinitely renormalizable: it admits renormalizations of arbitrarily large level. -/
def InfinitelyRenormalizable (F : QuadraticLike) : Prop := ∀ N : ℕ, ∃ n ≥ N, Renormalizable F n

/-- Base case of renormalization: a quadratic-like map with connected filled Julia set is
`1`-renormalizable, renormalized by itself. -/
theorem isRenormalization_one (F : QuadraticLike) (h : IsConnected F.filledJulia) :
    IsRenormalization F 1 F := by
  refine ⟨le_refl 1, subset_rfl, rfl, ?_, ?_, h⟩
  · intro x _
    simp
  · intro k hk
    interval_cases k
    simpa using Set.mapsTo_id F.V

/-- Auxiliary: along an orbit staying in `G.V`, iterates of `G.f` agree with iterates of
`F.f^[n]`. -/
lemma iterate_eq_of_orbit_mem {F G : QuadraticLike} {n : ℕ} (hEq : Set.EqOn G.f (F.f^[n]) G.V)
    {z : ℂ} {m : ℕ} (hz : ∀ j < m, G.f^[j] z ∈ G.V) :
    G.f^[m] z = (F.f^[n])^[m] z := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmem : G.f^[m] z ∈ G.V := hz m (Nat.lt_succ_self m)
      have ih' := ih fun j hj => hz j (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hEq hmem, ih']

/-- The filled Julia set of a renormalization is contained in the filled Julia set. -/
theorem filledJulia_subset_of_isRenormalization {F G : QuadraticLike} {n : ℕ}
    (h : IsRenormalization F n G) : G.filledJulia ⊆ F.filledJulia := by
  obtain ⟨hn, _hVsub, _hc, hEq, horb, _hconn⟩ := h
  intro z hz M
  have hzV : ∀ j : ℕ, G.f^[j] z ∈ G.V := hz
  have hkey : F.f^[n * (M / n)] z = G.f^[M / n] z := by
    rw [Function.iterate_mul]
    exact (iterate_eq_of_orbit_mem hEq (fun j _ => hzV j)).symm
  have hMsplit : M % n + n * (M / n) = M := Nat.mod_add_div M n
  have : F.f^[M] z = F.f^[M % n] (G.f^[M / n] z) := by
    conv_lhs => rw [← hMsplit]
    rw [Function.iterate_add_apply, hkey]
  rw [this]
  exact horb (M % n) (Nat.mod_lt _ (by omega)) (hzV (M / n))

/-- Renormalizations compose: an `m`-th renormalization of an `n`-th renormalization of `F` is an
`(n*m)`-th renormalization of `F`. -/
theorem IsRenormalization.comp {F G H : QuadraticLike} {n m : ℕ}
    (h₁ : IsRenormalization F n G) (h₂ : IsRenormalization G m H) :
    IsRenormalization F (n * m) H := by
  obtain ⟨hn, hVGF, hcG, hEqG, horbG, _⟩ := h₁
  obtain ⟨hm, hVHG, hcH, hEqH, horbH, hconnH⟩ := h₂
  have hstep : ∀ z ∈ H.V, ∀ q ≤ m, G.f^[q] z = (F.f^[n])^[q] z := by
    intro z hz q hq
    refine iterate_eq_of_orbit_mem hEqG ?_
    intro j hj
    exact horbH j (by omega) hz
  refine ⟨Nat.one_le_iff_ne_zero.2 (by positivity), hVHG.trans hVGF, hcH.trans hcG, ?_, ?_, hconnH⟩
  · intro z hz
    rw [hEqH hz, hstep z hz m le_rfl, ← Function.iterate_mul]
  · intro K hK z hz
    have hnpos : 0 < n := hn
    have hq : K / n < m := Nat.div_lt_of_lt_mul (by omega)
    have hkey : F.f^[n * (K / n)] z = G.f^[K / n] z := by
      rw [Function.iterate_mul]
      exact (hstep z hz (K / n) hq.le).symm
    have hsplit : K % n + n * (K / n) = K := Nat.mod_add_div K n
    have hz' : G.f^[K / n] z ∈ G.V := horbH (K / n) hq hz
    have : F.f^[K] z = F.f^[K % n] (G.f^[K / n] z) := by
      conv_lhs => rw [← hsplit]
      rw [Function.iterate_add_apply, hkey]
    rw [this]
    exact horbG (K % n) (Nat.mod_lt _ hnpos) hz'

/-- A tower of renormalizations of levels `≥ 2` makes `F` infinitely renormalizable. -/
theorem infinitelyRenormalizable_of_tower (Fs : ℕ → QuadraticLike) (lev : ℕ → ℕ)
    (h2 : ∀ i, 2 ≤ lev i) (hren : ∀ i, IsRenormalization (Fs i) (lev i) (Fs (i + 1))) :
    InfinitelyRenormalizable (Fs 0) := by
  have key : ∀ i : ℕ, ∃ n ≥ i + 1, IsRenormalization (Fs 0) n (Fs (i + 1)) := by
    intro i
    induction i with
    | zero => exact ⟨lev 0, by have := h2 0; omega, hren 0⟩
    | succ i ih =>
        obtain ⟨n, hn, hR⟩ := ih
        refine ⟨n * lev (i + 1), ?_, hR.comp (hren (i + 1))⟩
        have h2' := h2 (i + 1)
        calc i + 2 ≤ n * 2 := by omega
          _ ≤ n * lev (i + 1) := Nat.mul_le_mul_left n h2'
  intro N
  obtain ⟨n, hn, hR⟩ := key N
  exact ⟨n, by omega, ⟨Fs (N + 1), hR⟩⟩

/-! ## Rigidity: conjugacies transport filled Julia sets -/

/-- `h` conjugates the quadratic-like map `F` to the quadratic-like map `G`: it is a bijection
`F.U → G.U` restricting to a bijection `F.V → G.V` and intertwining the two dynamics on `F.V`. -/
def IsConjugacy (F G : QuadraticLike) (h : ℂ → ℂ) : Prop :=
  Set.BijOn h F.U G.U ∧ Set.BijOn h F.V G.V ∧ ∀ z ∈ F.V, h (F.f z) = G.f (h z)

/-- A conjugacy intertwines all iterates along orbits that stay in `F.V`. -/
lemma iterate_conj {F G : QuadraticLike} {h : ℂ → ℂ} (hc : IsConjugacy F G h) {z : ℂ} :
    ∀ n : ℕ, (∀ k < n, F.f^[k] z ∈ F.V) → h (F.f^[n] z) = G.f^[n] (h z) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hall
      have hmem : F.f^[n] z ∈ F.V := hall n (Nat.lt_succ_self n)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        hc.2.2 _ hmem, ih fun k hk => hall k (by omega)]

/-- **Rigidity of the filled Julia set under conjugacy.** A conjugacy between two quadratic-like
maps carries the filled Julia set of one onto the filled Julia set of the other. -/
theorem filledJulia_image_of_isConjugacy {F G : QuadraticLike} {h : ℂ → ℂ}
    (hc : IsConjugacy F G h) : h '' F.filledJulia = G.filledJulia := by
  obtain ⟨hU, hV, hcomm⟩ := hc
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩ n
    have : h (F.f^[n] z) = G.f^[n] (h z) :=
      iterate_conj ⟨hU, hV, hcomm⟩ n fun k _ => hz k
    rw [← this]
    exact hV.mapsTo (hz n)
  · intro w hw
    obtain ⟨z, hzV, rfl⟩ := hV.surjOn (by simpa using hw 0)
    have key : ∀ n : ℕ, ∀ k ≤ n, F.f^[k] z ∈ F.V := by
      intro n
      induction n with
      | zero => intro k hk; interval_cases k; simpa using hzV
      | succ n ih =>
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk' | rfl
          · exact ih k (by omega)
          · have hiter : h (F.f^[n + 1] z) = G.f^[n + 1] (h z) :=
              iterate_conj ⟨hU, hV, hcomm⟩ (n + 1) fun j hj => ih j (by omega)
            have hmemG : G.f^[n + 1] (h z) ∈ G.V := hw (n + 1)
            obtain ⟨y, hyV, hy⟩ := hV.surjOn (by rw [← hiter] at hmemG; exact hmemG)
            have hzU : F.f^[n + 1] z ∈ F.U := by
              rw [Function.iterate_succ_apply']
              exact F.mapsTo (ih n le_rfl)
            have : F.f^[n + 1] z = y :=
              hU.injOn hzU (F.V_subset_U hyV) (by rw [hy])
            rw [this]
            exact hyV
    exact ⟨z, fun n => key n n le_rfl, rfl⟩

/-! ## A concrete quadratic-like map: the squaring map -/

/-- Iterates of the squaring map. -/
lemma iterate_sq (n : ℕ) (z : ℂ) : (fun w : ℂ => w ^ 2)^[n] z = z ^ (2 ^ n) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih z, ← pow_mul, pow_succ]

/-- The squaring map `z ↦ z²` as a quadratic-like map on `V = B(0,2)`, `U = B(0,4)`. -/
def sq : QuadraticLike where
  U := Metric.ball 0 4
  V := Metric.ball 0 2
  f := fun z => z ^ 2
  c := 0
  isOpen_U := Metric.isOpen_ball
  isOpen_V := Metric.isOpen_ball
  closure_V_subset := by
    refine Metric.closure_ball_subset_closedBall.trans ?_
    intro z hz
    simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at *
    linarith
  isBounded_V := Metric.isBounded_ball
  isPreconnected_U := (convex_ball (0 : ℂ) 4).isPreconnected
  isPreconnected_V := (convex_ball (0 : ℂ) 2).isPreconnected
  analyticOn := by
    intro z _
    exact (analyticAt_id (𝕜 := ℂ) (z := z)).pow 2
  mapsTo := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right, norm_pow] at *
    nlinarith [norm_nonneg z]
  surjOn := by
    intro w hw
    simp only [Metric.mem_ball, dist_zero_right] at hw
    refine ⟨w ^ ((2 : ℕ) : ℂ)⁻¹, ?_, ?_⟩
    · have h : (w ^ ((2 : ℕ) : ℂ)⁻¹) ^ (2 : ℕ) = w := Complex.cpow_ofNat_inv_pow w 2
      have hn : ‖w ^ ((2 : ℕ) : ℂ)⁻¹‖ ^ 2 = ‖w‖ := by rw [← norm_pow, h]
      simp only [Metric.mem_ball, dist_zero_right]
      nlinarith [norm_nonneg (w ^ ((2 : ℕ) : ℂ)⁻¹)]
    · exact Complex.cpow_ofNat_inv_pow w 2
  proper := by
    intro L hL hLc
    have heq : Metric.ball (0 : ℂ) 2 ∩ (fun z : ℂ => z ^ 2) ⁻¹' L
        = Metric.closedBall (0 : ℂ) 2 ∩ (fun z : ℂ => z ^ 2) ⁻¹' L := by
      refine Set.Subset.antisymm (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall) ?_
      rintro z ⟨hz1, hz2⟩
      refine ⟨?_, hz2⟩
      have hz3 := hL hz2
      simp only [Metric.mem_ball, dist_zero_right, norm_pow] at hz3
      simp only [Metric.mem_closedBall, dist_zero_right] at hz1
      simp only [Metric.mem_ball, dist_zero_right]
      nlinarith [norm_nonneg z]
    rw [heq]
    exact (isCompact_closedBall _ _).inter_right (hLc.isClosed.preimage (by fun_prop))
  crit_mem := by simp
  crit_fiber := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball,
      dist_zero_right]
    constructor
    · rintro ⟨-, h⟩
      simpa using h
    · rintro rfl
      norm_num
  deg_two := by
    intro w hw hw0
    simp only [Metric.mem_ball, dist_zero_right] at hw
    have hw0' : w ≠ 0 := by simpa using hw0
    set s : ℂ := w ^ ((2 : ℕ) : ℂ)⁻¹ with hs
    have hs2 : s ^ (2 : ℕ) = w := Complex.cpow_ofNat_inv_pow w 2
    have hsnorm : ‖s‖ < 2 := by
      have : ‖s‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hs2]
      nlinarith [norm_nonneg s]
    have hsne : s ≠ 0 := by
      intro h
      apply hw0'
      rw [← hs2, h]
      ring
    have hset : Metric.ball (0 : ℂ) 2 ∩ (fun z : ℂ => z ^ 2) ⁻¹' {w} = {s, -s} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball,
        dist_zero_right, Set.mem_insert_iff]
      constructor
      · rintro ⟨-, h⟩
        have hfac : (z - s) * (z + s) = 0 := by
          rw [← hs2] at h
          linear_combination h
        rcases mul_eq_zero.1 hfac with h1 | h1
        · left; linear_combination h1
        · right; linear_combination h1
      · rintro (rfl | rfl)
        · exact ⟨hsnorm, hs2⟩
        · refine ⟨by simpa using hsnorm, ?_⟩
          rw [← hs2]; ring
    rw [hset]
    refine Set.ncard_pair ?_
    intro h
    apply hsne
    have h2 : (2 : ℂ) * s = 0 := by linear_combination h
    simpa using h2

/-- The filled Julia set of the squaring map is the closed unit disc. -/
theorem filledJulia_sq : sq.filledJulia = Metric.closedBall (0 : ℂ) 1 := by
  have hf : sq.f = fun w : ℂ => w ^ 2 := rfl
  have hV : sq.V = Metric.ball (0 : ℂ) 2 := rfl
  ext z
  simp only [QuadraticLike.filledJulia, Set.mem_setOf_eq, hf, hV, iterate_sq,
    Metric.mem_ball, Metric.mem_closedBall, dist_zero_right, norm_pow]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R := ℝ) 2 hc
    have h1 : ‖z‖ ^ k ≤ ‖z‖ ^ (2 ^ k) := pow_le_pow_right₀ hc.le (Nat.lt_two_pow_self).le
    have h2 := h k
    linarith
  · intro h n
    have : ‖z‖ ^ (2 ^ n) ≤ 1 := pow_le_one₀ (norm_nonneg z) h
    linarith

/-- The squaring map has connected filled Julia set, hence is `1`-renormalizable. -/
theorem renormalizable_sq : Renormalizable sq 1 := by
  refine ⟨sq, isRenormalization_one sq ?_⟩
  rw [filledJulia_sq]
  exact ⟨⟨0, by simp⟩, (convex_closedBall (0 : ℂ) 1).isPreconnected⟩

/-! ## Main statement -/

/-- **McMullen renormalization / rigidity package for quadratic-like maps.**

Formalized statements, all proved:

* the filled Julia set of a quadratic-like map is a nonempty compact set, completely invariant
  in `V` and forward invariant;
* (base case) a quadratic-like map with connected filled Julia set is `1`-renormalizable;
* the filled Julia set of an `n`-th renormalization is contained in that of the original map;
* renormalizations compose: renormalizing an `n`-th renormalization at level `m` gives an
  `(n*m)`-th renormalization — the reduction underlying infinite renormalization;
* a tower of renormalizations of levels `≥ 2` yields an infinitely renormalizable map;
* (rigidity) a conjugacy between quadratic-like maps carries filled Julia set onto filled
  Julia set;
* the class of quadratic-like maps is nonempty: the squaring map `z ↦ z²` on `B(0,2) → B(0,4)`
  is quadratic-like with filled Julia set the closed unit disc, hence renormalizable. -/
theorem mcmullen_renormalization :
    (∀ F : QuadraticLike,
        IsCompact F.filledJulia ∧ F.filledJulia.Nonempty ∧
        F.filledJulia = F.V ∩ F.f ⁻¹' F.filledJulia ∧
        Set.MapsTo F.f F.filledJulia F.filledJulia) ∧
    (∀ F : QuadraticLike, IsConnected F.filledJulia → Renormalizable F 1) ∧
    (∀ (F G : QuadraticLike) (n : ℕ), IsRenormalization F n G →
        G.filledJulia ⊆ F.filledJulia) ∧
    (∀ (F G H : QuadraticLike) (n m : ℕ), IsRenormalization F n G → IsRenormalization G m H →
        IsRenormalization F (n * m) H) ∧
    (∀ (Fs : ℕ → QuadraticLike) (lev : ℕ → ℕ), (∀ i, 2 ≤ lev i) →
        (∀ i, IsRenormalization (Fs i) (lev i) (Fs (i + 1))) →
        InfinitelyRenormalizable (Fs 0)) ∧
    (∀ (F G : QuadraticLike) (h : ℂ → ℂ), IsConjugacy F G h →
        h '' F.filledJulia = G.filledJulia) ∧
    (sq.filledJulia = Metric.closedBall (0 : ℂ) 1 ∧ Renormalizable sq 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    exact ⟨F.isCompact_filledJulia, F.nonempty_filledJulia, F.filledJulia_eq_preimage,
      F.mapsTo_filledJulia⟩
  · intro F h
    exact ⟨F, isRenormalization_one F h⟩
  · intro F G n h
    exact filledJulia_subset_of_isRenormalization h
  · intro F G H n m h₁ h₂
    exact h₁.comp h₂
  · intro Fs lev h2 hren
    exact infinitelyRenormalizable_of_tower Fs lev h2 hren
  · intro F G h hc
    exact filledJulia_image_of_isConjugacy hc
  · exact ⟨filledJulia_sq, renormalizable_sq⟩

end Frontier

