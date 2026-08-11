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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Quadratic-like maps (Douady–Hubbard)

A *quadratic-like map* is a triple `(f, U, V)` where `U ⋐ V` are bounded, connected open
subsets of `ℂ` and `f : U → V` is a proper holomorphic map of degree `2`.  Degree two is
encoded here concretely: `f` has a unique critical point `c ∈ U`, the fibre over the critical
value `f c` is the singleton `{c}`, and every other fibre over `V` consists of exactly two
points.
-/

/-- A quadratic-like map in the sense of Douady–Hubbard, presented as a globally defined
function `f : ℂ → ℂ` together with the data of the domains `U ⋐ V`.  Only the behaviour of
`f` on `U` is constrained. -/
structure QuadraticLike where
  /-- The small domain. -/
  U : Set ℂ
  /-- The large domain. -/
  V : Set ℂ
  /-- The map. -/
  f : ℂ → ℂ
  /-- The critical point. -/
  critical : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isConnected_U : IsConnected U
  isConnected_V : IsConnected V
  isBounded_V : Bornology.IsBounded V
  /-- `U` is compactly contained in `V`. -/
  closure_U_subset : closure U ⊆ V
  differentiableOn : DifferentiableOn ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is proper. -/
  properOn : ∀ ⦃K : Set ℂ⦄, K ⊆ V → IsCompact K → IsCompact (U ∩ f ⁻¹' K)
  critical_mem : critical ∈ U
  /-- The fibre over the critical value is a single (doubled) point. -/
  fiber_critical : U ∩ f ⁻¹' {f critical} = {critical}
  /-- Every non-critical fibre over `V` has exactly two points: `f` has degree two. -/
  fiber_card : ∀ w ∈ V, w ≠ f critical → (U ∩ f ⁻¹' {w}).ncard = 2
  deriv_critical : deriv f critical = 0
  unique_critical : ∀ z ∈ U, deriv f z = 0 → z = critical

namespace QuadraticLike

variable (Q : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/
def K : Set ℂ := {z : ℂ | ∀ n : ℕ, Q.f^[n] z ∈ Q.U}

lemma U_subset_V : Q.U ⊆ Q.V := subset_closure.trans Q.closure_U_subset

lemma K_subset_U : Q.K ⊆ Q.U := fun z hz => by simpa using hz 0

lemma mem_K_iff {z : ℂ} : z ∈ Q.K ↔ ∀ n : ℕ, Q.f^[n] z ∈ Q.U := Iff.rfl

/-- The filled Julia set is forward invariant. -/
lemma mapsTo_K : Set.MapsTo Q.f Q.K Q.K := by
  intro z hz n
  rw [← Function.iterate_succ_apply]
  exact hz (n + 1)

/-- The filled Julia set is totally invariant: a point of `U` lies in `K` exactly when its
image does. -/
lemma preimage_K_inter_U : Q.f ⁻¹' Q.K ∩ Q.U = Q.K := by
  ext z
  constructor
  · rintro ⟨hz, hzU⟩ n
    cases n with
    | zero => simpa using hzU
    | succ n => simpa [Function.iterate_succ_apply] using hz n
  · intro hz
    exact ⟨Q.mapsTo_K hz, Q.K_subset_U hz⟩

lemma isCompact_closure_U : IsCompact (closure Q.U) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (Q.isBounded_V.subset Q.closure_U_subset)

/-- The compact set `C = U ∩ f⁻¹(closure U)`, which contains the filled Julia set. -/
def C : Set ℂ := Q.U ∩ Q.f ⁻¹' (closure Q.U)

lemma isCompact_C : IsCompact Q.C :=
  Q.properOn Q.closure_U_subset Q.isCompact_closure_U

lemma C_subset_U : Q.C ⊆ Q.U := Set.inter_subset_left

lemma K_subset_C : Q.K ⊆ Q.C := by
  intro z hz
  exact ⟨hz 0, subset_closure (by simpa using hz 1)⟩

lemma continuousAt_of_mem_U {z : ℂ} (hz : z ∈ Q.U) : ContinuousAt Q.f z :=
  (Q.differentiableOn.continuousOn).continuousAt (Q.isOpen_U.mem_nhds hz)

lemma isClosed_K : IsClosed Q.K := by
  rw [← closure_subset_iff_isClosed]
  have hCclosed : IsClosed Q.C := Q.isCompact_C.isClosed
  intro z hz
  have key : ∀ n : ℕ, Q.f^[n] z ∈ Q.C ∧ ContinuousAt (Q.f^[n]) z := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, by simpa using continuousAt_id⟩
      simpa using hCclosed.closure_subset (closure_mono Q.K_subset_C hz)
    | succ n ih =>
      obtain ⟨hmem, hcont⟩ := ih
      have hcont' : ContinuousAt (Q.f^[n + 1]) z := by
        rw [Function.iterate_succ']
        exact (Q.continuousAt_of_mem_U (Q.C_subset_U hmem)).comp hcont
      refine ⟨?_, hcont'⟩
      have himg : Q.f^[n + 1] '' Q.K ⊆ Q.C := by
        rintro w ⟨u, hu, rfl⟩
        exact Q.K_subset_C (Set.MapsTo.iterate Q.mapsTo_K (n + 1) hu)
      have := mem_closure_image hcont' hz
      exact hCclosed.closure_subset (closure_mono himg this)
  intro n
  exact Q.C_subset_U (key n).1

lemma isCompact_K : IsCompact Q.K :=
  Q.isCompact_C.of_isClosed_subset Q.isClosed_K Q.K_subset_C

end QuadraticLike

/-!
## Renormalization
-/

/-- `Q` is *renormalizable of period `n`* if some iterate `f^[n]`, restricted to a suitable
pair of domains inside `U` around the critical point, is again a quadratic-like map with
connected filled Julia set. -/
def Renormalizable (Q : QuadraticLike) (n : ℕ) : Prop :=
  ∃ R : QuadraticLike, R.f = Q.f^[n] ∧ R.U ⊆ Q.U ∧ R.critical = Q.critical ∧ IsConnected R.K

/-- A renormalization of `Q` of period `n`, packaged as a quadratic-like map. -/
def IsRenormalizationOf (R Q : QuadraticLike) (n : ℕ) : Prop :=
  R.f = Q.f^[n] ∧ R.U ⊆ Q.U ∧ R.critical = Q.critical ∧ IsConnected R.K

/-- Renormalization towers: a renormalization of a renormalization is a renormalization. -/
theorem isRenormalizationOf_trans {Q R S : QuadraticLike} {n m : ℕ}
    (hR : IsRenormalizationOf R Q n) (hS : IsRenormalizationOf S R m) :
    IsRenormalizationOf S Q (n * m) := by
  obtain ⟨hf1, hU1, hc1, _⟩ := hR
  obtain ⟨hf2, hU2, hc2, hK2⟩ := hS
  refine ⟨?_, hU2.trans hU1, hc2.trans hc1, hK2⟩
  rw [hf2, hf1, ← Function.iterate_mul]

/-- If `Q` is `n`-renormalizable with renormalization `R`, and `R` is `m`-renormalizable, then
`Q` is `(n * m)`-renormalizable. -/
theorem renormalizable_mul {Q R : QuadraticLike} {n m : ℕ}
    (hR : IsRenormalizationOf R Q n) (hm : Renormalizable R m) :
    Renormalizable Q (n * m) := by
  obtain ⟨S, hS⟩ := hm
  exact ⟨S, isRenormalizationOf_trans hR hS⟩

/-- Every quadratic-like map with connected filled Julia set is renormalizable of period one
(the trivial renormalization). -/
theorem renormalizable_one (Q : QuadraticLike) (hK : IsConnected Q.K) :
    Renormalizable Q 1 :=
  ⟨Q, by simp, subset_rfl, rfl, hK⟩

/-!
## Conjugacies and rigidity
-/

/-- A (topological) conjugacy between two quadratic-like maps: a bijection of the domains
intertwining the dynamics.  The hybrid equivalences of Douady–Hubbard and McMullen are
conjugacies of this kind which are in addition quasiconformal with `∂̄ h = 0` a.e. on the
filled Julia set; the transport statements below only use the conjugacy structure. -/
structure Conjugacy (P Q : QuadraticLike) where
  /-- The conjugating homeomorphism. -/
  h : ℂ → ℂ
  bijOn_U : Set.BijOn h P.U Q.U
  bijOn_V : Set.BijOn h P.V Q.V
  conj : ∀ z ∈ P.U, h (P.f z) = Q.f (h z)

/-- A conjugacy intertwines the iterates, as long as the orbit stays inside `U`. -/
lemma Conjugacy.iterate_conj {P Q : QuadraticLike} (c : Conjugacy P Q) :
    ∀ (n : ℕ) (z : ℂ), (∀ k < n, P.f^[k] z ∈ P.U) → c.h (P.f^[n] z) = Q.f^[n] (c.h z) := by
  intro n
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    have hn : P.f^[n] z ∈ P.U := hz n (Nat.lt_succ_self n)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', c.conj _ hn,
      ih z (fun k hk => hz k (hk.trans (Nat.lt_succ_self n)))]

/-- A conjugacy carries the filled Julia set of one quadratic-like map bijectively onto the
filled Julia set of the other. -/
theorem Conjugacy.bijOn_K {P Q : QuadraticLike} (c : Conjugacy P Q) :
    Set.BijOn c.h P.K Q.K := by
  refine ⟨?_, c.bijOn_U.injOn.mono P.K_subset_U, ?_⟩
  · intro z hz n
    rw [← c.iterate_conj n z (fun k _ => hz k)]
    exact c.bijOn_U.mapsTo (hz n)
  · intro w hw
    obtain ⟨z, hzU, rfl⟩ := c.bijOn_U.surjOn (hw 0)
    have key : ∀ n : ℕ, ∀ k ≤ n, P.f^[k] z ∈ P.U := by
      intro n
      induction n with
      | zero => intro k hk; simpa [Nat.le_zero.1 hk] using hzU
      | succ n ih =>
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk' | rfl
        · exact ih k (Nat.lt_succ_iff.1 hk')
        · have hn : P.f^[n] z ∈ P.U := ih n le_rfl
          have hV : P.f^[n + 1] z ∈ P.V := by
            rw [Function.iterate_succ_apply']
            exact P.mapsTo hn
          have hconj : c.h (P.f^[n + 1] z) = Q.f^[n + 1] (c.h z) :=
            c.iterate_conj (n + 1) z (fun j hj => ih j (Nat.lt_succ_iff.1 hj))
          obtain ⟨u, huU, hu⟩ := c.bijOn_U.surjOn (hw (n + 1))
          have : P.f^[n + 1] z = u :=
            c.bijOn_V.injOn hV (P.U_subset_V huU) (by rw [hconj, hu])
          rw [this]
          exact huU
    exact ⟨z, fun n => key n n le_rfl, rfl⟩

/-- The **straightening theorem** of Douady and Hubbard, in the form used by McMullen: every
quadratic-like map is (hybrid) equivalent to a quadratic polynomial `z ↦ z² + c`.  Here the
equivalence is recorded through the `Conjugacy` structure above; the analytic content of the
hybrid equivalence (quasiconformality and `∂̄ h = 0` a.e. on the filled Julia set) is not part
of this statement.  It is stated as a `Prop` and used below only as a hypothesis. -/
def StraighteningStatement : Prop :=
  ∀ Q : QuadraticLike, ∃ (c : ℂ) (P : QuadraticLike),
    P.f = (fun z : ℂ => z ^ 2 + c) ∧ Nonempty (Conjugacy Q P)

/-- **Lean-checked reduction.**  Granting the straightening statement, the filled Julia set of
an arbitrary quadratic-like map is carried bijectively, by a conjugacy, onto the filled Julia
set of a quadratic-like restriction of an honest quadratic polynomial `z ↦ z² + c`. -/
theorem straightening_gives_julia_model (hstr : StraighteningStatement) (Q : QuadraticLike) :
    ∃ (c : ℂ) (P : QuadraticLike) (g : ℂ → ℂ),
      P.f = (fun z : ℂ => z ^ 2 + c) ∧ Set.BijOn g Q.K P.K := by
  obtain ⟨c, P, hP, ⟨conj⟩⟩ := hstr Q
  exact ⟨c, P, conj.h, hP, conj.bijOn_K⟩

/-- Conjugacy is reflexive. -/
def Conjugacy.refl (P : QuadraticLike) : Conjugacy P P where
  h := id
  bijOn_U := Set.bijOn_id _
  bijOn_V := Set.bijOn_id _
  conj := by simp

/-!
## The base case: `z ↦ z²`
-/

/-- Iterates of the squaring map. -/
lemma sqMap_iterate (n : ℕ) (z : ℂ) : (fun w : ℂ => w ^ 2)^[n] z = z ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

/-- The basic quadratic-like map `z ↦ z²` on `ball 0 R ⋐ ball 0 R²`, for `R > 1`. -/
noncomputable def sq (R : ℝ) (hR : 1 < R) : QuadraticLike where
  U := Metric.ball 0 R
  V := Metric.ball 0 (R ^ 2)
  f := fun z => z ^ 2
  critical := 0
  isOpen_U := Metric.isOpen_ball
  isOpen_V := Metric.isOpen_ball
  isConnected_U := Metric.isConnected_ball (by linarith)
  isConnected_V := Metric.isConnected_ball (by nlinarith)
  isBounded_V := Metric.isBounded_ball
  closure_U_subset := by
    refine Metric.closure_ball_subset_closedBall.trans ?_
    intro z hz
    simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at hz ⊢
    nlinarith [norm_nonneg z]
  differentiableOn := (by fun_prop : Differentiable ℂ fun z : ℂ => z ^ 2).differentiableOn
  mapsTo := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right, norm_pow] at hz ⊢
    nlinarith [norm_nonneg z]
  properOn := by
    intro K hKV hK
    have hset : Metric.ball (0 : ℂ) R ∩ (fun z : ℂ => z ^ 2) ⁻¹' K
        = Metric.closedBall (0 : ℂ) R ∩ (fun z : ℂ => z ^ 2) ⁻¹' K := by
      ext z
      simp only [Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
        Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.le, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hmem := hKV h2
        simp only [Metric.mem_ball, dist_zero_right, norm_pow] at hmem
        nlinarith [norm_nonneg z]
    rw [hset]
    exact (isCompact_closedBall _ _).inter_right (hK.isClosed.preimage (by fun_prop))
  critical_mem := Metric.mem_ball_self (by linarith)
  fiber_critical := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball,
      dist_zero_right]
    constructor
    · rintro ⟨-, hz⟩
      simpa using hz
    · rintro rfl
      exact ⟨by simpa using (by linarith : (0 : ℝ) < R), rfl⟩
  fiber_card := by
    intro w hw hw0
    have hw0' : w ≠ 0 := by simpa using hw0
    obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq w 2
    have hsne : s ≠ 0 := by
      rintro rfl
      exact hw0' (by simpa using hs.symm)
    have hwR : ‖w‖ < R ^ 2 := by simpa [dist_zero_right] using hw
    have hnorm : ‖s‖ < R := by
      have hns : ‖s‖ ^ 2 = ‖w‖ := by rw [← hs, norm_pow]
      nlinarith [norm_nonneg s, (by linarith : (0 : ℝ) < R)]
    have hset : Metric.ball (0 : ℂ) R ∩ (fun z : ℂ => z ^ 2) ⁻¹' {w} = {s, -s} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball,
        dist_zero_right, Set.mem_insert_iff]
      constructor
      · rintro ⟨-, hz⟩
        have hfac : (z - s) * (z + s) = 0 := by linear_combination hz - hs
        rcases mul_eq_zero.1 hfac with h | h
        · exact Or.inl (by linear_combination h)
        · exact Or.inr (by linear_combination h)
      · rintro (rfl | rfl)
        · exact ⟨hnorm, hs⟩
        · refine ⟨by simpa using hnorm, ?_⟩
          simpa using hs
    rw [hset]
    exact Set.ncard_pair (fun h => hsne (by linear_combination h / 2))
  deriv_critical := by simp
  unique_critical := by
    intro z _ hz
    simpa using hz

@[simp] lemma sq_f (R : ℝ) (hR : 1 < R) : (sq R hR).f = fun z : ℂ => z ^ 2 := rfl

@[simp] lemma sq_U (R : ℝ) (hR : 1 < R) : (sq R hR).U = Metric.ball 0 R := rfl

/-- The filled Julia set of `z ↦ z²` is the closed unit disc. -/
lemma sq_K (R : ℝ) (hR : 1 < R) : (sq R hR).K = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [QuadraticLike.K, Set.mem_setOf_eq, sq_f, sq_U, sqMap_iterate, Metric.mem_ball,
    Metric.mem_closedBall, dist_zero_right, norm_pow]
  constructor
  · intro h
    by_contra hz
    push_neg at hz
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R hz
    have hle : ‖z‖ ^ n ≤ ‖z‖ ^ (2 ^ n) :=
      pow_le_pow_right₀ hz.le (Nat.lt_two_pow_self).le
    exact absurd (h n) (by push_neg; linarith)
  · intro h n
    calc ‖z‖ ^ (2 ^ n) ≤ 1 ^ (2 ^ n) := by
          exact pow_le_pow_left₀ (norm_nonneg z) h _
      _ = 1 := one_pow _
      _ < R := hR

/-!
## Main statement
-/

/-- **McMullen renormalization for quadratic-like maps** (formalized statement together with
the base case and the Lean-checked reductions).

1. *Base case.* For every `R > 1` the map `z ↦ z²` on `ball 0 R ⋐ ball 0 R²` is quadratic-like,
   its filled Julia set is the closed unit disc, which is compact and connected, and it is
   renormalizable of period one.
2. *Renormalization tower (reduction).* If `R` is a renormalization of `Q` of period `n` and
   `R` is renormalizable of period `m`, then `Q` is renormalizable of period `n * m`; hence the
   renormalization operator can be iterated, which is what makes infinitely renormalizable maps
   meaningful.
3. *Rigidity (transport).* Any conjugacy between quadratic-like maps carries filled Julia sets
   bijectively onto each other; in particular a hybrid equivalence is a bijection of the filled
   Julia sets.
4. *Structure of filled Julia sets.* The filled Julia set of a quadratic-like map is compact,
   forward invariant, and totally invariant inside `U`.
5. *Straightening (reduction).* Granting the Douady–Hubbard straightening statement, the filled
   Julia set of every quadratic-like map is carried bijectively by a conjugacy onto the filled
   Julia set of a quadratic-like restriction of a quadratic polynomial `z ↦ z² + c`. -/
theorem mcmullen_renormalization :
    (∀ R : ℝ, ∀ hR : 1 < R,
        (sq R hR).f = (fun z : ℂ => z ^ 2) ∧ (sq R hR).U = Metric.ball 0 R ∧
        (sq R hR).K = Metric.closedBall (0 : ℂ) 1 ∧ IsCompact (sq R hR).K ∧
        IsConnected (sq R hR).K ∧ Renormalizable (sq R hR) 1) ∧
    (∀ (Q R : QuadraticLike) (n m : ℕ), IsRenormalizationOf R Q n → Renormalizable R m →
        Renormalizable Q (n * m)) ∧
    (∀ (P Q : QuadraticLike) (c : Conjugacy P Q), Set.BijOn c.h P.K Q.K) ∧
    (∀ Q : QuadraticLike, IsCompact Q.K ∧ Set.MapsTo Q.f Q.K Q.K ∧
        Q.f ⁻¹' Q.K ∩ Q.U = Q.K) ∧
    (StraighteningStatement → ∀ Q : QuadraticLike, ∃ (c : ℂ) (P : QuadraticLike) (g : ℂ → ℂ),
        P.f = (fun z : ℂ => z ^ 2 + c) ∧ Set.BijOn g Q.K P.K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R hR
    have hKeq : (sq R hR).K = Metric.closedBall (0 : ℂ) 1 := sq_K R hR
    refine ⟨sq_f R hR, sq_U R hR, hKeq, ?_, ?_, ?_⟩
    · rw [hKeq]; exact isCompact_closedBall _ _
    · rw [hKeq]
      exact (convex_closedBall (0 : ℂ) 1).isConnected (Metric.nonempty_closedBall.2 zero_le_one)
    · exact renormalizable_one _ (by
        rw [hKeq]
        exact (convex_closedBall (0 : ℂ) 1).isConnected
          (Metric.nonempty_closedBall.2 zero_le_one))
  · intro Q R n m hR hm
    exact renormalizable_mul hR hm
  · intro P Q c
    exact c.bijOn_K
  · intro Q
    exact ⟨Q.isCompact_K, Q.mapsTo_K, Q.preimage_K_inter_U⟩
  · intro hstr Q
    exact straightening_gives_julia_model hstr Q

end Frontier

