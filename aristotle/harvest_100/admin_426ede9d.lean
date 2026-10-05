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

/-
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A linear operator `T` with domain the submodule `D` of a complex Hilbert space is
*symmetric* if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/
def IsSymmetricOn (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop :=
  ∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫

/-- `IsAdjointPair D T u v` says that `u` lies in the domain of the adjoint `T†` of the
densely defined operator `T` and that `T† u = v`, i.e. `⟪T x, u⟫ = ⟪x, v⟫` for every `x`
in the domain of `T`. -/
def IsAdjointPair (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) (u v : H) : Prop :=
  ∀ x : D, ⟪T x, u⟫ = ⟪(x : H), v⟫

/-- `T` is *essentially self-adjoint* when its adjoint `T†` is again symmetric; for a densely
defined symmetric operator this is the standard characterisation of the closure `T̄ = T††`
being self-adjoint. -/
def EssentiallySelfAdjoint (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop :=
  ∀ u v u' v' : H, IsAdjointPair D T u v → IsAdjointPair D T u' v' → ⟪v, u'⟫ = ⟪u, v'⟫

/-- *Weak regularity* (the limit-point condition for the deficiency ODE): the only weak
solutions of the deficiency equations `T† u = ± i u` are trivial, i.e. both deficiency
spaces `ker (T† ∓ i)` vanish. -/
def WeakRegularity (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop :=
  ∀ u : H,
    (IsAdjointPair D T u (Complex.I • u) ∨ IsAdjointPair D T u (-(Complex.I • u))) → u = 0

/-- The graph closure of `T`: `GraphLimit D T p q` says that `(p, q)` is a limit of points
`(x, T x)` with `x` in the domain of `T`. -/
def GraphLimit (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) (p q : H) : Prop :=
  ∃ x : ℕ → D, Tendsto (fun n => ((x n : H))) atTop (𝓝 p) ∧
    Tendsto (fun n => T (x n)) atTop (𝓝 q)

variable {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}

/-- Symmetry passes to the graph closure. -/
theorem inner_graphLimit_symm (hsym : IsSymmetricOn D T) {p q p' q' : H}
    (h : GraphLimit D T p q) (h' : GraphLimit D T p' q') : ⟪q, p'⟫ = ⟪p, q'⟫ := by
  obtain ⟨x, hx, hTx⟩ := h
  obtain ⟨y, hy, hTy⟩ := h'
  have h1 : Tendsto (fun n => ⟪T (x n), (y n : H)⟫) atTop (𝓝 ⟪q, p'⟫) := hTx.inner hy
  have h2 : Tendsto (fun n => ⟪(x n : H), T (y n)⟫) atTop (𝓝 ⟪p, q'⟫) := hx.inner hTy
  have he : (fun n => ⟪T (x n), (y n : H)⟫) = fun n => ⟪(x n : H), T (y n)⟫ :=
    funext fun n => hsym _ _
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

/-- Every point of the graph closure is an adjoint pair. -/
theorem isAdjointPair_of_graphLimit (hsym : IsSymmetricOn D T) {p q : H}
    (h : GraphLimit D T p q) : IsAdjointPair D T p q := by
  obtain ⟨x, hx, hTx⟩ := h
  intro z
  have h1 : Tendsto (fun n => ⟪T z, (x n : H)⟫) atTop (𝓝 ⟪T z, p⟫) :=
    tendsto_const_nhds.inner hx
  have h2 : Tendsto (fun n => ⟪(z : H), T (x n)⟫) atTop (𝓝 ⟪(z : H), q⟫) :=
    tendsto_const_nhds.inner hTx
  have he : (fun n => ⟪T z, (x n : H)⟫) = fun n => ⟪(z : H), T (x n)⟫ :=
    funext fun n => hsym _ _
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

/-- The Pythagoras identity `‖T x + c x‖² = ‖T x‖² + ‖c x‖²` for purely imaginary `c`. -/
theorem norm_add_smul_sq (hsym : IsSymmetricOn D T) {c : ℂ} (hc : c.re = 0) (x : D) :
    ‖T x + c • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + ‖c • (x : H)‖ ^ 2 := by
  have hreal : (⟪T x, (x : H)⟫).im = 0 := by
    have h : (starRingEnd ℂ) ⟪T x, (x : H)⟫ = ⟪T x, (x : H)⟫ := by
      rw [inner_conj_symm]; exact (hsym x x).symm
    have h' := congrArg Complex.im h
    simp only [Complex.conj_im] at h'
    linarith
  have hzero : RCLike.re (⟪T x, c • (x : H)⟫) = 0 := by
    rw [inner_smul_right]
    simp [hc, hreal]
  rw [norm_add_sq (𝕜 := ℂ), hzero]
  ring

/-- Weak regularity makes the range of `T + c` dense for `c = ± i`. -/
theorem dense_range_add_smul [CompleteSpace H] (hreg : WeakRegularity D T) {c : ℂ}
    (hc : c = Complex.I ∨ c = -Complex.I) (y : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : D, ‖(T x + c • (x : H)) - y‖ < ε := by
  set S : Submodule ℂ H := LinearMap.range (T + c • D.subtype) with hSdef
  have hmem : ∀ x : D, T x + c • (x : H) ∈ S := by
    intro x
    exact ⟨x, by simp [LinearMap.add_apply, LinearMap.smul_apply]⟩
  have hSperp : Sᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hz' : ∀ x : D, ⟪T x + c • (x : H), z⟫ = 0 := fun x => hz _ (hmem x)
    rcases hc with rfl | rfl
    · refine hreg z (Or.inl ?_)
      intro x
      have h0 := hz' x
      rw [inner_add_left, inner_smul_left] at h0
      rw [inner_smul_right]
      simp only [Complex.conj_I] at h0
      linear_combination h0
    · refine hreg z (Or.inr ?_)
      intro x
      have h0 := hz' x
      rw [inner_add_left, inner_smul_left] at h0
      rw [inner_neg_right, inner_smul_right]
      simp only [map_neg, Complex.conj_I, neg_neg] at h0
      linear_combination h0
  have htop : S.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hSperp
  have hy : y ∈ closure (S : Set H) := by
    have h1 : y ∈ S.topologicalClosure := by rw [htop]; exact Submodule.mem_top
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h1
  rw [Metric.mem_closure_iff] at hy
  obtain ⟨b, hbS, hb⟩ := hy ε hε
  obtain ⟨x, hx⟩ := hbS
  refine ⟨x, ?_⟩
  have hxb : T x + c • (x : H) = b := by
    rw [← hx]; simp [LinearMap.add_apply, LinearMap.smul_apply]
  rw [hxb, ← dist_eq_norm, dist_comm]
  exact hb

/-- With weak regularity, `T̄ + c` is surjective for `c = ± i`. -/
theorem exists_graphLimit [CompleteSpace H] (hsym : IsSymmetricOn D T)
    (hreg : WeakRegularity D T) {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I) (y : H) :
    ∃ p q : H, GraphLimit D T p q ∧ q + c • p = y := by
  have hcre : c.re = 0 := by rcases hc with rfl | rfl <;> simp
  have hcnorm : ‖c‖ = 1 := by rcases hc with rfl | rfl <;> simp
  have hex : ∀ n : ℕ, ∃ z : D, ‖(T z + c • (z : H)) - y‖ < 1 / (n + 1 : ℝ) := by
    intro n
    exact dense_range_add_smul hreg hc y (by positivity)
  choose x hx using hex
  set s : ℕ → H := fun n => T (x n) + c • (x n : H) with hsdef
  have hs : Tendsto s atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hkey : ∀ n m : ℕ, ‖(x n : H) - (x m : H)‖ ≤ ‖s n - s m‖ ∧
      ‖T (x n) - T (x m)‖ ≤ ‖s n - s m‖ := by
    intro n m
    have hz : s n - s m = T (x n - x m) + c • ((x n - x m : D) : H) := by
      simp only [hsdef, map_sub, Submodule.coe_sub, smul_sub]
      abel
    have hpy := norm_add_smul_sq hsym hcre (x n - x m)
    rw [← hz] at hpy
    rw [norm_smul, hcnorm, one_mul] at hpy
    rw [map_sub] at hpy
    rw [Submodule.coe_sub] at hpy
    constructor
    · nlinarith [norm_nonneg ((x n : H) - (x m : H)), norm_nonneg (s n - s m),
        norm_nonneg (T (x n) - T (x m))]
    · nlinarith [norm_nonneg ((x n : H) - (x m : H)), norm_nonneg (s n - s m),
        norm_nonneg (T (x n) - T (x m))]
  have hsc : CauchySeq s := hs.cauchySeq
  rw [Metric.cauchySeq_iff] at hsc
  have hxc : CauchySeq (fun n => (x n : H)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hsc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_le_of_lt (hkey m n).1 h1
  have hTc : CauchySeq (fun n => T (x n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hsc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_le_of_lt (hkey m n).2 h1
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hxc
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hTc
  refine ⟨p, q, ⟨x, hp, hq⟩, ?_⟩
  have hlim : Tendsto s atTop (𝓝 (q + c • p)) := hq.add (hp.const_smul c)
  exact tendsto_nhds_unique hlim hs

/-- **Basic criterion** (von Neumann): a symmetric operator with trivial deficiency spaces is
essentially self-adjoint. -/
theorem essentiallySelfAdjoint_of_weakRegularity [CompleteSpace H] (hsym : IsSymmetricOn D T)
    (hreg : WeakRegularity D T) : EssentiallySelfAdjoint D T := by
  have key : ∀ u v : H, IsAdjointPair D T u v → GraphLimit D T u v := by
    intro u v huv
    obtain ⟨p, q, hpq, hEq⟩ :=
      exists_graphLimit hsym hreg (Or.inl rfl) (v + Complex.I • u)
    have hpq' : IsAdjointPair D T p q := isAdjointPair_of_graphLimit hsym hpq
    have hvq : v - q = -(Complex.I • (u - p)) := by
      have : q + Complex.I • p = v + Complex.I • u := hEq
      rw [smul_sub]
      linear_combination (norm := module) -this
    have hw : IsAdjointPair D T (u - p) (-(Complex.I • (u - p))) := by
      intro z
      rw [inner_sub_right, huv z, hpq' z, ← inner_sub_right, ← hvq]
    have hw0 : u - p = 0 := hreg _ (Or.inr hw)
    have hup : u = p := sub_eq_zero.mp hw0
    have hvq0 : v = q := by
      have h1 : v - q = 0 := by rw [hvq, hw0, smul_zero, neg_zero]
      exact sub_eq_zero.mp h1
    rw [hup, hvq0]
    exact hpq
  intro u v u' v' h1 h2
  exact inner_graphLimit_symm hsym (key u v h1) (key u' v' h2)

/-- **Schrödinger operators are essentially self-adjoint under weak regularity.**

`T = K + P` is a Schrödinger operator on a complex Hilbert space `H`, written as the sum of a
symmetric kinetic part `K` and a symmetric potential part `P`, both defined on a common domain
`D`.  If `T` is weakly regular — the limit-point condition, i.e. the deficiency ODEs
`T† u = ± i u` have no nontrivial weak solutions in `H` — then `T` is essentially self-adjoint.

Formerly this was stated with the essential-self-adjointness criterion assumed as a named
hypothesis; here that hypothesis is discharged (see
`Brockian.Weyl.DeficiencyODE.essentiallySelfAdjoint_of_weakRegularity`), making the statement
unconditional. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity [CompleteSpace H]
    (K P : D →ₗ[ℂ] H) (hK : IsSymmetricOn D K) (hP : IsSymmetricOn D P)
    (hreg : WeakRegularity D (K + P)) : EssentiallySelfAdjoint D (K + P) := by
  have hsym : IsSymmetricOn D (K + P) := by
    intro x y
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hK x y, hP x y]
  exact essentiallySelfAdjoint_of_weakRegularity hsym hreg

/-- Sanity check: the hypotheses of the main theorem are satisfiable non-vacuously.  On any
complex Hilbert space the zero operator with full domain is symmetric and weakly regular. -/
example [CompleteSpace H] : EssentiallySelfAdjoint (⊤ : Submodule ℂ H) (0 + 0) := by
  refine schrodinger_essentiallySelfAdjoint_of_weakRegularity 0 0 (fun x y => by simp)
    (fun x y => by simp) ?_
  intro u hu
  have hz : ⟪u, u⟫ = 0 := by
    rcases hu with hu | hu
    · have h := hu ⟨u, Submodule.mem_top⟩
      have h2 : (0 : ℂ) = Complex.I * ⟪u, u⟫ := by simpa [inner_smul_right] using h
      rcases mul_eq_zero.mp h2.symm with h3 | h3
      · exact absurd h3 Complex.I_ne_zero
      · exact h3
    · have h := hu ⟨u, Submodule.mem_top⟩
      have h2 : (0 : ℂ) = -(Complex.I * ⟪u, u⟫) := by
        simpa [inner_neg_right, inner_smul_right] using h
      rcases mul_eq_zero.mp (neg_eq_zero.mp h2.symm) with h3 | h3
      · exact absurd h3 Complex.I_ne_zero
      · exact h3
  exact inner_self_eq_zero.mp hz

end Brockian.Weyl.DeficiencyODE

