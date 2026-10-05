import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
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
## Overview

We formalize the *spin–statistics connection* in the algebraic form in which it is proved in
the Wightman framework (Streater–Wightman, Theorem 4-10): a relativistic quantum field which
obeys the *wrong* connection between spin and statistics annihilates the vacuum, hence is
trivial.  Equivalently, for a nontrivial field the statistics sign `ε` (`+1` for Bose,
`-1` for Fermi commutation relations at spacelike separation) must equal `(-1) ^ (2j)`,
where `j` is the spin: integer spin forces Bose statistics and half-integer spin forces
Fermi statistics.

The structure `Frontier.WightmanTheory` bundles the inputs of the argument:

* the fields `phi f` are operators on a complex inner product space, indexed by (smeared)
  test functions `f`, with `conj f` the test function implementing the adjoint;
* `hermitian`: `phi (conj f)` is the adjoint of `phi f`;
* `locality`: at spacelike separation the fields commute (`ε = 1`) or anticommute (`ε = -1`),
  according to the assumed statistics;
* `wlc`: *weak local commutativity* at Jost points, `W(f,g) = (-1)^(2j) W(g,f)`.  This is the
  standard consequence of Lorentz covariance of a spin-`j` field together with the analyticity
  of the Wightman functions;
* `analyticContinuation`: the edge-of-the-wedge/analytic-continuation input, namely that a
  two-point Wightman function vanishing for all spacelike-separated arguments vanishes
  identically.

The theorem `Frontier.spin_statistics` is then a fully Lean-checked reduction: from these
axioms and nontriviality of the field, the spin–statistics relation `ε = (-1)^(2j)` follows.

Two concrete toy models (`Frontier.boseModel`, `Frontier.fermiModel`) are constructed at the
end of the file, showing that the axiom system is consistent and that both the Bose case
(`2j` even) and the Fermi case (`2j` odd) really occur.
-/

/-- The two possible statistics of a field: commuting (Bose) or anticommuting (Fermi)
at spacelike separation. -/
inductive Statistics where
  | bose
  | fermi
deriving DecidableEq, Repr

/-- The sign `ε` occurring in the (anti)commutation relations: `+1` for Bose, `-1` for Fermi. -/
def Statistics.sign : Statistics → ℂ
  | .bose => 1
  | .fermi => -1

/-- A Wightman-type quantum field theory of a field of spin `j` (recorded through
`twoSpin = 2j : ℕ`) with a prescribed statistics, given by its smeared field operators on a
complex inner product space `H` of states, together with the structural axioms used in the
proof of the spin–statistics theorem. -/
structure WightmanTheory (T : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The smeared field operator `phi f` associated with a test function `f`. -/
  phi : T → H →ₗ[ℂ] H
  /-- The vacuum state. -/
  vacuum : H
  /-- Complex conjugation of test functions; `phi (conj f)` is the adjoint of `phi f`. -/
  conj : T → T
  /-- Spacelike separation of the supports of two test functions. -/
  Spacelike : T → T → Prop
  /-- Twice the spin of the field. -/
  twoSpin : ℕ
  /-- The statistics obeyed by the field. -/
  statistics : Statistics
  /-- Hermiticity: `phi (conj f)` is the adjoint of `phi f`. -/
  hermitian : ∀ (f : T) (x y : H), inner ℂ (phi f x) y = inner ℂ x (phi (conj f) y)
  /-- Locality: at spacelike separation the fields commute or anticommute according to the
  assumed statistics. -/
  locality : ∀ f g, Spacelike f g → ∀ x, phi f (phi g x) = statistics.sign • phi g (phi f x)
  /-- Weak local commutativity at Jost points, the consequence of Lorentz covariance of a
  spin-`j` field and of the analyticity of the Wightman functions. -/
  wlc : ∀ f g, Spacelike f g →
      (inner ℂ vacuum (phi f (phi g vacuum)) : ℂ)
        = (-1 : ℂ) ^ twoSpin * inner ℂ vacuum (phi g (phi f vacuum))
  /-- Analytic continuation (edge of the wedge): a two-point function vanishing at all
  spacelike separations vanishes identically. -/
  analyticContinuation :
      (∀ f g, Spacelike f g → (inner ℂ vacuum (phi f (phi g vacuum)) : ℂ) = 0) →
      ∀ f g, (inner ℂ vacuum (phi f (phi g vacuum)) : ℂ) = 0

variable {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two-point Wightman function of the vacuum, `W(f,g) = ⟪Ω, φ(f) φ(g) Ω⟫`. -/
noncomputable def WightmanTheory.twoPoint (W : WightmanTheory T H) (f g : T) : ℂ :=
  inner ℂ W.vacuum (W.phi f (W.phi g W.vacuum))

/-- If the statistics sign does not match the spin parity, then locality and weak local
commutativity force the two-point function to vanish at spacelike separation. -/
theorem twoPoint_eq_zero_of_spacelike (W : WightmanTheory T H)
    (h : W.statistics.sign ≠ (-1 : ℂ) ^ W.twoSpin) :
    ∀ f g, W.Spacelike f g → W.twoPoint f g = 0 := by
  intro f g hfg
  -- Locality gives `W(f,g) = ε · W(g,f)`.
  have h1 : W.twoPoint f g = W.statistics.sign * W.twoPoint g f := by
    simp only [WightmanTheory.twoPoint]
    rw [W.locality f g hfg, inner_smul_right]
  -- Weak local commutativity gives `W(f,g) = (-1)^(2j) · W(g,f)`.
  have h2 : W.twoPoint f g = (-1 : ℂ) ^ W.twoSpin * W.twoPoint g f := W.wlc f g hfg
  have hb : W.twoPoint g f = 0 := by
    have h3 : (W.statistics.sign - (-1 : ℂ) ^ W.twoSpin) * W.twoPoint g f = 0 := by
      linear_combination h1.symm.trans h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) h
    · exact h4
  rw [h1, hb, mul_zero]

/-- **Wrong statistics implies a trivial field.**  If the statistics sign does not match the
spin parity `(-1)^(2j)`, then every smeared field operator annihilates the vacuum. -/
theorem vacuum_annihilated_of_wrong_statistics (W : WightmanTheory T H)
    (h : W.statistics.sign ≠ (-1 : ℂ) ^ W.twoSpin) (f : T) : W.phi f W.vacuum = 0 := by
  have hall := W.analyticContinuation (twoPoint_eq_zero_of_spacelike W h)
  have h0 : (inner ℂ (W.phi f W.vacuum) (W.phi f W.vacuum) : ℂ) = 0 := by
    rw [W.hermitian f W.vacuum (W.phi f W.vacuum)]
    exact hall _ _
  exact inner_self_eq_zero.1 h0

/-- **The spin–statistics connection.**  In a Wightman theory whose field does not annihilate
the vacuum, the statistics sign is determined by the spin: it equals `(-1)^(2j)`.  Thus a
field of integer spin obeys Bose statistics and a field of half-integer spin obeys Fermi
statistics. -/
theorem spin_statistics (W : WightmanTheory T H) (hnt : ∃ f, W.phi f W.vacuum ≠ 0) :
    W.statistics.sign = (-1 : ℂ) ^ W.twoSpin := by
  by_contra h
  obtain ⟨f, hf⟩ := hnt
  exact hf (vacuum_annihilated_of_wrong_statistics W h f)

/-- A nontrivial field obeying Bose statistics has integer spin. -/
theorem even_twoSpin_of_bose (W : WightmanTheory T H) (hnt : ∃ f, W.phi f W.vacuum ≠ 0)
    (hb : W.statistics = Statistics.bose) : Even W.twoSpin := by
  have h := spin_statistics W hnt
  rw [hb] at h
  exact (neg_one_pow_eq_one_iff_even (R := ℂ) (by norm_num)).1 h.symm

/-- A nontrivial field obeying Fermi statistics has half-integer spin. -/
theorem odd_twoSpin_of_fermi (W : WightmanTheory T H) (hnt : ∃ f, W.phi f W.vacuum ≠ 0)
    (hf : W.statistics = Statistics.fermi) : Odd W.twoSpin := by
  have h := spin_statistics W hnt
  rw [hf] at h
  rcases Nat.even_or_odd W.twoSpin with he | ho
  · rw [he.neg_one_pow, Statistics.sign] at h
    exact absurd h (by norm_num)
  · exact ho

/-!
## Consistency: two concrete models

The following two models show that the axioms of `WightmanTheory` are consistent and that
both branches of the spin–statistics alternative are realized.
-/

/-- A one-mode toy model of a neutral scalar field: spin `0`, Bose statistics, all test
functions mutually "spacelike".  It is nontrivial, and indeed `ε = 1 = (-1)^0`. -/
noncomputable def boseModel : WightmanTheory ℝ ℂ where
  phi t := (t : ℂ) • LinearMap.id
  vacuum := 1
  conj t := t
  Spacelike _ _ := True
  twoSpin := 0
  statistics := Statistics.bose
  hermitian f x y := by
    simp [RCLike.inner_apply, Complex.conj_ofReal]
    ring
  locality f g _ x := by
    simp [Statistics.sign]
    ring
  wlc f g _ := by
    simp [RCLike.inner_apply]
    ring
  analyticContinuation h f g := h f g trivial

theorem boseModel_nontrivial : ∃ f : ℝ, boseModel.phi f boseModel.vacuum ≠ 0 := by
  refine ⟨1, ?_⟩
  simp [boseModel]

/-- The Bose model satisfies the spin–statistics relation, as it must. -/
theorem boseModel_spin_statistics :
    boseModel.statistics.sign = (-1 : ℂ) ^ boseModel.twoSpin :=
  spin_statistics boseModel boseModel_nontrivial

/-- The two-dimensional "Clifford" toy model of a spin-`1/2` field: test functions are
vectors `f ∈ ℝ²`, the field is `φ(f) = f₁σ₁ + f₂σ₂`, spacelike separation is orthogonality
of `f` and `g`, and the statistics is Fermi. -/
noncomputable def fermiPhi (f : ℝ × ℝ) :
    EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun x :=
    (WithLp.toLp 2 ![(starRingEnd ℂ) (f.1 + f.2 * Complex.I) * x 1,
      (f.1 + f.2 * Complex.I) * x 0] : EuclideanSpace ℂ (Fin 2))
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

/-- A spin-`1/2` toy model with Fermi statistics: nontrivial, with `ε = -1 = (-1)^1`. -/
noncomputable def fermiModel : WightmanTheory (ℝ × ℝ) (EuclideanSpace ℂ (Fin 2)) where
  phi := fermiPhi
  vacuum := (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℂ (Fin 2))
  conj f := f
  Spacelike f g := f.1 * g.1 + f.2 * g.2 = 0
  twoSpin := 1
  statistics := Statistics.fermi
  hermitian f x y := by
    simp [fermiPhi, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  locality f g hfg x := by
    have h : (f.1 : ℂ) * g.1 + (f.2 : ℂ) * g.2 = 0 := by exact_mod_cast hfg
    ext i
    fin_cases i <;>
      simp only [fermiPhi, Statistics.sign, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, PiLp.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I, Fin.isValue, Fin.zero_eta, Fin.mk_one, WithLp.ofLp_toLp]
    · linear_combination (2 * (x 0)) * h + (-2 * (f.2 : ℂ) * (g.2 : ℂ) * (x 0)) * Complex.I_sq
    · linear_combination (2 * (x 1)) * h + (-2 * (f.2 : ℂ) * (g.2 : ℂ) * (x 1)) * Complex.I_sq
  wlc f g hfg := by
    have h : (f.1 : ℂ) * g.1 + (f.2 : ℂ) * g.2 = 0 := by exact_mod_cast hfg
    simp only [fermiPhi, PiLp.inner_apply, Fin.sum_univ_two, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, RCLike.inner_apply, map_one, map_zero, mul_zero, add_zero, pow_one]
    linear_combination (2 : ℂ) * h + (-2 * (f.2 : ℂ) * (g.2 : ℂ)) * Complex.I_sq
  analyticContinuation h f g := by
    exfalso
    have h1 := h (1, 0) (0, 1) (by norm_num)
    simp [fermiPhi, PiLp.inner_apply, Fin.sum_univ_two, Complex.ext_iff] at h1

theorem fermiModel_nontrivial : ∃ f : ℝ × ℝ, fermiModel.phi f fermiModel.vacuum ≠ 0 := by
  refine ⟨(1, 0), ?_⟩
  intro h
  have := congrFun (congrArg (fun v : EuclideanSpace ℂ (Fin 2) => (WithLp.ofLp v)) h) 1
  simp [fermiModel, fermiPhi] at this

/-- The Fermi model satisfies the spin–statistics relation, as it must. -/
theorem fermiModel_spin_statistics :
    fermiModel.statistics.sign = (-1 : ℂ) ^ fermiModel.twoSpin :=
  spin_statistics fermiModel fermiModel_nontrivial

end Frontier

