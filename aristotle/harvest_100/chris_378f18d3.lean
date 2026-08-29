/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is a
-- block comment; the same header is repeated as a module docstring below.)

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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The spin–statistics connection

We formalize the algebraic core of the spin–statistics theorem in the Wightman
framework, in the form of Pauli's argument.

A relativistic quantum field is described by:

* a complex inner product space `H` of states with a distinguished vacuum vector `Ω`;
* smeared field operators `φ(f)` and their adjoints `φ(f)†`, indexed by a type `T`
  of test functions;
* a relation `spacelike f g` recording that the supports of `f` and `g` are
  mutually spacelike separated;
* the number `twiceSpin = 2j ∈ ℕ` attached to the (finite dimensional) Lorentz
  representation carried by the field;
* a statistics sign `stat = ε ∈ {+1, -1}`, namely `ε = +1` if the field is
  quantized with commutators (Bose statistics) and `ε = -1` if it is quantized
  with anticommutators (Fermi statistics).

The two dynamical inputs are:

* **Locality**: for spacelike separated `f, g`, the fields (anti)commute, so the
  two Wightman functions `⟪Ω, φ(f) φ(g)† Ω⟫` and `⟪Ω, φ(g)† φ(f) Ω⟫` agree up to
  the statistics sign `ε`.
* **Rotation covariance / analyticity** (the "PCT / Bargmann–Hall–Wightman" input):
  the analytic continuation of the Wightman function to the extended tube, together
  with the behaviour of a spin-`j` field under a `2π` rotation, exchanges the two
  orderings up to the factor `(-1)^{2j}`.

The conclusion, `Frontier.spin_statistics`, is that a field whose two-point
function does not vanish identically at spacelike separation must satisfy
`ε = (-1)^{2j}`: integer spin forces Bose statistics, half-integer spin forces
Fermi statistics.  Equivalently (`Frontier.RelativisticField.wightman_eq_zero_of_wrong_statistics`),
quantizing with the wrong statistics kills the two-point function.

The last two sections show that the hypotheses are not vacuous by exhibiting
an explicit spin-`0` Bose model and an explicit spin-`1/2` Fermi model.
-/

/-- The data and axioms of (the two-point sector of) a relativistic quantum field:
a vacuum vector, smeared field operators together with their adjoints, a notion of
spacelike separation of test functions, the doubled spin `2j`, the statistics sign
`ε`, locality, and the rotation/analyticity relation. -/
structure RelativisticField (T : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vacuum state. -/
  vacuum : H
  /-- The smeared field operator `φ(f)`. -/
  field : T → (H →ₗ[ℂ] H)
  /-- The adjoint field operator `φ(f)†`. -/
  adjField : T → (H →ₗ[ℂ] H)
  /-- `adjField f` really is the adjoint of `field f`. -/
  adj_inner : ∀ (f : T) (x y : H), ⟪adjField f x, y⟫_ℂ = ⟪x, field f y⟫_ℂ
  /-- Mutual spacelike separation of the supports of two test functions. -/
  spacelike : T → T → Prop
  /-- Twice the spin, `2j`, of the Lorentz representation carried by the field. -/
  twiceSpin : ℕ
  /-- The statistics sign: `+1` for commutators, `-1` for anticommutators. -/
  stat : ℤ
  /-- The statistics parameter is a sign. -/
  stat_isSign : stat = 1 ∨ stat = -1
  /-- Locality: at spacelike separation the fields commute (`ε = 1`) or
  anticommute (`ε = -1`). -/
  locality : ∀ f g : T, spacelike f g →
    ⟪vacuum, field f (adjField g vacuum)⟫_ℂ
      = (stat : ℂ) * ⟪vacuum, adjField g (field f vacuum)⟫_ℂ
  /-- Rotation covariance together with the analyticity of the Wightman function
  exchanges the two orderings up to the `2π`-rotation phase `(-1)^{2j}`. -/
  rotation : ∀ f g : T, spacelike f g →
    ⟪vacuum, field f (adjField g vacuum)⟫_ℂ
      = (-1 : ℂ) ^ twiceSpin * ⟪vacuum, adjField g (field f vacuum)⟫_ℂ

namespace RelativisticField

variable {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (F : RelativisticField T H)

/-- The two-point Wightman function `W(f, g) = ⟪Ω, φ(g)† φ(f) Ω⟫`. -/
noncomputable def wightman (f g : T) : ℂ :=
  ⟪F.vacuum, F.adjField g (F.field f F.vacuum)⟫_ℂ

/-- The spin `j` of the field, as a rational number. -/
def spin : ℚ := (F.twiceSpin : ℚ) / 2

/-- The field is *nondegenerate* if its two-point function does not vanish for
some spacelike separated pair of test functions.  For a nonzero Wightman field
this follows from the Reeh–Schlieder theorem. -/
def Nondegenerate : Prop :=
  ∃ f g : T, F.spacelike f g ∧ F.wightman f g ≠ 0

/-- The two-point function is the overlap of the states `φ(f) Ω` and `φ(g) Ω`. -/
theorem wightman_eq_inner (f g : T) :
    F.wightman f g = ⟪F.field g F.vacuum, F.field f F.vacuum⟫_ℂ := by
  simpa [wightman] using
    (F.adj_inner g F.vacuum (F.field f F.vacuum)).symm ▸ rfl

/-- **Pauli's argument.** If a field is quantized with the statistics that does
*not* match its spin, then its two-point function vanishes at all spacelike
separations. -/
theorem wightman_eq_zero_of_wrong_statistics
    (h : (F.stat : ℂ) ≠ (-1 : ℂ) ^ F.twiceSpin) :
    ∀ f g : T, F.spacelike f g → F.wightman f g = 0 := by
  intro f g hfg
  have h1 := F.locality f g hfg
  have h2 := F.rotation f g hfg
  have h3 : (F.stat : ℂ) * F.wightman f g = (-1 : ℂ) ^ F.twiceSpin * F.wightman f g := by
    simpa [wightman] using h1.symm.trans h2
  have h4 : ((F.stat : ℂ) - (-1 : ℂ) ^ F.twiceSpin) * F.wightman f g = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd (sub_eq_zero.mp h5) h
  · exact h5

end RelativisticField

/-- **The spin–statistics theorem** (algebraic core, Pauli's argument).

For a relativistic quantum field whose two-point function does not vanish
identically at spacelike separation, the statistics sign `ε` is determined by the
spin: `ε = (-1)^{2j}`.  Thus integer-spin fields are bosonic and half-integer-spin
fields are fermionic. -/
theorem spin_statistics {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : RelativisticField T H) (hF : F.Nondegenerate) :
    F.stat = (-1 : ℤ) ^ F.twiceSpin := by
  obtain ⟨f, g, hfg, hne⟩ := hF
  by_contra hstat
  have hcast : (F.stat : ℂ) ≠ (-1 : ℂ) ^ F.twiceSpin := by
    intro h
    apply hstat
    have : ((F.stat : ℤ) : ℂ) = (((-1 : ℤ) ^ F.twiceSpin : ℤ) : ℂ) := by push_cast; simpa using h
    exact_mod_cast this
  exact hne (F.wightman_eq_zero_of_wrong_statistics hcast f g hfg)

/-- Integer spin implies Bose statistics. -/
theorem spin_statistics_boson {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : RelativisticField T H) (hF : F.Nondegenerate) (hspin : Even F.twiceSpin) :
    F.stat = 1 := by
  rw [spin_statistics F hF, hspin.neg_one_pow]

/-- Half-integer spin implies Fermi statistics. -/
theorem spin_statistics_fermion {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : RelativisticField T H) (hF : F.Nondegenerate) (hspin : Odd F.twiceSpin) :
    F.stat = -1 := by
  rw [spin_statistics F hF, hspin.neg_one_pow]

/-- Equivalently: the field is bosonic if and only if its spin is an integer. -/
theorem spin_statistics_iff {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : RelativisticField T H) (hF : F.Nondegenerate) :
    F.stat = 1 ↔ ∃ n : ℤ, F.spin = (n : ℚ) := by
  constructor
  · intro h
    refine ⟨(F.twiceSpin / 2 : ℕ), ?_⟩
    have hpow : ((-1 : ℤ)) ^ F.twiceSpin = 1 := by rw [← spin_statistics F hF]; exact h
    have heven : Even F.twiceSpin := by
      rcases Nat.even_or_odd F.twiceSpin with he | ho
      · exact he
      · rw [ho.neg_one_pow] at hpow; norm_num at hpow
    obtain ⟨k, hk⟩ := heven
    subst hk
    have : (k + k) / 2 = k := by omega
    rw [RelativisticField.spin, this]
    push_cast
    ring
  · rintro ⟨n, hn⟩
    have heven : Even F.twiceSpin := by
      rcases Nat.even_or_odd F.twiceSpin with he | ho
      · exact he
      · exfalso
        obtain ⟨k, hk⟩ := ho
        rw [RelativisticField.spin, hk] at hn
        have : (2 * (k : ℚ) + 1) = 2 * (n : ℚ) := by
          field_simp at hn
          push_cast at hn ⊢
          linarith
        have hz : (2 * (k : ℤ) + 1) = 2 * n := by exact_mod_cast this
        omega
    exact spin_statistics_boson F hF heven

/-!
## Non-vacuity: an explicit spin-0 Bose model

`H = ℂ`, one test function, `φ = 1`.  Its two-point function is `1 ≠ 0`, so the
hypotheses of `Frontier.spin_statistics` are consistent, and indeed `ε = +1 = (-1)^0`.
-/

/-- A spin-`0` field quantized with commutators, with nonvanishing two-point function. -/
noncomputable def scalarBoseModel : RelativisticField Unit ℂ where
  vacuum := 1
  field _ := LinearMap.id
  adjField _ := LinearMap.id
  adj_inner _ x y := by simp [RCLike.inner_apply]
  spacelike _ _ := True
  twiceSpin := 0
  stat := 1
  stat_isSign := Or.inl rfl
  locality _ _ _ := by simp
  rotation _ _ _ := by simp

theorem scalarBoseModel_nondegenerate : scalarBoseModel.Nondegenerate := by
  refine ⟨(), (), trivial, ?_⟩
  simp [RelativisticField.wightman, scalarBoseModel, RCLike.inner_apply]

/-- The Bose model has spin `0`. -/
theorem scalarBoseModel_spin : scalarBoseModel.spin = 0 := by
  simp [RelativisticField.spin, scalarBoseModel]

/-- Consistency check: the spin-`0` model satisfies the conclusion of the theorem. -/
theorem scalarBoseModel_stat : scalarBoseModel.stat = 1 :=
  spin_statistics_boson _ scalarBoseModel_nondegenerate (by simp [scalarBoseModel])

/-!
## Non-vacuity: an explicit spin-1/2 Fermi model

`H = ℂ²`, two test functions with operators
`φ(f) = [[0,1],[1,0]]`, `φ(g) = [[0,1],[-1,0]]`, vacuum `Ω = e₀`.
Then `⟪Ω, φ(f) φ(g)† Ω⟫ = 1` and `⟪Ω, φ(g)† φ(f) Ω⟫ = -1`, realizing
`ε = -1 = (-1)^1`.
-/

/-- The operator `[[0,1],[1,0]]` on `ℂ²`. -/
noncomputable def swapOp : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun x := WithLp.toLp 2 ![x 1, x 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- The operator `[[0,1],[-1,0]]` on `ℂ²`. -/
noncomputable def rotOp : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun x := WithLp.toLp 2 ![x 1, -x 0]
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- The adjoint `[[0,-1],[1,0]]` of `rotOp`. -/
noncomputable def rotOpAdj : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun x := WithLp.toLp 2 ![-x 1, x 0]
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- A spin-`1/2` field quantized with anticommutators, with nonvanishing two-point
function. -/
noncomputable def spinorFermiModel : RelativisticField Bool (EuclideanSpace ℂ (Fin 2)) where
  vacuum := WithLp.toLp 2 ![1, 0]
  field b := if b then swapOp else rotOp
  adjField b := if b then swapOp else rotOpAdj
  adj_inner b x y := by
    cases b <;>
      simp [swapOp, rotOp, rotOpAdj, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply] <;>
      ring
  spacelike f g := f ≠ g
  twiceSpin := 1
  stat := -1
  stat_isSign := Or.inr rfl
  locality f g _ := by
    cases f <;> cases g <;>
      simp [swapOp, rotOp, rotOpAdj, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  rotation f g _ := by
    cases f <;> cases g <;>
      simp [swapOp, rotOp, rotOpAdj, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]

theorem spinorFermiModel_nondegenerate : spinorFermiModel.Nondegenerate := by
  refine ⟨true, false, by simp, ?_⟩
  simp [RelativisticField.wightman, spinorFermiModel, swapOp, rotOpAdj,
    PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]

/-- The Fermi model has spin `1/2`. -/
theorem spinorFermiModel_spin : spinorFermiModel.spin = 1 / 2 := by
  simp [RelativisticField.spin, spinorFermiModel]

/-- Consistency check: the spin-`1/2` model satisfies the conclusion of the theorem. -/
theorem spinorFermiModel_stat : spinorFermiModel.stat = -1 :=
  spin_statistics_fermion _ spinorFermiModel_nondegenerate (by simp [spinorFermiModel])

end Frontier

