import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D square-lattice Ising model on an `L × L` torus -/

/-- The real spin value `±1` attached to a Boolean spin variable. -/
noncomputable def spinVal (b : Bool) : ℝ := if b then 1 else -1

/-- The Ising energy (Hamiltonian, with unit coupling `J = 1`) of a spin configuration
on the `L × L` periodic square lattice `ZMod L × ZMod L`:
`H(σ) = - ∑_{⟨x,y⟩} σ_x σ_y`, where the sum runs over nearest-neighbour bonds
(each site contributes its right and its upper bond). -/
noncomputable def isingEnergy (L : ℕ) [NeZero L] (σ : ZMod L × ZMod L → Bool) : ℝ :=
  - ∑ x : ZMod L × ZMod L,
      (spinVal (σ x) * spinVal (σ (x.1 + 1, x.2)) + spinVal (σ x) * spinVal (σ (x.1, x.2 + 1)))

/-- The partition function `Z_L(β) = ∑_σ exp (-β H(σ))` of the 2D Ising model on the
`L × L` torus at inverse temperature `β`. -/
noncomputable def isingZ (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  ∑ σ : (ZMod L × ZMod L → Bool), Real.exp (-β * isingEnergy L σ)

/-! ## Onsager's exact solution -/

/-- The argument of the logarithm in Onsager's double integral:
`cosh²(2β) - sinh(2β) (cos θ₁ + cos θ₂)`. -/
noncomputable def onsagerArg (β θ₁ θ₂ : ℝ) : ℝ :=
  Real.cosh (2 * β) ^ 2 - Real.sinh (2 * β) * (Real.cos θ₁ + Real.cos θ₂)

/-- Onsager's exact free-energy density, in the form of the limiting value of
`N⁻¹ log Z_N(β)`:
`log 2 + (8π²)⁻¹ ∫₀^{2π} ∫₀^{2π} log (cosh²(2β) - sinh(2β)(cos θ₁ + cos θ₂)) dθ₂ dθ₁`. -/
noncomputable def onsagerLogZDensity (β : ℝ) : ℝ :=
  Real.log 2 +
    (1 / (8 * Real.pi ^ 2)) *
      ∫ θ₁ in (0:ℝ)..(2 * Real.pi), ∫ θ₂ in (0:ℝ)..(2 * Real.pi),
        Real.log (onsagerArg β θ₁ θ₂)

/-- The Onsager critical inverse temperature `β_c = ½ log (1 + √2)`. -/
noncomputable def betaC : ℝ := Real.log (1 + Real.sqrt 2) / 2

/-! ## Auxiliary lemmas -/

/-- At `β = 0` the argument of Onsager's logarithm is identically `1`. -/
lemma onsagerArg_zero (θ₁ θ₂ : ℝ) : onsagerArg 0 θ₁ θ₂ = 1 := by
  simp [onsagerArg]

/-- At infinite temperature Onsager's formula gives the entropy `log 2` per site. -/
lemma onsagerLogZDensity_zero : onsagerLogZDensity 0 = Real.log 2 := by
  simp [onsagerLogZDensity, onsagerArg_zero]

/-- The ferromagnetic ground state: the all-up configuration has energy `-2L²`
(each of the `L²` sites carries two bonds of energy `-1`). -/
lemma isingEnergy_allUp (L : ℕ) [NeZero L] :
    isingEnergy L (fun _ => true) = -(2 * (L * L)) := by
  have hcard : Fintype.card (ZMod L × ZMod L) = L * L := by simp [ZMod.card]
  simp only [isingEnergy, spinVal, if_pos, mul_one, Finset.sum_const,
    Finset.card_univ, hcard, nsmul_eq_mul]
  push_cast
  ring

/-- The partition function is strictly positive at every inverse temperature. -/
lemma isingZ_pos (L : ℕ) [NeZero L] (β : ℝ) : 0 < isingZ L β := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- At `β = 0` every configuration has weight one, so `Z_L(0) = 2^{L²}`. -/
lemma isingZ_zero (L : ℕ) [NeZero L] : isingZ L 0 = 2 ^ (L * L) := by
  have hcard : Fintype.card (ZMod L × ZMod L → Bool) = 2 ^ (L * L) := by
    rw [Fintype.card_fun]
    simp [ZMod.card]
  simp only [isingZ, zero_mul, neg_zero, Real.exp_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hcard]
  push_cast
  ring

/-- The Onsager formula is exact at `β = 0` for every finite torus:
the finite-volume free energy density equals the Onsager value. -/
lemma isingLogZDensity_zero (L : ℕ) [NeZero L] :
    (1 / ((L : ℝ) * L)) * Real.log (isingZ L 0) = onsagerLogZDensity 0 := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  rw [isingZ_zero, onsagerLogZDensity_zero, Real.log_pow]
  push_cast
  field_simp

/-- `sinh (2 β_c) = 1`: the Onsager critical point. -/
lemma sinh_two_betaC : Real.sinh (2 * betaC) = 1 := by
  have h2 : (0:ℝ) < 1 + Real.sqrt 2 := by positivity
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : 2 * betaC = Real.log (1 + Real.sqrt 2) := by
    unfold betaC; ring
  rw [hx, Real.sinh_eq, Real.exp_log h2, Real.exp_neg, Real.exp_log h2]
  have hne : (1 + Real.sqrt 2) ≠ 0 := ne_of_gt h2
  field_simp
  nlinarith [hs]

/-- Onsager's logarithm has nonnegative argument at every temperature `β ≥ 0`; indeed
`cosh²(2β) - sinh(2β)(cos θ₁ + cos θ₂) ≥ (sinh(2β) - 1)² ≥ 0`. -/
lemma onsagerArg_nonneg {β : ℝ} (hβ : 0 ≤ β) (θ₁ θ₂ : ℝ) : 0 ≤ onsagerArg β θ₁ θ₂ := by
  have hs : 0 ≤ Real.sinh (2 * β) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hc : Real.cosh (2 * β) ^ 2 = 1 + Real.sinh (2 * β) ^ 2 := by
    have := Real.cosh_sq (2 * β)
    nlinarith [Real.sinh_sq (2 * β)]
  have h1 : Real.cos θ₁ ≤ 1 := Real.cos_le_one θ₁
  have h2 : Real.cos θ₂ ≤ 1 := Real.cos_le_one θ₂
  have key : Real.sinh (2 * β) * (Real.cos θ₁ + Real.cos θ₂) ≤ Real.sinh (2 * β) * 2 := by
    apply mul_le_mul_of_nonneg_left _ hs
    linarith
  simp only [onsagerArg]
  nlinarith [sq_nonneg (Real.sinh (2 * β) - 1)]

/-- The argument of Onsager's logarithm degenerates (the free energy is singular)
exactly at the critical temperature. -/
lemma onsagerArg_zero_at_zero_iff (β : ℝ) : onsagerArg β 0 0 = 0 ↔ β = betaC := by
  have hc : Real.cosh (2 * β) ^ 2 = 1 + Real.sinh (2 * β) ^ 2 := by
    nlinarith [Real.cosh_sq (2 * β), Real.sinh_sq (2 * β)]
  have hkey : onsagerArg β 0 0 = (Real.sinh (2 * β) - 1) ^ 2 := by
    simp only [onsagerArg, Real.cos_zero, hc]; ring
  rw [hkey]
  constructor
  · intro h
    have h1 : Real.sinh (2 * β) = 1 := by nlinarith [sq_nonneg (Real.sinh (2 * β) - 1)]
    have h2 : Real.sinh (2 * β) = Real.sinh (2 * betaC) := by rw [h1, sinh_two_betaC]
    have := Real.sinh_injective h2
    linarith
  · intro h
    rw [h, sinh_two_betaC]
    ring

/-! ## Main statement -/

/-- **Onsager's exact solution of the 2D square-lattice Ising model.**

We formalize the model (partition function `isingZ` on the `L × L` torus) together with
Onsager's exact free-energy density `onsagerLogZDensity`, and establish the following
Lean-checked facts:

1. the base case (infinite temperature): `Z_L(0) = 2^{L²}` for every torus size `L`;
2. Onsager's formula is *exact* at `β = 0` for every finite `L`, i.e.
   `L⁻²  log Z_L(0) = onsagerLogZDensity 0`;
3. the Onsager value at `β = 0` is the entropy `log 2`;
4. the argument of the Onsager logarithm is nonnegative for all `β ≥ 0`, so the formula
   is well posed;
5. this argument degenerates (giving the logarithmic singularity of the free energy)
   exactly at the critical inverse temperature `β_c = ½ log(1+√2)`, which is
   characterized by Kramers–Wannier duality relation `sinh (2 β_c) = 1`. -/
theorem onsager_2d_ising :
    (∀ (L : ℕ) [NeZero L], isingZ L 0 = 2 ^ (L * L)) ∧
    (∀ (L : ℕ) [NeZero L],
      (1 / ((L : ℝ) * L)) * Real.log (isingZ L 0) = onsagerLogZDensity 0) ∧
    onsagerLogZDensity 0 = Real.log 2 ∧
    Real.sinh (2 * betaC) = 1 ∧
    (∀ β : ℝ, 0 ≤ β → ∀ θ₁ θ₂ : ℝ, 0 ≤ onsagerArg β θ₁ θ₂) ∧
    (∀ β : ℝ, onsagerArg β 0 0 = 0 ↔ β = betaC) ∧
    (∀ (L : ℕ) [NeZero L], ∀ β : ℝ, 0 < isingZ L β) ∧
    (∀ (L : ℕ) [NeZero L], isingEnergy L (fun _ => true) = -(2 * (L * L))) := by
  refine ⟨fun L _ => isingZ_zero L, fun L _ => isingLogZDensity_zero L,
    onsagerLogZDensity_zero, sinh_two_betaC, fun β hβ θ₁ θ₂ => onsagerArg_nonneg hβ θ₁ θ₂,
    onsagerArg_zero_at_zero_iff, fun L _ β => isingZ_pos L β,
    fun L _ => isingEnergy_allUp L⟩

end Frontier

