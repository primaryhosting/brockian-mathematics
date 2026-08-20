import Mathlib
/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

namespace Chem

/-! ## An affine dimension count for linear systems -/

/-- For a surjective linear map `f`, the solution set of `f v = b` is nonempty and its
direction (the vector span of the solution set) is exactly `ker f`. -/
theorem vectorSpan_solution_set {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (hf : Function.Surjective f) (b : W) :
    {v : V | f v = b}.Nonempty ∧
      vectorSpan ℝ {v : V | f v = b} = LinearMap.ker f := by
  obtain ⟨v₀, hv₀⟩ := hf b
  refine ⟨⟨v₀, hv₀⟩, le_antisymm ?_ ?_⟩
  · rw [vectorSpan_def]
    apply Submodule.span_le.2
    rintro x ⟨p, hp, q, hq, rfl⟩
    simp only [Set.mem_setOf_eq] at hp hq
    simp [LinearMap.mem_ker, vsub_eq_sub, hp, hq]
  · intro w hw
    have hrw : w = (v₀ + w) -ᵥ v₀ := by simp
    rw [hrw]
    refine vsub_mem_vectorSpan ℝ ?_ hv₀
    simp only [Set.mem_setOf_eq, map_add, hv₀, LinearMap.mem_ker.1 hw, add_zero]

/-- **Key intermediate lemma (affine rank–nullity).**  If `f : V →ₗ[ℝ] W` is surjective and
`V` is finite dimensional, then for every `b` the affine solution set `{v | f v = b}` is
nonempty and its affine dimension is `finrank V - finrank W`. -/
theorem finrank_vectorSpan_solution_set {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f) (b : W) :
    {v : V | f v = b}.Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ {v : V | f v = b}) + Module.finrank ℝ W
        = Module.finrank ℝ V := by
  obtain ⟨hne, hspan⟩ := vectorSpan_solution_set f hf b
  refine ⟨hne, ?_⟩
  rw [hspan]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hf] at h
  simp only [finrank_top] at h
  omega

/-! ## The intensive state space of a `P`-phase, `C`-component system -/

/-- The space of intensive variables of a system with `C` components and `P` phases:
temperature, pressure, and the mole fraction of each component in each phase. -/
abbrev PhaseState (C P : ℕ) : Type := ℝ × ℝ × (Fin P → Fin C → ℝ)

/-- The normalization constraints: in each phase the mole fractions sum to `1`.
This linear map sends a state to the vector of per-phase sums of mole fractions. -/
def normalization (C P : ℕ) : PhaseState C P →ₗ[ℝ] (Fin P → ℝ) where
  toFun s j := ∑ i, s.2.2 j i
  map_add' := by intro s t; funext j; simp [Finset.sum_add_distrib]
  map_smul' := by intro c s; funext j; simp [Finset.mul_sum]

/-- The full constraint map: normalization of mole fractions in each phase together with the
`(P-1) * C` equalities of chemical potentials between phases (encoded by a linear map
`equil`, i.e. the linearization of the equilibrium conditions). -/
def constraints (C P : ℕ) (equil : PhaseState C P →ₗ[ℝ] (Fin (P - 1) → Fin C → ℝ)) :
    PhaseState C P →ₗ[ℝ] ((Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)) :=
  (normalization C P).prod equil

theorem finrank_matrix_space (n m : ℕ) :
    Module.finrank ℝ (Fin n → Fin m → ℝ) = n * m := by
  rw [Module.finrank_pi_fintype ℝ]
  simp

theorem finrank_phaseState (C P : ℕ) :
    Module.finrank ℝ (PhaseState C P) = 2 + P * C := by
  show Module.finrank ℝ (ℝ × ℝ × (Fin P → Fin C → ℝ)) = 2 + P * C
  rw [Module.finrank_prod, Module.finrank_prod, finrank_matrix_space, Module.finrank_self]
  omega

theorem finrank_constraintSpace (C P : ℕ) :
    Module.finrank ℝ ((Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)) = P + (P - 1) * C := by
  rw [Module.finrank_prod, finrank_matrix_space, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-! ## The Gibbs phase rule -/

/-- **Gibbs phase rule.**  Consider a system of `C` components distributed over `P ≥ 1`
phases.  Its intensive state is described by temperature, pressure and the mole fractions
`x j i` of component `i` in phase `j`.  The equilibrium conditions are:

* normalization: `∑ i, x j i = 1` for each phase `j`;
* equality of the chemical potentials of each component across the phases, encoded as a
  linear map `equil : PhaseState C P →ₗ[ℝ] (Fin (P-1) → Fin C → ℝ)`, giving `(P-1) * C`
  conditions.

Under the nondegeneracy hypothesis that these constraints are independent (the combined
constraint map is surjective), the set of equilibrium states is a nonempty affine subspace
whose dimension — the number `F` of degrees of freedom — satisfies `F + P = C + 2`,
i.e. `F = C - P + 2`. -/
theorem gibbs_phase_rule (C P : ℕ) (hP : 1 ≤ P)
    (equil : PhaseState C P →ₗ[ℝ] (Fin (P - 1) → Fin C → ℝ))
    (hsurj : Function.Surjective (constraints C P equil)) :
    ({s : PhaseState C P | (∀ j, ∑ i, s.2.2 j i = 1) ∧ equil s = 0}).Nonempty ∧
      Module.finrank ℝ
          (vectorSpan ℝ {s : PhaseState C P | (∀ j, ∑ i, s.2.2 j i = 1) ∧ equil s = 0})
        + P = C + 2 := by
  have hset : {s : PhaseState C P | (∀ j, ∑ i, s.2.2 j i = 1) ∧ equil s = 0}
      = {s : PhaseState C P | constraints C P equil s = (1, 0)} := by
    ext s
    simp only [Set.mem_setOf_eq, constraints, LinearMap.prod_apply, Pi.prod, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨funext fun j => by simpa [normalization] using h1 j, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ?_, h2⟩
      have := congrFun h1 j
      simpa [normalization] using this
  rw [hset]
  obtain ⟨hne, hrank⟩ :=
    finrank_vectorSpan_solution_set (constraints C P equil) hsurj (1, 0)
  refine ⟨hne, ?_⟩
  rw [finrank_phaseState, finrank_constraintSpace] at hrank
  have hrank' : Module.finrank ℝ
      (vectorSpan ℝ {s : PhaseState C P | constraints C P equil s = (1, 0)})
      + (P + (P - 1) * C) = 2 + P * C := hrank
  have h1 : (P - 1) * C = P * C - C := by
    cases P with
    | zero => simp
    | succ n => simp [Nat.succ_mul]
  have h2 : C ≤ P * C := Nat.le_mul_of_pos_left C hP
  omega

/-- Non-vacuity check: for a one-phase system with at least one component the nondegeneracy
hypothesis of `Chem.gibbs_phase_rule` is satisfiable (so the phase rule applies, giving
`F = C + 1` degrees of freedom). -/
theorem exists_nondegenerate_single_phase (C : ℕ) (hC : 1 ≤ C) :
    ∃ equil : PhaseState C 1 →ₗ[ℝ] (Fin (1 - 1) → Fin C → ℝ),
      Function.Surjective (constraints C 1 equil) := by
  refine ⟨0, ?_⟩
  rintro ⟨a, b⟩
  refine ⟨(0, 0, fun j i => if i = ⟨0, hC⟩ then a j else 0), ?_⟩
  have hb : b = 0 := by funext k; exact absurd k.2 (by omega)
  simp [constraints, normalization, hb, LinearMap.prod_apply, Finset.sum_ite_eq']

end Chem

