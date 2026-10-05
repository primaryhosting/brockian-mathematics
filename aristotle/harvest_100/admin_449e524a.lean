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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- Index set of the intensive variables of a heterogeneous system with `C` components
distributed over `P` phases: the two field variables (temperature and pressure), encoded by
`Bool`, together with the mole fraction `x j i` of component `i` in phase `j`.
Hence there are `2 + P * C` variables. -/
abbrev VarIndex (C P : ℕ) : Type := Bool ⊕ (Fin P × Fin C)

/-- Index set of the equilibrium constraints: one normalization condition
`∑ i, x j i = 1` per phase `j` (that is `P` conditions), together with the equalities of
chemical potentials between consecutive phases, `μ i (j) = μ i (j+1)`, one for each component
`i` and each of the `P - 1` consecutive pairs of phases.
Hence there are `P + (P - 1) * C` constraints. -/
abbrev ConIndex (C P : ℕ) : Type := Fin P ⊕ (Fin (P - 1) × Fin C)

/-- The number of intensive variables is `2 + P * C`. -/
lemma card_varIndex (C P : ℕ) : Fintype.card (VarIndex C P) = 2 + P * C := by
  simp [VarIndex, Fintype.card_sum]

/-- The number of equilibrium constraints is `P + (P - 1) * C`. -/
lemma card_conIndex (C P : ℕ) : Fintype.card (ConIndex C P) = P + (P - 1) * C := by
  simp [ConIndex, Fintype.card_sum]

/-- The bookkeeping behind the phase rule: (number of variables) − (number of constraints)
equals `C - P + 2`, computed in `ℤ` (here `1 ≤ P`). -/
lemma phase_rule_count (C P : ℕ) (hP : 1 ≤ P) :
    (Fintype.card (VarIndex C P) : ℤ) - (Fintype.card (ConIndex C P) : ℤ)
      = (C : ℤ) - (P : ℤ) + 2 := by
  have hP' : ((P - 1 : ℕ) : ℤ) = (P : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (P : ℤ) := by exact_mod_cast hP
    push_cast [Nat.cast_sub hP]
    ring
  rw [card_varIndex, card_conIndex]
  push_cast [hP']
  ring

/-- The hypotheses of the phase rule are not vacuous: whenever `1 ≤ P` and `P ≤ C + 2`
(i.e. whenever the predicted number of degrees of freedom is nonnegative) there really is a
surjective constraint map from the variable space to the constraint space. -/
lemma exists_surjective_constraints (C P : ℕ) (hP : 1 ≤ P) (hPC : P ≤ C + 2) :
    ∃ L : (VarIndex C P → ℝ) →ₗ[ℝ] (ConIndex C P → ℝ), Function.Surjective L := by
  have hcard : Fintype.card (ConIndex C P) ≤ Fintype.card (VarIndex C P) := by
    rw [card_varIndex, card_conIndex]
    obtain ⟨k, rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.succ_mul]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨LinearMap.funLeft ℝ ℝ e, LinearMap.funLeft_surjective_of_injective ℝ ℝ e e.injective⟩

/-- The lower phase `j` of the `k`-th consecutive pair of phases. -/
def phaseLo {P : ℕ} (k : Fin (P - 1)) : Fin P := ⟨k.1, by have := k.isLt; omega⟩

/-- The upper phase `j + 1` of the `k`-th consecutive pair of phases. -/
def phaseHi {P : ℕ} (k : Fin (P - 1)) : Fin P := ⟨k.1 + 1, by have := k.isLt; omega⟩

/-- The linearized equilibrium constraint map of a system with `C` components and `P` phases,
built explicitly from the physical conditions.  Given the linearized chemical potentials
`mu j i : (VarIndex C P → ℝ) →ₗ[ℝ] ℝ` of component `i` in phase `j`, the constraint map sends a
state `x` to the tuple consisting of

* the sum `∑ i, x (j, i)` of the mole fractions in each phase `j`, and
* the differences `mu j i x - mu (j+1) i x` of chemical potentials between consecutive phases. -/
noncomputable def constraintMap (C P : ℕ)
    (mu : Fin P → Fin C → ((VarIndex C P → ℝ) →ₗ[ℝ] ℝ)) :
    (VarIndex C P → ℝ) →ₗ[ℝ] (ConIndex C P → ℝ) where
  toFun x := Sum.elim (fun j => ∑ i, x (Sum.inr (j, i)))
      (fun p => mu (phaseLo p.1) p.2 x - mu (phaseHi p.1) p.2 x)
  map_add' x y := by
    funext c
    cases c with
    | inl j => simp [Finset.sum_add_distrib]
    | inr p => simp; ring
  map_smul' c x := by
    funext d
    cases d with
    | inl j => simp [Finset.mul_sum]
    | inr p => simp; ring

/-- An auxiliary embedding: when `1 ≤ C` and `P ≤ C + 2` the `(P-1) * C` chemical-potential
constraints can be indexed injectively by variables other than the distinguished mole
fractions `x j 0`, one of which is reserved for each phase to absorb the normalization. -/
lemma exists_embedding_avoiding_reserved (C P : ℕ) (hC : 1 ≤ C) (hPC : P ≤ C + 2) :
    ∃ e : (Fin (P - 1) × Fin C) ↪ VarIndex C P,
      ∀ (c : Fin (P - 1) × Fin C) (j : Fin P), e c ≠ Sum.inr (j, (⟨0, hC⟩ : Fin C)) := by
  classical
  have hcard : Fintype.card (Fin (P - 1) × Fin C)
      ≤ Fintype.card (Bool ⊕ (Fin P × Fin (C - 1))) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
    rcases P with _ | q
    · simp
    · simp only [Nat.succ_sub_one]
      have h1 : q * (c + 1) = q * c + q := by ring
      have h2 : (q + 1) * c = q * c + c := by ring
      omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨f.trans ⟨Sum.elim (fun t => Sum.inl t)
      (fun q => Sum.inr (q.1, ⟨q.2.1 + 1, by have := q.2.isLt; omega⟩)), ?_⟩, ?_⟩
  · rintro (a | a) (b | b) h <;> simp_all [Fin.ext_iff, Prod.ext_iff]
  · rintro c j
    simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    rcases h : f c with a | a <;> simp [Fin.ext_iff]

/-- Non-vacuity of the explicit form of the phase rule: whenever there is at least one component
and `P ≤ C + 2` (the range in which the predicted number of degrees of freedom is nonnegative),
there are linearized chemical potentials `mu` whose equilibrium constraints really are
independent, i.e. for which `constraintMap C P mu` is surjective. -/
lemma exists_surjective_constraintMap (C P : ℕ) (hC : 1 ≤ C) (hPC : P ≤ C + 2) :
    ∃ mu : Fin P → Fin C → ((VarIndex C P → ℝ) →ₗ[ℝ] ℝ),
      Function.Surjective (constraintMap C P mu) := by
  classical
  obtain ⟨e, he⟩ := exists_embedding_avoiding_reserved C P hC hPC
  set i0 : Fin C := ⟨0, hC⟩ with hi0
  set r : Fin (P - 1) → Fin C → ((VarIndex C P → ℝ) →ₗ[ℝ] ℝ) :=
    fun k i => LinearMap.proj (e (k, i)) with hr
  refine ⟨fun j i => ∑ l ∈ Finset.univ.filter (fun l : Fin (P - 1) => (j : ℕ) ≤ (l : ℕ)), r l i, ?_⟩
  intro b
  set y : VarIndex C P → ℝ :=
    fun v => if h : ∃ c, e c = v then b (Sum.inr h.choose) else 0 with hy
  set x : VarIndex C P → ℝ :=
    Sum.elim (fun t => y (Sum.inl t))
      (fun p => if p.2 = i0 then
          b (Sum.inl p.1) - ∑ i' ∈ Finset.univ.erase i0, y (Sum.inr (p.1, i'))
        else y (Sum.inr p)) with hx
  have hye : ∀ c : Fin (P - 1) × Fin C, y (e c) = b (Sum.inr c) := by
    intro c
    have hex : ∃ c', e c' = e c := ⟨c, rfl⟩
    have hch : hex.choose = c := e.injective hex.choose_spec
    simp only [hy, dif_pos hex, hch]
  have hA : ∀ v : VarIndex C P, (∀ j : Fin P, v ≠ Sum.inr (j, i0)) → x v = y v := by
    rintro (t | ⟨j, i⟩) h
    · simp [hx]
    · have hne : i ≠ i0 := by rintro rfl; exact h j rfl
      simp [hx, hne]
  refine ⟨x, ?_⟩
  funext c
  rcases c with j | ⟨k, i⟩
  · show ∑ i, x (Sum.inr (j, i)) = b (Sum.inl j)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    have h1 : x (Sum.inr (j, i0))
        = b (Sum.inl j) - ∑ i' ∈ Finset.univ.erase i0, y (Sum.inr (j, i')) := by simp [hx]
    have h2 : ∑ i' ∈ Finset.univ.erase i0, x (Sum.inr (j, i'))
        = ∑ i' ∈ Finset.univ.erase i0, y (Sum.inr (j, i')) := by
      refine Finset.sum_congr rfl fun i' hi' => ?_
      have hne : i' ≠ i0 := (Finset.mem_erase.mp hi').1
      simp [hx, hne]
    rw [h1, h2]; ring
  · show (∑ l ∈ Finset.univ.filter (fun l : Fin (P - 1) => ((phaseLo k : Fin P) : ℕ) ≤ (l : ℕ)),
            r l i) x
        - (∑ l ∈ Finset.univ.filter (fun l : Fin (P - 1) => ((phaseHi k : Fin P) : ℕ) ≤ (l : ℕ)),
            r l i) x
        = b (Sum.inr (k, i))
    have hsplit :
        Finset.univ.filter (fun l : Fin (P - 1) => ((phaseLo k : Fin P) : ℕ) ≤ (l : ℕ))
          = insert k
            (Finset.univ.filter (fun l : Fin (P - 1) => ((phaseHi k : Fin P) : ℕ) ≤ (l : ℕ))) := by
      ext l
      simp [phaseLo, phaseHi, Fin.ext_iff]
      omega
    have hnot :
        k ∉ Finset.univ.filter (fun l : Fin (P - 1) => ((phaseHi k : Fin P) : ℕ) ≤ (l : ℕ)) := by
      simp [phaseHi]
    have hrk : r k i x = b (Sum.inr (k, i)) := by
      have hxy : x (e (k, i)) = y (e (k, i)) := hA _ (fun j => he (k, i) j)
      simp only [hr, LinearMap.proj_apply, hxy, hye (k, i)]
    rw [hsplit]
    simp only [LinearMap.sum_apply, Finset.sum_insert hnot, LinearMap.add_apply, hrk]
    ring

/-- **Gibbs' phase rule**, as an affine dimension count.

Consider a heterogeneous system with `C` components and `P ≥ 1` phases.  Its state is described
by the `2 + P * C` intensive variables indexed by `VarIndex C P` (temperature, pressure, and the
mole fractions of each component in each phase), and equilibrium is expressed by the
`P + (P - 1) * C` conditions indexed by `ConIndex C P` (normalization of the mole fractions in
each phase, and equality of the chemical potential of each component across the phases).

Linearizing these conditions at an equilibrium state gives a linear map `L`, and the standard
non‑degeneracy assumption of the derivation is that the constraints are independent, i.e. that
`L` is surjective.  Then, for any admissible right-hand side `b`, the set of solutions is a
nonempty affine subspace — a coset of `ker L` — whose dimension, the number of degrees of
freedom, is

  `F = C - P + 2`. -/
theorem gibbs_phase_rule (C P : ℕ) (hP : 1 ≤ P)
    (L : (VarIndex C P → ℝ) →ₗ[ℝ] (ConIndex C P → ℝ))
    (hL : Function.Surjective L) (b : ConIndex C P → ℝ) :
    (Module.finrank ℝ (LinearMap.ker L) : ℤ) = (C : ℤ) - (P : ℤ) + 2 ∧
      ∃ x₀ : VarIndex C P → ℝ,
        {x : VarIndex C P → ℝ | L x = b}
          = {x : VarIndex C P → ℝ | x - x₀ ∈ LinearMap.ker L} := by
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hL
  have hrk : Module.finrank ℝ (LinearMap.range L) + Module.finrank ℝ (LinearMap.ker L)
      = Module.finrank ℝ (VarIndex C P → ℝ) := LinearMap.finrank_range_add_finrank_ker L
  have hrange' : Module.finrank ℝ (LinearMap.range L) = Fintype.card (ConIndex C P) := by
    rw [hrange]
    simp
  have hdom : Module.finrank ℝ (VarIndex C P → ℝ) = Fintype.card (VarIndex C P) :=
    Module.finrank_fintype_fun_eq_card ℝ
  rw [hrange', hdom] at hrk
  constructor
  · have : (Fintype.card (ConIndex C P) : ℤ) + (Module.finrank ℝ (LinearMap.ker L) : ℤ)
        = (Fintype.card (VarIndex C P) : ℤ) := by exact_mod_cast hrk
    have hcount := phase_rule_count C P hP
    linarith
  · obtain ⟨x₀, hx₀⟩ := hL b
    refine ⟨x₀, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, LinearMap.mem_ker, map_sub, hx₀, sub_eq_zero]

/-- **Gibbs' phase rule** for the explicitly constructed constraint map.

The equilibrium states of a system of `C` components in `P ≥ 1` phases are the states `x`
(temperature, pressure, and mole fractions) whose mole fractions are normalized in every phase
and for which the chemical potential of every component agrees in all phases.  Assuming, as in
the classical derivation, that these linearized conditions are independent (surjectivity of
`constraintMap C P mu`), the set of equilibrium states is an affine subspace — a coset of the
kernel — of dimension `F = C - P + 2`. -/
theorem gibbs_phase_rule_explicit (C P : ℕ) (hP : 1 ≤ P)
    (mu : Fin P → Fin C → ((VarIndex C P → ℝ) →ₗ[ℝ] ℝ))
    (hmu : Function.Surjective (constraintMap C P mu)) :
    (Module.finrank ℝ (LinearMap.ker (constraintMap C P mu)) : ℤ) = (C : ℤ) - (P : ℤ) + 2 ∧
      ∃ x₀ : VarIndex C P → ℝ,
        {x : VarIndex C P → ℝ |
            (∀ j : Fin P, ∑ i, x (Sum.inr (j, i)) = 1) ∧
            (∀ (k : Fin (P - 1)) (i : Fin C),
              mu (phaseLo k) i x = mu (phaseHi k) i x)}
          = {x : VarIndex C P → ℝ | x - x₀ ∈ LinearMap.ker (constraintMap C P mu)} := by
  obtain ⟨hdim, x₀, hx₀⟩ :=
    gibbs_phase_rule C P hP (constraintMap C P mu) hmu
      (Sum.elim (fun _ => 1) (fun _ => 0))
  refine ⟨hdim, x₀, ?_⟩
  rw [← hx₀]
  ext x
  simp only [Set.mem_setOf_eq, funext_iff, Sum.forall, Prod.forall, constraintMap,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, sub_eq_zero]

/-- An unconditional form of the phase rule: for any physically meaningful data
(`1 ≤ C` components, `1 ≤ P ≤ C + 2` phases) there exist linearized chemical potentials whose
equilibrium constraints are independent, and for those the space of equilibrium states has
dimension exactly `F = C - P + 2`. -/
theorem gibbs_phase_rule_nonvacuous (C P : ℕ) (hP : 1 ≤ P) (hC : 1 ≤ C) (hPC : P ≤ C + 2) :
    ∃ mu : Fin P → Fin C → ((VarIndex C P → ℝ) →ₗ[ℝ] ℝ),
      Function.Surjective (constraintMap C P mu) ∧
      (Module.finrank ℝ (LinearMap.ker (constraintMap C P mu)) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  obtain ⟨mu, hmu⟩ := exists_surjective_constraintMap C P hC hPC
  exact ⟨mu, hmu, (gibbs_phase_rule_explicit C P hP mu hmu).1⟩

end Chem

