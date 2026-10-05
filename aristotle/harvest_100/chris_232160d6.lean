import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the statement that the seven–qubit Steane CSS code corrects an
arbitrary error on a single qubit, in the standard Knill–Laflamme form:

for any two single–qubit Pauli errors `E₁`, `E₂` there is a constant `c`
(depending only on the errors) such that
`⟪E₁ ψ, E₂ φ⟫ = c * ⟪ψ, φ⟫` for all code states `ψ, φ`.

Everything is set up concretely.  The `2^7`-dimensional state space is modelled
as the space of functions `V → ℂ` where `V = Fin 7 → ZMod 2` indexes the
computational basis.  Pauli operators `X^a Z^b` act by
`(X^a Z^b) |v⟩ = (-1)^{b·v} |v + a⟩`, i.e. by `pauliOp`.  The Steane code space
is spanned by the two logical basis states
`|0_L⟩ = Σ_{v ∈ C} |v⟩` and `|1_L⟩ = Σ_{v ∈ C^⊥ \ C} |v⟩`,
where `C` is the `[7,3]` simplex code (the row span of the Hamming parity check
matrix `Hm`) and `C^⊥` is the `[7,4]` Hamming code.  Concretely a codeword `v`
lies in `C^⊥` iff all three parity checks vanish (`InD v`), and it lies in `C`
iff moreover it has even weight (`par v = 0`).
-/

namespace QI

/-- Bit strings of length seven: the index set of the computational basis. -/
abbrev V := Fin 7 → ZMod 2

/-- The mod-2 inner product of two bit strings. -/
def dotp (u v : V) : ZMod 2 := ∑ i, u i * v i

/-- The parity check matrix of the `[7,4,3]` Hamming code: the `i`-th column is
the binary expansion of `i + 1`. -/
def Hm : Fin 3 → V := fun k i => if ((i.val + 1) >>> k.val) % 2 = 1 then 1 else 0

/-- `InD v` says that `v` lies in the Hamming code `C^⊥`, i.e. all parity checks
vanish. -/
def InD (v : V) : Prop := ∀ k, dotp (Hm k) v = 0

instance (v : V) : Decidable (InD v) := by unfold InD; infer_instance

/-- The parity (weight mod 2) of a bit string. -/
def par (v : V) : ZMod 2 := dotp (fun _ => 1) v

/-- The sign `(-1)^t` of a bit `t`. -/
noncomputable def sgn (t : ZMod 2) : ℂ := if t = 0 then 1 else -1

/-- The Pauli operator `X^a Z^b`, acting on a state vector by
`(X^a Z^b) |v⟩ = (-1)^{b·v} |v + a⟩`. -/
noncomputable def pauliOp (a b : V) (f : V → ℂ) : V → ℂ := fun u => sgn (dotp b (u + a)) * f (u + a)

/-- The hermitian inner product on the state space. -/
noncomputable def ip (f g : V → ℂ) : ℂ := ∑ v, (starRingEnd ℂ) (f v) * g v

/-- The generic state of the Steane code space: `α |0_L⟩ + β |1_L⟩`. -/
noncomputable def codeState (α β : ℂ) : V → ℂ :=
  fun v => if InD v then (if par v = 0 then α else β) else 0

/-- A Pauli error `X^a Z^b` acting on at most one qubit. -/
def SinglePauli (a b : V) : Prop := ∃ i : Fin 7, ∀ k, k ≠ i → a k = 0 ∧ b k = 0

/-! ### Basic arithmetic in characteristic two -/

lemma zmod2_add_self (t : ZMod 2) : t + t = 0 := by revert t; decide +kernel

lemma V_add_self (x : V) : x + x = 0 := by
  funext i; simpa using zmod2_add_self (x i)

lemma zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide +kernel

lemma dotp_add_right (u v w : V) : dotp u (v + w) = dotp u v + dotp u w := by
  simp [dotp, mul_add, Finset.sum_add_distrib]

lemma dotp_add_left (u v w : V) : dotp (u + v) w = dotp u w + dotp v w := by
  simp [dotp, add_mul, Finset.sum_add_distrib]

lemma dotp_comm (u v : V) : dotp u v = dotp v u := by
  simp [dotp, mul_comm]

lemma dotp_zero (u : V) : dotp u 0 = 0 := by simp [dotp]

lemma dotp_zero_left (u : V) : dotp 0 u = 0 := by simp [dotp]

lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  rcases zmod2_cases s with hs | hs <;> rcases zmod2_cases t with ht | ht <;>
    subst hs <;> subst ht <;> simp [sgn, show (1 : ZMod 2) + 1 = 0 by decide]

lemma sgn_conj (t : ZMod 2) : (starRingEnd ℂ) (sgn t) = sgn t := by
  rcases zmod2_cases t with h | h <;> subst h <;> simp [sgn]

lemma sgn_one : sgn 1 = -1 := by norm_num [sgn]

/-! ### Properties of the Hamming parity check matrix -/

lemma Hm_selforth (k l : Fin 3) : dotp (Hm k) (Hm l) = 0 := by revert k l; decide +kernel

lemma Hm_even (k : Fin 3) : par (Hm k) = 0 := by revert k; decide +kernel

lemma InD_Hm (k : Fin 3) : InD (Hm k) := fun l => Hm_selforth l k

/-- Minimum-distance property: a vector of the Hamming code supported on at most
two coordinates is zero (the Hamming code has minimum distance three). -/
lemma InD_of_two_support_eq_zero :
    ∀ (i j : Fin 7) (a : V), (∀ k, k ≠ i → k ≠ j → a k = 0) → InD a → a = 0 := by
  unfold InD
  decide +kernel

lemma InD_add {u v : V} (hu : InD u) (hv : InD v) : InD (u + v) := by
  intro k
  rw [dotp_add_right, hu k, hv k, add_zero]

lemma InD_zero : InD (0 : V) := fun _ => dotp_zero _

lemma par_add (u v : V) : par (u + v) = par u + par v := dotp_add_right _ _ _

/-! ### The code space -/

lemma codeState_supp {α β : ℂ} {v : V} (h : codeState α β v ≠ 0) : InD v := by
  by_contra hv
  simp [codeState, hv] at h

/-- The logical basis states are invariant under translation by an even-weight
Hamming codeword; in particular under translation by a codeword of the simplex
code `C`. -/
lemma codeState_shift (α β : ℂ) {w : V} (hw : InD w) (hpw : par w = 0) (v : V) :
    codeState α β (v + w) = codeState α β v := by
  have h1 : InD (v + w) ↔ InD v := by
    constructor
    · intro h
      have := InD_add h hw
      simpa [add_assoc, V_add_self] using this
    · intro h; exact InD_add h hw
  have h2 : par (v + w) = par v := by rw [par_add, hpw, add_zero]
  simp [codeState, h1, h2]

/-- The Steane code space is two dimensional: the logical basis states are
linearly independent. -/
lemma codeState_eq_zero_iff (α β : ℂ) : codeState α β = 0 ↔ α = 0 ∧ β = 0 := by
  constructor
  · intro h
    have h0 := congrFun h (0 : V)
    have h1 := congrFun h (fun _ => 1 : V)
    have hD0 : InD (0 : V) := InD_zero
    have hp0 : par (0 : V) = 0 := dotp_zero _
    have hD1 : InD (fun _ => 1 : V) := by decide +kernel
    have hp1 : par (fun _ => 1 : V) = 1 := by decide +kernel
    simp [codeState, hD0, hp0, hD1, hp1] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    funext v
    simp [codeState]

/-- The code states are `+1` eigenvectors of the `X`-type stabiliser generators. -/
theorem steane_stabilizer_X (k : Fin 3) (α β : ℂ) :
    pauliOp (Hm k) 0 (codeState α β) = codeState α β := by
  funext u
  simp only [pauliOp, dotp_zero_left, sgn_zero, one_mul]
  exact codeState_shift α β (InD_Hm k) (Hm_even k) u

/-- The code states are `+1` eigenvectors of the `Z`-type stabiliser generators. -/
theorem steane_stabilizer_Z (k : Fin 3) (α β : ℂ) :
    pauliOp 0 (Hm k) (codeState α β) = codeState α β := by
  funext u
  simp only [pauliOp, add_zero]
  by_cases h : codeState α β u = 0
  · simp [h]
  · have hu : InD u := codeState_supp h
    rw [hu k, sgn_zero, one_mul]

/-! ### Reduction of the Knill–Laflamme overlap -/

lemma ip_pauliOp (a₁ b₁ a₂ b₂ : V) (f g : V → ℂ) :
    ip (pauliOp a₁ b₁ f) (pauliOp a₂ b₂ g)
      = sgn (dotp b₂ (a₁ + a₂)) *
          ∑ v, sgn (dotp (b₁ + b₂) v) * (starRingEnd ℂ) (f v) * g (v + (a₁ + a₂)) := by
  rw [ip, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight a₁)
      (fun u => (starRingEnd ℂ) (pauliOp a₁ b₁ f u) * pauliOp a₂ b₂ g u)]
  refine Finset.sum_congr rfl ?_
  intro v _
  have hv : (v + a₁) + a₁ = v := by
    rw [add_assoc, V_add_self, add_zero]
  simp only [Equiv.coe_addRight, pauliOp, map_mul, sgn_conj, hv]
  have h2 : (v + a₁) + a₂ = v + (a₁ + a₂) := by rw [add_assoc]
  rw [h2]
  have hsg : sgn (dotp (b₁ + b₂) v) = sgn (dotp b₁ v) * sgn (dotp b₂ v) := by
    rw [dotp_add_left, sgn_add]
  rw [dotp_add_right b₂ v (a₁ + a₂), sgn_add, hsg]
  ring

/-- Character-sum vanishing: if `b` is not orthogonal to the simplex code then the
`b`-twisted overlap of two code states vanishes. -/
lemma twisted_overlap_zero {b : V} (k : Fin 3) (hk : dotp (Hm k) b = 1) (α β γ δ : ℂ) :
    ∑ v, sgn (dotp b v) * (starRingEnd ℂ) (codeState α β v) * codeState γ δ v = 0 := by
  set w : V := Hm k with hw
  set S := ∑ v, sgn (dotp b v) * (starRingEnd ℂ) (codeState α β v) * codeState γ δ v with hS
  have key : S = -S := by
    conv_lhs =>
      rw [hS, ← Equiv.sum_comp (Equiv.addRight w)
        (fun v => sgn (dotp b v) * (starRingEnd ℂ) (codeState α β v) * codeState γ δ v)]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro v _
    have hbw : dotp b w = 1 := by rw [dotp_comm]; exact hk
    have h1 : sgn (dotp b (v + w)) = - sgn (dotp b v) := by
      rw [dotp_add_right, sgn_add, hbw, sgn_one]
      ring
    have h2 : codeState α β (v + w) = codeState α β v :=
      codeState_shift α β (InD_Hm k) (Hm_even k) v
    have h3 : codeState γ δ (v + w) = codeState γ δ v :=
      codeState_shift γ δ (InD_Hm k) (Hm_even k) v
    simp only [Equiv.coe_addRight, h1, h2, h3]
    ring
  have h2 : (2 : ℂ) * S = 0 := by linear_combination key
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- **The Steane code corrects an arbitrary single–qubit error.**

For any two single–qubit Pauli errors `E₁ = X^{a₁} Z^{b₁}` and
`E₂ = X^{a₂} Z^{b₂}` there is a scalar `c` such that
`⟪E₁ ψ, E₂ φ⟫ = c ⟪ψ, φ⟫` for all states `ψ, φ` of the code space.  This is the
Knill–Laflamme error–correction criterion for the error set consisting of all
single–qubit Paulis, so the seven–qubit Steane code corrects any single–qubit
error. -/
theorem steane_code (a₁ b₁ a₂ b₂ : V) (h₁ : SinglePauli a₁ b₁) (h₂ : SinglePauli a₂ b₂) :
    ∃ c : ℂ, ∀ α β γ δ : ℂ,
      ip (pauliOp a₁ b₁ (codeState α β)) (pauliOp a₂ b₂ (codeState γ δ))
        = c * ip (codeState α β) (codeState γ δ) := by
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  set a : V := a₁ + a₂ with ha
  set b : V := b₁ + b₂ with hb
  have hsuppa : ∀ k, k ≠ i → k ≠ j → a k = 0 := by
    intro k hki hkj
    simp [ha, (hi k hki).1, (hj k hkj).1]
  have hsuppb : ∀ k, k ≠ i → k ≠ j → b k = 0 := by
    intro k hki hkj
    simp [hb, (hi k hki).2, (hj k hkj).2]
  by_cases hA : InD a
  · -- the `X`-part of `E₁† E₂` must be trivial
    have ha0 : a = 0 := InD_of_two_support_eq_zero i j a hsuppa hA
    by_cases hB : InD b
    · -- `E₁† E₂` is (proportional to) the identity
      have hb0 : b = 0 := InD_of_two_support_eq_zero i j b hsuppb hB
      refine ⟨1, fun α β γ δ => ?_⟩
      rw [ip_pauliOp, ← ha, ← hb, ha0, hb0]
      simp only [dotp_zero, sgn_zero, one_mul, dotp_zero_left, add_zero]
      rw [ip]
    · -- the errors have different syndromes, the overlap vanishes
      obtain ⟨k, hk⟩ : ∃ k, dotp (Hm k) b = 1 := by
        unfold InD at hB
        push_neg at hB
        obtain ⟨k, hk⟩ := hB
        exact ⟨k, (zmod2_cases _).resolve_left hk⟩
      refine ⟨0, fun α β γ δ => ?_⟩
      rw [ip_pauliOp, ← ha, ← hb, ha0]
      simp only [add_zero, zero_mul]
      rw [twisted_overlap_zero k hk α β γ δ]
      ring
  · -- the `X`-part maps the code space off itself
    refine ⟨0, fun α β γ δ => ?_⟩
    rw [ip_pauliOp, ← ha, ← hb]
    have : ∀ v : V, sgn (dotp b v) * (starRingEnd ℂ) (codeState α β v)
        * codeState γ δ (v + a) = 0 := by
      intro v
      by_cases hv : codeState α β v = 0
      · simp [hv]
      · by_cases hva : codeState γ δ (v + a) = 0
        · simp [hva]
        · exact absurd (by
            have h1 : InD v := codeState_supp hv
            have h2 : InD (v + a) := codeState_supp hva
            have := InD_add h1 h2
            simpa [← add_assoc, V_add_self] using this) hA
    rw [Finset.sum_congr rfl (fun v _ => this v)]
    simp

/-! ### Non-degeneracy: the inner product on the code space -/

/-- The simplex code `C` (even-weight Hamming codewords) has eight elements. -/
lemma card_simplex : (Finset.univ.filter (fun v : V => InD v ∧ par v = 0)).card = 8 := by
  decide +kernel

/-- The coset `C^⊥ \ C` also has eight elements. -/
lemma card_simplex_coset : (Finset.univ.filter (fun v : V => InD v ∧ par v = 1)).card = 8 := by
  decide +kernel

/-- The inner product of two code states: the logical basis states are orthogonal
and have squared norm eight, so the code space is a genuine two-dimensional space
and the Knill–Laflamme identity is not vacuous. -/
lemma ip_codeState (α β γ δ : ℂ) :
    ip (codeState α β) (codeState γ δ)
      = 8 * ((starRingEnd ℂ) α * γ + (starRingEnd ℂ) β * δ) := by
  have hsummand : ∀ v : V, (starRingEnd ℂ) (codeState α β v) * codeState γ δ v
      = (if (InD v ∧ par v = 0) then (starRingEnd ℂ) α * γ else 0)
        + (if (InD v ∧ par v = 1) then (starRingEnd ℂ) β * δ else 0) := by
    intro v
    by_cases hv : InD v
    · rcases zmod2_cases (par v) with hp | hp <;> simp [codeState, hv, hp]
    · simp [codeState, hv]
  rw [ip, Finset.sum_congr rfl (fun v _ => hsummand v), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    card_simplex, card_simplex_coset]
  ring


end QI

#print axioms QI.steane_code
#print axioms QI.ip_codeState

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

