import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with the state space of nine qubits, realized concretely as the space of
complex-valued functions on the set `Bs` of computational basis states, where a basis
state is an assignment of a bit to each of the nine qubits.  Qubits are indexed by
`Qb = Fin 3 × Fin 3`: the first component is the index of one of the three blocks of the
Shor code, the second is the position inside that block.

An *arbitrary single-qubit error* acting on qubit `q` is the operator `qop q M` attached to
an arbitrary `2 × 2` complex matrix `M : Bool → Bool → ℂ` acting on qubit `q` and acting as
the identity on all other qubits.  Every completely arbitrary (not necessarily unitary)
one-qubit operation is of this form.

The Shor codewords are

  `cw false = (1/(2√2)) (|000⟩+|111⟩) ⊗ (|000⟩+|111⟩) ⊗ (|000⟩+|111⟩)`
  `cw true  = (1/(2√2)) (|000⟩-|111⟩) ⊗ (|000⟩-|111⟩) ⊗ (|000⟩-|111⟩)`

and the code space is their complex span.

The theorem `QI.shor_code_corrects` states that

* the two codewords are orthonormal, so the code space is a genuine two-dimensional
  (one logical qubit) subspace; and
* for **any** pair of single-qubit errors `E = qop q₁ M₁` and `F = qop q₂ M₂` there is a
  scalar `c` with `⟪E x, F y⟫ = c ⟪x, y⟫` for all code vectors `x, y`.

The second item is exactly the Knill–Laflamme error-correction condition
`P E† F P = c_{EF} P` for the set of all single-qubit errors, i.e. the statement that the
Shor code corrects an arbitrary single-qubit error.
-/

namespace QI

open Finset

/-- Qubit labels: `(block, position in block)`. -/
abbrev Qb := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits. -/
abbrev Bs := Qb → Bool

/-- Labels for the eight basis states that occur in the Shor codewords: a bit per block. -/
abbrev Sg := Fin 3 → Bool

/-- The basis state in which all three qubits of block `i` carry the bit `s i`. -/
def rep (s : Sg) : Bs := fun p => s p.1

/-- The (unnormalized) Hermitian inner product on nine-qubit states. -/
noncomputable def ip (x y : Bs → ℂ) : ℂ := ∑ b : Bs, (starRingEnd ℂ) (x b) * y b

/-- The operator acting by the `2 × 2` matrix `M` on qubit `q` and trivially elsewhere.
This is the general form of an arbitrary single-qubit error on qubit `q`. -/
noncomputable def qop (q : Qb) (M : Bool → Bool → ℂ) (v : Bs → ℂ) : Bs → ℂ :=
  fun b => ∑ a : Bool, M (b q) a * v (Function.update b q a)

/-- `(-1)^b`. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- Sign of the basis state `rep s` in the codeword `cw κ`. -/
def sg (κ : Bool) (s : Sg) : ℂ := if κ then sgn (s 0) * sgn (s 1) * sgn (s 2) else 1

/-- Normalization constant `1/(2√2)` of the Shor codewords. -/
noncomputable def nrm : ℂ := ((Real.sqrt 8)⁻¹ : ℝ)

/-- The two Shor codewords `|0_L⟩` (`κ = false`) and `|1_L⟩` (`κ = true`). -/
noncomputable def cw (κ : Bool) : Bs → ℂ :=
  fun b => ∑ s : Sg, (nrm * sg κ s) * (if rep s = b then 1 else 0)

/-- The Shor code space: the complex span of the two codewords. -/
def codeSpace : Set (Bs → ℂ) := {x | ∃ α β : ℂ, x = fun b => α * cw false b + β * cw true b}

/-! ### Basic facts about the normalization and the signs -/

lemma cw_eq (κ : Bool) :
    cw κ = fun b => ∑ s : Sg, (nrm * sg κ s) * (if rep s = b then 1 else 0) := rfl

lemma conj_nrm : (starRingEnd ℂ) nrm = nrm := Complex.conj_ofReal _

lemma nrm_mul_nrm : nrm * nrm = 1 / 8 := by
  have h : ((Real.sqrt 8)⁻¹ : ℝ) * ((Real.sqrt 8)⁻¹ : ℝ) = 1 / 8 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  calc nrm * nrm = ((((Real.sqrt 8)⁻¹ : ℝ) * ((Real.sqrt 8)⁻¹ : ℝ) : ℝ) : ℂ) := by
        simp [nrm]
    _ = 1 / 8 := by rw [h]; norm_num

lemma conj_sgn (b : Bool) : (starRingEnd ℂ) (sgn b) = sgn b := by
  cases b <;> simp [sgn]

lemma conj_sg (κ : Bool) (s : Sg) : (starRingEnd ℂ) (sg κ s) = sg κ s := by
  cases κ <;> simp [sg, conj_sgn]

lemma sg_mul_self (κ : Bool) (s : Sg) : sg κ s * sg κ s = 1 := by
  cases κ
  · simp [sg]
  · rcases Bool.dichotomy (s 0) with h0 | h0 <;> rcases Bool.dichotomy (s 1) with h1 | h1 <;>
      rcases Bool.dichotomy (s 2) with h2 | h2 <;> simp [sg, sgn, h0, h1, h2]

lemma sg_mul_sg_of_ne {κ lam : Bool} (h : κ ≠ lam) (s : Sg) : sg κ s * sg lam s = sg true s := by
  cases κ <;> cases lam <;> simp_all [sg]

/-! ### Expansion of sums over the eight code basis labels -/

/-- The equivalence between triples of bits and bit-assignments to the three blocks. -/
def sgEquiv : (Bool × Bool × Bool) ≃ Sg where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun s := (s 0, s 1, s 2)
  left_inv p := by simp
  right_inv s := by funext i; fin_cases i <;> rfl

lemma sum_Sg (F : Sg → ℂ) : ∑ s : Sg, F s = ∑ p : Bool × Bool × Bool, F ![p.1, p.2.1, p.2.2] :=
  (Equiv.sum_comp sgEquiv F).symm

/-- The key cancellation: summing the sign of `|1_L⟩` against any function of the bits of at
most two of the three blocks gives zero, because the remaining block is summed freely. -/
lemma sum_sg_true_zero (F : Bool → Bool → ℂ) (i₁ i₂ : Fin 3) :
    ∑ s : Sg, sg true s * F (s i₁) (s i₂) = 0 := by
  rw [sum_Sg]
  fin_cases i₁ <;> fin_cases i₂ <;>
    simp [Fintype.sum_prod_type, sg, sgn] <;> ring

/-! ### Combinatorics of the basis states involved -/

lemma rep_inj (s t : Sg) : rep s = rep t ↔ s = t := by decide +kernel +revert

set_option maxRecDepth 100000 in
/-- Two basis states obtained from code basis states by resetting the *same* qubit agree iff
the code basis states and the reset values agree. -/
lemma update_eq_update_same (q : Qb) (s t : Sg) (z w : Bool) :
    Function.update (rep s) q z = Function.update (rep t) q w ↔ (z = w ∧ s = t) := by
  decide +kernel +revert

set_option maxRecDepth 100000 in
/-- Two basis states obtained from code basis states by resetting two *different* qubits agree
iff the code basis states agree and the reset values are the original ones.  This uses that
each block contains three qubits, so any two qubits leave a qubit of every block untouched. -/
lemma update_eq_update_diff (q₁ q₂ : Qb) (h : q₁ ≠ q₂) (s t : Sg) (z w : Bool) :
    Function.update (rep s) q₁ z = Function.update (rep t) q₂ w ↔
      (w = rep s q₂ ∧ s = t ∧ z = rep t q₁) := by
  revert h; decide +kernel +revert

/-! ### Inner products of states given as combinations of basis states -/

lemma ip_of_spread {I J : Type} [Fintype I] [Fintype J]
    (f : I → ℂ) (g : J → ℂ) (u : I → Bs) (u' : J → Bs) :
    ip (fun b => ∑ i, f i * (if u i = b then 1 else 0))
       (fun b => ∑ j, g j * (if u' j = b then 1 else 0))
    = ∑ i, ∑ j, (starRingEnd ℂ) (f i) * g j * (if u i = u' j then 1 else 0) := by
  have h : ∀ b : Bs, (starRingEnd ℂ) (∑ i, f i * (if u i = b then 1 else 0)) *
      (∑ j, g j * (if u' j = b then 1 else 0))
      = ∑ i, ∑ j, (starRingEnd ℂ) (f i) * g j *
          ((if u i = b then 1 else 0) * (if u' j = b then 1 else 0)) := by
    intro b
    have h1 : (starRingEnd ℂ) (∑ i, f i * (if u i = b then 1 else 0))
        = ∑ i, (starRingEnd ℂ) (f i) * (if u i = b then 1 else 0) := by
      simp only [map_sum, map_mul, apply_ite, map_one, map_zero]
    rw [h1, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [ip, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp [Finset.sum_ite_eq]

/-- Acting by a single-qubit error on a combination of the code basis states again produces a
combination of basis states, indexed by a code basis label together with the new value of the
affected qubit. -/
lemma qop_spread (q : Qb) (M : Bool → Bool → ℂ) (f : Sg → ℂ) :
    qop q M (fun b => ∑ s : Sg, f s * (if rep s = b then 1 else 0))
    = fun b => ∑ p : Sg × Bool, (f p.1 * M p.2 (rep p.1 q)) *
        (if Function.update (rep p.1) q p.2 = b then 1 else 0) := by
  funext b
  rw [Fintype.sum_prod_type]
  simp only [qop, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hA : ∀ x, x ≠ q → rep s x = b x
  · have e1 : ∀ a : Bool, (rep s = Function.update b q a) ↔ (rep s q = a) := by
      intro a
      rw [Function.eq_update_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, hA⟩⟩
    have e2 : ∀ z : Bool, (Function.update (rep s) q z = b) ↔ (z = b q) := by
      intro z
      rw [Function.update_eq_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, fun x hx => hA x hx⟩⟩
    simp only [e1, e2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  · push_neg at hA
    obtain ⟨x, hx, hxb⟩ := hA
    have e1 : ∀ a : Bool, ¬ (rep s = Function.update b q a) := fun a h =>
      hxb (by rw [h, Function.update_of_ne hx])
    have e2 : ∀ z : Bool, ¬ (Function.update (rep s) q z = b) := fun z h =>
      hxb (by rw [← h, Function.update_of_ne hx])
    simp only [e1, e2, if_false, mul_zero, Finset.sum_const_zero]

/-! ### Orthonormality of the codewords -/

theorem ip_cw_cw (κ lam : Bool) : ip (cw κ) (cw lam) = if κ = lam then 1 else 0 := by
  have h : ip (cw κ) (cw lam)
      = ∑ s : Sg, ∑ t : Sg, (starRingEnd ℂ) (nrm * sg κ s) * (nrm * sg lam t) *
          (if rep s = rep t then 1 else 0) := by
    rw [cw_eq κ, cw_eq lam, ip_of_spread]
  rw [h]
  simp only [rep_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hk : κ = lam
  · subst hk
    have : ∀ s : Sg, (starRingEnd ℂ) (nrm * sg κ s) * (nrm * sg κ s) = 1 / 8 := by
      intro s
      have := sg_mul_self κ s
      calc (starRingEnd ℂ) (nrm * sg κ s) * (nrm * sg κ s)
          = (sg κ s * sg κ s) * (nrm * nrm) := by
            simp only [map_mul, conj_nrm, conj_sg]; ring
        _ = 1 / 8 := by rw [this, one_mul, nrm_mul_nrm]
    simp only [this]
    rw [sum_Sg]
    simp
  · have : ∀ s : Sg, (starRingEnd ℂ) (nrm * sg κ s) * (nrm * sg lam s)
        = sg true s * ((nrm * nrm) * (fun _ _ : Bool => (1:ℂ)) (s 0) (s 0)) := by
      intro s
      calc (starRingEnd ℂ) (nrm * sg κ s) * (nrm * sg lam s)
          = (sg κ s * sg lam s) * (nrm * nrm) := by
            simp only [map_mul, conj_nrm, conj_sg]; ring
        _ = sg true s * ((nrm * nrm) * 1) := by rw [sg_mul_sg_of_ne hk s]; ring
    simp only [this, if_neg hk]
    exact sum_sg_true_zero (fun _ _ => (nrm * nrm) * 1) 0 0

/-! ### The Knill–Laflamme computation -/

lemma ip_qop_expand (q₁ q₂ : Qb) (M₁ M₂ : Bool → Bool → ℂ) (κ lam : Bool) :
    ip (qop q₁ M₁ (cw κ)) (qop q₂ M₂ (cw lam))
    = ∑ p : Sg × Bool, ∑ p' : Sg × Bool,
        (starRingEnd ℂ) (nrm * sg κ p.1 * M₁ p.2 (rep p.1 q₁)) *
        (nrm * sg lam p'.1 * M₂ p'.2 (rep p'.1 q₂)) *
        (if Function.update (rep p.1) q₁ p.2 = Function.update (rep p'.1) q₂ p'.2 then 1 else 0) := by
  rw [cw_eq κ, cw_eq lam, qop_spread, qop_spread, ip_of_spread]

/-- Both errors act on the same qubit. -/
lemma ip_qop_same (q : Qb) (M₁ M₂ : Bool → Bool → ℂ) (κ lam : Bool) :
    ip (qop q M₁ (cw κ)) (qop q M₂ (cw lam))
    = ∑ s : Sg, ∑ z : Bool, (starRingEnd ℂ) (nrm * sg κ s * M₁ z (s q.1)) *
        (nrm * sg lam s * M₂ z (s q.1)) := by
  rw [ip_qop_expand]
  simp only [Fintype.sum_prod_type, update_eq_update_same, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- The errors act on two different qubits. -/
lemma ip_qop_diff (q₁ q₂ : Qb) (h : q₁ ≠ q₂) (M₁ M₂ : Bool → Bool → ℂ) (κ lam : Bool) :
    ip (qop q₁ M₁ (cw κ)) (qop q₂ M₂ (cw lam))
    = ∑ s : Sg, (starRingEnd ℂ) (nrm * sg κ s * M₁ (s q₁.1) (s q₁.1)) *
        (nrm * sg lam s * M₂ (s q₂.1) (s q₂.1)) := by
  rw [ip_qop_expand]
  simp only [Fintype.sum_prod_type, update_eq_update_diff q₁ q₂ h, ite_and, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- The diagonal Knill–Laflamme matrix elements do not depend on the logical basis state. -/
theorem ip_qop_diag (q₁ q₂ : Qb) (M₁ M₂ : Bool → Bool → ℂ) (κ : Bool) :
    ip (qop q₁ M₁ (cw κ)) (qop q₂ M₂ (cw κ))
      = ip (qop q₁ M₁ (cw false)) (qop q₂ M₂ (cw false)) := by
  have key : ∀ (s : Sg) (A B : ℂ), (starRingEnd ℂ) (nrm * sg κ s * A) * (nrm * sg κ s * B)
      = (starRingEnd ℂ) (nrm * sg false s * A) * (nrm * sg false s * B) := by
    intro s A B
    have h1 := sg_mul_self κ s
    calc (starRingEnd ℂ) (nrm * sg κ s * A) * (nrm * sg κ s * B)
        = (sg κ s * sg κ s) * ((starRingEnd ℂ) nrm * (starRingEnd ℂ) A * (nrm * B)) := by
          simp only [map_mul, conj_sg]; ring
      _ = (starRingEnd ℂ) nrm * (starRingEnd ℂ) A * (nrm * B) := by rw [h1, one_mul]
      _ = (starRingEnd ℂ) (nrm * sg false s * A) * (nrm * sg false s * B) := by
          simp only [sg, map_mul, map_one, if_neg (Bool.false_ne_true)]; ring
  by_cases hq : q₁ = q₂
  · subst hq
    rw [ip_qop_same, ip_qop_same]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun z _ => key s _ _
  · rw [ip_qop_diff q₁ q₂ hq, ip_qop_diff q₁ q₂ hq]
    exact Finset.sum_congr rfl fun s _ => key s _ _

/-- The off-diagonal Knill–Laflamme matrix elements vanish. -/
theorem ip_qop_offdiag (q₁ q₂ : Qb) (M₁ M₂ : Bool → Bool → ℂ) {κ lam : Bool} (h : κ ≠ lam) :
    ip (qop q₁ M₁ (cw κ)) (qop q₂ M₂ (cw lam)) = 0 := by
  by_cases hq : q₁ = q₂
  · subst hq
    rw [ip_qop_same]
    have : ∀ s : Sg, (∑ z : Bool, (starRingEnd ℂ) (nrm * sg κ s * M₁ z (s q₁.1)) *
        (nrm * sg lam s * M₂ z (s q₁.1)))
        = sg true s * (fun x y : Bool => ∑ z : Bool, (starRingEnd ℂ) (nrm * M₁ z x) *
            (nrm * M₂ z y)) (s q₁.1) (s q₁.1) := by
      intro s
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      calc (starRingEnd ℂ) (nrm * sg κ s * M₁ z (s q₁.1)) * (nrm * sg lam s * M₂ z (s q₁.1))
          = (sg κ s * sg lam s) * ((starRingEnd ℂ) (nrm * M₁ z (s q₁.1)) *
              (nrm * M₂ z (s q₁.1))) := by
            simp only [map_mul, conj_sg]; ring
        _ = sg true s * ((starRingEnd ℂ) (nrm * M₁ z (s q₁.1)) * (nrm * M₂ z (s q₁.1))) := by
            rw [sg_mul_sg_of_ne h s]
    rw [Finset.sum_congr rfl fun s _ => this s]
    exact sum_sg_true_zero
      (fun x y : Bool => ∑ z : Bool, (starRingEnd ℂ) (nrm * M₁ z x) * (nrm * M₂ z y)) q₁.1 q₁.1
  · rw [ip_qop_diff q₁ q₂ hq]
    have : ∀ s : Sg, (starRingEnd ℂ) (nrm * sg κ s * M₁ (s q₁.1) (s q₁.1)) *
        (nrm * sg lam s * M₂ (s q₂.1) (s q₂.1))
        = sg true s * (fun x y : Bool => (starRingEnd ℂ) (nrm * M₁ x x) * (nrm * M₂ y y))
            (s q₁.1) (s q₂.1) := by
      intro s
      calc (starRingEnd ℂ) (nrm * sg κ s * M₁ (s q₁.1) (s q₁.1)) *
            (nrm * sg lam s * M₂ (s q₂.1) (s q₂.1))
          = (sg κ s * sg lam s) * ((starRingEnd ℂ) (nrm * M₁ (s q₁.1) (s q₁.1)) *
              (nrm * M₂ (s q₂.1) (s q₂.1))) := by
            simp only [map_mul, conj_sg]; ring
        _ = sg true s * ((starRingEnd ℂ) (nrm * M₁ (s q₁.1) (s q₁.1)) *
              (nrm * M₂ (s q₂.1) (s q₂.1))) := by rw [sg_mul_sg_of_ne h s]
    rw [Finset.sum_congr rfl fun s _ => this s]
    exact sum_sg_true_zero
      (fun x y : Bool => (starRingEnd ℂ) (nrm * M₁ x x) * (nrm * M₂ y y)) q₁.1 q₂.1

/-! ### Linearity -/

lemma qop_lin (q : Qb) (M : Bool → Bool → ℂ) (α β : ℂ) (x y : Bs → ℂ) :
    qop q M (fun b => α * x b + β * y b) = fun b => α * qop q M x b + β * qop q M y b := by
  funext b
  simp only [qop, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma ip_lin (α β γ δ : ℂ) (x y u v : Bs → ℂ) :
    ip (fun b => α * x b + β * y b) (fun b => γ * u b + δ * v b)
      = (starRingEnd ℂ) α * γ * ip x u + (starRingEnd ℂ) α * δ * ip x v
        + (starRingEnd ℂ) β * γ * ip y u + (starRingEnd ℂ) β * δ * ip y v := by
  simp only [ip, map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ### Main theorem -/

/-- The codewords lie in the code space, so the statement below is not vacuous. -/
lemma cw_mem_codeSpace (κ : Bool) : cw κ ∈ codeSpace := by
  cases κ
  · exact ⟨1, 0, by funext b; ring⟩
  · exact ⟨0, 1, by funext b; ring⟩

/-- **The 9-qubit Shor code corrects an arbitrary single-qubit error.**

The first conjunct says that the two Shor codewords are orthonormal, so that the code space
is a two-dimensional subspace encoding one logical qubit.

The second conjunct is the Knill–Laflamme error-correction condition for the set of all
single-qubit errors: for arbitrary qubits `q₁, q₂` and arbitrary (not necessarily unitary)
one-qubit operations `M₁, M₂` there is a scalar `c` such that
`⟪(M₁ on q₁) x, (M₂ on q₂) y⟫ = c ⟪x, y⟫` for all vectors `x, y` of the code space; i.e.
`P E† F P = c P` for all single-qubit errors `E`, `F`.  This is precisely the necessary and
sufficient condition for the existence of a recovery operation undoing an arbitrary error on
any single one of the nine qubits. -/
theorem shor_code_corrects :
    (∀ κ lam : Bool, ip (cw κ) (cw lam) = if κ = lam then 1 else 0) ∧
    (∀ (q₁ q₂ : Qb) (M₁ M₂ : Bool → Bool → ℂ), ∃ c : ℂ,
      ∀ x ∈ codeSpace, ∀ y ∈ codeSpace,
        ip (qop q₁ M₁ x) (qop q₂ M₂ y) = c * ip x y) := by
  refine ⟨ip_cw_cw, fun q₁ q₂ M₁ M₂ => ⟨ip (qop q₁ M₁ (cw false)) (qop q₂ M₂ (cw false)), ?_⟩⟩
  rintro x ⟨α, β, rfl⟩ y ⟨γ, δ, rfl⟩
  rw [qop_lin, qop_lin, ip_lin, ip_lin]
  rw [ip_qop_diag q₁ q₂ M₁ M₂ true,
    ip_qop_offdiag q₁ q₂ M₁ M₂ (κ := false) (lam := true) (by decide),
    ip_qop_offdiag q₁ q₂ M₁ M₂ (κ := true) (lam := false) (by decide)]
  simp only [ip_cw_cw, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, mul_zero,
    add_zero, mul_one]
  ring

end QI

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

