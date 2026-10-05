/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is a plain block comment; it is repeated verbatim as the module
-- docstring immediately after the import.)

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## The classical ingredients: the `[7,4,3]` Hamming code and its dual -/

/-- A binary register of 7 bits.  Also used to index the computational basis of the
7-qubit Hilbert space. -/
abbrev Reg := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form used both for parity checks and for Pauli phases. -/
def dotp (x y : Reg) : ZMod 2 := ∑ i, x i * y i

/-- Hamming weight of a register. -/
def wt (a : Reg) : ℕ := (Finset.univ.filter (fun i => a i ≠ 0)).card

/-- The three rows of the Hamming parity-check matrix (columns are the binary
expansions of `1, …, 7`). -/
def r1 : Reg := ![1,0,1,0,1,0,1]
def r2 : Reg := ![0,1,1,0,0,1,1]
def r3 : Reg := ![0,0,0,1,1,1,1]

/-- The parity-check matrix of the `[7,4,3]` Hamming code. -/
def Hmat : Fin 3 → Reg := ![r1, r2, r3]

/-- The all-ones vector: a representative of the nontrivial coset of the dual code
inside the Hamming code, i.e. the logical `X`. -/
def tv : Reg := ![1,1,1,1,1,1,1]

/-- Membership in the `[7,4,3]` Hamming code `C = ker H`. -/
def inHamming (v : Reg) : Prop := ∀ k, dotp (Hmat k) v = 0

instance (v : Reg) : Decidable (inHamming v) := by unfold inHamming; infer_instance

/-- The dual code `C⊥` (the `[7,3,4]` simplex code), listed explicitly. -/
def Sfin : Finset Reg := {0, r1, r2, r1+r2, r3, r1+r3, r2+r3, r1+r2+r3}

/-! ### Structural sanity checks on the two classical codes -/

/-- `Sfin` is exactly the row space of the parity check matrix, i.e. the dual code. -/
lemma Sfin_eq_rowSpace (v : Reg) :
    v ∈ Sfin ↔ ∃ c : Fin 3 → ZMod 2, v = c 0 • r1 + c 1 • r2 + c 2 • r3 := by
  revert v; decide

/-- The Steane code is a CSS code: the dual code is contained in the Hamming code
(the parity-check matrix is self-orthogonal). -/
lemma Sfin_subset_Hamming : ∀ v ∈ Sfin, inHamming v := by decide

/-- The dual code has 8 elements (dimension 3). -/
lemma Sfin_card : Sfin.card = 8 := by decide

/-- The all-ones vector lies in the Hamming code but not in its dual, so it
represents the logical `X` operator. -/
lemma tv_mem_Hamming : inHamming tv := by decide

lemma tv_not_mem_Sfin : tv ∉ Sfin := by decide

/-! ### The distance facts, all verified by finite computation -/

/-- Minimum distance 3 of the Hamming code. -/
lemma hamming_min_dist : ∀ v : Reg, wt v ≤ 2 → inHamming v → v = 0 := by decide

/-- Two dual-code words at Hamming distance ≤ 2 coincide (the dual code has
minimum distance 4). -/
lemma dual_min_dist : ∀ u ∈ Sfin, ∀ u' ∈ Sfin, wt (u + u') ≤ 2 → u + u' = 0 := by decide

/-- The nontrivial coset of the dual code has minimum weight 3. -/
lemma coset_min_wt : ∀ u ∈ Sfin, ∀ u' ∈ Sfin, ¬ (wt (u + u' + tv) ≤ 2) := by decide

/-- The two cosets of the dual code inside the Hamming code are disjoint. -/
lemma cosets_disjoint : ∀ u ∈ Sfin, ∀ u' ∈ Sfin, u ≠ u' + tv := by decide

/-- The sign character attached to a nonzero low-weight vector is nontrivial on the
dual code, hence sums to zero over it. -/
def sgnZ (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma character_sum_zero :
    ∀ b : Reg, wt b ≤ 2 → b ≠ 0 → (∑ u ∈ Sfin, sgnZ (dotp b u)) = 0 := by decide

/-! ### Elementary algebraic facts -/

lemma add_self_reg (x : Reg) : x + x = 0 := by
  funext i; revert i
  simp only [Pi.add_apply, Pi.zero_apply]
  intro i
  revert x
  intro x
  have : ∀ y : ZMod 2, y + y = 0 := by decide
  exact this (x i)

lemma dotp_add_right (x y z : Reg) : dotp x (y + z) = dotp x y + dotp x z := by
  simp only [dotp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotp_add_left (x y z : Reg) : dotp (x + y) z = dotp x z + dotp y z := by
  simp only [dotp, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotp_zero_left (z : Reg) : dotp 0 z = 0 := by
  simp [dotp]

lemma sgnZ_add (x y : ZMod 2) : sgnZ (x + y) = sgnZ x * sgnZ y := by
  revert x y; decide

lemma sgnZ_zero : sgnZ 0 = 1 := rfl

/-- Support contained in two positions forces weight ≤ 2. -/
lemma wt_le_two_of_supp {a : Reg} {p q : Fin 7} (h : ∀ k, k ≠ p → k ≠ q → a k = 0) :
    wt a ≤ 2 := by
  have hsub : (Finset.univ.filter (fun i => a i ≠ 0)) ⊆ ({p, q} : Finset (Fin 7)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    by_cases hp : k = p
    · simp [hp]
    · by_cases hq : k = q
      · simp [hq]
      · exact absurd (h k hp hq) hk
  calc wt a ≤ ({p, q} : Finset (Fin 7)).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp

/-! ## The 7-qubit Hilbert space, Pauli errors and the Steane code space -/

/-- Pauli operators.  `pauliLM a b` is (up to an irrelevant global phase) the
Pauli operator `X^a Z^b`: it flips the bits selected by `a` and applies the sign
`(-1)^{b·v}`.  With `a = b = eᵢ` one gets `Yᵢ` up to phase, so for a fixed qubit
`q` the four operators `pauliLM a b` with `a, b` supported in `{q}` span all
operators acting on that qubit. -/
noncomputable def pauliLM (a b : Reg) : EuclideanSpace ℂ Reg →ₗ[ℂ] EuclideanSpace ℂ Reg where
  toFun f := WithLp.toLp 2 (fun v => (sgnZ (dotp b v) : ℂ) * f (v + a))
  map_add' f g := by ext v; simp [mul_add]
  map_smul' c f := by ext v; simp [mul_left_comm]

@[simp] lemma pauliLM_apply (a b : Reg) (f : EuclideanSpace ℂ Reg) (v : Reg) :
    pauliLM a b f v = (sgnZ (dotp b v) : ℂ) * f (v + a) := rfl

/-- `a`, `b` are supported on (at most) a single qubit. -/
def SingleQubit (a b : Reg) : Prop := ∃ q : Fin 7, ∀ k, k ≠ q → a k = 0 ∧ b k = 0

/-- The shift defining the two cosets: `0` for the logical `|0⟩`, the all-ones
vector for the logical `|1⟩`. -/
def shiftv (j : Bool) : Reg := if j then tv else 0

/-- The two cosets of the dual code inside the Hamming code. -/
def cosetOf (j : Bool) : Finset Reg := Sfin.image (fun u => u + shiftv j)

/-- The (unnormalized) logical basis states as functions on the computational basis. -/
def psiF (j : Bool) (v : Reg) : ℂ := if v ∈ cosetOf j then 1 else 0

/-- The two logical basis states of the Steane code:
`|0_L⟩ = Σ_{u ∈ C⊥} |u⟩` and `|1_L⟩ = Σ_{u ∈ C⊥} |u + 1111111⟩`. -/
noncomputable def psi (j : Bool) : EuclideanSpace ℂ Reg := WithLp.toLp 2 (psiF j)

@[simp] lemma psi_apply (j : Bool) (v : Reg) : psi j v = psiF j v := rfl

/-- The Steane code space: the span of the two logical basis states. -/
noncomputable def codeSpace : Submodule ℂ (EuclideanSpace ℂ Reg) :=
  Submodule.span ℂ (Set.range psi)

/-- Syndrome of a Pauli error `X^a Z^b`: the `Z`-type stabilizers measure the
Hamming syndrome of `a`, the `X`-type stabilizers that of `b`. -/
def syndrome (a b : Reg) : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  (fun k => dotp (Hmat k) a, fun k => dotp (Hmat k) b)

/-! ## The core computation -/

lemma psiF_mul_self (j : Bool) (v : Reg) : psiF j v * psiF j v = psiF j v := by
  unfold psiF
  split
  · exact one_mul 1
  · exact mul_zero 0

/-- Cancellation of a common shift in characteristic two. -/
lemma char2_cancel (x y s : Reg) : (x + s) + (y + s) = x + y := by
  have h : (x + s) + (y + s) = (x + y) + (s + s) := by ring
  rw [h, add_self_reg, add_zero]

lemma char2_regroup (x y s s' : Reg) : (x + s) + (y + s') = (x + y) + (s + s') := by ring

lemma shiftv_add_shiftv {i j : Bool} (hij : i ≠ j) : shiftv i + shiftv j = tv := by
  cases i <;> cases j <;> simp_all [shiftv]

/-- Off-diagonal / shifted terms vanish: this is where the distance-3 property
of the Steane code enters. -/
lemma psiF_mul_shift_eq_zero (a : Reg) (i j : Bool) (ha : wt a ≤ 2)
    (h : a ≠ 0 ∨ i ≠ j) (v : Reg) : psiF i v * psiF j (v + a) = 0 := by
  unfold psiF
  by_cases h1 : v ∈ cosetOf i
  · by_cases h2 : v + a ∈ cosetOf j
    · exfalso
      rw [cosetOf, Finset.mem_image] at h1 h2
      obtain ⟨u, hu, hu'⟩ := h1
      obtain ⟨u', hu2, hu2'⟩ := h2
      -- in characteristic two, `a = (v + a) + v`
      have hav : a = (v + a) + v := by
        rw [add_comm v a, add_assoc, add_self_reg, add_zero]
      by_cases hij : i = j
      · subst hij
        have haa : a = u' + u := by
          rw [hav, ← hu2', ← hu', char2_cancel]
        have hd := dual_min_dist u' hu2 u hu (by rw [← haa]; exact ha)
        rw [← haa] at hd
        exact (h.resolve_right (fun hne => hne rfl)) hd
      · -- `i ≠ j`, so the two shifts differ by the all-ones vector
        have haa : a = u' + u + tv := by
          rw [hav, ← hu2', ← hu', char2_regroup, add_comm (shiftv j) (shiftv i),
            shiftv_add_shiftv hij]
        exact coset_min_wt u' hu2 u hu (by rw [← haa]; exact ha)
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

/-- The master inner-product computation. -/
lemma key_sum (a b : Reg) (i j : Bool) (ha : wt a ≤ 2) (hb : wt b ≤ 2) :
    (∑ v : Reg, (sgnZ (dotp b v) : ℂ) * (psiF i v * psiF j (v + a)))
      = if a = 0 ∧ b = 0 ∧ i = j then 8 else 0 := by
  by_cases ha0 : a = 0
  · by_cases hij : i = j
    · subst ha0; subst hij
      simp only [add_zero, psiF_mul_self]
      -- sum over the coset of the character
      have step1 : (∑ v : Reg, (sgnZ (dotp b v) : ℂ) * psiF i v)
          = ∑ v ∈ cosetOf i, (sgnZ (dotp b v) : ℂ) := by
        unfold psiF
        rw [← Finset.sum_filter_ne_zero]
        rw [Finset.sum_congr rfl (fun v _ => rfl)]
        classical
        have : ∀ v : Reg, (sgnZ (dotp b v) : ℂ) * (if v ∈ cosetOf i then 1 else 0)
            = if v ∈ cosetOf i then (sgnZ (dotp b v) : ℂ) else 0 := by
          intro v; split <;> simp
        simp only [this]
        rw [Finset.sum_filter_ne_zero]
        rw [Finset.sum_ite_mem]
        simp
      rw [step1]
      have hinj : Set.InjOn (fun u => u + shiftv i) Sfin := by
        intro x _ y _ hxy
        simpa using add_right_cancel hxy
      rw [cosetOf, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
      have hd : ∀ u : Reg, (sgnZ (dotp b (u + shiftv i)) : ℂ)
          = (sgnZ (dotp b (shiftv i)) : ℂ) * (sgnZ (dotp b u) : ℂ) := by
        intro u
        rw [dotp_add_right, sgnZ_add]
        push_cast
        ring
      simp only [hd]
      rw [← Finset.mul_sum]
      by_cases hb0 : b = 0
      · subst hb0
        simp only [dotp_zero_left, sgnZ_zero]
        rw [Finset.sum_const]
        simp [Sfin_card]
      · have : (∑ u ∈ Sfin, (sgnZ (dotp b u) : ℂ)) = ((∑ u ∈ Sfin, sgnZ (dotp b u) : ℤ) : ℂ) := by
          push_cast; ring
        rw [this, character_sum_zero b hb hb0]
        simp [hb0]
    · have : ∀ v : Reg, (sgnZ (dotp b v) : ℂ) * (psiF i v * psiF j (v + a)) = 0 := by
        intro v
        rw [psiF_mul_shift_eq_zero a i j ha (Or.inr hij) v, mul_zero]
      simp [this, hij]
  · have : ∀ v : Reg, (sgnZ (dotp b v) : ℂ) * (psiF i v * psiF j (v + a)) = 0 := by
      intro v
      rw [psiF_mul_shift_eq_zero a i j ha (Or.inl ha0) v, mul_zero]
    simp [this, ha0]

lemma psiF_real (j : Bool) (v : Reg) : star (psiF j v) = psiF j v := by
  unfold psiF; split <;> simp

/-- The inner product of two Pauli-corrupted logical states. -/
lemma inner_pauli (a₁ b₁ a₂ b₂ : Reg) (i j : Bool)
    (ha : wt (a₁ + a₂) ≤ 2) (hb : wt (b₁ + b₂) ≤ 2) :
    ⟪pauliLM a₁ b₁ (psi i), pauliLM a₂ b₂ (psi j)⟫_ℂ
      = (sgnZ (dotp (b₁ + b₂) a₁) : ℂ) *
          (if a₁ + a₂ = 0 ∧ b₁ + b₂ = 0 ∧ i = j then 8 else 0) := by
  have hip : ⟪pauliLM a₁ b₁ (psi i), pauliLM a₂ b₂ (psi j)⟫_ℂ
      = ∑ v : Reg, star (pauliLM a₁ b₁ (psi i) v) * (pauliLM a₂ b₂ (psi j) v) := by
    rw [PiLp.inner_apply]; simp [RCLike.inner_apply, mul_comm]
  rw [hip]
  have hterm : ∀ v : Reg, star (pauliLM a₁ b₁ (psi i) v) * (pauliLM a₂ b₂ (psi j) v)
      = (sgnZ (dotp (b₁ + b₂) v) : ℂ) * (psiF i (v + a₁) * psiF j (v + a₂)) := by
    intro v
    simp only [pauliLM_apply, psi_apply, star_mul']
    rw [dotp_add_left, sgnZ_add]
    have h1 : star ((sgnZ (dotp b₁ v) : ℂ)) = ((sgnZ (dotp b₁ v) : ℂ)) := by
      simp
    rw [psiF_real, h1]
    push_cast
    ring
  simp only [hterm]
  -- reindex `v ↦ v + a₁`
  have hre : (∑ v : Reg, (sgnZ (dotp (b₁ + b₂) v) : ℂ) * (psiF i (v + a₁) * psiF j (v + a₂)))
      = ∑ w : Reg, (sgnZ (dotp (b₁ + b₂) (w + a₁)) : ℂ) *
          (psiF i w * psiF j (w + (a₁ + a₂))) := by
    refine (Fintype.sum_equiv (Equiv.addRight a₁) _ _ ?_).symm
    intro w
    simp only [Equiv.coe_addRight]
    have e1 : w + a₁ + a₁ = w := by rw [add_assoc, add_self_reg, add_zero]
    have e2 : w + a₁ + a₂ = w + (a₁ + a₂) := add_assoc w a₁ a₂
    rw [e1, e2]
  rw [hre]
  have hfac : ∀ w : Reg, (sgnZ (dotp (b₁ + b₂) (w + a₁)) : ℂ) *
      (psiF i w * psiF j (w + (a₁ + a₂)))
      = (sgnZ (dotp (b₁ + b₂) a₁) : ℂ) *
        ((sgnZ (dotp (b₁ + b₂) w) : ℂ) * (psiF i w * psiF j (w + (a₁ + a₂)))) := by
    intro w
    rw [dotp_add_right, sgnZ_add]
    push_cast
    ring
  simp only [hfac]
  rw [← Finset.mul_sum, key_sum (a₁ + a₂) (b₁ + b₂) i j ha hb]

/-! ## Support bookkeeping for single-qubit errors -/

lemma wt_add_le_two {a₁ b₁ a₂ b₂ : Reg} (h1 : SingleQubit a₁ b₁) (h2 : SingleQubit a₂ b₂) :
    wt (a₁ + a₂) ≤ 2 ∧ wt (b₁ + b₂) ≤ 2 := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  constructor
  · exact wt_le_two_of_supp (p := p) (q := q) (fun k hkp hkq => by
      simp [(hp k hkp).1, (hq k hkq).1])
  · exact wt_le_two_of_supp (p := p) (q := q) (fun k hkp hkq => by
      simp [(hp k hkp).2, (hq k hkq).2])

lemma add_eq_zero_iff_reg (x y : Reg) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have : x + y + y = 0 + y := by rw [h]
    rwa [add_assoc, add_self_reg, add_zero, zero_add] at this
  · intro h; subst h; exact add_self_reg x

/-! ## Main theorem -/

/--
**The 7-qubit Steane code corrects any single-qubit error.**

The statement has three parts.

1. The two logical states `|0_L⟩`, `|1_L⟩` are orthogonal and nonzero, so the code
   space is genuinely two-dimensional (it encodes one qubit).

2. The Knill–Laflamme error-correction conditions hold for the set of all
   single-qubit errors: for any two Pauli operators `E₁ = X^{a₁}Z^{b₁}`,
   `E₂ = X^{a₂}Z^{b₂}` each supported on a single qubit, there is a constant `c`
   (independent of the logical state) with
   `⟨ψ_i| E₁† E₂ |ψ_j⟩ = c · δ_{ij}`.
   Since for each qubit `q` the four operators `X^a Z^b` with `a, b` supported in
   `{q}` span (up to phases) all operators on that qubit, this is exactly the
   necessary and sufficient condition for the existence of a recovery channel
   correcting an arbitrary error on one unknown qubit.

3. Operationally: the stabilizer syndrome separates single-qubit Pauli errors —
   two single-qubit Pauli errors with the same syndrome are equal, so syndrome
   measurement followed by the corresponding Pauli correction recovers the state.
-/
theorem steane_code :
    (∀ i j : Bool, ⟪psi i, psi j⟫_ℂ = if i = j then 8 else 0) ∧
    (∀ a₁ b₁ a₂ b₂ : Reg, SingleQubit a₁ b₁ → SingleQubit a₂ b₂ →
      ∃ c : ℂ, ∀ i j : Bool,
        ⟪pauliLM a₁ b₁ (psi i), pauliLM a₂ b₂ (psi j)⟫_ℂ = if i = j then c else 0) ∧
    (∀ a₁ b₁ a₂ b₂ : Reg, SingleQubit a₁ b₁ → SingleQubit a₂ b₂ →
      syndrome a₁ b₁ = syndrome a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h0 : SingleQubit 0 0 := ⟨0, fun k _ => ⟨rfl, rfl⟩⟩
    have := inner_pauli 0 0 0 0 i j (by simpa using (wt_add_le_two h0 h0).1)
      (by simpa using (wt_add_le_two h0 h0).2)
    have hp : ∀ (k : Bool), pauliLM 0 0 (psi k) = psi k := by
      intro k
      ext v
      simp [dotp_zero_left, sgnZ_zero]
    rw [hp, hp] at this
    rw [this]
    simp [dotp_zero_left, sgnZ_zero]
  · intro a₁ b₁ a₂ b₂ h1 h2
    obtain ⟨ha, hb⟩ := wt_add_le_two h1 h2
    refine ⟨(sgnZ (dotp (b₁ + b₂) a₁) : ℂ) *
      (if a₁ + a₂ = 0 ∧ b₁ + b₂ = 0 then 8 else 0), fun i j => ?_⟩
    rw [inner_pauli a₁ b₁ a₂ b₂ i j ha hb]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  · intro a₁ b₁ a₂ b₂ h1 h2 hs
    obtain ⟨ha, hb⟩ := wt_add_le_two h1 h2
    have hsa : ∀ k, dotp (Hmat k) (a₁ + a₂) = 0 := by
      intro k
      rw [dotp_add_right]
      have : dotp (Hmat k) a₁ = dotp (Hmat k) a₂ := congrFun (congrArg Prod.fst hs) k
      rw [this]
      have : ∀ y : ZMod 2, y + y = 0 := by decide
      exact this _
    have hsb : ∀ k, dotp (Hmat k) (b₁ + b₂) = 0 := by
      intro k
      rw [dotp_add_right]
      have : dotp (Hmat k) b₁ = dotp (Hmat k) b₂ := congrFun (congrArg Prod.snd hs) k
      rw [this]
      have : ∀ y : ZMod 2, y + y = 0 := by decide
      exact this _
    exact ⟨(add_eq_zero_iff_reg _ _).1 (hamming_min_dist _ ha hsa),
      (add_eq_zero_iff_reg _ _).1 (hamming_min_dist _ hb hsb)⟩

end QI

