import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical setup: the Hamming `[7,4,3]` code and its dual -/

/-- Bit strings of length 7 (the computational basis labels of 7 qubits). -/
abbrev Bits := Fin 7 → ZMod 2

/-- The parity check matrix of the classical Hamming `[7,4,3]` code. -/
def Hmat : Fin 3 → Bits :=
  ![![1, 0, 1, 0, 1, 0, 1], ![0, 1, 1, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 1, 1]]

/-- The `𝔽₂`-valued dot product of two bit strings. -/
def dotp (u v : Bits) : ZMod 2 := ∑ i, u i * v i

/-- The dual Hamming code `C₂ = C₁^⊥` (the `[7,3,4]` simplex code): the row space of
`Hmat`. -/
def inC2 (v : Bits) : Prop := ∃ y : Fin 3 → ZMod 2, ∀ i, v i = ∑ k, y k * Hmat k i

instance : DecidablePred inC2 := fun v => by unfold inC2; infer_instance

/-- Hamming weight of a bit string. -/
def wtv (v : Bits) : ℕ := (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- The weight of the Pauli operator `X^a Z^b`, i.e. the number of qubits it acts on
nontrivially. -/
def wt (a b : Bits) : ℕ := (Finset.univ.filter (fun i => a i ≠ 0 ∨ b i ≠ 0)).card

/-- The all-ones bit string. -/
def ones : Bits := fun _ => 1

/-! ## The quantum side -/

/-- The Hilbert space of 7 qubits, realised as complex-valued functions on the
computational basis labels. -/
abbrev Vec := Bits → ℂ

/-- The sign character `t ↦ (-1)^t` of `ZMod 2`. -/
def sgn (t : ZMod 2) : ℂ := if t = 0 then 1 else -1

/-- The standard Hermitian inner product on `Vec`. -/
noncomputable def ip (v w : Vec) : ℂ := ∑ u, (starRingEnd ℂ) (v u) * w u

/-- The bit string attached to a logical basis label: `0` for the logical `|0⟩`,
the all-ones string for the logical `|1⟩`. -/
def lvec (l : ZMod 2) : Bits := if l = 0 then 0 else ones

/-- The two logical basis states of the Steane code: `psi 0 = ∑_{c ∈ C₂} |c⟩` and
`psi 1 = ∑_{c ∈ C₂} |c + 1111111⟩` (unnormalised). -/
def psi (l : ZMod 2) : Vec := fun u => if inC2 (u + lvec l) then 1 else 0

/-- The Pauli operator `X^a Z^b` acting on `Vec`:
`X^a Z^b |w⟩ = (-1)^{b·w} |w + a⟩`. -/
def pauli (a b : Bits) (v : Vec) : Vec := fun u => sgn (dotp b (u + a)) * v (u + a)

/-- The character sum of `b` over the dual code `C₂`. -/
noncomputable def charsum (b : Bits) : ℂ := ∑ c ∈ Finset.univ.filter inC2, sgn (dotp b c)

/-! ## Brute-force facts about the classical codes -/

/-- `C₂` has minimum distance 4: no nonzero word of weight `≤ 2`. -/
theorem C2_min_weight : ∀ a : Bits, wtv a ≤ 2 → inC2 a → a = 0 := by decide

/-- The coset `C₂ + 1111111` contains no word of weight `≤ 2` (its minimum weight is 3). -/
theorem C2_shift_min_weight : ∀ a : Bits, wtv a ≤ 2 → ¬ inC2 (a + ones) := by decide

/-- Since the Hamming code `C₁ = C₂^⊥` has minimum distance 3, any nonzero string of
weight `≤ 2` fails to be orthogonal to `C₂`. -/
theorem exists_C2_nonorth : ∀ b : Bits, wtv b ≤ 2 → b ≠ 0 → ∃ c : Bits, inC2 c ∧ dotp b c = 1 := by
  decide

/-- `C₂` has 8 elements. -/
theorem card_C2 : (Finset.univ.filter inC2).card = 8 := by decide

/-! ## Basic algebra -/

theorem sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  fin_cases s <;> fin_cases t <;> simp [sgn]
  decide

theorem sgn_mul_self (s : ZMod 2) : sgn s * sgn s = 1 := by
  fin_cases s <;> simp [sgn]

theorem sgn_conj (t : ZMod 2) : (starRingEnd ℂ) (sgn t) = sgn t := by
  unfold sgn; split <;> simp

theorem dotp_add_right (u v w : Bits) : dotp u (v + w) = dotp u v + dotp u w := by
  unfold dotp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_add]

theorem dotp_add_left (u v w : Bits) : dotp (u + v) w = dotp u w + dotp v w := by
  unfold dotp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [add_mul]

theorem inC2_zero : inC2 (0 : Bits) := ⟨0, by simp⟩

theorem inC2_add {c d : Bits} (hc : inC2 c) (hd : inC2 d) : inC2 (c + d) := by
  obtain ⟨y, hy⟩ := hc
  obtain ⟨z, hz⟩ := hd
  refine ⟨y + z, fun i => ?_⟩
  simp [hy i, hz i, add_mul, Finset.sum_add_distrib]

theorem inC2_add_iff {c d : Bits} (hc : inC2 c) : inC2 (c + d) ↔ inC2 d := by
  constructor
  · intro h
    have : inC2 (c + (c + d)) := inC2_add hc h
    simpa [← add_assoc, CharTwo.add_self_eq_zero] using this
  · intro h; exact inC2_add hc h

theorem add_self_bits (x : Bits) : x + x = 0 := by
  funext i; simp [CharTwo.add_self_eq_zero]

theorem ind_conj (P : Prop) [Decidable P] :
    (starRingEnd ℂ) (if P then (1 : ℂ) else 0) = if P then (1 : ℂ) else 0 := by
  split <;> simp

theorem bits_cancel (x y : Bits) : x + y + y = x := by
  rw [add_assoc, add_self_bits, add_zero]

theorem bits_add_eq_zero_iff (x y : Bits) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have : x + y + y = 0 + y := by rw [h]
    rwa [bits_cancel, zero_add] at this
  · rintro rfl; exact add_self_bits x

theorem lvec_add_lvec (i j : ZMod 2) :
    lvec i + lvec j = if i = j then 0 else ones := by
  revert i j; decide

/-! ## Weight bookkeeping -/

theorem wtv_le_wt_left (a b : Bits) : wtv a ≤ wt a b := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact Or.inl hi

theorem wtv_le_wt_right (a b : Bits) : wtv b ≤ wt a b := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact Or.inr hi

theorem wtv_add_le (u v : Bits) : wtv (u + v) ≤ wtv u + wtv v := by
  classical
  have hsub : (Finset.univ.filter (fun i => (u + v) i ≠ 0)) ⊆
      (Finset.univ.filter (fun i => u i ≠ 0)) ∪ (Finset.univ.filter (fun i => v i ≠ 0)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Pi.add_apply] at hi ⊢
    by_contra hcon
    push_neg at hcon
    simp [hcon.1, hcon.2] at hi
  calc wtv (u + v) ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

/-! ## Character sums over the dual code -/

theorem charsum_zero : charsum (0 : Bits) = 8 := by
  have hd : ∀ c : Bits, dotp 0 c = 0 := by
    intro c; unfold dotp; simp
  unfold charsum
  simp only [hd, sgn, Finset.sum_const, card_C2]
  norm_num

theorem charsum_eq_zero {b : Bits} (h : ∃ c : Bits, inC2 c ∧ dotp b c = 1) :
    charsum b = 0 := by
  obtain ⟨c0, hc0, hdot⟩ := h
  have hmem : ∀ c : Bits, c ∈ Finset.univ.filter inC2 ↔
      (Equiv.addRight c0) c ∈ Finset.univ.filter inC2 := by
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight]
    constructor
    · intro hc; exact inC2_add hc hc0
    · intro hc
      have : inC2 (c0 + (c + c0)) := inC2_add hc0 hc
      have e : c0 + (c + c0) = c := by
        have : c0 + (c + c0) = c + (c0 + c0) := by abel
        rw [this, add_self_bits, add_zero]
      rwa [e] at this
  have key : ∑ c ∈ Finset.univ.filter inC2, sgn (dotp b (c + c0)) = charsum b := by
    unfold charsum
    exact Finset.sum_equiv (Equiv.addRight c0) hmem (fun c _ => rfl)
  have key2 : ∑ c ∈ Finset.univ.filter inC2, sgn (dotp b (c + c0)) = -charsum b := by
    unfold charsum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dotp_add_right, sgn_add, hdot]
    simp [sgn]
  rw [key] at key2
  linear_combination key2 / 2

/-! ## The core computation -/

theorem shift_sum (s : Bits) (T : Bits → ℂ) : ∑ u, T u = ∑ c, T (c + s) :=
  (Fintype.sum_equiv (Equiv.addRight s) (fun c => T (c + s)) T (fun _ => rfl)).symm

theorem sum_ind_pair (d : Bits) (f : Bits → ℂ) :
    ∑ c : Bits, (if inC2 c then (1 : ℂ) else 0) * f c * (if inC2 (c + d) then (1 : ℂ) else 0)
      = if inC2 d then ∑ c ∈ Finset.univ.filter inC2, f c else 0 := by
  by_cases hd : inC2 d
  · simp only [hd, if_true]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : inC2 c
    · have hcd : inC2 (c + d) := (inC2_add_iff hc).2 hd
      simp [hc, hcd]
    · simp [hc]
  · simp only [hd, if_false]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : inC2 c
    · have hcd : ¬ inC2 (c + d) := by rw [inC2_add_iff hc]; exact hd
      simp [hcd]
    · simp [hc]

/-- The general matrix element of a product of two Pauli operators between logical
basis states. -/
theorem ip_pauli_pauli (a b a' b' : Bits) (i j : ZMod 2) :
    ip (pauli a b (psi i)) (pauli a' b' (psi j))
      = if inC2 (a + a' + (lvec i + lvec j)) then
          sgn (dotp b (lvec i)) * sgn (dotp b' (lvec i + (a + a'))) * charsum (b + b')
        else 0 := by
  have expand : ip (pauli a b (psi i)) (pauli a' b' (psi j))
      = ∑ c : Bits, (if inC2 c then (1 : ℂ) else 0) *
          (sgn (dotp (b + b') c) * (sgn (dotp b (lvec i)) * sgn (dotp b' (lvec i + (a + a'))))) *
          (if inC2 (c + (a + a' + (lvec i + lvec j))) then (1 : ℂ) else 0) := by
    unfold ip
    rw [shift_sum (lvec i + a)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e2 : c + (lvec i + a) + a = c + lvec i := by
      have h : c + (lvec i + a) + a = c + lvec i + (a + a) := by abel
      rw [h, add_self_bits, add_zero]
    have e4 : c + (lvec i + a) + a' = c + (lvec i + (a + a')) := by abel
    have e1 : c + lvec i + lvec i = c := bits_cancel c (lvec i)
    have e3 : c + (lvec i + (a + a')) + lvec j = c + (a + a' + (lvec i + lvec j)) := by abel
    simp only [pauli, psi, e2, e4, e1, e3, map_mul, sgn_conj, ind_conj]
    rw [dotp_add_right, dotp_add_right, sgn_add, sgn_add, dotp_add_left, sgn_add]
    ring
  rw [expand, sum_ind_pair]
  by_cases hd : inC2 (a + a' + (lvec i + lvec j))
  · simp only [hd, if_true]
    rw [← Finset.sum_mul, ← charsum]
    ring
  · simp [hd]

/-! ## Main theorem -/

/-- **The Steane code corrects any single-qubit error.**

`psi 0, psi 1` span the code space of the 7-qubit Steane CSS code, and `pauli a b`
with `wt a b ≤ 1` ranges over the Pauli operators supported on at most one qubit;
these span all operators acting on a single qubit.  The identity below is exactly the
Knill–Laflamme error-correction condition
`⟨ψᵢ| E† F |ψⱼ⟩ = c_{E,F} δᵢⱼ`
for that error set, with the nondegenerate coefficient matrix `c_{E,F} = 8 δ_{E,F}`
(8 being the squared norm of the unnormalised logical states). -/
theorem steane_code (a b a' b' : Bits) (h1 : wt a b ≤ 1) (h2 : wt a' b' ≤ 1) (i j : ZMod 2) :
    ip (pauli a b (psi i)) (pauli a' b' (psi j))
      = (if a = a' ∧ b = b' then (8 : ℂ) else 0) * (if i = j then 1 else 0) := by
  have hwA : wtv (a + a') ≤ 2 :=
    le_trans (wtv_add_le a a')
      (by have := wtv_le_wt_left a b; have := wtv_le_wt_left a' b'; omega)
  have hwB : wtv (b + b') ≤ 2 :=
    le_trans (wtv_add_le b b')
      (by have := wtv_le_wt_right a b; have := wtv_le_wt_right a' b'; omega)
  rw [ip_pauli_pauli, lvec_add_lvec]
  by_cases hij : i = j
  · simp only [hij]
    by_cases hA : inC2 (a + a')
    · have haa : a = a' := (bits_add_eq_zero_iff a a').1 (C2_min_weight _ hwA hA)
      subst haa
      rw [add_self_bits] at *
      simp only [inC2_zero, if_true, add_zero]
      by_cases hB : b + b' = 0
      · have hbb : b = b' := (bits_add_eq_zero_iff b b').1 hB
        subst hbb
        rw [hB, charsum_zero]
        rw [sgn_mul_self]
        simp
      · rw [charsum_eq_zero (exists_C2_nonorth _ hwB hB)]
        have hbne : b ≠ b' := by rintro rfl; exact hB (add_self_bits b)
        simp [hbne]
    · have hne : ¬ (a = a' ∧ b = b') := by
        rintro ⟨rfl, -⟩
        exact hA (by rw [add_self_bits]; exact inC2_zero)
      simp [hA, hne]
  · simp only [hij, if_false, mul_zero]
    have hd : ¬ inC2 (a + a' + ones) := C2_shift_min_weight _ hwA
    simp [hd]

/-! ## Sanity corollaries -/

theorem wt_zero : wt (0 : Bits) 0 = 0 := by decide

theorem pauli_zero (v : Vec) : pauli 0 0 v = v := by
  funext u
  unfold pauli dotp sgn
  simp

/-- The two (unnormalised) logical basis states are orthogonal and each has squared
norm 8; in particular the Steane code space is genuinely two-dimensional. -/
theorem steane_logical_inner (i j : ZMod 2) :
    ip (psi i) (psi j) = if i = j then (8 : ℂ) else 0 := by
  have h := steane_code 0 0 0 0 (by simp [wt_zero]) (by simp [wt_zero]) i j
  rw [pauli_zero, pauli_zero] at h
  rw [h]
  by_cases hij : i = j <;> simp [hij]

end QI

