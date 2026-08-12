/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Basic setting: 7 qubits, computational basis indexed by bit strings -/

/-- Labels of the computational basis of `(ℂ²)^{⊗7}`: bit strings of length 7. -/
abbrev Bits := Fin 7 → ZMod 2

/-- Syndrome values: three bits (one per parity check of each CSS type). -/
abbrev Chk := Fin 3 → ZMod 2

/-- A state of the 7-qubit register, in the computational basis. -/
abbrev State := Bits → ℂ

/-- Mod-2 inner product of two bit strings. -/
def dot (v w : Bits) : ZMod 2 := ∑ i, v i * w i

/-- The sign `(-1)^a` for `a : ZMod 2`. -/
def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

/-- The parity-check matrix of the `[7,4,3]` Hamming code: the `i`-th column is the
binary representation of `i+1`. -/
def Hrow (k : Fin 3) : Bits := fun i => if Nat.testBit (i.val + 1) k.val then 1 else 0

/-- The Pauli `X` operator associated to a bit string `v` (a tensor product of `X`'s on
the support of `v`): `X_v |u⟩ = |u + v⟩`. -/
def Xop (v : Bits) (psi : State) : State := fun u => psi (u + v)

/-- The Pauli `Z` operator associated to a bit string `w`: `Z_w |u⟩ = (-1)^{w·u} |u⟩`. -/
def Zop (w : Bits) (psi : State) : State := fun u => sgn (dot w u) * psi u

/-- A general Pauli error (up to phase): `E_{v,w} = X_v Z_w`. -/
def Err (v w : Bits) (psi : State) : State := Xop v (Zop w psi)

/-- The recovery operator inverting `Err v w`, namely `Z_w X_v`. -/
def Rec (v w : Bits) (psi : State) : State := Zop w (Xop v psi)

/-- The Steane code space: the joint `+1` eigenspace of the six stabilizer generators
`X_{H_k}`, `Z_{H_k}` (`k = 0,1,2`). -/
def IsCode (psi : State) : Prop := ∀ k : Fin 3, Xop (Hrow k) psi = psi ∧ Zop (Hrow k) psi = psi

/-- The syndrome of a bit string: the vector of parity checks `H · v`. -/
def syn (v : Bits) : Chk := fun k => dot (Hrow k) v

/-- The unit bit string supported on qubit `i`. -/
def unitv (i : Fin 7) : Bits := fun j => if j = i then 1 else 0

/-- `pauliVec a i` is `a` at position `i` and `0` elsewhere. -/
def pauliVec (a : ZMod 2) (i : Fin 7) : Bits := fun j => if j = i then a else 0

/-- The Hamming decoder: given a syndrome, return the (unique) weight ≤ 1 bit string
having that syndrome. -/
def decode (s : Chk) : Bits := fun i => if syn (unitv i) = s then 1 else 0

/-- A Pauli error `E_{v,w}` acts on at most one qubit. -/
def IsSingleQubit (v w : Bits) : Prop := ∃ i : Fin 7, ∀ j : Fin 7, j ≠ i → v j = 0 ∧ w j = 0

/-! ## Elementary algebra of the operators -/

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> simp [sgn, show (1 : ZMod 2) + 1 = 0 by decide]

lemma sgn_mul_self (a : ZMod 2) : sgn a * sgn a = 1 := by
  fin_cases a <;> simp [sgn]

lemma dot_comm (v w : Bits) : dot v w = dot w v := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dot_add_right (v u w : Bits) : dot v (u + w) = dot v u + dot v w := by
  simp only [dot, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

lemma add_self_bits (v : Bits) : v + v = 0 := by
  funext i; simp [CharTwo.add_self_eq_zero]

lemma Xop_Xop (a b : Bits) (psi : State) : Xop a (Xop b psi) = Xop (a + b) psi := by
  funext u; simp only [Xop]; rw [add_assoc]

lemma Xop_self (v : Bits) (psi : State) : Xop v (Xop v psi) = psi := by
  rw [Xop_Xop, add_self_bits]; funext u; simp [Xop]

lemma Zop_Zop (a b : Bits) (psi : State) : Zop a (Zop b psi) = Zop (a + b) psi := by
  funext u
  simp only [Zop, dot, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib, sgn_add]
  ring

lemma Zop_self (w : Bits) (psi : State) : Zop w (Zop w psi) = psi := by
  rw [Zop_Zop, add_self_bits]
  funext u; simp [Zop, dot, sgn]

lemma Xop_Zop_comm (v w : Bits) (psi : State) :
    Xop v (Zop w psi) = sgn (dot w v) • Zop w (Xop v psi) := by
  funext u
  simp only [Xop, Zop, Pi.smul_apply, smul_eq_mul]
  rw [dot_add_right, sgn_add]
  ring

lemma Xop_add (v : Bits) (psi phi : State) : Xop v (psi + phi) = Xop v psi + Xop v phi := rfl

lemma Xop_smul (v : Bits) (c : ℂ) (psi : State) : Xop v (c • psi) = c • Xop v psi := rfl

lemma Zop_add (w : Bits) (psi phi : State) : Zop w (psi + phi) = Zop w psi + Zop w phi := by
  funext u; simp [Zop, mul_add]

lemma Zop_smul (w : Bits) (c : ℂ) (psi : State) : Zop w (c • psi) = c • Zop w psi := by
  funext u; simp [Zop]; ring

/-! ## Syndrome measurement -/

/-- Measuring the `Z`-type stabilizer `Z_{H_k}` on an erroneous code state `E_{v,w} ψ`
returns the sign `(-1)^{(H v)_k}`, i.e. the `k`-th bit of the syndrome of the `X`-part
of the error. -/
theorem steane_syndrome_Z (v w : Bits) (psi : State) (hpsi : IsCode psi) (k : Fin 3) :
    Zop (Hrow k) (Err v w psi) = sgn (syn v k) • Err v w psi := by
  have hz : Zop (Hrow k) (Zop w psi) = Zop w psi := by
    rw [Zop_Zop, add_comm, ← Zop_Zop, (hpsi k).2]
  have key := Xop_Zop_comm v (Hrow k) (Zop w psi)
  rw [hz] at key
  have h2 : Err v w psi = sgn (syn v k) • Zop (Hrow k) (Err v w psi) := key
  conv_rhs => rw [h2]
  rw [smul_smul, sgn_mul_self, one_smul]

/-- Measuring the `X`-type stabilizer `X_{H_k}` on an erroneous code state `E_{v,w} ψ`
returns the sign `(-1)^{(H w)_k}`, i.e. the `k`-th bit of the syndrome of the `Z`-part
of the error. -/
theorem steane_syndrome_X (v w : Bits) (psi : State) (hpsi : IsCode psi) (k : Fin 3) :
    Xop (Hrow k) (Err v w psi) = sgn (syn w k) • Err v w psi := by
  have h1 : Xop (Hrow k) (Zop w psi) = sgn (syn w k) • Zop w psi := by
    rw [Xop_Zop_comm, (hpsi k).1, dot_comm]; rfl
  calc Xop (Hrow k) (Err v w psi) = Xop v (Xop (Hrow k) (Zop w psi)) := by
        simp only [Err, Xop_Xop, add_comm]
    _ = sgn (syn w k) • Err v w psi := by rw [h1, Xop_smul]; rfl

/-! ## The decoder is correct on weight ≤ 1 errors -/

lemma decode_syn_of_weight_le_one :
    ∀ v : Bits, (∃ i : Fin 7, ∀ j : Fin 7, j ≠ i → v j = 0) → decode (syn v) = v := by
  decide

lemma syn_pauliVec_injective (i : Fin 7) (a a' : ZMod 2) :
    syn (pauliVec a i) = syn (pauliVec a' i) → a = a' := by
  revert i a a'; decide

/-! ## Recovery -/

lemma Rec_Err (v w : Bits) (psi : State) : Rec v w (Err v w psi) = psi := by
  simp only [Rec, Err, Xop_self, Zop_self]

lemma Rec_smul (v w : Bits) (c : ℂ) (psi : State) : Rec v w (c • psi) = c • Rec v w psi := by
  simp only [Rec, Xop_smul, Zop_smul]

/-- The syndrome-determined recovery operator inverts a single-qubit Pauli error. -/
lemma steane_recovery_pauli (v w : Bits) (hvw : IsSingleQubit v w) (psi : State) :
    Rec (decode (syn v)) (decode (syn w)) (Err v w psi) = psi := by
  obtain ⟨i, hi⟩ := hvw
  have hv : decode (syn v) = v :=
    decode_syn_of_weight_le_one v ⟨i, fun j hj => (hi j hj).1⟩
  have hw : decode (syn w) = w :=
    decode_syn_of_weight_le_one w ⟨i, fun j hj => (hi j hj).2⟩
  rw [hv, hw, Rec_Err]

/-- **The Steane code corrects any single-qubit error.**
Let `ψ` be any state of the Steane code space and let `E_{v,w}` be any Pauli error acting
on at most one of the seven qubits.  Then:

* measuring the three `Z`-type stabilizers of the code on the corrupted state `E_{v,w} ψ`
  is deterministic and returns the syndrome bits `(H v)_k`;
* measuring the three `X`-type stabilizers is deterministic and returns the syndrome bits
  `(H w)_k`;
* the recovery operator obtained by Hamming-decoding *only these six measured syndrome
  bits* restores the original code state `ψ` exactly.

Since the four Pauli operators at a given qubit span all one-qubit operators, this is the
usual discretization statement of single-qubit error correction; the version for an
arbitrary (non-Pauli) one-qubit error is `QI.steane_code_arbitrary_error` below. -/
theorem steane_code (v w : Bits) (hvw : IsSingleQubit v w) (psi : State) (hpsi : IsCode psi) :
    (∀ k : Fin 3, Zop (Hrow k) (Err v w psi) = sgn (syn v k) • Err v w psi) ∧
    (∀ k : Fin 3, Xop (Hrow k) (Err v w psi) = sgn (syn w k) • Err v w psi) ∧
    Rec (decode (syn v)) (decode (syn w)) (Err v w psi) = psi :=
  ⟨fun k => steane_syndrome_Z v w psi hpsi k, fun k => steane_syndrome_X v w psi hpsi k,
    steane_recovery_pauli v w hvw psi⟩

/-! ## The code space is nontrivial -/

/-- The dual Hamming code `C₂ = ⟨H₀,H₁,H₂⟩` (row space of the parity-check matrix). -/
def combo (a : Chk) : Bits := fun i => ∑ k, a k * Hrow k i

/-- Membership in the row space of `H`. -/
def RS (u : Bits) : Prop := ∃ a : Chk, combo a = u

instance : DecidablePred RS := fun u => inferInstanceAs (Decidable (∃ a : Chk, combo a = u))

/-- The logical `|0_L⟩` state of the Steane code. -/
noncomputable def logicalZero : State := fun u => if RS u then 1 else 0

lemma RS_shift : ∀ (k : Fin 3) (u : Bits), (RS (u + Hrow k) ↔ RS u) := by decide

lemma RS_dot_zero : ∀ (k : Fin 3) (u : Bits), RS u → dot (Hrow k) u = 0 := by decide

theorem logicalZero_isCode : IsCode logicalZero := by
  intro k
  constructor
  · funext u
    simp only [Xop, logicalZero]
    exact if_congr (RS_shift k u) rfl rfl
  · funext u
    simp only [Zop, logicalZero]
    by_cases h : RS u
    · rw [RS_dot_zero k u h, if_pos h]
      simp [sgn]
    · rw [if_neg h]
      simp

theorem logicalZero_ne_zero : logicalZero ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [logicalZero, if_pos (show RS 0 by decide)] at h0
  exact one_ne_zero h0

/-- The all-ones bit string; it lies in the Hamming code but not in its dual, so it is a
representative of the nontrivial coset used to build the second logical basis state. -/
def ones : Bits := fun _ => 1

/-- The logical `|1_L⟩` state of the Steane code. -/
noncomputable def logicalOne : State := fun u => if RS (u + ones) then 1 else 0

lemma RS_shift_ones : ∀ (k : Fin 3) (u : Bits), (RS (u + Hrow k + ones) ↔ RS (u + ones)) := by
  decide

lemma RS_ones_dot_zero : ∀ (k : Fin 3) (u : Bits), RS (u + ones) → dot (Hrow k) u = 0 := by decide

theorem logicalOne_isCode : IsCode logicalOne := by
  intro k
  constructor
  · funext u
    simp only [Xop, logicalOne]
    exact if_congr (RS_shift_ones k u) rfl rfl
  · funext u
    simp only [Zop, logicalOne]
    by_cases h : RS (u + ones)
    · rw [RS_ones_dot_zero k u h, if_pos h]
      simp [sgn]
    · rw [if_neg h]
      simp

/-- The Steane code space is at least two-dimensional: it encodes a logical qubit.
Hence the error-correction statements below are not vacuous. -/
theorem logical_independent (x y : ℂ) (h : x • logicalZero + y • logicalOne = 0) :
    x = 0 ∧ y = 0 := by
  constructor
  · have h0 := congrFun h 0
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, logicalZero, logicalOne,
      if_pos (show RS 0 by decide), if_neg (show ¬ RS ((0 : Bits) + ones) by decide)] at h0
    simpa using h0
  · have h1 := congrFun h ones
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, logicalZero, logicalOne,
      if_neg (show ¬ RS ones by decide), if_pos (show RS (ones + ones) by decide)] at h1
    simpa using h1

/-! ## Arbitrary (not necessarily Pauli) single-qubit errors -/

/-- `X_v` as a linear map. -/
def XopL (v : Bits) : State →ₗ[ℂ] State where
  toFun := Xop v
  map_add' := Xop_add v
  map_smul' := fun c psi => Xop_smul v c psi

/-- `Z_w` as a linear map. -/
def ZopL (w : Bits) : State →ₗ[ℂ] State where
  toFun := Zop w
  map_add' := Zop_add w
  map_smul' := fun c psi => Zop_smul w c psi

/-- The projector `(1 + (-1)^s Z_{H_k})/2` onto the `k`-th `Z`-syndrome bit `s`. -/
noncomputable def zfacL (s : ZMod 2) (k : Fin 3) : State →ₗ[ℂ] State :=
  (2 : ℂ)⁻¹ • (LinearMap.id + sgn s • ZopL (Hrow k))

/-- The projector `(1 + (-1)^s X_{H_k})/2` onto the `k`-th `X`-syndrome bit `s`. -/
noncomputable def xfacL (s : ZMod 2) (k : Fin 3) : State →ₗ[ℂ] State :=
  (2 : ℂ)⁻¹ • (LinearMap.id + sgn s • XopL (Hrow k))

/-- The projector onto the joint eigenspace of the six stabilizers with syndrome
`(sz, sx)`; this is exactly the post-measurement projection of a syndrome measurement. -/
noncomputable def syndProj (sz sx : Chk) : State →ₗ[ℂ] State :=
  (zfacL (sz 0) 0).comp <| (zfacL (sz 1) 1).comp <| (zfacL (sz 2) 2).comp <|
    (xfacL (sx 0) 0).comp <| (xfacL (sx 1) 1).comp (xfacL (sx 2) 2)

/-- An arbitrary error acting on qubit `i` only, written in the Pauli basis of the
one-qubit operators at site `i`. -/
noncomputable def SingleQubitError (i : Fin 7) (c : ZMod 2 → ZMod 2 → ℂ) (psi : State) : State :=
  ∑ a : ZMod 2, ∑ b : ZMod 2, c a b • Err (pauliVec a i) (pauliVec b i) psi

lemma sgn_mul_of_ne {s t : ZMod 2} (h : s ≠ t) : sgn s * sgn t = -1 := by
  fin_cases s <;> fin_cases t <;> simp_all [sgn]

lemma zfacL_eigen (s t : ZMod 2) (k : Fin 3) (phi : State)
    (h : Zop (Hrow k) phi = sgn t • phi) :
    zfacL s k phi = (if s = t then (1 : ℂ) else 0) • phi := by
  have hZ : ZopL (Hrow k) phi = sgn t • phi := h
  simp only [zfacL, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hZ, smul_smul]
  by_cases hst : s = t
  · subst hst
    rw [sgn_mul_self, if_pos rfl, one_smul, ← two_smul ℂ phi, smul_smul]
    norm_num
  · rw [sgn_mul_of_ne hst, if_neg hst, zero_smul, neg_one_smul, add_neg_cancel, smul_zero]

lemma xfacL_eigen (s t : ZMod 2) (k : Fin 3) (phi : State)
    (h : Xop (Hrow k) phi = sgn t • phi) :
    xfacL s k phi = (if s = t then (1 : ℂ) else 0) • phi := by
  have hX : XopL (Hrow k) phi = sgn t • phi := h
  simp only [xfacL, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hX, smul_smul]
  by_cases hst : s = t
  · subst hst
    rw [sgn_mul_self, if_pos rfl, one_smul, ← two_smul ℂ phi, smul_smul]
    norm_num
  · rw [sgn_mul_of_ne hst, if_neg hst, zero_smul, neg_one_smul, add_neg_cancel, smul_zero]

lemma syndProj_Err (sz sx : Chk) (v w : Bits) (psi : State) (hpsi : IsCode psi) :
    syndProj sz sx (Err v w psi) = if sz = syn v ∧ sx = syn w then Err v w psi else 0 := by
  have hzf : ∀ k : Fin 3, zfacL (sz k) k (Err v w psi)
      = (if sz k = syn v k then (1 : ℂ) else 0) • Err v w psi :=
    fun k => zfacL_eigen _ _ _ _ (steane_syndrome_Z v w psi hpsi k)
  have hxf : ∀ k : Fin 3, xfacL (sx k) k (Err v w psi)
      = (if sx k = syn w k then (1 : ℂ) else 0) • Err v w psi :=
    fun k => xfacL_eigen _ _ _ _ (steane_syndrome_X v w psi hpsi k)
  simp only [syndProj, LinearMap.comp_apply, map_smul, hzf, hxf, smul_smul]
  by_cases h : sz = syn v ∧ sx = syn w
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp
  · rw [if_neg h]
    have hex : (∃ k : Fin 3, sz k ≠ syn v k) ∨ (∃ k : Fin 3, sx k ≠ syn w k) := by
      by_contra hc
      push_neg at hc
      exact h ⟨funext fun k => hc.1 k, funext fun k => hc.2 k⟩
    have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hex with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rcases hk3 k with rfl | rfl | rfl <;>
      rw [if_neg hk] <;> simp

/-- **The Steane code corrects an arbitrary single-qubit error.**
For an arbitrary error acting on qubit `i` (an arbitrary linear combination of the four
one-qubit Paulis at site `i`), each syndrome measurement outcome `(sz, sx)` projects the
corrupted state onto a state which, after the syndrome-determined recovery, is exactly
the original code state `ψ` up to the (outcome-probability) amplitude `c a b`. -/
theorem steane_code_arbitrary_error (i : Fin 7) (c : ZMod 2 → ZMod 2 → ℂ) (psi : State)
    (hpsi : IsCode psi) (a b : ZMod 2) :
    Rec (decode (syn (pauliVec a i))) (decode (syn (pauliVec b i)))
        (syndProj (syn (pauliVec a i)) (syn (pauliVec b i)) (SingleQubitError i c psi))
      = c a b • psi := by
  have hdec : ∀ a' : ZMod 2, decode (syn (pauliVec a' i)) = pauliVec a' i := by
    intro a'
    refine decode_syn_of_weight_le_one _ ⟨i, ?_⟩
    intro j hj
    simp [pauliVec, hj]
  have hproj : syndProj (syn (pauliVec a i)) (syn (pauliVec b i)) (SingleQubitError i c psi)
      = c a b • Err (pauliVec a i) (pauliVec b i) psi := by
    simp only [SingleQubitError, map_sum, map_smul, syndProj_Err _ _ _ _ _ hpsi]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro b' _ hb'
        rw [if_neg, smul_zero]
        rintro ⟨-, h2⟩
        exact hb' (syn_pauliVec_injective i b b' h2).symm
      · intro hb; exact absurd (Finset.mem_univ b) hb
    · intro a' _ ha'
      refine Finset.sum_eq_zero ?_
      intro b' _
      rw [if_neg, smul_zero]
      rintro ⟨h1, -⟩
      exact ha' (syn_pauliVec_injective i a a' h1).symm
    · intro ha; exact absurd (Finset.mem_univ a) ha
  rw [hproj, hdec, hdec, Rec_smul, Rec_Err]

end QI

