/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Steane `[[7,1,3]]` code corrects any single-qubit error

The Steane code is the CSS code built from the classical `[7,4,3]` Hamming code, whose
parity-check matrix `H` has as its `i`-th column the binary expansion of `i + 1`.  The same
matrix supplies the three `X`-type and the three `Z`-type stabilizer generators.

We work with the honest quantum state space of seven qubits, realised as the `2 ^ 7`-dimensional
complex vector space `Bits → ℂ` of amplitude functions on computational basis states
`Bits = Fin 7 → ZMod 2`, with the Hermitian form `ip f g = ∑ v, conj (f v) * g v`.
For `a b : Bits`, `pauli a b` is the Pauli operator `X(a) Z(b)` (up to an irrelevant global
sign), acting by `(pauli a b f) v = (-1) ^ (b ⬝ v) * f (v + a)`.

The code space is the joint `+1` eigenspace `IsStabilized` of the six stabilizer generators;
it is nontrivial, as witnessed by the logical `|0⟩` state `zeroL`.

The main theorem `QI.steane_code` records three facts:

1. **the code space is nonzero** (`zeroL` is a stabilizer state and `zeroL ≠ 0`);
2. **the Knill–Laflamme error-correction condition** holds for the set of all single-qubit
   Pauli errors: for codewords `f, g` and single-qubit Pauli errors `E, F`,
   `⟪E f, F g⟫ = c (E, F) * ⟪f, g⟫` with `c (E, F) = 1` if `E = F` and `0` otherwise.
   By the Knill–Laflamme theorem this is exactly the statement that the code corrects any
   single-qubit error;
3. **explicit syndrome decoding**: the decoder `decodeErr` reconstructs every single-qubit
   Pauli error from its measured syndrome.
-/

set_option maxRecDepth 40000

namespace QI

/-! ### The classical Hamming parity-check matrix -/

/-- Parity-check matrix of the classical `[7,4,3]` Hamming code: the `i`-th column is the
binary expansion of `i + 1`. -/
def H (k : Fin 3) (i : Fin 7) : ZMod 2 := if (i.val + 1).testBit k.val then 1 else 0

/-- The `i`-th column of `H` (the syndrome pattern of a single error on qubit `i`). -/
def col (i : Fin 7) : Fin 3 → ZMod 2 := fun k => H k i

/-- The `k`-th row of `H`, i.e. the support of the `k`-th stabilizer generator. -/
def row (k : Fin 3) : Fin 7 → ZMod 2 := fun j => H k j

/-- Being a codeword of the classical Hamming code. -/
def IsCodeword (x : Fin 7 → ZMod 2) : Prop := ∀ k, ∑ j, H k j * x j = 0

instance : DecidablePred IsCodeword := fun _ => by unfold IsCodeword; infer_instance

/-- Hamming weight of a binary vector. -/
def wt (x : Fin 7 → ZMod 2) : ℕ := (Finset.univ.filter (fun j => x j ≠ 0)).card

/-- The columns of `H` are nonzero, so every single-qubit error is detected. -/
theorem col_ne_zero (i : Fin 7) : col i ≠ 0 := by revert i; decide

/-- The columns of `H` are pairwise distinct, so single-qubit errors are located. -/
theorem col_injective : Function.Injective col := by decide

/-- CSS commutation relation `H Hᵀ = 0` over `GF(2)`: the `X`-type and `Z`-type stabilizer
generators of the Steane code commute. -/
theorem css_commute (a b : Fin 3) : ∑ j, H a j * H b j = 0 := by revert a b; decide

/-- The classical Hamming code has `2 ^ 4 = 16` codewords. -/
theorem card_codewords : (Finset.univ.filter IsCodeword).card = 16 := by decide

/-- The classical Hamming code has minimum distance `3`. -/
theorem min_distance_three (x : Fin 7 → ZMod 2) (hx : IsCodeword x) (hx0 : x ≠ 0) :
    3 ≤ wt x := by revert x; decide

/-! ### Single-qubit Pauli errors and syndrome decoding -/

/-- A Pauli error on seven qubits in symplectic notation: the `X`- and `Z`-components on
each qubit (`(1,0) = X`, `(0,1) = Z`, `(1,1) = Y`, `(0,0) = I`). -/
abbrev PauliErr := Fin 7 → ZMod 2 × ZMod 2

/-- The single-qubit Pauli error with symplectic label `p` acting on qubit `i`. -/
def pauliErr (i : Fin 7) (p : ZMod 2 × ZMod 2) : PauliErr :=
  fun j => if j = i then p else 0

/-- `X`-component of a Pauli error. -/
def xv (e : PauliErr) : Fin 7 → ZMod 2 := fun j => (e j).1

/-- `Z`-component of a Pauli error. -/
def zv (e : PauliErr) : Fin 7 → ZMod 2 := fun j => (e j).2

/-- The pair of syndromes (`Z`-stabilizer outcomes, `X`-stabilizer outcomes) of a Pauli
error `e`, written symplectically. -/
def syndrome (e : PauliErr) : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  (fun k => ∑ j, H k j * (e j).1, fun k => ∑ j, H k j * (e j).2)

/-- The explicit syndrome decoder: put an `X` (resp. `Z`) on the unique qubit whose Hamming
column equals the measured `X`- (resp. `Z`-) syndrome. -/
def decodeErr (s : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : PauliErr :=
  fun j => (if col j = s.1 then 1 else 0, if col j = s.2 then 1 else 0)

/-- The decoder recovers every single-qubit Pauli error from its syndrome. -/
theorem decodeErr_syndrome (i : Fin 7) (p : ZMod 2 × ZMod 2) :
    decodeErr (syndrome (pauliErr i p)) = pauliErr i p := by
  revert i p; decide

/-- Distinct single-qubit Pauli errors have distinct syndromes. -/
theorem syndrome_injective_on_single (i j : Fin 7) (p q : ZMod 2 × ZMod 2)
    (h : syndrome (pauliErr i p) = syndrome (pauliErr j q)) :
    pauliErr i p = pauliErr j q := by
  rw [← decodeErr_syndrome i p, ← decodeErr_syndrome j q, h]

/-! ### The seven-qubit Hilbert space, Pauli operators and the code space -/

/-- Computational basis labels for seven qubits. -/
abbrev Bits := Fin 7 → ZMod 2

/-- Amplitude functions: the `2 ^ 7`-dimensional state space of seven qubits. -/
abbrev St := Bits → ℂ

/-- The sign `(-1) ^ b`. -/
def sgn (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

/-- The `GF(2)` inner product of two bit strings. -/
def dot (a v : Bits) : ZMod 2 := ∑ j, a j * v j

/-- The Pauli operator `X(a) Z(b)` (up to a global sign) acting on amplitude functions. -/
def pauli (a b : Bits) (f : St) : St := fun v => sgn (dot b v) * f (v + a)

/-- The Hermitian inner product on the seven-qubit state space. -/
noncomputable def ip (f g : St) : ℂ := ∑ v, star (f v) * g v

/-- The operator implementing a symplectic Pauli error `e`. -/
def errOp (e : PauliErr) : St → St := pauli (xv e) (zv e)

/-- Membership in the Steane code space: fixed by all six stabilizer generators. -/
def IsStabilized (f : St) : Prop := ∀ k, pauli (row k) 0 f = f ∧ pauli 0 (row k) f = f

/-- The logical `|0⟩` of the Steane code: the uniform superposition of the `16` classical
Hamming codewords. -/
def zeroL : St := fun v => if (∀ k, dot (row k) v = 0) then 1 else 0

/-! ### Elementary algebraic lemmas -/

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    subst ha <;> subst hb <;> simp [sgn, (by decide : (1 : ZMod 2) + 1 = 0)]

theorem star_sgn (a : ZMod 2) : star (sgn a) = sgn a := by
  rcases zmod2_cases a with ha | ha <;> subst ha <;> simp [sgn]

theorem sgn_mul_self (a : ZMod 2) : sgn a * sgn a = 1 := by
  rcases zmod2_cases a with ha | ha <;> subst ha <;> norm_num [sgn]

theorem dot_add_right (a v w : Bits) : dot a (v + w) = dot a v + dot a w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_add_left (a b v : Bits) : dot (a + b) v = dot a v + dot b v := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (v : Bits) : dot 0 v = 0 := by simp [dot]

theorem dot_zero_right (a : Bits) : dot a 0 = 0 := by simp [dot]

theorem add_self_bits (x c : Bits) : x + c + c = x := by
  funext j
  simp [add_assoc, (by decide : ∀ y : ZMod 2, y + y = 0)]

theorem bits_add_self (c : Bits) : c + c = 0 := by
  have := add_self_bits 0 c; simpa using this

/-- Rows of `H` are Hamming codewords: this is the CSS commutation relation. -/
theorem dot_row_row (m k : Fin 3) : dot (row m) (row k) = 0 := by
  revert m k; decide

/-! ### The auxiliary bilinear quantity `T` -/

/-- The quantity `⟪X(a₁)Z(b₁) f, X(a₂)Z(b₂) g⟫` depends on `b₁, b₂` only through `b₁ + b₂`;
`T b a₁ a₂ f g` is that common value for `b = b₁ + b₂`. -/
noncomputable def T (b a1 a2 : Bits) (f g : St) : ℂ :=
  ∑ v, sgn (dot b v) * (star (f (v + a1)) * g (v + a2))

theorem ip_pauli_eq_T (a1 b1 a2 b2 : Bits) (f g : St) :
    ip (pauli a1 b1 f) (pauli a2 b2 g) = T (b1 + b2) a1 a2 f g := by
  unfold ip pauli T
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [star_mul', star_sgn, dot_add_left, sgn_add]
  ring

theorem T_zero_diag (a : Bits) (f g : St) : T 0 a a f g = ip f g := by
  rw [T, ip, ← Equiv.sum_comp (Equiv.addRight a) (fun v : Bits => star (f v) * g v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [sgn, dot]

/-- Invariance under a stabilizer generator `pauli c d` fixing both states: the quantity `T`
is multiplied by the symplectic sign. -/
theorem T_stab (c d b a1 a2 : Bits) (f g : St)
    (hf : pauli c d f = f) (hg : pauli c d g = g) :
    T b a1 a2 f g = sgn (dot d a1 + dot d a2 + dot b c) * T b a1 a2 f g := by
  have key : ∀ v : Bits, sgn (dot b v) * (star (f (v + a1)) * g (v + a2))
      = sgn (dot d a1 + dot d a2) *
        (sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c))) := by
    intro v
    conv_lhs => rw [← hf, ← hg]
    simp only [pauli, dot_add_right, sgn_add, star_mul', star_sgn]
    have hss := sgn_mul_self (dot d v)
    linear_combination (sgn (dot b v) * sgn (dot d a1) * sgn (dot d a2) *
      (star (f (v + a1 + c)) * g (v + a2 + c))) * hss
  have step1 : T b a1 a2 f g
      = sgn (dot d a1 + dot d a2) *
        ∑ v : Bits, sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => key v
  have step2 : (∑ v : Bits, sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c)))
      = sgn (dot b c) * T b a1 a2 f g := by
    rw [T, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight c)
      (fun v : Bits => sgn (dot b v) * (star (f (v + a1 + c)) * g (v + a2 + c)))]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.coe_addRight]
    rw [dot_add_right, sgn_add,
      show v + c + a1 + c = v + a1 by rw [add_right_comm v c a1, add_self_bits],
      show v + c + a2 + c = v + a2 by rw [add_right_comm v c a2, add_self_bits]]
    ring
  rw [sgn_add, mul_assoc, ← step2, ← step1]

/-- If the error difference anticommutes with a stabilizer generator, the overlap vanishes. -/
theorem T_eq_zero_of_anticommute (c d b a1 a2 : Bits) (f g : St)
    (hf : pauli c d f = f) (hg : pauli c d g = g)
    (hsign : dot d a1 + dot d a2 + dot b c = 1) :
    T b a1 a2 f g = 0 := by
  have h := T_stab c d b a1 a2 f g hf hg
  rw [hsign] at h
  simp only [sgn, if_neg (by decide : ¬ (1 : ZMod 2) = 0)] at h
  linear_combination h / 2

/-! ### The code space is nontrivial -/

theorem zeroL_stabilized : IsStabilized zeroL := by
  intro k
  constructor
  · funext v
    simp only [pauli, dot_zero_left, sgn, zeroL]
    have hiff : (∀ m, dot (row m) (v + row k) = 0) ↔ (∀ m, dot (row m) v = 0) := by
      constructor
      · intro h m
        have := h m
        rwa [dot_add_right, dot_row_row, add_zero] at this
      · intro h m
        rw [dot_add_right, dot_row_row, add_zero]
        exact h m
    by_cases hv : ∀ m, dot (row m) v = 0
    · rw [if_pos (hiff.mpr hv), if_pos hv]; norm_num
    · rw [if_neg (fun hc => hv (hiff.mp hc)), if_neg hv]; norm_num
  · funext v
    simp only [pauli, add_zero, zeroL]
    by_cases hv : ∀ m, dot (row m) v = 0
    · rw [if_pos hv, hv k]
      simp [sgn]
    · rw [if_neg hv, mul_zero]

theorem zeroL_ne_zero : zeroL ≠ 0 := by
  intro h
  have h0 : zeroL 0 = 0 := by rw [h]; rfl
  rw [zeroL, if_pos (fun m => dot_zero_right (row m))] at h0
  exact one_ne_zero h0

/-- The logical `|0⟩` has squared norm `16`: it is the uniform superposition of the `16`
classical Hamming codewords. -/
theorem ip_zeroL : ip zeroL zeroL = 16 := by
  have h : ∀ v : Bits,
      star (zeroL v) * zeroL v = if (∀ k, dot (row k) v = 0) then (1 : ℂ) else 0 := by
    intro v; by_cases hv : ∀ k, dot (row k) v = 0 <;> simp [zeroL, hv]
  rw [ip, Finset.sum_congr rfl fun v _ => h v, Finset.sum_boole,
    show (Finset.univ.filter fun v : Bits => ∀ k, dot (row k) v = 0).card = 16 from by decide]
  norm_num

/-! ### Knill–Laflamme condition for single-qubit errors -/

/-- If a pair of single-qubit Pauli errors has trivial relative syndrome, the two errors are
equal.  (Equivalently: the Hamming code has minimum distance `3 > 2`.) -/
theorem single_error_sep (i j : Fin 7) (p q : ZMod 2 × ZMod 2)
    (hx : ∀ k, dot (row k) (xv (pauliErr i p)) + dot (row k) (xv (pauliErr j q)) = 0)
    (hz : ∀ k, dot (zv (pauliErr i p) + zv (pauliErr j q)) (row k) = 0) :
    pauliErr i p = pauliErr j q := by
  revert hx hz; revert i j p q; decide

/-- **Knill–Laflamme condition.**  For codewords `f, g` of the Steane code and single-qubit
Pauli errors `E, F`, the overlap `⟪E f, F g⟫` equals `⟪f, g⟫` if `E = F` and vanishes
otherwise; in particular the coefficient is independent of the codewords, which is exactly the
Knill–Laflamme criterion for correctability of the whole set of single-qubit errors. -/
theorem knill_laflamme (i j : Fin 7) (p q : ZMod 2 × ZMod 2) (f g : St)
    (hf : IsStabilized f) (hg : IsStabilized g) :
    ip (errOp (pauliErr i p) f) (errOp (pauliErr j q) g)
      = if pauliErr i p = pauliErr j q then ip f g else 0 := by
  by_cases h : pauliErr i p = pauliErr j q
  · rw [if_pos h, h, errOp, ip_pauli_eq_T, bits_add_self, T_zero_diag]
  · rw [if_neg h, errOp, errOp, ip_pauli_eq_T]
    by_cases hx : ∀ k, dot (row k) (xv (pauliErr i p)) + dot (row k) (xv (pauliErr j q)) = 0
    · by_cases hz : ∀ k, dot (zv (pauliErr i p) + zv (pauliErr j q)) (row k) = 0
      · exact absurd (single_error_sep i j p q hx hz) h
      · push_neg at hz
        obtain ⟨k, hk⟩ := hz
        refine T_eq_zero_of_anticommute (row k) 0 _ _ _ f g (hf k).1 (hg k).1 ?_
        rw [dot_zero_left, dot_zero_left]
        rcases zmod2_cases (dot (zv (pauliErr i p) + zv (pauliErr j q)) (row k)) with h0 | h1
        · exact absurd h0 hk
        · rw [h1]; ring
    · push_neg at hx
      obtain ⟨k, hk⟩ := hx
      refine T_eq_zero_of_anticommute 0 (row k) _ _ _ f g (hf k).2 (hg k).2 ?_
      rw [dot_zero_right]
      rcases zmod2_cases (dot (row k) (xv (pauliErr i p)) +
          dot (row k) (xv (pauliErr j q))) with h0 | h1
      · exact absurd h0 hk
      · rw [add_zero, h1]

/-! ### Main theorem -/

/-- **The 7-qubit Steane code corrects any single-qubit error.**

1. The code space is nontrivial: the logical `|0⟩` state `zeroL` is a nonzero state (of squared
   norm `16`) fixed by all six stabilizer generators.
2. The Knill–Laflamme error-correction condition holds for the set of all single-qubit Pauli
   errors `{I, X, Y, Z}` on any of the seven qubits: for codewords `f, g`,
   `⟪E f, F g⟫ = c (E, F) ⟪f, g⟫` with `c (E, F) = 1` for `E = F` and `0` otherwise.  By the
   Knill–Laflamme theorem this says precisely that the code corrects any single-qubit error.
3. Concretely, the explicit decoder `decodeErr` reconstructs every single-qubit Pauli error
   from its measured stabilizer syndrome. -/
theorem steane_code :
    (IsStabilized zeroL ∧ zeroL ≠ 0 ∧ ip zeroL zeroL = 16) ∧
      (∀ (i j : Fin 7) (p q : ZMod 2 × ZMod 2) (f g : St),
          IsStabilized f → IsStabilized g →
          ip (errOp (pauliErr i p) f) (errOp (pauliErr j q) g)
            = if pauliErr i p = pauliErr j q then ip f g else 0) ∧
      (∀ (i : Fin 7) (p : ZMod 2 × ZMod 2),
          decodeErr (syndrome (pauliErr i p)) = pauliErr i p) := by
  exact ⟨⟨zeroL_stabilized, zeroL_ne_zero, ip_zeroL⟩,
    fun i j p q f g hf hg => knill_laflamme i j p q f g hf hg,
    decodeErr_syndrome⟩

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

