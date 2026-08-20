/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 8000

open scoped BigOperators Matrix

/-!
## Setup

We work with operators on nine qubits as matrices indexed by bit strings `Bits = Fin 9 → ZMod 2`
(so the Hilbert space is `ℂ^(2^9)`).  For `x z : Bits`, `pauli x z` is the Pauli operator
`X^x Z^z`, acting on basis states by `|v⟩ ↦ (-1)^(z·v) |v + x⟩`.

The Shor code is the stabilizer code with the eight generators
`Z₁Z₂, Z₂Z₃, Z₄Z₅, Z₅Z₆, Z₇Z₈, Z₈Z₉, X₁X₂X₃X₄X₅X₆, X₄X₅X₆X₇X₈X₉`;
`shorStab t` is the stabilizer element with exponent vector `t : Fin 8 → ZMod 2`, and
`shorProj = (1/256) ∑ t, shorStab t` is the projector onto the code space.

`onQubit i M` is the operator acting as the arbitrary `2 × 2` matrix `M` on qubit `i` and as the
identity on the other eight qubits; these are exactly the single-qubit errors.  The main theorem
`QI.shor_code_corrects` is the Knill–Laflamme error-correction condition for this error set.
-/

namespace QI

/-- Computational basis labels of nine qubits: bit strings of length `9`. -/
abbrev Bits := Fin 9 → ZMod 2

/-- Index type for the elements of the stabilizer group of the Shor code:
one `ZMod 2` exponent for each of the eight stabilizer generators. -/
abbrev Gen := Fin 8 → ZMod 2

/-- The sign `(-1)^a` for `a : ZMod 2`. -/
noncomputable def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

/-- The `ZMod 2`-valued inner product of two bit strings. -/
def dot (a b : Bits) : ZMod 2 := ∑ i, a i * b i

/-- The (phase-free) Pauli operator `X^x Z^z` on nine qubits, acting on basis states by
`X^x Z^z |v⟩ = (-1)^(z·v) |v + x⟩`. -/
noncomputable def pauli (x z : Bits) : Matrix Bits Bits ℂ :=
  Matrix.of fun u v => if u = v + x then sgn (dot z v) else 0

@[simp] lemma pauli_apply (x z : Bits) (u v : Bits) :
    pauli x z u v = if u = v + x then sgn (dot z v) else 0 := rfl

/-- The `X`-part of the stabilizer element with exponents `t`.
The two `X`-type generators are `X₁X₂X₃X₄X₅X₆` (exponent `t 6`)
and `X₄X₅X₆X₇X₈X₉` (exponent `t 7`). -/
def xPart (t : Gen) : Bits :=
  ![t 6, t 6, t 6, t 6 + t 7, t 6 + t 7, t 6 + t 7, t 7, t 7, t 7]

/-- The `Z`-part of the stabilizer element with exponents `t`.
The six `Z`-type generators are `Z₁Z₂, Z₂Z₃, Z₄Z₅, Z₅Z₆, Z₇Z₈, Z₈Z₉`
(exponents `t 0, …, t 5`). -/
def zPart (t : Gen) : Bits :=
  ![t 0, t 0 + t 1, t 1, t 2, t 2 + t 3, t 3, t 4, t 4 + t 5, t 5]

/-- The stabilizer element with exponent vector `t`. -/
noncomputable def shorStab (t : Gen) : Matrix Bits Bits ℂ := pauli (xPart t) (zPart t)

/-- The orthogonal projector onto the code space of the nine-qubit Shor code,
`P = (1/|S|) ∑_{s ∈ S} s`. -/
noncomputable def shorProj : Matrix Bits Bits ℂ := (256 : ℂ)⁻¹ • ∑ t : Gen, shorStab t

/-- `unit i` is the bit string with a single `1` in position `i`. -/
def unit (i : Fin 9) : Bits := fun k => if k = i then 1 else 0

/-- The operator acting as the `2 × 2` matrix `M` on qubit `i` and as the identity elsewhere. -/
noncomputable def onQubit (i : Fin 9) (M : Matrix (ZMod 2) (ZMod 2) ℂ) : Matrix Bits Bits ℂ :=
  Matrix.of fun u v => if (∀ k, k ≠ i → u k = v k) then M (u i) (v i) else 0

@[simp] lemma onQubit_apply (i : Fin 9) (M : Matrix (ZMod 2) (ZMod 2) ℂ) (u v : Bits) :
    onQubit i M u v = if (∀ k, k ≠ i → u k = v k) then M (u i) (v i) else 0 := rfl

/-! ### Basic algebra of Pauli operators -/

lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    (norm_num [sgn]; try decide)

lemma bits_add_add_cancel (v x : Bits) : v + x + x = v := by
  ext k
  have : ∀ a b : ZMod 2, a + b + b = a := by decide
  simpa using this (v k) (x k)

lemma dot_comm (a b : Bits) : dot a b = dot b a := by
  simp [dot, mul_comm]

lemma dot_add_right (a b c : Bits) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_add_left (a b c : Bits) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma pauli_mul (x₁ z₁ x₂ z₂ : Bits) :
    pauli x₁ z₁ * pauli x₂ z₂ = sgn (dot z₁ x₂) • pauli (x₁ + x₂) (z₁ + z₂) := by
  ext u v
  rw [Matrix.mul_apply, Finset.sum_eq_single (v + x₂)]
  · simp only [pauli_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    by_cases h : u = v + (x₁ + x₂)
    · rw [if_pos (by rw [h]; abel), if_pos h, dot_add_right, dot_add_left, sgn_add, sgn_add]
      ring
    · rw [if_neg (by intro hh; exact h (by rw [hh]; abel)), if_neg h]; ring
  · intro b _ hb
    simp only [pauli_apply, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The stabilizer group -/

lemma xPart_add (t s : Gen) : xPart (t + s) = xPart t + xPart s := by
  ext i; fin_cases i <;> simp [xPart] <;> ring

lemma zPart_add (t s : Gen) : zPart (t + s) = zPart t + zPart s := by
  ext i; fin_cases i <;> simp [zPart] <;> ring

lemma dot_zPart_xPart (t s : Gen) : dot (zPart t) (xPart s) = 0 := by
  simp only [dot, Fin.sum_univ_succ, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, zPart, xPart, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring_nf
  simp [show (2 : ZMod 2) = 0 by decide]

lemma shorStab_mul (t s : Gen) : shorStab t * shorStab s = shorStab (t + s) := by
  rw [shorStab, shorStab, pauli_mul, dot_zPart_xPart, sgn_zero, one_smul, shorStab,
    xPart_add, zPart_add]

lemma card_gen : Fintype.card Gen = 256 := by simp

lemma sum_shorStab_shift (s : Gen) : ∑ t : Gen, shorStab (s + t) = ∑ t : Gen, shorStab t :=
  Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun _ => rfl)

lemma shorStab_mul_proj (t : Gen) : shorStab t * shorProj = shorProj := by
  rw [shorProj, Matrix.mul_smul, Finset.mul_sum]
  simp_rw [shorStab_mul]
  rw [sum_shorStab_shift]

lemma proj_mul_shorStab (t : Gen) : shorProj * shorStab t = shorProj := by
  rw [shorProj, Matrix.smul_mul, Finset.sum_mul]
  simp_rw [shorStab_mul, add_comm _ t]
  rw [sum_shorStab_shift]

lemma shorProj_idem : shorProj * shorProj = shorProj := by
  nth_rewrite 1 [shorProj]
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [shorStab_mul_proj]
  rw [Finset.sum_const, Finset.card_univ, card_gen, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

lemma sgn_star (a : ZMod 2) : star (sgn a) = sgn a := by
  rcases zmod_two_cases a with rfl | rfl <;> simp [sgn]

lemma pauli_conjTranspose (x z : Bits) : (pauli x z)ᴴ = sgn (dot z x) • pauli x z := by
  ext u v
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, pauli_apply, pauli_apply, smul_eq_mul]
  by_cases h : u = v + x
  · have h' : v = u + x := by rw [h, bits_add_add_cancel]
    rw [if_pos h', if_pos h, h', dot_add_right, sgn_add, sgn_star]
    have : sgn (dot z x) * sgn (dot z x) = 1 := by
      rcases zmod_two_cases (dot z x) with hh | hh <;> rw [hh] <;> norm_num [sgn]
    calc sgn (dot z u) = sgn (dot z u) * 1 := by ring
      _ = sgn (dot z x) * (sgn (dot z u) * sgn (dot z x)) := by rw [← this]; ring
  · have h' : ¬ v = u + x := by
      intro hh; exact h (by rw [hh, bits_add_add_cancel])
    rw [if_neg h', if_neg h]
    simp

lemma shorProj_conjTranspose : shorProjᴴ = shorProj := by
  rw [shorProj, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp_rw [shorStab, pauli_conjTranspose, dot_zPart_xPart, sgn_zero, one_smul]
  simp

lemma bits_self_add_iff (v x : Bits) : v = v + x ↔ x = 0 := by
  constructor
  · intro h
    funext k
    have H : ∀ a b : ZMod 2, a = a + b → b = 0 := by decide
    exact H _ _ (congrFun h k)
  · rintro rfl; simp

lemma dot_zero_left (v : Bits) : dot 0 v = 0 := by simp [dot]

lemma dot_unit_left (i : Fin 9) (v : Bits) : dot (unit i) v = v i := by
  simp [dot, unit, Finset.sum_ite_eq']

/-- Character sum: the signs `(-1)^(z·v)` cancel unless `z = 0`. -/
lemma sum_sgn_dot (z : Bits) : ∑ v : Bits, sgn (dot z v) = if z = 0 then 512 else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp [dot_zero_left, sgn_zero]
  · rw [if_neg hz]
    obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (funext hc)
    have hzk : z k = 1 := (zmod_two_cases (z k)).resolve_left hk
    have hshift : ∑ v : Bits, sgn (dot z (v + unit k)) = ∑ v : Bits, sgn (dot z v) :=
      Equiv.sum_comp (Equiv.addRight (unit k)) (fun v => sgn (dot z v))
    have hval : ∀ v : Bits, sgn (dot z (v + unit k)) = - sgn (dot z v) := by
      intro v
      rw [dot_add_right, sgn_add, dot_comm z (unit k), dot_unit_left, hzk]
      simp [sgn]
    rw [Finset.sum_congr rfl (fun v _ => hval v), Finset.sum_neg_distrib] at hshift
    linear_combination (-1/2 : ℂ) * hshift

lemma pauli_trace (x z : Bits) :
    Matrix.trace (pauli x z) = if x = 0 then (if z = 0 then (512 : ℂ) else 0) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pauli_apply]
  by_cases hx : x = 0
  · subst hx
    simp only [add_zero, if_true]
    exact sum_sgn_dot z
  · rw [if_neg hx]
    refine Finset.sum_eq_zero (fun v _ => ?_)
    rw [if_neg]
    intro h
    exact hx ((bits_self_add_iff v x).1 h)

lemma xPart_zero : xPart 0 = 0 := by ext k; fin_cases k <;> simp [xPart]

lemma zPart_zero : zPart 0 = 0 := by ext k; fin_cases k <;> simp [zPart]

lemma gen_eq_zero_of (t : Gen) (hx : xPart t = 0) (hz : zPart t = 0) : t = 0 := by
  have h0 : t 0 = 0 := by simpa [zPart] using congrFun hz 0
  have h1 : t 1 = 0 := by simpa [zPart] using congrFun hz 2
  have h2 : t 2 = 0 := by simpa [zPart] using congrFun hz 3
  have h3 : t 3 = 0 := by simpa [zPart] using congrFun hz 5
  have h4 : t 4 = 0 := by simpa [zPart] using congrFun hz 6
  have h5 : t 5 = 0 := by simpa [zPart] using congrFun hz 8
  have h6 : t 6 = 0 := by simpa [xPart] using congrFun hx 0
  have h7 : t 7 = 0 := by simpa [xPart] using congrFun hx 8
  funext m
  fin_cases m <;> simp only [Pi.zero_apply] <;>
    first
      | exact h0 | exact h1 | exact h2 | exact h3
      | exact h4 | exact h5 | exact h6 | exact h7

/-- The code space is two-dimensional: the projector has trace `2`. -/
lemma shorProj_trace : Matrix.trace shorProj = 2 := by
  rw [shorProj, Matrix.trace_smul, Matrix.trace_sum]
  have hterm : ∀ t : Gen, Matrix.trace (shorStab t) = if t = 0 then (512 : ℂ) else 0 := by
    intro t
    rw [shorStab, pauli_trace]
    by_cases ht : t = 0
    · subst ht
      rw [xPart_zero, zPart_zero]
      simp
    · rw [if_neg ht]
      by_cases hxt : xPart t = 0
      · rw [if_pos hxt, if_neg (fun hzt => ht (gen_eq_zero_of t hxt hzt))]
      · rw [if_neg hxt]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_ite_eq' Finset.univ (0 : Gen)]
  norm_num

lemma shorProj_ne_zero : shorProj ≠ 0 := by
  intro h
  have := shorProj_trace
  rw [h, Matrix.trace_zero] at this
  exact two_ne_zero this.symm

/-! ### The key combinatorial dichotomy -/

lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

/-- Among three distinct indices, at least one avoids both `i` and `j`. -/
lemma pick_three {α : Type*} [DecidableEq α] (i j a b c : α)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (a ≠ i ∧ a ≠ j) ∨ (b ≠ i ∧ b ≠ j) ∨ (c ≠ i ∧ c ≠ j) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  by_cases hai : a = i
  · have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
    have hci : c ≠ i := fun h => hac (hai.trans h.symm)
    exact hbc ((h2 hbi).trans (h3 hci).symm)
  · have haj := h1 hai
    by_cases hbi : b = i
    · have hci : c ≠ i := fun h => hbc (hbi.trans h.symm)
      exact hac (haj.trans (h3 hci).symm)
    · exact hab (haj.trans (h2 hbi).symm)

/-- The syndrome of the Pauli error `X^x Z^z` against the stabilizer element with
exponent vector `t`. -/
lemma syndrome_formula (t : Gen) (x z : Bits) :
    dot (zPart t) x + dot (xPart t) z =
      t 0 * (x 0 + x 1) + t 1 * (x 1 + x 2) + t 2 * (x 3 + x 4) + t 3 * (x 4 + x 5)
        + t 4 * (x 6 + x 7) + t 5 * (x 7 + x 8)
        + t 6 * (z 0 + z 1 + z 2 + z 3 + z 4 + z 5)
        + t 7 * (z 3 + z 4 + z 5 + z 6 + z 7 + z 8) := by
  simp [dot, Fin.sum_univ_succ, zPart, xPart]
  ring

/-- The exponent vector selecting the `k`-th stabilizer generator. -/
def genv (k : Fin 8) : Gen := fun m => if m = k then 1 else 0

/-- Any Pauli error supported on at most two qubits either anticommutes with some element of
the stabilizer group, or belongs to the stabilizer group. -/
lemma stab_dichotomy (i j : Fin 9) (x z : Bits)
    (hsupp : ∀ k, k ≠ i → k ≠ j → x k = 0 ∧ z k = 0) :
    (∃ t : Gen, dot (zPart t) x + dot (xPart t) z = 1) ∨
      (∃ t : Gen, x = xPart t ∧ z = zPart t) := by
  by_cases hall : ∃ t : Gen, dot (zPart t) x + dot (xPart t) z = 1
  · exact Or.inl hall
  right
  push_neg at hall
  have key : ∀ t : Gen, dot (zPart t) x + dot (xPart t) z = 0 := fun t =>
    (zmod_two_cases _).resolve_right (hall t)
  -- the eight generator equations
  have e0 : x 0 + x 1 = 0 := by
    have h := key (genv 0); rw [syndrome_formula] at h; simpa [genv] using h
  have e1 : x 1 + x 2 = 0 := by
    have h := key (genv 1); rw [syndrome_formula] at h; simpa [genv] using h
  have e2 : x 3 + x 4 = 0 := by
    have h := key (genv 2); rw [syndrome_formula] at h; simpa [genv] using h
  have e3 : x 4 + x 5 = 0 := by
    have h := key (genv 3); rw [syndrome_formula] at h; simpa [genv] using h
  have e4 : x 6 + x 7 = 0 := by
    have h := key (genv 4); rw [syndrome_formula] at h; simpa [genv] using h
  have e5 : x 7 + x 8 = 0 := by
    have h := key (genv 5); rw [syndrome_formula] at h; simpa [genv] using h
  have e6 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 0 := by
    have h := key (genv 6); rw [syndrome_formula] at h; simpa [genv] using h
  have e7 : z 3 + z 4 + z 5 + z 6 + z 7 + z 8 = 0 := by
    have h := key (genv 7); rw [syndrome_formula] at h; simpa [genv] using h
  -- the `X`-part vanishes: it is constant on each block of three qubits
  have x01 := zmod2_eq_of_add_eq_zero e0
  have x12 := zmod2_eq_of_add_eq_zero e1
  have x34 := zmod2_eq_of_add_eq_zero e2
  have x45 := zmod2_eq_of_add_eq_zero e3
  have x67 := zmod2_eq_of_add_eq_zero e4
  have x78 := zmod2_eq_of_add_eq_zero e5
  have hx0 : x 0 = 0 := by
    rcases pick_three i j (0 : Fin 9) 1 2 (by decide) (by decide) (by decide) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hsupp 0 h1 h2).1
    · rw [x01]; exact (hsupp 1 h1 h2).1
    · rw [x01, x12]; exact (hsupp 2 h1 h2).1
  have hx3 : x 3 = 0 := by
    rcases pick_three i j (3 : Fin 9) 4 5 (by decide) (by decide) (by decide) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hsupp 3 h1 h2).1
    · rw [x34]; exact (hsupp 4 h1 h2).1
    · rw [x34, x45]; exact (hsupp 5 h1 h2).1
  have hx6 : x 6 = 0 := by
    rcases pick_three i j (6 : Fin 9) 7 8 (by decide) (by decide) (by decide) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hsupp 6 h1 h2).1
    · rw [x67]; exact (hsupp 7 h1 h2).1
    · rw [x67, x78]; exact (hsupp 8 h1 h2).1
  -- the `Z`-part has even weight in each block of three qubits
  have hmem : ∀ k : Fin 9, z k ≠ 0 → ¬ (k ≠ i ∧ k ≠ j) := by
    intro k hk hc; exact hk (hsupp k hc.1 hc.2).2
  have hw0 : z 0 + z 1 + z 2 = 0 := by
    by_contra hne
    have h1 : z 0 + z 1 + z 2 = 1 := (zmod_two_cases _).resolve_left hne
    have h2 : z 3 + z 4 + z 5 = 1 := by
      have H : ∀ p q r s u v : ZMod 2, p + q + r + s + u + v = 0 → p + q + r = 1 →
          s + u + v = 1 := by decide
      exact H _ _ _ _ _ _ e6 h1
    have h3 : z 6 + z 7 + z 8 = 1 := by
      have H : ∀ p q r s u v : ZMod 2, p + q + r + s + u + v = 0 → p + q + r = 1 →
          s + u + v = 1 := by decide
      exact H _ _ _ _ _ _ e7 h2
    have nz : ∀ p q r : ZMod 2, p + q + r = 1 → p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0 := by decide
    obtain ⟨a, ha, hza⟩ : ∃ a : Fin 9, (a : ℕ) < 3 ∧ z a ≠ 0 := by
      rcases nz _ _ _ h1 with h | h | h
      exacts [⟨0, by norm_num, h⟩, ⟨1, by norm_num, h⟩, ⟨2, by norm_num, h⟩]
    obtain ⟨b, hb, hb2, hzb⟩ : ∃ b : Fin 9, 3 ≤ (b : ℕ) ∧ (b : ℕ) < 6 ∧ z b ≠ 0 := by
      rcases nz _ _ _ h2 with h | h | h
      exacts [⟨3, by norm_num, by norm_num, h⟩, ⟨4, by norm_num, by norm_num, h⟩,
        ⟨5, by norm_num, by norm_num, h⟩]
    obtain ⟨c, hc, hzc⟩ : ∃ c : Fin 9, 6 ≤ (c : ℕ) ∧ z c ≠ 0 := by
      rcases nz _ _ _ h3 with h | h | h
      exacts [⟨6, by norm_num, h⟩, ⟨7, by norm_num, h⟩, ⟨8, by norm_num, h⟩]
    have hab : a ≠ b := by intro h; rw [h] at ha; omega
    have hbc : b ≠ c := by intro h; rw [h] at hb2; omega
    have hac : a ≠ c := by intro h; rw [h] at ha; omega
    rcases pick_three i j a b c hab hbc hac with h | h | h
    exacts [hmem a hza h, hmem b hzb h, hmem c hzc h]
  have hw1 : z 3 + z 4 + z 5 = 0 := by
    have H : ∀ p q r s u v : ZMod 2, p + q + r + s + u + v = 0 → p + q + r = 0 →
        s + u + v = 0 := by decide
    exact H _ _ _ _ _ _ e6 hw0
  have hw2 : z 6 + z 7 + z 8 = 0 := by
    have H : ∀ p q r s u v : ZMod 2, p + q + r + s + u + v = 0 → p + q + r = 0 →
        s + u + v = 0 := by decide
    exact H _ _ _ _ _ _ e7 hw1
  -- build the stabilizer element
  refine ⟨fun m => if m = 0 then z 0 else if m = 1 then z 2 else if m = 2 then z 3
    else if m = 3 then z 5 else if m = 4 then z 6 else if m = 5 then z 8 else 0, ?_, ?_⟩
  · have hx1 : x 1 = 0 := by rw [← x01]; exact hx0
    have hx2 : x 2 = 0 := by rw [← x12, ← x01]; exact hx0
    have hx4 : x 4 = 0 := by rw [← x34]; exact hx3
    have hx5 : x 5 = 0 := by rw [← x45, ← x34]; exact hx3
    have hx7 : x 7 = 0 := by rw [← x67]; exact hx6
    have hx8 : x 8 = 0 := by rw [← x78, ← x67]; exact hx6
    ext k
    fin_cases k <;> simp [xPart] <;>
      first
        | exact hx0 | exact hx1 | exact hx2 | exact hx3 | exact hx4
        | exact hx5 | exact hx6 | exact hx7 | exact hx8
  · have hz1 : z 0 + z 2 = z 1 := by
      have H : ∀ a b c : ZMod 2, a + b + c = 0 → a + c = b := by decide
      exact H _ _ _ hw0
    have hz4 : z 3 + z 5 = z 4 := by
      have H : ∀ a b c : ZMod 2, a + b + c = 0 → a + c = b := by decide
      exact H _ _ _ hw1
    have hz7 : z 6 + z 8 = z 7 := by
      have H : ∀ a b c : ZMod 2, a + b + c = 0 → a + c = b := by decide
      exact H _ _ _ hw2
    ext k
    fin_cases k <;> simp [zPart] <;> first | exact hz1.symm | exact hz4.symm | exact hz7.symm

/-! ### The Knill–Laflamme condition -/

lemma sgn_of_add_eq_one (a b : ZMod 2) (h : a + b = 1) : sgn b = - sgn a := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    first
      | (exfalso; revert h; decide)
      | norm_num [sgn]

lemma pauli_anticomm (x z : Bits) (t : Gen)
    (h : dot (zPart t) x + dot (xPart t) z = 1) :
    pauli x z * shorStab t = - (shorStab t * pauli x z) := by
  rw [shorStab, pauli_mul, pauli_mul, ← neg_smul, add_comm (xPart t) x, add_comm (zPart t) z]
  congr 1
  rw [dot_comm z (xPart t)]
  exact sgn_of_add_eq_one _ _ h

lemma sandwich_anticomm (x z : Bits) (t : Gen)
    (h : dot (zPart t) x + dot (xPart t) z = 1) :
    shorProj * pauli x z * shorProj = 0 := by
  have key : shorProj * pauli x z * shorProj = -(shorProj * pauli x z * shorProj) :=
    calc shorProj * pauli x z * shorProj
        = shorProj * pauli x z * (shorStab t * shorProj) := by rw [shorStab_mul_proj]
      _ = shorProj * (pauli x z * shorStab t) * shorProj := by noncomm_ring
      _ = shorProj * (-(shorStab t * pauli x z)) * shorProj := by rw [pauli_anticomm x z t h]
      _ = -(shorProj * shorStab t * pauli x z * shorProj) := by noncomm_ring
      _ = -(shorProj * pauli x z * shorProj) := by rw [proj_mul_shorStab]
  have h2 : (2 : ℂ) • (shorProj * pauli x z * shorProj) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [key]
    simp
  simpa using h2

lemma sandwich_pauli (i j : Fin 9) (x z : Bits)
    (hsupp : ∀ k, k ≠ i → k ≠ j → x k = 0 ∧ z k = 0) :
    ∃ c : ℂ, shorProj * pauli x z * shorProj = c • shorProj := by
  rcases stab_dichotomy i j x z hsupp with ⟨t, ht⟩ | ⟨t, hx, hz⟩
  · exact ⟨0, by rw [sandwich_anticomm x z t ht, zero_smul]⟩
  · refine ⟨1, ?_⟩
    have : pauli x z = shorStab t := by rw [hx, hz, shorStab]
    rw [this, proj_mul_shorStab, shorProj_idem, one_smul]

lemma eq_add_unit_iff (u v : Bits) (i : Fin 9) :
    u = v + unit i ↔ ((∀ k, k ≠ i → u k = v k) ∧ u i = v i + 1) := by
  constructor
  · rintro rfl
    exact ⟨fun k hk => by simp [unit, hk], by simp [unit]⟩
  · rintro ⟨h1, h2⟩
    ext k
    rcases eq_or_ne k i with rfl | hk
    · simpa [unit] using h2
    · simp [unit, hk, h1 k hk]

lemma onQubit_decomp (i : Fin 9) (M : Matrix (ZMod 2) (ZMod 2) ℂ) :
    onQubit i M =
      ((M 0 0 + M 1 1) / 2) • pauli 0 0
        + ((M 0 1 + M 1 0) / 2) • pauli (unit i) 0
        + ((M 0 0 - M 1 1) / 2) • pauli 0 (unit i)
        + ((M 1 0 - M 0 1) / 2) • pauli (unit i) (unit i) := by
  ext u v
  simp only [Matrix.add_apply, Matrix.smul_apply, pauli_apply, onQubit_apply, smul_eq_mul,
    add_zero, dot_zero_left, dot_unit_left, sgn_zero]
  by_cases h : ∀ k, k ≠ i → u k = v k
  · simp only [if_pos h]
    rcases eq_or_ne (u i) (v i) with h2 | h2
    · have huv : u = v := by
        ext k; rcases eq_or_ne k i with rfl | hk
        · exact h2
        · exact h k hk
      have hne : ¬ (u = v + unit i) := by
        rw [eq_add_unit_iff]
        rintro ⟨-, hh⟩
        rw [h2] at hh
        exact (by decide : ∀ a : ZMod 2, ¬ (a = a + 1)) (v i) hh
      simp only [if_pos huv, if_neg hne]
      rcases zmod_two_cases (v i) with hv | hv <;> rw [h2, hv] <;> norm_num [sgn] <;> ring
    · have hui : u i = v i + 1 := by
        rcases zmod_two_cases (u i) with h3 | h3 <;> rcases zmod_two_cases (v i) with h4 | h4
        · exact absurd (h3.trans h4.symm) h2
        · rw [h3, h4]; decide
        · rw [h3, h4]; decide
        · exact absurd (h3.trans h4.symm) h2
      have hyes : u = v + unit i := (eq_add_unit_iff u v i).2 ⟨h, hui⟩
      have hno : ¬ (u = v) := fun hh => h2 (by rw [hh])
      simp only [if_neg hno, if_pos hyes]
      rcases zmod_two_cases (v i) with hv | hv <;>
        simp only [hui, hv, show (0 : ZMod 2) + 1 = 1 from by decide,
          show (1 : ZMod 2) + 1 = 0 from by decide] <;>
        norm_num [sgn] <;> ring
  · have h1 : ¬ (u = v) := fun hh => h (fun k _ => by rw [hh])
    have h2 : ¬ (u = v + unit i) := fun hh => h ((eq_add_unit_iff u v i).1 hh).1
    simp only [if_neg h, if_neg h1, if_neg h2]
    ring

lemma onQubit_conjTranspose (i : Fin 9) (M : Matrix (ZMod 2) (ZMod 2) ℂ) :
    (onQubit i M)ᴴ = onQubit i Mᴴ := by
  ext u v
  rw [Matrix.conjTranspose_apply, onQubit_apply, onQubit_apply]
  by_cases h : ∀ k, k ≠ i → u k = v k
  · have h' : ∀ k, k ≠ i → v k = u k := fun k hk => (h k hk).symm
    rw [if_pos h, if_pos h']
    rfl
  · have h' : ¬ ∀ k, k ≠ i → v k = u k := fun hh => h (fun k hk => (hh k hk).symm)
    rw [if_neg h, if_neg h']
    simp

/-- The linear map `A ↦ P A P`. -/
noncomputable def sandwichMap : Matrix Bits Bits ℂ →ₗ[ℂ] Matrix Bits Bits ℂ where
  toFun A := shorProj * A * shorProj
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] lemma sandwichMap_apply (A : Matrix Bits Bits ℂ) :
    sandwichMap A = shorProj * A * shorProj := rfl

/-- The `ℂ`-subspace of operators `A` with `P A P ∈ ℂ ∙ P`. -/
noncomputable def corrSub : Submodule ℂ (Matrix Bits Bits ℂ) :=
  (Submodule.span ℂ {shorProj}).comap sandwichMap

lemma pauli_pair_mem (i j : Fin 9) (x₁ z₁ x₂ z₂ : Bits)
    (h₁ : ∀ k, k ≠ i → x₁ k = 0 ∧ z₁ k = 0)
    (h₂ : ∀ k, k ≠ j → x₂ k = 0 ∧ z₂ k = 0) :
    pauli x₁ z₁ * pauli x₂ z₂ ∈ corrSub := by
  have hsupp : ∀ k, k ≠ i → k ≠ j → (x₁ + x₂) k = 0 ∧ (z₁ + z₂) k = 0 := by
    intro k hki hkj
    have a := h₁ k hki
    have b := h₂ k hkj
    simp [a.1, a.2, b.1, b.2]
  obtain ⟨c, hc⟩ := sandwich_pauli i j (x₁ + x₂) (z₁ + z₂) hsupp
  refine Submodule.mem_comap.mpr ?_
  rw [sandwichMap_apply, pauli_mul, Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩

lemma onQubit_mem_span (i j : Fin 9) (E F : Matrix (ZMod 2) (ZMod 2) ℂ) :
    onQubit i E * onQubit j F ∈ corrSub := by
  rw [onQubit_decomp i E, onQubit_decomp j F]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  repeat' refine Submodule.add_mem _ ?_ ?_
  all_goals
    refine Submodule.smul_mem _ _ ?_
    exact pauli_pair_mem i j _ _ _ _ (by intro k hk; simp [unit, hk])
      (by intro k hk; simp [unit, hk])

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

`shorProj` is the projector onto the code space, which is two-dimensional
(`QI.shorProj_trace`, together with `QI.shorProj_idem` and `QI.shorProj_conjTranspose`).
For arbitrary single-qubit operators `E` acting on qubit `i` and `F` acting on qubit `j`,
the Knill–Laflamme condition `P Eᴴ F P = c • P` holds; by the Knill–Laflamme theorem this is
exactly the statement that the code corrects an arbitrary error supported on a single qubit. -/
theorem shor_code_corrects (i j : Fin 9) (E F : Matrix (ZMod 2) (ZMod 2) ℂ) :
    ∃ c : ℂ, shorProj * (onQubit i E)ᴴ * (onQubit j F) * shorProj = c • shorProj := by
  have h := onQubit_mem_span i j Eᴴ F
  rw [corrSub, Submodule.mem_comap, sandwichMap_apply, Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [onQubit_conjTranspose, mul_assoc shorProj (onQubit i Eᴴ) (onQubit j F), ← hc]

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

