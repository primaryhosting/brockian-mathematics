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

