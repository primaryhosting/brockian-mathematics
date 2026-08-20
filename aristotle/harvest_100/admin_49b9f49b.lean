import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to precede all other commands, including module docstrings.)
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

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

@[simp] lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma one_le_rad (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  exact_mod_cast rad_pos n

/-- The set of `abc`-exceptions for a given `ε`: triples `(a, b, c)` of positive integers with
`a` and `b` coprime, `a + b = c`, and `c > rad (a * b * c) ^ (1 + ε)`. -/
def ABCExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
    ((rad (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 + ε) < (t.2.2 : ℝ))}

/-- **The abc conjecture** (finiteness form): for every `ε > 0` there are only finitely many
coprime triples `a + b = c` of positive integers with `c > rad (a * b * c) ^ (1 + ε)`. -/
def ABCFinitenessForm : Prop := ∀ ε : ℝ, 0 < ε → (ABCExceptions ε).Finite

/-- **The abc conjecture** (constant form): for every `ε > 0` there is a constant `K` with
`c ≤ K * rad (a * b * c) ^ (1 + ε)` for all coprime triples `a + b = c` of positive integers. -/
def ABCConstantForm : Prop := ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ,
  0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- The exceptional sets are antitone in `ε`. -/
lemma ABCExceptions_subset {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    ABCExceptions ε₂ ⊆ ABCExceptions ε₁ := by
  rintro ⟨a, b, c⟩ ⟨ha, hb, hab, habc, hlt⟩
  refine ⟨ha, hb, hab, habc, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le (one_le_rad _) (by linarith)

/-- It suffices to prove the abc conjecture for arbitrarily small `ε`. -/
lemma ABCFinitenessForm_of_small {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ ε : ℝ, 0 < ε → ε < δ → (ABCExceptions ε).Finite) : ABCFinitenessForm := by
  intro ε hε
  rcases lt_or_ge ε (δ / 2) with hlt | hge
  · exact h ε hε (by linarith)
  · exact (h (δ / 2) (by linarith) (by linarith)).subset (ABCExceptions_subset hge)

/-- Any set of triples whose last coordinate is bounded, and whose first two coordinates sum
to the last, is finite. -/
lemma finite_of_bounded (M : ℕ) :
    {t : ℕ × ℕ × ℕ | t.1 + t.2.1 = t.2.2 ∧ t.2.2 ≤ M}.Finite := by
  apply Set.Finite.subset
    (Finset.finite_toSet ((Finset.range (M + 1)) ×ˢ (Finset.range (M + 1)) ×ˢ
      (Finset.range (M + 1))))
  rintro ⟨a, b, c⟩ ⟨hsum, hle⟩
  dsimp only at hsum hle
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
  refine ⟨by omega, by omega, by omega⟩

/-- `rad 72 = 6`. -/
lemma rad_72 : rad 72 = 6 := by
  have h : (72 : ℕ).primeFactors = {2, 3} := by decide +kernel
  simp [rad, h]

/-- A concrete `abc`-exception, showing the exceptional sets are not vacuously empty:
`1 + 8 = 9` with `rad (1 * 8 * 9) = 6` and `6 ^ (6/5) < 9`. -/
lemma mem_ABCExceptions_one_eight_nine :
    ((1, 8, 9) : ℕ × ℕ × ℕ) ∈ ABCExceptions (1 / 5) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have hrad : rad (1 * 8 * 9) = 6 := by norm_num [rad_72]
  rw [hrad]
  have h65 : (1 : ℝ) + 1 / 5 = (6 : ℝ) / 5 := by norm_num
  rw [h65]
  have h5 : ((6 : ℝ) ^ ((6 : ℝ) / 5)) ^ (5 : ℕ) = 6 ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast ((6 : ℝ) ^ ((6 : ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hcon
  push_neg at hcon
  have h : ((9 : ℕ) : ℝ) ^ (5 : ℕ) ≤ ((6 : ℝ) ^ ((6 : ℝ) / 5)) ^ (5 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hcon 5
  rw [h5] at h
  norm_num at h

/-- For every `ε ≤ 1/5` there is at least one `abc`-exception. -/
lemma ABCExceptions_nonempty {ε : ℝ} (hε : ε ≤ 1 / 5) : (ABCExceptions ε).Nonempty :=
  ⟨(1, 8, 9), ABCExceptions_subset hε mem_ABCExceptions_one_eight_nine⟩

/-- **The abc conjecture, stated in Lean, together with a checked reduction**: the finiteness
form of the conjecture is equivalent to the constant form.

Neither side is known (the abc conjecture is open); what is proved here is the equivalence of
the two standard formulations. Note that the constant form for `ε` follows from the finiteness
form for the *same* `ε`, while the converse uses the constant form for `ε/2`. -/
theorem abc_statement : ABCFinitenessForm ↔ ABCConstantForm := by
  constructor
  · -- finiteness ⟹ constant form
    intro hfin ε hε
    obtain ⟨B, hB⟩ :=
      ((hfin ε hε).image (fun t : ℕ × ℕ × ℕ => (t.2.2 : ℝ))).bddAbove
    refine ⟨max 1 B, ?_⟩
    intro a b c ha hb hab habc
    have hR : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := one_le_rad _
    have hRpow : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) :=
      Real.one_le_rpow hR (by linarith)
    have hK1 : (1 : ℝ) ≤ max 1 B := le_max_left _ _
    by_cases hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ ABCExceptions ε
    · have hcB : (c : ℝ) ≤ B := hB ⟨(a, b, c), hmem, rfl⟩
      calc (c : ℝ) ≤ max 1 B := le_trans hcB (le_max_right _ _)
        _ = max 1 B * 1 := by ring
        _ ≤ max 1 B * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
            exact mul_le_mul_of_nonneg_left hRpow (by linarith)
    · have hnot : ¬ ((rad (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ)) := by
        intro hlt
        exact hmem ⟨ha, hb, hab, habc, hlt⟩
      calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := not_lt.mp hnot
        _ = 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by ring
        _ ≤ max 1 B * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
            exact mul_le_mul_of_nonneg_right hK1 (by linarith)
  · -- constant form ⟹ finiteness
    intro hconst ε hε
    obtain ⟨K₀, hK₀⟩ := hconst (ε / 2) (by linarith)
    set K : ℝ := max 1 K₀ with hKdef
    have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
    have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
    have hK : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
      intro a b c ha hb hab habc
      refine le_trans (hK₀ a b c ha hb hab habc) ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (by positivity) _)
    -- a uniform bound on `c` for exceptions
    set M : ℝ := K * (K ^ (2 / ε)) ^ (1 + ε / 2) with hMdef
    have hbound : ∀ t ∈ ABCExceptions ε, (t.2.2 : ℝ) ≤ M := by
      rintro ⟨a, b, c⟩ ⟨ha, hb, hab, habc, hlt⟩
      set R : ℝ := (rad (a * b * c) : ℝ) with hRdef
      have hR1 : (1 : ℝ) ≤ R := one_le_rad _
      have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
      have hle : (c : ℝ) ≤ K * R ^ (1 + ε / 2) := hK a b c ha hb hab habc
      have hsplit : R ^ (1 + ε) = R ^ (1 + ε / 2) * R ^ (ε / 2) := by
        rw [← Real.rpow_add hR0]
        ring_nf
      have hpos : (0 : ℝ) < R ^ (1 + ε / 2) := Real.rpow_pos_of_pos hR0 _
      have hstep : R ^ (1 + ε / 2) * R ^ (ε / 2) < K * R ^ (1 + ε / 2) := by
        rw [← hsplit]
        exact lt_of_lt_of_le hlt hle
      have hKlt : R ^ (ε / 2) < K := by
        have := hstep
        rw [mul_comm (R ^ (1 + ε / 2)) (R ^ (ε / 2))] at this
        exact lt_of_mul_lt_mul_right (by linarith [this]) (le_of_lt hpos)
      have hRle : R ≤ K ^ (2 / ε) := by
        have h1 : (R ^ (ε / 2)) ^ (2 / ε) ≤ K ^ (2 / ε) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hR0) _) (le_of_lt hKlt)
            (by positivity)
        have h2 : (R ^ (ε / 2)) ^ (2 / ε) = R := by
          rw [← Real.rpow_mul (le_of_lt hR0)]
          rw [show ε / 2 * (2 / ε) = 1 by field_simp]
          exact Real.rpow_one R
        rwa [h2] at h1
      calc (c : ℝ) ≤ K * R ^ (1 + ε / 2) := hle
        _ ≤ K * (K ^ (2 / ε)) ^ (1 + ε / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hK0)
            exact Real.rpow_le_rpow (le_of_lt hR0) hRle (by linarith)
    refine (finite_of_bounded ⌈M⌉₊).subset ?_
    rintro ⟨a, b, c⟩ ht
    obtain ⟨ha, hb, hab, habc, hlt⟩ := ht
    refine ⟨habc, ?_⟩
    have : (c : ℝ) ≤ M := hbound (a, b, c) ⟨ha, hb, hab, habc, hlt⟩
    calc c = ⌈(c : ℝ)⌉₊ := by simp
      _ ≤ ⌈M⌉₊ := Nat.ceil_le_ceil this

end Frontier

