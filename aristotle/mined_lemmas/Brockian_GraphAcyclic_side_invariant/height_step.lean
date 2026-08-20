import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

lemma height_step (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    ∀ ⦃x y : {a : ZMod M | twinAdm a}⦄,
      (SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)).Adj x y →
      height M y = height M x + 1 ∨ height M y = height M x - 1 := by
  intro x y hadj
  -- Extract the adjacency condition from plusThreeGraph
  simp only [SimpleGraph.induce] at hadj
  simp only [plusThreeGraph] at hadj
  obtain ⟨hdiff, _⟩ := hadj
  -- hdiff : y - x = 3 ∨ x - y = 3
  -- First, establish that 3 * 3⁻¹ = 1 in ZMod M
  have h3inv : (3 : ZMod M) * (3 : ZMod M)⁻¹ = 1 := three_mul_inv h3
  obtain h | h := hdiff
  · -- Case: y = x + 3
    -- Then y * 3⁻¹ = x * 3⁻¹ + 1
    left
    -- From h : y - x = 3, we get y = x + 3
    -- The subtype coercion preserves subtraction
    have hdiff' : (y : ZMod M) - (x : ZMod M) = 3 := by
      simpa using h
    have hy : (y : ZMod M) = (x : ZMod M) + 3 := by
      have := hdiff'; rw [sub_eq_iff_eq_add] at this; rw [add_comm] at this; exact this
    -- So y * 3⁻¹ = x * 3⁻¹ + 1
    have hprod : (y : ZMod M) * (3 : ZMod M)⁻¹ = (x : ZMod M) * (3 : ZMod M)⁻¹ + 1 := by
      rw [hy]; ring_nf
      rw [mul_comm ((3 : ZMod M)⁻¹) 3]; rw [h3inv]; ring
    -- Since y is twin-admissible, y is a unit, so y ≠ 0
    haveI : NeZero M := ‹_›
    haveI : Fact (1 < M) := ⟨hM⟩
    haveI : Nontrivial (ZMod M) := ZMod.nontrivial M
    have hy_unit : IsUnit (y : ZMod M) := y.2.1
    have hy_ne_zero : (y : ZMod M) ≠ 0 := hy_unit.ne_zero
    -- If (x * 3⁻¹).val = M - 1, then x * 3⁻¹ + 1 = 0, so y * 3⁻¹ = 0, so y = 0
    -- This contradicts y ≠ 0. So (x * 3⁻¹).val < M - 1
    have hval_lt : ((x : ZMod M) * (3 : ZMod M)⁻¹).val < M - 1 := by
      by_contra h_contra
      push_neg at h_contra
      -- Since val is in [0, M-1], we have (x * 3⁻¹).val = M - 1
      have hval_eq : ((x : ZMod M) * (3 : ZMod M)⁻¹).val = M - 1 := by
        have h1 : ((x : ZMod M) * (3 : ZMod M)⁻¹).val < M := ZMod.val_lt _
        omega
      -- In ZMod M, x * 3⁻¹ = M - 1 = -1
      have hx3inv_eq_neg1 : (x : ZMod M) * (3 : ZMod M)⁻¹ = -1 := by
        have h1 : ((M - 1 : ℕ) : ZMod M) = -1 := by
          have h2 : ((M - 1 : ℕ) : ZMod M) + 1 = 0 := by simp [Nat.cast_sub (by omega : 1 ≤ M)]
          exact eq_neg_of_add_eq_zero_left h2
        rw [← h1, ← hval_eq]
        rw [ZMod.natCast_val, ZMod.cast_id]
      -- So y * 3⁻¹ = -1 + 1 = 0
      have hy3inv_eq_zero : (y : ZMod M) * (3 : ZMod M)⁻¹ = 0 := by
        rw [hprod, hx3inv_eq_neg1]; ring
      -- Since 3⁻¹ is a unit, y = 0
      have hy_eq_zero : (y : ZMod M) = 0 := by
        have h3_ne_zero : (3 : ZMod M) ≠ 0 := by
          intro h3eq0
          rw [h3eq0] at h3inv
          simp at h3inv
        have h3inv_ne_zero : (3 : ZMod M)⁻¹ ≠ 0 := by
          intro h3inv_eq0
          rw [h3inv_eq0] at h3inv
          simp at h3inv
        by_cases hy : (y : ZMod M) = 0
        · exact hy
        · exfalso
          have h1 : (y : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 0 := by rw [hy3inv_eq_zero]; ring
          rw [mul_assoc] at h1
          rw [mul_comm (3 : ZMod M)⁻¹ 3, h3inv] at h1
          simp at h1
          exact hy h1
      exact hy_ne_zero hy_eq_zero
    -- Now use hval_lt to show the val equality
    have hval_eq' : ((y : ZMod M) * (3 : ZMod M)⁻¹).val = ((x : ZMod M) * (3 : ZMod M)⁻¹).val + 1 := by
      rw [hprod]
      have hv : ((x : ZMod M) * (3 : ZMod M)⁻¹).val < M := ZMod.val_lt _
      have hv' : ((x : ZMod M) * (3 : ZMod M)⁻¹).val + 1 < M := by omega
      have hne : (y : ZMod M) * (3 : ZMod M)⁻¹ ≠ 0 := by
        intro heq
        apply hy_ne_zero
        -- if y * 3⁻¹ = 0 and 3⁻¹ ≠ 0, then y = 0
        have h3inv_ne : (3 : ZMod M)⁻¹ ≠ 0 := by
          intro h
          rw [h] at h3inv
          simp at h3inv
        -- Multiply both sides by 3: y * 3⁻¹ * 3 = 0 * 3 = 0
        have : (y : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 0 := by rw [heq]; ring
        rw [mul_assoc, mul_comm (3 : ZMod M)⁻¹ 3, h3inv, mul_one] at this
        exact this
      have hval_eq' := val_succ_of_ne_zero hprod hne
      norm_cast at hval_eq'
      rw [hprod] at hval_eq'
      exact hval_eq'
    simp [height, hval_eq']
  · -- Case: x = y + 3
    -- Then x * 3⁻¹ = y * 3⁻¹ + 1, so y * 3⁻¹ = x * 3⁻¹ - 1
    right
    haveI : NeZero M := ‹_›
    haveI : Fact (1 < M) := ⟨hM⟩
    haveI : Nontrivial (ZMod M) := ZMod.nontrivial M
    -- From h : x - y = 3, we get x = y + 3
    have hdiff' : (x : ZMod M) - (y : ZMod M) = 3 := by simpa using h
    have hx : (x : ZMod M) = (y : ZMod M) + 3 := by
      have := hdiff'; rw [sub_eq_iff_eq_add] at this; rw [add_comm] at this; exact this
    -- So x * 3⁻¹ = y * 3⁻¹ + 1
    have hprod : (x : ZMod M) * (3 : ZMod M)⁻¹ = (y : ZMod M) * (3 : ZMod M)⁻¹ + 1 := by
      rw [hx]; ring_nf
      rw [mul_comm ((3 : ZMod M)⁻¹) 3]; rw [h3inv]; ring
    -- x is a unit, so x ≠ 0, so x * 3⁻¹ ≠ 0
    have hx_unit : IsUnit (x : ZMod M) := x.2.1
    have hx_ne_zero : (x : ZMod M) ≠ 0 := hx_unit.ne_zero
    -- So (x * 3⁻¹).val ≥ 1
    have hx3inv_ne : (x : ZMod M) * (3 : ZMod M)⁻¹ ≠ 0 := by
      intro heq
      have h3inv_ne : (3 : ZMod M)⁻¹ ≠ 0 := by
        intro h
        rw [h] at h3inv
        simp at h3inv
      have : (x : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 0 := by rw [heq]; ring
      rw [mul_assoc, mul_comm (3 : ZMod M)⁻¹ 3, h3inv, mul_one] at this
      exact hx_ne_zero this
    have hx3inv_val_pos : ((x : ZMod M) * (3 : ZMod M)⁻¹).val ≥ 1 := by
      by_contra h_neg
      have h0 : ((x : ZMod M) * (3 : ZMod M)⁻¹).val = 0 := by omega
      simp [ZMod.val_eq_zero] at h0
      exact hx3inv_ne h0
    -- Now show (y * 3⁻¹).val = (x * 3⁻¹).val - 1
    have hval_eq' : ((y : ZMod M) * (3 : ZMod M)⁻¹).val = ((x : ZMod M) * (3 : ZMod M)⁻¹).val - 1 := by
      have heq : (y : ZMod M) * (3 : ZMod M)⁻¹ = (x : ZMod M) * (3 : ZMod M)⁻¹ - 1 := by
        rw [hprod]; ring
      rw [heq]
      -- We'll show (x * 3⁻¹ - 1).val = (x * 3⁻¹).val - 1
      -- First show x * 3⁻¹ - 1 ≠ 0
      have hne : (x : ZMod M) * (3 : ZMod M)⁻¹ - 1 ≠ 0 := by
        intro hsub
        have hx3eq1 : (x : ZMod M) * (3 : ZMod M)⁻¹ = 1 := by linear_combination hsub
        -- From x * 3⁻¹ = 1, we get x = 3
        have hx_eq_3 : (x : ZMod M) = 3 := by
          have : (x : ZMod M) * (3 : ZMod M)⁻¹ * 3 = 1 * 3 := by rw [hx3eq1]
          rw [mul_assoc, mul_comm (3 : ZMod M)⁻¹ 3, h3inv, mul_one, one_mul] at this
          exact this
        -- Since x = y + 3 and x = 3, we get y = 0
        have hy_eq_0 : (y : ZMod M) = 0 := by simpa [hx_eq_3] using hx
        -- But y is twin-admissible, so y is a unit, so y ≠ 0
        exact y.2.1.ne_zero hy_eq_0
      -- Now use that (a - 1).val = a.val - 1 when a ≠ 0 and a - 1 ≠ 0
      set a := (x : ZMod M) * (3 : ZMod M)⁻¹ with ha_def
      have ha_ne : a ≠ 0 := hx3inv_ne
      have ha_eq_b1 : a = (a - 1) + 1 := by ring
      have hab : (a.val : ℤ) = ((a - 1).val : ℤ) + 1 :=
        val_succ_of_ne_zero ha_eq_b1 ha_ne
      omega
    show (((y : ZMod M) * (3 : ZMod M)⁻¹).val : ℤ) = (((x : ZMod M) * (3 : ZMod M)⁻¹).val : ℤ) - 1
    rw [hval_eq', Int.ofNat_sub hx3inv_val_pos]; rfl

end Arith

/-- Gate sub-brick 2 (the hard SimpleGraph step): for a modulus M coprime to 3, the induced
subgraph of the +3 flow on the twin-admissible residues is ACYCLIC. Intuition: when gcd(3,M)=1
the +3 map is a single M-cycle over all of ℤ/M; the residue 0 is never twin-admissible (0 is not
a unit for M>1), so the admissible vertex set is a PROPER subset — deleting ≥1 vertex from a cycle
leaves a disjoint union of paths, which has no cycle. (Arithmetic facts available to reproduce:
`a + 3*(k:ZMod M) = a → M ∣ k` for a unit 3, and 0 is not a unit in a nontrivial ZMod M.) -/
