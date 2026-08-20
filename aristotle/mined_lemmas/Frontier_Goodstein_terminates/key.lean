/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring command, so the header above is
-- kept verbatim as a plain block comment.)

import Mathlib

namespace Frontier

open Ordinal

/-- Syntax trees for hereditary base-`b` representations:
`oadd e c r` denotes `b ^ (value of e) * c + (value of r)`. -/
inductive HB where
  | zero : HB
  | oadd : HB → ℕ → HB → HB
deriving DecidableEq

namespace HB

/-- Size of a tree, used as a termination measure. -/

lemma key {b : ℕ} (hb : 2 ≤ b) {x : Ordinal} (hx : (b : Ordinal) ≤ x) (N : ℕ) :
    (∀ t u : HB, t.size + u.size ≤ N → WF b t → WF b u →
        (evalN b t < evalN b u → evalO x t < evalO x u) ∧
        (evalN b t = evalN b u → evalO x t = evalO x u))
      ∧ (∀ t E : HB, t.size + E.size ≤ N → WF b t → WF b E → evalN b t < b ^ evalN b E →
        evalO x t < x ^ evalO x E) := by
  have hx0 : (0 : Ordinal) < x :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < b)) hx
  induction N with
  | zero =>
    constructor
    · intro t u hN _ _
      have h1 : t = .zero := size_eq_zero (by omega)
      have h2 : u = .zero := size_eq_zero (by omega)
      subst h1; subst h2
      exact ⟨by simp [evalN], fun _ => rfl⟩
    · intro t E hN _ _ _
      have h1 : t = .zero := size_eq_zero (by omega)
      subst h1
      simpa [evalO] using opow_pos (evalO x E) hx0
  | succ N ih =>
    constructor
    · rintro (_ | ⟨e, c, r⟩) (_ | ⟨f, d, s⟩) hN ht hu
      · exact ⟨by simp [evalN], fun _ => rfl⟩
      · refine ⟨fun _ => ?_, fun h => ?_⟩
        · simpa [evalO] using evalO_pos hx0 hu (by simp)
        · exact absurd h.symm (evalN_pos (by omega) hu (by simp)).ne'
      · refine ⟨fun h => ?_, fun h => ?_⟩
        · exact absurd h (Nat.not_lt_zero _)
        · exact absurd h (evalN_pos (by omega) ht (by simp)).ne'
      · cases ht with
        | oadd he hr hc hcb hlt =>
        cases hu with
        | oadd hf hs hd hdb hlts =>
        simp only [size] at hN
        have m_ef : e.size + f.size ≤ N := by omega
        have m_rs : r.size + s.size ≤ N := by omega
        have m_rf : r.size + f.size ≤ N := by omega
        have m_tf : (HB.oadd e c r).size + f.size ≤ N := by simp only [size]; omega
        have ht : WF b (HB.oadd e c r) := WF.oadd he hr hc hcb hlt
        have hu : WF b (HB.oadd f d s) := WF.oadd hf hs hd hdb hlts
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases lt_trichotomy (evalN b e) (evalN b f) with hef | hef | hef
          · have hb2 : evalN b (HB.oadd e c r) < b ^ evalN b f :=
              lt_of_lt_of_le (evalN_lt_pow_succ ht) (Nat.pow_le_pow_right (by omega) (by omega))
            have h1 : evalO x (HB.oadd e c r) < x ^ evalO x f := ih.2 _ _ m_tf ht hf hb2
            refine lt_of_lt_of_le h1 ?_
            calc x ^ evalO x f = x ^ evalO x f * 1 := (mul_one _).symm
              _ ≤ x ^ evalO x f * (d : Ordinal) := by
                  refine mul_le_mul_right ?_ _
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
              _ ≤ evalO x (HB.oadd f d s) := by
                  simp only [evalO]
                  exact le_self_add
          · have hEF : evalO x e = evalO x f := (ih.1 e f m_ef he hf).2 hef
            simp only [evalN] at h
            rw [hef] at h hlt
            rcases nat_digit_lt hlts h with hcd | ⟨hcd, hrs⟩
            · have h2 : evalO x r < x ^ evalO x f := ih.2 r f m_rf hr hf hlt
              simp only [evalO]
              rw [hEF]
              exact ord_lt_of_digit_lt hcd h2
            · subst hcd
              simp only [evalO]
              rw [hEF]
              exact add_lt_add_right ((ih.1 r s m_rs hr hs).1 hrs) _
          · exact absurd h (asymm (evalN_lt_of_exp_lt (by omega) hu ht hef))
        · have hef : evalN b e = evalN b f := by
            rcases lt_trichotomy (evalN b e) (evalN b f) with h1 | h1 | h1
            · exact absurd h (ne_of_lt (evalN_lt_of_exp_lt (by omega) ht hu h1))
            · exact h1
            · exact absurd h.symm (ne_of_lt (evalN_lt_of_exp_lt (by omega) hu ht h1))
          have hEF : evalO x e = evalO x f := (ih.1 e f m_ef he hf).2 hef
          simp only [evalN] at h
          rw [hef] at h hlt
          obtain ⟨hcd, hrs⟩ := nat_digit_eq hlt hlts h
          have hRS : evalO x r = evalO x s := (ih.1 r s m_rs hr hs).2 hrs
          simp only [evalO]
          rw [hEF, hcd, hRS]
    · rintro (_ | ⟨e, c, r⟩) E hN ht hE h
      · simpa [evalO] using opow_pos (evalO x E) hx0
      · cases ht with
        | oadd he hr hc hcb hlt =>
        simp only [size] at hN
        have m_eE : e.size + E.size ≤ N := by omega
        have m_re : r.size + e.size ≤ N := by omega
        have hle : b ^ evalN b e ≤ evalN b (HB.oadd e c r) := by
          have h1 : b ^ evalN b e * 1 ≤ b ^ evalN b e * c := Nat.mul_le_mul_left _ hc
          simp only [evalN]
          omega
        have hexp : evalN b e < evalN b E :=
          (Nat.pow_lt_pow_iff_right (by omega : 1 < b)).mp (lt_of_le_of_lt hle h)
        have h1 : evalO x e < evalO x E := (ih.1 e E m_eE he hE).1 hexp
        have h2 : evalO x r < x ^ evalO x e := ih.2 r e m_re hr he hlt
        have h3 : evalO x (HB.oadd e c r) < x ^ (evalO x e + 1) := by
          simp only [evalO]
          exact ord_term_lt (lt_of_lt_of_le (by exact_mod_cast hcb) hx) h2
        exact lt_of_lt_of_le h3 (opow_le_opow_right hx0 (Order.add_one_le_iff.mpr h1))

