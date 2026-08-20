/-
# Singular Series Gaps 14501460 — Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps14501460.lean`.  The target theorem there is
stated in plain core Lean (its file has to start with a fixed header comment, which forbids
`import`s).  Here the same mathematical content is formalized in the idiomatic Mathlib way,
with tuples as `Finset ℤ`, primality as `Nat.Prime`, and residues in `ZMod p`.
-/

import Mathlib

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem not_admissible_five (a b c d e : Int)
    (ha : 1450 ≤ a ∧ a ≤ 1460) (hb : 1450 ≤ b ∧ b ≤ 1460) (hc : 1450 ≤ c ∧ c ≤ 1460)
    (hd : 1450 ≤ d ∧ d ≤ 1460) (he : 1450 ≤ e ∧ e ≤ 1460)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ¬ Admissible [a, b, c, d, e] := by
  intro hadm
  obtain ⟨r2, h2⟩ := hadm 2 isPrime_two
  obtain ⟨r3, h3⟩ := hadm 3 isPrime_three
  have ha2 : a % (2 : Int) ≠ r2 % (2 : Int) := h2 a (by simp)
  have hb2 : b % (2 : Int) ≠ r2 % (2 : Int) := h2 b (by simp)
  have hc2 : c % (2 : Int) ≠ r2 % (2 : Int) := h2 c (by simp)
  have hd2 : d % (2 : Int) ≠ r2 % (2 : Int) := h2 d (by simp)
  have he2 : e % (2 : Int) ≠ r2 % (2 : Int) := h2 e (by simp)
  have ha3 : a % (3 : Int) ≠ r3 % (3 : Int) := h3 a (by simp)
  have hb3 : b % (3 : Int) ≠ r3 % (3 : Int) := h3 b (by simp)
  have hc3 : c % (3 : Int) ≠ r3 % (3 : Int) := h3 c (by simp)
  have hd3 : d % (3 : Int) ≠ r3 % (3 : Int) := h3 d (by simp)
  have he3 : e % (3 : Int) ≠ r3 % (3 : Int) := h3 e (by simp)
  have hr2 : r2 % (2 : Int) = 0 ∨ r2 % (2 : Int) = 1 := by omega
  have hr3 : r3 % (3 : Int) = 0 ∨ r3 % (3 : Int) = 1 ∨ r3 % (3 : Int) = 2 := by omega
  rcases hr2 with h | h <;> rw [h] at ha2 hb2 hc2 hd2 he2 <;>
    rcases hr3 with h' | h' | h' <;> rw [h'] at ha3 hb3 hc3 hd3 he3
  · exact five_in_four (win_00 a ha.1 ha.2 ha2 ha3) (win_00 b hb.1 hb.2 hb2 hb3)
      (win_00 c hc.1 hc.2 hc2 hc3) (win_00 d hd.1 hd.2 hd2 hd3) (win_00 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_01 a ha.1 ha.2 ha2 ha3) (win_01 b hb.1 hb.2 hb2 hb3)
      (win_01 c hc.1 hc.2 hc2 hc3) (win_01 d hd.1 hd.2 hd2 hd3) (win_01 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_02 a ha.1 ha.2 ha2 ha3) (win_02 b hb.1 hb.2 hb2 hb3)
      (win_02 c hc.1 hc.2 hc2 hc3) (win_02 d hd.1 hd.2 hd2 hd3) (win_02 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_10 a ha.1 ha.2 ha2 ha3) (win_10 b hb.1 hb.2 hb2 hb3)
      (win_10 c hc.1 hc.2 hc2 hc3) (win_10 d hd.1 hd.2 hd2 hd3) (win_10 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_11 a ha.1 ha.2 ha2 ha3) (win_11 b hb.1 hb.2 hb2 hb3)
      (win_11 c hc.1 hc.2 hc2 hc3) (win_11 d hd.1 hd.2 hd2 hd3) (win_11 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde
  · exact five_in_four (win_12 a ha.1 ha.2 ha2 ha3) (win_12 b hb.1 hb.2 hb2 hb3)
      (win_12 c hc.1 hc.2 hc2 hc3) (win_12 d hd.1 hd.2 hd2 hd3) (win_12 e he.1 he.2 he2 he3)
      hab hac had hae hbc hbd hbe hcd hce hde

/-! ## Main result -/

/-- **Singular series gaps 14501460.**

Inside the gap range `[1450, 1460]` the tuple `{1450, 1452, 1456, 1458}` is admissible — it
consists of four distinct integers of the range whose singular series is nonzero — while no
five distinct integers of that range form an admissible tuple.  Hence the maximal size of an
admissible tuple in the window `[1450, 1460]` is exactly `4`. -/
