import Mathlib
namespace Brockian.MsWilsonPrimePower

open Finset

/-- If an odd prime power `p ^ k` divides `(a - 1) * (a + 1)`, then it divides one of the two
factors, since `p` cannot divide both `a - 1` and `a + 1`. -/

private lemma prod_units_eq_neg_one (p k : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hodd : Odd p) :
    (∏ x : (ZMod (p ^ k))ˣ, x) = -1 := by
  classical
  have hinv : ∀ x : (ZMod (p ^ k))ˣ, x⁻¹ = x → x = 1 ∨ x = -1 := by
    intro x hxx
    refine units_sq_eq_one p k hp hodd x ?_
    nth_rewrite 1 [← hxx]
    exact inv_mul_cancel x
  have h : (∏ x ∈ (univ : Finset (ZMod (p ^ k))ˣ).erase (-1), x) = 1 := by
    refine Finset.prod_involution (fun x _ => x⁻¹) (by simp) ?_ ?_ (by simp)
    · intro a ha ha1 hinva
      rcases hinv a hinva with h1 | h1
      · exact ha1 h1
      · exact (Finset.mem_erase.mp ha).1 h1
    · intro a ha
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hcon
      exact (Finset.mem_erase.mp ha).1 (by simpa using congrArg (fun y => y⁻¹) hcon)
  rw [← Finset.insert_erase (Finset.mem_univ (-1 : (ZMod (p ^ k))ˣ)),
    Finset.prod_insert (Finset.notMem_erase _ _), h, mul_one]

/-- Gauss's extension of Wilson's theorem: for an odd prime p and k ≥ 1, the product of all
    units of ℤ/(p^k) equals −1.

    (The instance argument `[NeZero (p ^ k)]`, which follows from `hp` and `hk`, is only needed so
    that `ZMod (p ^ k)` is known to be a finite type when the product is elaborated. The hypothesis
    `hk : 0 < k` is kept as stated, although the proof does not need it.) -/
