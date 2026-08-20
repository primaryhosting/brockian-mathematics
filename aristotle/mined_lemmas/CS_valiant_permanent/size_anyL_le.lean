/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.PermanentGadget

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalization

The statement "the `0/1` permanent is `#P`-complete" has two halves.  What is formalized here is

* the *membership* half, in full: the `0/1` permanent is the counting function of an explicitly
  constructed family of Boolean verifier circuits of polynomial size (`InSharpP perm01Count`);
* the combinatorial identity underlying the problem: the permanent of a `0/1` matrix is the
  number of perfect matchings of the associated bipartite graph;
* the weight-elimination step of Valiant's hardness argument: restricting to `0/1` entries loses
  no generality, since every matrix of natural numbers has the same permanent as a `0/1` matrix
  of controlled size.

The remaining half of Valiant's theorem, namely the parsimonious reduction of an arbitrary `#P`
verifier to a permanent (the gadget construction), is *not* formalized here.
-/

set_option autoImplicit false

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas) over a set `ι` of input variables. -/
inductive Circuit (ι : Type) where
  | var : ι → Circuit ι
  | const : Bool → Circuit ι
  | not : Circuit ι → Circuit ι
  | and : Circuit ι → Circuit ι → Circuit ι
  | or : Circuit ι → Circuit ι → Circuit ι

namespace Circuit

variable {ι : Type}

/-- Evaluation of a circuit at a Boolean assignment of its variables. -/

theorem size_anyL_le (l : List (Circuit ι)) (s : ℕ) (h : ∀ c ∈ l, c.size ≤ s) :
    (anyL l).size ≤ 1 + l.length * (1 + s) := by
  induction l with
  | nil => simp [anyL, size]
  | cons c cs ih =>
      have hc : c.size ≤ s := h c (by simp)
      have := ih (fun d hd => h d (by simp [hd]))
      simp only [anyL, size, List.length_cons, Nat.succ_mul]
      omega

end Circuit

/-! ## A non-uniform version of the counting class `#P`

A family of counting functions `f n : (ι n → Bool) → ℕ` belongs to `InSharpP` if there is a
family of polynomial-size Boolean verifier circuits `C n`, taking the input bits together with
polynomially many witness bits, such that `f n x` is exactly the number of witnesses accepted
by `C n` on input `x`.  This is the standard witness-counting description of `#P`, with
"polynomial-time verifier" modelled by "polynomial-size Boolean circuit" (i.e. the
non-uniform class `#P/poly`). -/
