/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## Overview

This file formalises the *hardness versus randomness* theorem of Impagliazzo and
Wigderson: strong (exponential) circuit lower bounds imply `P = BPP`.

The development is self contained (it uses only the Lean 4 core library) and is
organised in three clearly separated layers.

* **Boolean circuits and pseudorandomness.**  Boolean circuits, their size, the
  number of accepted inputs of a Boolean function, and the notion of a *pseudorandom
  generator* (a map on short seeds whose output distribution `1/12`-fools every small
  circuit) are defined concretely.  The derandomisation gap lemma
  (`CS.fooled_gap`) — the combinatorial heart of the argument — is proved from
  scratch: a fooled circuit whose acceptance probability is at least `2/3` accepts a
  strict majority of the generator's seeds, and one whose acceptance probability is at
  most `1/3` does not.

* **An abstract model of deterministic polynomial time.**  Rather than fixing a
  Turing machine model, the structure `CS.Model` axiomatises the standard closure
  properties of deterministic polynomial time that the argument needs: a deterministic
  algorithm is a randomised algorithm ignoring its randomness (`poly2_const`), a
  polynomial-time randomised algorithm is simulated on each input by a polynomial-size
  circuit acting on its random bits (`circuit_sim`, Cook–Levin), and polynomial time is
  closed under taking a majority vote over a polynomially large seed space
  (`derandomize`).  The classes `Model.P` and `Model.BPP` are then defined in the usual
  way, `BPP` with the standard two-sided error bounds `2/3` and `1/3`.

* **The Nisan–Wigderson / Impagliazzo–Wigderson generator.**  The construction of a
  pseudorandom generator with logarithmic seed length out of an exponentially hard
  function is taken as an explicit hypothesis `hIW` of the main theorem; the strong
  circuit lower bound itself is the hypothesis `hHard`.

The main theorem `CS.impagliazzo_wigderson` then proves `BPP = P`.  Both inclusions
are established; the substantial one derandomises an arbitrary `BPP` algorithm by
taking the majority vote of its answers over all seeds of the generator.

Randomness is modelled by a natural number `k < 2 ^ m` whose bits `k.testBit i`,
`i < m`, are the `m` random bits; the uniform distribution on `{0,1}^m` is therefore
the uniform distribution on `{0, …, 2^m - 1}`, and probabilities are expressed as
counting inequalities between natural numbers.
-/

namespace CS

/-- Binary strings, the inputs of our algorithms. -/
abbrev Str := List Bool

/-- A language is a predicate on binary strings. -/
abbrev Lang := Str → Bool

/-! ### Counting -/

/-- `countLt p N` is the number of `k < N` with `p k = true`. -/

theorem BPP_subset_P_of_generator (M : Model) (hG : M.HasIWGenerator) (L : Lang)
    (hL : M.BPP L) : M.P L := by
  obtain ⟨A, m, hA, hm, hAL⟩ := hL
  -- polynomial size circuits simulating `A` on each input
  obtain ⟨s, hs, hsim⟩ := M.circuit_sim A m hA hm
  -- a generator fooling all those circuits
  obtain ⟨l, G, hl, hPG, hGlt, hfool⟩ := hG m s hm hs
  -- the derandomised algorithm decides `L`
  have hD := M.derandomize A l G hA hPG hl
  have hEq : (fun x => decide (2 ^ l x.length <
      2 * countLt (fun u => A x (G x.length u)) (2 ^ l x.length))) = L := by
    funext x
    obtain ⟨C, hCu, hCs, hCe⟩ := hsim x
    have hseed : countLt (fun u => A x (G x.length u)) (2 ^ l x.length)
        = countLt (fun u => C.eval (G x.length u)) (2 ^ l x.length) :=
      countLt_congr _ (fun u _ => (hCe _ (hGlt x.length u)).symm)
    have hunif : countLt (A x) (2 ^ m x.length) = countLt C.eval (2 ^ m x.length) :=
      countLt_congr _ (fun k hk => (hCe k hk).symm)
    obtain ⟨hyes, hno⟩ := fooled_gap (hfool x.length) hCu hCs
    rw [hseed]
    cases hLx : L x
    · have h := hno (by
        have := (hAL x).2 hLx
        rw [accCount, hunif] at this
        exact this)
      simp only [decide_eq_false_iff_not, Nat.not_lt]
      omega
    · have h := hyes (by
        have := (hAL x).1 hLx
        rw [accCount, hunif] at this
        exact this)
      simp [h]
  rw [hEq] at hD
  exact hD

/-! ### The Impagliazzo–Wigderson theorem -/

/-- **Impagliazzo–Wigderson: strong circuit lower bounds imply `P = BPP`.**

In any model of deterministic polynomial-time computation satisfying the standard
closure properties collected in `CS.Model`, if some language of `E` requires Boolean
circuits of size `2 ^ Ω(n)` (`hHard`), and hence, by the Nisan–Wigderson generator
construction (`hIW`), there are polynomial-time computable pseudorandom generators
with logarithmic seed length fooling all polynomial-size circuits, then `BPP = P`. -/
