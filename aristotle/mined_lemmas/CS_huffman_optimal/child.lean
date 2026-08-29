import Mathlib

/-!
# Kraft's inequality

This file proves the Kraft inequality for finite prefix-free binary codes.
It is part of the development of `CS.huffman_optimal`.
-/

namespace CS

open List

/-- A list of binary codewords is prefix-free when no codeword is a prefix of another. -/

def child (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | [] :: L => child b L
  | (c :: t) :: L => if c = b then t :: child b L else child b L

/-- Total length of all codewords, used as a termination measure. -/
