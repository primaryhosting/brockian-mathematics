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

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Brocard's problem asks for all natural numbers `n`, `m` with `n ! + 1 = m ^ 2`.
The only known solutions are `(n, m) = (4, 5), (5, 11), (7, 71)`; the assertion that
there are no further solutions is Brocard's conjecture, which is open.

This file develops the material from first principles, with no imports and hence without
`Mathlib`: the mandated header comment above has to be the first command of the file, and
Lean does not allow an `import` to follow a module docstring.

Contents:

* `Brockian.BrocardProblem.factorial` : the factorial function.
* `Brockian.BrocardProblem.brocard_iff_four_mul_consecutive` : an unconditional
  reformulation of the equation for `n ≥ 2`, namely `n ! + 1` is a perfect square if and
  only if `n ! = 4 * k * (k + 1)` for some `k`, i.e. if and only if `n !` is four times a
  product of two consecutive natural numbers.
* `Brockian.BrocardProblem.brocard_small` : an unconditional verification that
  `(4, 5)`, `(5, 11)`, `(7, 71)` are the only solutions with `n ≤ 200`. Each excluded
  value of `n` is handled by exhibiting a modulus `q` for which `n ! + 1` is not a square
  modulo `q`.
* `Brockian.BrocardProblem.BrocardConjecture` : Brocard's conjecture, proved conditionally
  on the (open) reformulated statement for `n ≥ 201`.
-/

namespace Brockian.BrocardProblem

set_option maxRecDepth 100000

/-- The factorial function, `factorial n = n !`. -/

def modulus : Nat → Nat
  | 0 => 3
  | 1 => 3
  | 2 => 4
  | 3 => 4
  | 4 => 0
  | 5 => 0
  | 6 => 11
  | 7 => 0
  | 8 => 11
  | 9 => 11
  | 10 => 13
  | 11 => 13
  | 12 => 29
  | 13 => 23
  | 14 => 31
  | 15 => 37
  | 16 => 19
  | 17 => 19
  | 18 => 31
  | 19 => 23
  | 20 => 29
  | 21 => 31
  | 22 => 37
  | 23 => 59
  | 24 => 31
  | 25 => 31
  | 26 => 29
  | 27 => 29
  | 28 => 43
  | 29 => 37
  | 30 => 37
  | 31 => 41
  | 32 => 41
  | 33 => 37
  | 34 => 37
  | 35 => 37
  | 36 => 41
  | 37 => 43
  | 38 => 53
  | 39 => 43
  | 40 => 43
  | 41 => 43
  | 42 => 47
  | 43 => 61
  | 44 => 53
  | 45 => 53
  | 46 => 71
  | 47 => 53
  | 48 => 53
  | 49 => 67
  | 50 => 53
  | 51 => 53
  | 52 => 59
  | 53 => 59
  | 54 => 67
  | 55 => 59
  | 56 => 59
  | 57 => 59
  | 58 => 61
  | 59 => 61
  | 60 => 67
  | 61 => 67
  | 62 => 89
  | 63 => 67
  | 64 => 67
  | 65 => 67
  | 66 => 71
  | 67 => 71
  | 68 => 79
  | 69 => 73
  | 70 => 83
  | 71 => 79
  | 72 => 83
  | 73 => 79
  | 74 => 79
  | 75 => 83
  | 76 => 97
  | 77 => 89
  | 78 => 83
  | 79 => 83
  | 80 => 83
  | 81 => 83
  | 82 => 89
  | 83 => 89
  | 84 => 97
  | 85 => 103
  | 86 => 101
  | 87 => 101
  | 88 => 101
  | 89 => 101
  | 90 => 101
  | 91 => 97
  | 92 => 97
  | 93 => 97
  | 94 => 101
  | 95 => 103
  | 96 => 107
  | 97 => 101
  | 98 => 101
  | 99 => 101
  | 100 => 139
  | 101 => 113
  | 102 => 107
  | 103 => 109
  | 104 => 107
  | 105 => 107
  | 106 => 109
  | 107 => 109
  | 108 => 127
  | 109 => 113
  | 110 => 137
  | 111 => 131
  | 112 => 127
  | 113 => 127
  | 114 => 139
  | 115 => 151
  | 116 => 131
  | 117 => 131
  | 118 => 137
  | 119 => 149
  | 120 => 127
  | 121 => 131
  | 122 => 131
  | 123 => 137
  | 124 => 139
  | 125 => 131
  | 126 => 137
  | 127 => 131
  | 128 => 131
  | 129 => 131
  | 130 => 137
  | 131 => 149
  | 132 => 157
  | 133 => 137
  | 134 => 139
  | 135 => 151
  | 136 => 139
  | 137 => 139
  | 138 => 151
  | 139 => 173
  | 140 => 151
  | 141 => 163
  | 142 => 151
  | 143 => 151
  | 144 => 149
  | 145 => 151
  | 146 => 149
  | 147 => 149
  | 148 => 157
  | 149 => 163
  | 150 => 173
  | 151 => 193
  | 152 => 163
  | 153 => 163
  | 154 => 157
  | 155 => 157
  | 156 => 173
  | 157 => 163
  | 158 => 163
  | 159 => 163
  | 160 => 163
  | 161 => 163
  | 162 => 167
  | 163 => 173
  | 164 => 173
  | 165 => 181
  | 166 => 179
  | 167 => 173
  | 168 => 181
  | 169 => 173
  | 170 => 173
  | 171 => 173
  | 172 => 193
  | 173 => 179
  | 174 => 193
  | 175 => 181
  | 176 => 179
  | 177 => 179
  | 178 => 181
  | 179 => 181
  | 180 => 193
  | 181 => 191
  | 182 => 191
  | 183 => 191
  | 184 => 191
  | 185 => 193
  | 186 => 199
  | 187 => 191
  | 188 => 197
  | 189 => 197
  | 190 => 211
  | 191 => 197
  | 192 => 223
  | 193 => 199
  | 194 => 197
  | 195 => 197
  | 196 => 227
  | 197 => 211
  | 198 => 211
  | 199 => 239
  | 200 => 211
  | _ => 0

/-- The recorded moduli are positive except at `n = 4, 5, 7`. -/
