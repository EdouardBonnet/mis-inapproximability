import Lax759944.TuringPolytime

/-!
---
title: Polynomial-time computation on the Lax759944 finite-Turing model
type: definition
---
All algorithms in this submission compute total functions on finite words of
natural numbers.  Polynomial time is exactly Lax759944's predicate: a fixed
finite multi-stack Turing machine transforms the canonical binary encoding of
the input word into the canonical binary encoding of its output within a
polynomial number of transitions.

In particular, a program's semantic function is tied to an actual finite
Turing machine by $TuringPolytime$.  Randomized algorithms receive a finite
list of independent uniform bits, represented by the words $0$ and $1$.
-/

set_option autoImplicit false

namespace Lax614640.Machine

open Lax759944.BinaryWordEncoding Lax759944.TuringPolytime

/-- A finite machine word.  Boolean data use the entries $0$ and $1$. -/
abbrev BitString := List ℕ

/-- The convenient monomial bound $c(n+1)^k$. -/
def polynomialBound (c k n : ℕ) : ℕ :=
  c * (n + 1) ^ k

/-- A total word function computed in polynomial time by a finite Turing machine. -/
structure PolytimeProgram where
  function : BitString → BitString
  polytime : TuringPolytime function

/-- The semantic output certified by the program's finite Turing machine. -/
def PolytimeProgram.output (program : PolytimeProgram)
    (input : BitString) : BitString :=
  program.function input

/-- A length-prefixed pairing of two finite words. -/
def pairBits (left right : BitString) : BitString :=
  left.length :: left ++ right

/-- A uniformly random string of exactly $r$ bits. -/
abbrev RandomSeed (r : ℕ) := Fin r → Bool

/-- Encode one Boolean as a natural-number word. -/
def bitWord (bit : Bool) : ℕ :=
  if bit then 1 else 0

/-- The word representation of a fixed-length random seed. -/
def RandomSeed.bits {r : ℕ} (seed : RandomSeed r) : BitString :=
  (List.ofFn seed).map bitWord

end Lax614640.Machine
