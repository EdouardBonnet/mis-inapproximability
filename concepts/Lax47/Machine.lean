import Lax51.TuringPolytime

/-!
---
title: Polynomial-time computation on the Lax51 finite-Turing model
type: definition
---
All algorithms in this submission compute total functions on finite words of
natural numbers.  Polynomial time is exactly Lax51's predicate: a fixed
finite multi-stack Turing machine transforms the canonical binary encoding of
the input word into the canonical binary encoding of its output within a
polynomial number of transitions.

In particular, a program's semantic function is tied to an actual finite
Turing machine by $TuringPolytime$.  Randomized algorithms receive a finite
list of independent uniform bits, represented by the words $0$ and $1$.
-/

set_option autoImplicit false

namespace Lax47.Machine

open Lax51.BinaryWordEncoding Lax51.TuringPolytime

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

/-- A decision problem over finite words. -/
abbrev Language := Set BitString

/-- A polynomial-time verifier whose certificate binary size is polynomially bounded. -/
structure NPVerifier (language : Language) where
  program : PolytimeProgram
  certificateConstant : ℕ
  certificateExponent : ℕ
  certificateConstant_pos : 0 < certificateConstant
  correctness : ∀ input : BitString,
    input ∈ language ↔ ∃ certificate : BitString,
      bitSize certificate ≤ polynomialBound
        certificateConstant certificateExponent (bitSize input) ∧
      program.output (pairBits input certificate) = [1]

/-- Membership in $NP$ in the Lax51 finite-Turing model. -/
def InNP (language : Language) : Prop :=
  Nonempty (NPVerifier language)

/-- A polynomial-time randomized decision program using polynomially many uniform bits. -/
structure BPPAlgorithm (language : Language) where
  program : PolytimeProgram
  randomnessConstant : ℕ
  randomnessExponent : ℕ
  randomnessConstant_pos : 0 < randomnessConstant
  correctness : ∀ input : BitString,
    let randomBitCount := polynomialBound
      randomnessConstant randomnessExponent (bitSize input)
    let seeds : Finset (RandomSeed randomBitCount) := Finset.univ
    let accepting := seeds.filter fun seed ↦
      program.output (pairBits input seed.bits) = [1]
    (input ∈ language → 2 * seeds.card ≤ 3 * accepting.card) ∧
      (input ∉ language → 3 * accepting.card ≤ seeds.card)

/-- Membership in $BPP$ in the same finite-Turing model. -/
def InBPP (language : Language) : Prop :=
  Nonempty (BPPAlgorithm language)

/-- The complexity-class inclusion appearing in the inapproximability theorem. -/
def NPSubsetBPP : Prop :=
  ∀ language : Language, InNP language → InBPP language

end Lax47.Machine
