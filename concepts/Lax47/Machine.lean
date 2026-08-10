import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: An operational machine model for polynomial-time computation
type: definition
---
Computations are finite multi-stack Turing machines over binary input and
output alphabets. A run is evaluated by the recursive bounded interpreter
below. One unit of time is one transition of the fixed finite machine, and a
polynomial-time program must prove that this interpreter reaches a halted
configuration within $c(n+1)^k$ transitions on every input of length $n$.

In particular, programs do not contain arbitrary Lean functions describing
their answers, and time bounds are not annotations detached from evaluation.
The semantic output function used below extracts the result returned by that
bounded interpreter. Randomized algorithms receive a finite list of uniformly
random input bits.
-/

set_option autoImplicit false

namespace Lax47.Machine

/-- A finite binary input, output, certificate, or random seed. -/
abbrev BitString := List Bool

/-- A finite machine whose designated input and output alphabets are binary. -/
abbrev BitMachine := Turing.TM2ComputableAux Bool Bool

/--
Run at most the supplied number of transitions, returning the first halted
configuration and returning no result if the fuel is exhausted first.
-/
def runConfigWithin (tm : Turing.FinTM2) :
    (fuel : ℕ) → tm.Cfg → Option tm.Cfg
  | 0, cfg =>
      match cfg.l with
      | none => some cfg
      | some _ => none
  | fuel + 1, cfg =>
      match cfg.l with
      | none => some cfg
      | some _ =>
          match tm.step cfg with
          | none => none
          | some next => runConfigWithin tm fuel next

/-- The binary output produced by a machine within the supplied fuel. -/
def evalWithin (machine : BitMachine) (fuel : ℕ)
    (input : BitString) : Option BitString :=
  match runConfigWithin machine.tm fuel
      (Turing.initList machine.tm
        (input.map machine.inputAlphabet.invFun)) with
  | none => none
  | some cfg => some ((cfg.stk machine.tm.k₁).map machine.outputAlphabet)

/-- The convenient monomial polynomial bound $c(n+1)^k$. -/
def polynomialBound (c k n : ℕ) : ℕ :=
  c * (n + 1) ^ k

/-- A binary Turing program whose actual bounded evaluation always halts. -/
structure PolytimeProgram where
  machine : BitMachine
  timeConstant : ℕ
  timeExponent : ℕ
  timeConstant_pos : 0 < timeConstant
  terminates : ∀ input : BitString,
    ∃ output, evalWithin machine
      (polynomialBound timeConstant timeExponent input.length) input = some output

/-- The certified bounded evaluation returns a result. -/
theorem PolytimeProgram.output_isSome (program : PolytimeProgram)
    (input : BitString) :
    (evalWithin program.machine
      (polynomialBound program.timeConstant program.timeExponent input.length)
      input).isSome :=
  Option.isSome_iff_exists.2 (program.terminates input)

/-- The executable output obtained from the certified bounded machine run. -/
def PolytimeProgram.output (program : PolytimeProgram)
    (input : BitString) : BitString :=
  (evalWithin program.machine
    (polynomialBound program.timeConstant program.timeExponent input.length)
    input).get (program.output_isSome input)

/-- The extracted output is produced by the operational evaluator. -/
theorem PolytimeProgram.output_spec (program : PolytimeProgram)
    (input : BitString) :
    evalWithin program.machine
      (polynomialBound program.timeConstant program.timeExponent input.length) input =
        some (program.output input) := by
  simpa only [PolytimeProgram.output] using
    Option.eq_some_of_isSome (program.output_isSome input)

/-- A self-delimiting pairing of two binary strings. -/
def pairBits (left right : BitString) : BitString :=
  List.replicate left.length true ++ false :: left ++ right

/-- A uniformly random string of exactly $r$ bits. -/
abbrev RandomSeed (r : ℕ) := Fin r → Bool

/-- The list representation of a fixed-length random seed. -/
def RandomSeed.bits {r : ℕ} (seed : RandomSeed r) : BitString :=
  List.ofFn seed

/-- A decision problem over finite binary inputs. -/
abbrev Language := Set BitString

/-- A polynomial-time verifier with polynomially bounded certificates. -/
structure NPVerifier (language : Language) where
  program : PolytimeProgram
  certificateConstant : ℕ
  certificateExponent : ℕ
  certificateConstant_pos : 0 < certificateConstant
  correctness : ∀ input : BitString,
    input ∈ language ↔ ∃ certificate : BitString,
      certificate.length ≤ polynomialBound
        certificateConstant certificateExponent input.length ∧
      program.output (pairBits input certificate) = [true]

/-- Membership in $NP$ in the operational binary-machine model. -/
def InNP (language : Language) : Prop :=
  Nonempty (NPVerifier language)

/-- A polynomial-time randomized decision program using finitely many bits. -/
structure BPPAlgorithm (language : Language) where
  program : PolytimeProgram
  randomnessConstant : ℕ
  randomnessExponent : ℕ
  randomnessConstant_pos : 0 < randomnessConstant
  correctness : ∀ input : BitString,
    let randomBitCount := polynomialBound
      randomnessConstant randomnessExponent input.length
    let seeds : Finset (RandomSeed randomBitCount) := Finset.univ
    let accepting := seeds.filter fun seed ↦
      program.output (pairBits input seed.bits) = [true]
    (input ∈ language → 2 * seeds.card ≤ 3 * accepting.card) ∧
      (input ∉ language → 3 * accepting.card ≤ seeds.card)

/-- Membership in $BPP$ in the same operational binary-machine model. -/
def InBPP (language : Language) : Prop :=
  Nonempty (BPPAlgorithm language)

/-- The complexity-class inclusion appearing in the inapproximability theorem. -/
def NPSubsetBPP : Prop :=
  ∀ language : Language, InNP language → InBPP language

end Lax47.Machine
