import Lax47.Complexity
import Lax41.MoserTardosDefinitions
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Probability.ProductMeasure

/-!
---
title: Finite-bit reduction to triangle-free Max Independent Set
type: definition
---
This concept defines the fixed randomized reduction used by the proof. An
$n$-vertex graph is sent to a graph on the $n\times n$ blow-up of its vertices.
The program receives one finite block of fair bits for every table cell that a
polynomially truncated resampling loop can read. It scans the finite list of
ordered vertex triples, resamples the three edges of the first present
triangle, and stops after $12(n+1)^6$ rounds. If the final scan still finds a
triangle, it emits the edgeless graph.

The counter state and its operation count are returned by the same structural
recursion. The mathematical infinite table used in the probability proof is
not an input to this executable reduction.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax47.Reduction

open Lax41.MoserTardosDefinitions
open Lax47.Complexity

/-- Vertices of the complete $n$-fold blow-up. -/
abbrev BlowupVertex (n : ℕ) := Fin n × Fin n

/-- Edge variables used by the resampling construction. -/
abbrev EdgeVariable (n : ℕ) := Sym2 (BlowupVertex n)

/-- The infinite table of Boolean samples read lazily by Moser--Tardos. -/
abbrev SampleTable (n : ℕ) :=
  ResamplingTable (fun _ : EdgeVariable n ↦ Bool)

/- ### Fixed finite-bit execution of the reduction -/

/-- Ordered triples scanned by the executable triangle-removal loop. -/
abbrev ExecutionTriple (n : ℕ) :=
  BlowupVertex n × BlowupVertex n × BlowupVertex n

/-- First vertex of an ordered execution triple. -/
def executionFirstVertex {n : ℕ} (triple : ExecutionTriple n) : BlowupVertex n :=
  triple.1

/-- Second vertex of an ordered execution triple. -/
def executionSecondVertex {n : ℕ} (triple : ExecutionTriple n) : BlowupVertex n :=
  triple.2.1

/-- Third vertex of an ordered execution triple. -/
def executionThirdVertex {n : ℕ} (triple : ExecutionTriple n) : BlowupVertex n :=
  triple.2.2

/-- The three unordered edge variables of an ordered triple. -/
def executionTriangleVariables {n : ℕ} (triple : ExecutionTriple n) :
    Finset (EdgeVariable n) :=
  {s(executionFirstVertex triple, executionSecondVertex triple),
    s(executionFirstVertex triple, executionThirdVertex triple),
    s(executionSecondVertex triple, executionThirdVertex triple)}

/-- Number of fair bits used to realize one Bernoulli edge sample. -/
def executionSampleBits (n : ℕ) : ℕ :=
  Nat.log2 (100 * (n + 1)) + 1

/-- Maximum number of Moser--Tardos rounds executed. -/
def executionBudget (n : ℕ) : ℕ :=
  12 * (n + 1) ^ 6

/--
The actual random input: one finite fair-bit block for every edge and every
row that the bounded loop can read.
-/
abbrev ExecutionSeed (n : ℕ) :=
  EdgeVariable n → Fin (executionBudget n + 1) →
    Fin (executionSampleBits n) → Bool

/-- Decode one block of fair bits as a Bernoulli sample. -/
def executionBlockValue {n : ℕ}
    (block : Fin (executionSampleBits n) → Bool) : Bool :=
  decide (∀ bit, block bit = true)

/-- Read a sampled edge cell, returning false outside the finite prefix. -/
def executionCell {n : ℕ} (seed : ExecutionSeed n)
    (edge : EdgeVariable n) (row : ℕ) : Bool :=
  if h : row < executionBudget n + 1 then
    executionBlockValue (seed edge ⟨row, h⟩)
  else false

/-- Boolean adjacency in the complete blow-up of an encoded input graph. -/
def executionBlowupAdjacent {n : ℕ} (input : GraphCode n)
    (left right : BlowupVertex n) : Bool :=
  input.adjacent left.1 right.1

/-- Whether an ordered triple is a currently present blow-up triangle. -/
def executionViolates {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ)
    (triple : ExecutionTriple n) : Bool :=
  executionBlowupAdjacent input (executionFirstVertex triple)
      (executionSecondVertex triple) &&
    executionBlowupAdjacent input (executionFirstVertex triple)
      (executionThirdVertex triple) &&
    executionBlowupAdjacent input (executionSecondVertex triple)
      (executionThirdVertex triple) &&
    executionCell seed s(executionFirstVertex triple, executionSecondVertex triple)
      (counts s(executionFirstVertex triple, executionSecondVertex triple)) &&
    executionCell seed s(executionFirstVertex triple, executionThirdVertex triple)
      (counts s(executionFirstVertex triple, executionThirdVertex triple)) &&
    executionCell seed s(executionSecondVertex triple, executionThirdVertex triple)
      (counts s(executionSecondVertex triple, executionThirdVertex triple))

/-- A conservative elementary-operation charge for testing one triple. -/
def executionTestSteps (n : ℕ) : ℕ :=
  20 * (executionBudget n + 1) * (executionSampleBits n + 1)

/--
Scan a concrete list of ordered triples.  The returned step count is produced
by the same recursion as the selected triple.
-/
def scanExecutionTriples {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ) :
    List (ExecutionTriple n) → Option (ExecutionTriple n) × ℕ
  | [] => (none, 1)
  | triple :: rest =>
      if executionViolates input seed counts triple then
        (some triple, executionTestSteps n)
      else
        let tail := scanExecutionTriples input seed counts rest
        (tail.1, executionTestSteps n + tail.2)

/-- Scan all $n^6$ ordered triples in the fixed finite enumeration. -/
def executionTriples (n : ℕ) : List (ExecutionTriple n) :=
  (List.finRange n).flatMap fun a ↦
    (List.finRange n).flatMap fun a' ↦
      (List.finRange n).flatMap fun b ↦
        (List.finRange n).flatMap fun b' ↦
          (List.finRange n).flatMap fun c ↦
            (List.finRange n).map fun c' ↦
              ((a, a'), (b, b'), (c, c'))

@[simp] lemma mem_executionTriples {n : ℕ} (triple : ExecutionTriple n) :
    triple ∈ executionTriples n := by
  rcases triple with ⟨⟨a, a'⟩, ⟨⟨b, b'⟩, ⟨c, c'⟩⟩⟩
  simp [executionTriples]

/-- Scan all $n^6$ ordered triples in the fixed finite enumeration. -/
def findExecutionViolation {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ) :
    Option (ExecutionTriple n) × ℕ :=
  scanExecutionTriples input seed counts (executionTriples n)

/-- Increment exactly the three counters of a selected triangle. -/
def advanceExecutionCounts {n : ℕ} (counts : EdgeVariable n → ℕ)
    (selected : Option (ExecutionTriple n)) : EdgeVariable n → ℕ :=
  selected.elim counts fun triple edge ↦
    if edge ∈ executionTriangleVariables triple then counts edge + 1 else counts edge

/--
Run a fixed number of rounds.  Result and step count are paired by this
structural recursion; there is no independently supplied cost function.
-/
def executeRounds {n : ℕ} (input : GraphCode n) (seed : ExecutionSeed n) :
    (rounds : ℕ) → (EdgeVariable n → ℕ) → (EdgeVariable n → ℕ) × ℕ
  | 0, counts => (counts, 1)
  | rounds + 1, counts =>
      let prior := executeRounds input seed rounds counts
      let scan := findExecutionViolation input seed prior.1
      (advanceExecutionCounts prior.1 scan.1, prior.2 + scan.2 + 1)

/-- Counter state after the polynomially bounded resampling loop. -/
def executionCounts {n : ℕ} (input : GraphCode n) (seed : ExecutionSeed n) :
    EdgeVariable n → ℕ :=
  (executeRounds input seed (executionBudget n) (fun _ ↦ 0)).1

/-- The loop has halted when its final deterministic scan finds no triangle. -/
def executionHalted {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) : Bool :=
  (findExecutionViolation input seed (executionCounts input seed)).1.isNone

/-- Pair encoding of the vertices of the $n\times n$ blow-up. -/
def decodeBlowupVertex {n : ℕ} (vertex : Fin (n * n)) : BlowupVertex n :=
  finProdFinEquiv.symm vertex

@[simp] lemma decodeBlowupVertex_encode {n : ℕ} (vertex : BlowupVertex n) :
    decodeBlowupVertex (finProdFinEquiv vertex) = vertex :=
  finProdFinEquiv.symm_apply_apply vertex

/-- The graph emitted by the fixed finite-bit reduction. -/
def executionOutput {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) : GraphCode (n * n) where
  adjacent left right :=
    if executionHalted input seed then
      let u := decodeBlowupVertex left
      let v := decodeBlowupVertex right
      input.adjacent u.1 v.1 &&
        executionCell seed s(u, v) (executionCounts input seed s(u, v))
    else false
  loopless := by
    intro vertex
    simp [decodeBlowupVertex, input.loopless]
  symmetric := by
    intro left right
    by_cases h : executionHalted input seed
    · simp only [h, if_true, decodeBlowupVertex]
      rw [input.symmetric]
      rw [Sym2.eq_swap]
    · simp [h]

/-- Actual counted work of the bounded reduction, including its final scan. -/
def executionSteps {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) : ℕ :=
  (executeRounds input seed (executionBudget n) (fun _ ↦ 0)).2 +
    (findExecutionViolation input seed (executionCounts input seed)).2 +
    (n + 1) ^ 4

end Lax47.Reduction
