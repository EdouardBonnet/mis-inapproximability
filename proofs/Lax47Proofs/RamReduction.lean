import Lax47Proofs.FlatReduction
import Lax51Proofs.TMToRam.NativeBounded
import Lax51Proofs.TuringRamPolytimeEquivalence
import Lax13Proofs.Refine.Codegen.Harness

/-!
The reduction used by the gap solver is implemented here as one fixed IMP+
program.  IMP+ has a grounded compiler to the Lax13 word RAM, and Lax51 has a
grounded polynomial-overhead simulation from that RAM to a finite Turing
machine.  Thus every cost below is attached to an actual execution trace.

The machine copies its length-prefixed logical input into `raw`, caps the
advertised order by that length, and uses zero for every absent/non-Boolean
entry.  `counts` is the square table of Moser--Tardos resampling counters and
`graph` receives the complete row-major output word.  All loops have bounds
computed from the capped order.
-/

set_option autoImplicit false

namespace Lax47Proofs.RamReduction

open Lax47.Machine Lax47.Complexity Lax47.Reduction
open Lax47Proofs.FlatReduction
open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax13Proofs.Codegen

/-! ### Fixed names and small syntax combinators -/

def rawArray : String := "r.raw"
def countsArray : String := "r.counts"
def graphArray : String := "r.graph"

def rawLenVar : String := "r.rawLen"
def loadIndexVar : String := "r.loadIndex"
def tempVar : String := "r.temp"
def orderVar : String := "r.n"
def blowupVar : String := "r.N"
def countLenVar : String := "r.countLen"
def tripleLenVar : String := "r.tripleLen"
def budgetVar : String := "r.budget"
def sampleBitsVar : String := "r.sampleBits"
def sampleTargetVar : String := "r.sampleTarget"
def powVar : String := "r.pow"
def roundVar : String := "r.round"
def rankVar : String := "r.rank"
def foundVar : String := "r.found"
def selectedVar : String := "r.selected"
def firstVar : String := "r.u"
def secondVar : String := "r.v"
def thirdVar : String := "r.w"
def firstBaseVar : String := "r.ub"
def secondBaseVar : String := "r.vb"
def thirdBaseVar : String := "r.wb"
def edgeOneVar : String := "r.e1"
def edgeTwoVar : String := "r.e2"
def edgeThreeVar : String := "r.e3"
def selectedEdgeOneVar : String := "r.se1"
def selectedEdgeTwoVar : String := "r.se2"
def selectedEdgeThreeVar : String := "r.se3"
def rowVar : String := "r.row"
def bitVar : String := "r.bit"
def rawIndexVar : String := "r.rawIndex"
def okVar : String := "r.ok"
def markVar : String := "r.mark"
def countIndexVar : String := "r.countIndex"
def haltedVar : String := "r.halted"
def outputIndexVar : String := "r.outputIndex"

def Com.block : List Com → Com
  | [] => .skip
  | command :: commands => .seq command (Com.block commands)

@[simp] lemma Com.block_nil : Com.block [] = .skip := rfl
@[simp] lemma Com.block_cons (command : Com) (commands : List Com) :
    Com.block (command :: commands) = .seq command (Com.block commands) := rfl

def increment (name : String) : Com :=
  .assign name (.add (.var name) (.lit 1))

def setZero (name : String) : Com := .assign name (.lit 0)
def setOne (name : String) : Com := .assign name (.lit 1)

def minExpr (left right : Expr) : Expr :=
  -- The result is materialized by `edgeSlotCom`; this expression is used only
  -- in documentation and pure cost estimates.
  .sub (.add left right) (.sub left right)

/-! ### Input decoding and arithmetic parameters -/

/-- Copy the length-prefixed logical input into the pre-sized raw array. -/
def inputPrelude : Com :=
  readScalarsThenArr [rawLenVar] rawArray loadIndexVar rawLenVar tempVar

/-- Read `raw[index] = 1`, returning zero outside the copied input. -/
def readRawBit (index : Expr) (destination : String) : Com :=
  .ite (.lt index (.var rawLenVar))
    (.ite (.eq (.get rawArray index) (.lit 1))
      (setOne destination) (setZero destination))
    (setZero destination)

/-- Replace `n` by the capped order `min(raw[1], raw.length)`. -/
def decodeOrder : Com :=
  Com.block [
    setZero orderVar,
    .ite (.lt (.lit 1) (.var rawLenVar))
      (.assign orderVar (.get rawArray (.lit 1))) .skip,
    .ite (.lt (.var rawLenVar) (.var orderVar))
      (.assign orderVar (.var rawLenVar)) .skip]

/-- Fixed expression for $(n+1)^6$. -/
def orderPlusOnePowSix : Expr :=
  let b := Expr.add (.var orderVar) (.lit 1)
  .mul (.mul (.mul b b) (.mul b b)) (.mul b b)

/-- Compute all polynomial loop bounds except the dyadic sample width. -/
def computeParameters : Com :=
  Com.block [
    .assign blowupVar (.mul (.var orderVar) (.var orderVar)),
    .assign countLenVar (.mul (.var blowupVar) (.var blowupVar)),
    .assign tripleLenVar
      (.mul (.mul (.var blowupVar) (.var blowupVar)) (.var blowupVar)),
    .assign budgetVar (.mul (.lit 12) orderPlusOnePowSix),
    .assign sampleTargetVar
      (.mul (.lit 100) (.add (.var orderVar) (.lit 1)))]

/-- The loop computes the least $b$ with $100(n+1)<2^b$, namely
`executionSampleBits n`. -/
def computeSampleBits : Com :=
  Com.block [
    setZero sampleBitsVar,
    .assign powVar (.lit 1),
    .while (.lt (.var powVar) (.add (.var sampleTargetVar) (.lit 1)))
      (Com.block [
        increment sampleBitsVar,
        .assign powVar (.mul (.var powVar) (.lit 2))])]

/-! ### Arithmetic decoding of triples and edge slots -/

/-- Store the canonical square-table slot of the two vertex ranks in
`destination`. -/
def edgeSlotCom (left right : String) (destination : String) : Com :=
  .ite (.lt (.var left) (.var right))
    (.assign destination (.add (.mul (.var left) (.var blowupVar)) (.var right)))
    (.assign destination (.add (.mul (.var right) (.var blowupVar)) (.var left)))

/-- Decode the current mixed-radix rank into three vertex ranks and bases. -/
def decodeTripleRanks : Com :=
  Com.block [
    .assign firstVar
      (.div (.var rankVar) (.mul (.var blowupVar) (.var blowupVar))),
    .assign secondVar
      (.div (.var rankVar) (.var blowupVar)),
    .assign secondVar
      (.sub (.var secondVar)
        (.mul (.div (.var secondVar) (.var blowupVar)) (.var blowupVar))),
    .assign thirdVar
      (.sub (.var rankVar)
        (.mul (.div (.var rankVar) (.var blowupVar)) (.var blowupVar))),
    .assign firstBaseVar (.div (.var firstVar) (.var orderVar)),
    .assign secondBaseVar (.div (.var secondVar) (.var orderVar)),
    .assign thirdBaseVar (.div (.var thirdVar) (.var orderVar))]

/-- Materialize the three canonical square-table edge slots. -/
def decodeTripleEdges : Com :=
  Com.block [
    edgeSlotCom firstVar secondVar edgeOneVar,
    edgeSlotCom firstVar thirdVar edgeTwoVar,
    edgeSlotCom secondVar thirdVar edgeThreeVar]

/-- Decode the current mixed-radix triple and its three canonical edge slots. -/
def decodeTriple : Com := .seq decodeTripleRanks decodeTripleEdges

/-- Require one directed entry of the symmetrized raw graph to be true. -/
def requireRawAdjacencyDirection (leftBase rightBase : String) : Com :=
  Com.block [
    .assign rawIndexVar
      (.add (.lit 2)
        (.add (.mul (.var leftBase) (.var orderVar)) (.var rightBase))),
    readRawBit (.var rawIndexVar) tempVar,
    .ite (.eq (.var tempVar) (.lit 1)) .skip (setZero okVar)]

/-- Require one adjacency of `rawGraphCodeAt`, including looplessness and
both directed matrix entries. -/
def requireGraphAdjacency (leftBase rightBase : String) : Com :=
  .ite (.eq (.var leftBase) (.var rightBase))
    (setZero okVar)
    (Com.block [
      requireRawAdjacencyDirection leftBase rightBase,
      requireRawAdjacencyDirection rightBase leftBase])

/-- One iteration over a fair-bit block for the specified edge slot. -/
def sampleBitBody (edge : String) : Com :=
  Com.block [
    .assign rawIndexVar
      (.add (.add (.lit 2)
          (.mul (.var orderVar) (.var orderVar)))
        (.add
          (.mul
            (.add
              (.mul (.var edge) (.add (.var budgetVar) (.lit 1)))
              (.var rowVar))
            (.var sampleBitsVar))
          (.var bitVar))),
    readRawBit (.var rawIndexVar) tempVar,
    .ite (.eq (.var tempVar) (.lit 1)) .skip (setZero okVar),
    increment bitVar]

/-- Scan one complete fixed-width fair-bit block from left to right. -/
def sampleBlockLoop (edge : String) : Com :=
  .seq (setZero bitVar)
    (.while (.lt (.var bitVar) (.var sampleBitsVar))
      (sampleBitBody edge))

/-- Test the complete fair-bit block for one edge at its current counter. -/
def requireSampledEdge (edge : String) : Com :=
  Com.block [
    .assign rowVar (.get countsArray (.var edge)),
    .ite (.lt (.var rowVar) (.add (.var budgetVar) (.lit 1)))
      (sampleBlockLoop edge)
      (setZero okVar)]

/-- Test whether the current rank is a present blow-up triangle. -/
def testCurrentTriple : Com :=
  Com.block [
    decodeTriple,
    setOne okVar,
    requireGraphAdjacency firstBaseVar secondBaseVar,
    requireGraphAdjacency firstBaseVar thirdBaseVar,
    requireGraphAdjacency secondBaseVar thirdBaseVar,
    requireSampledEdge edgeOneVar,
    requireSampledEdge edgeTwoVar,
    requireSampledEdge edgeThreeVar]

/-- Save the decoded edge slots of the current first violation. -/
def rememberCurrentTriple : Com :=
  Com.block [
    setOne foundVar,
    .assign selectedVar (.var rankVar),
    .assign selectedEdgeOneVar (.var edgeOneVar),
    .assign selectedEdgeTwoVar (.var edgeTwoVar),
    .assign selectedEdgeThreeVar (.var edgeThreeVar)]

/-- One fixed-length iteration of the first-violation scan. -/
def scanTriplesBody : Com :=
  Com.block [
    .ite (.eq (.var foundVar) (.lit 0))
      (Com.block [
        testCurrentTriple,
        .ite (.eq (.var okVar) (.lit 1)) rememberCurrentTriple .skip])
      .skip,
    increment rankVar]

/-- The rank loop of a scan, including its zero initialization. -/
def scanTriplesLoop : Com :=
  .seq (setZero rankVar)
    (.while (.lt (.var rankVar) (.var tripleLenVar)) scanTriplesBody)

/-- Scan ranks in order and retain the first violation.  Once one is found the
remaining iterations are constant-time no-ops; this fixed-length loop makes the
polynomial execution bound independent of the random tape. -/
def scanTriples : Com :=
  Com.block [
    setZero foundVar,
    setZero selectedVar,
    scanTriplesLoop]

/-- Increment the selected triangle's three square-table slots, suppressing
duplicates exactly as the finite-set definition does. -/
def advanceCounters : Com :=
  Com.block [
    .ite (.eq (.var foundVar) (.lit 1))
      (Com.block [
        .store countsArray (.var selectedEdgeOneVar)
          (.add (.get countsArray (.var selectedEdgeOneVar)) (.lit 1)),
        .ite (.eq (.var selectedEdgeTwoVar) (.var selectedEdgeOneVar))
          .skip
          (.store countsArray (.var selectedEdgeTwoVar)
            (.add (.get countsArray (.var selectedEdgeTwoVar)) (.lit 1))),
        .ite (.eq (.var selectedEdgeThreeVar) (.var selectedEdgeOneVar))
          .skip
          (.ite (.eq (.var selectedEdgeThreeVar) (.var selectedEdgeTwoVar))
            .skip
            (.store countsArray (.var selectedEdgeThreeVar)
              (.add (.get countsArray (.var selectedEdgeThreeVar)) (.lit 1))))])
      .skip]

/-- Run exactly the polynomially bounded number of resampling rounds. -/
def resamplingRounds : Com :=
  .seq (setZero roundVar)
    (.while (.lt (.var roundVar) (.var budgetVar))
      (Com.block [scanTriples, advanceCounters, increment roundVar]))

/-! ### Output construction -/

/-- Decode the endpoint ranks and their canonical sampled-edge slot. -/
def outputPairPrelude : Com :=
  Com.block [
    .assign firstBaseVar (.div (.var firstVar) (.var orderVar)),
    .assign secondBaseVar (.div (.var secondVar) (.var orderVar)),
    edgeSlotCom firstVar secondVar edgeOneVar]

/-- Decode one row-major adjacency-matrix position into its endpoints. -/
def decodeOutputRanks : Com :=
  Com.block [
    .assign firstVar (.div (.var outputIndexVar) (.var blowupVar)),
    .assign secondVar
      (.sub (.var outputIndexVar)
        (.mul (.div (.var outputIndexVar) (.var blowupVar))
          (.var blowupVar)))]

/-- Decode the two endpoint ranks held in `firstVar` and `secondVar`, then
test their output adjacency against the final counter table. -/
def testOutputEdge : Com :=
  Com.block [
    outputPairPrelude,
    setOne okVar,
    requireGraphAdjacency firstBaseVar secondBaseVar,
    requireSampledEdge edgeOneVar]

/-- One adjacency-matrix output position. -/
def outputLoopBody : Com :=
  Com.block [
    decodeOutputRanks,
    .ite (.eq (.var haltedVar) (.lit 1))
      testOutputEdge (setZero okVar),
    .store graphArray (.add (.var outputIndexVar) (.lit 1)) (.var okVar),
    increment outputIndexVar]

/-- Fill every adjacency-matrix output position. -/
def outputLoop : Com :=
  .seq (setZero outputIndexVar)
    (.while (.lt (.var outputIndexVar) (.var countLenVar)) outputLoopBody)

/-- Emit the vertex count followed by the complete adjacency matrix. -/
def buildOutputGraph : Com :=
  Com.block [
    .store graphArray (.lit 0) (.var blowupVar),
    outputLoop]

/-- The reduction phases run after the input word and its order are decoded. -/
def reductionAfterDecode : Com :=
  Com.block [
    computeParameters,
    computeSampleBits,
    resamplingRounds,
    scanTriples,
    .ite (.eq (.var foundVar) (.lit 0))
      (setOne haltedVar) (setZero haltedVar),
    buildOutputGraph]

/-- The complete fixed reduction command. -/
def reductionCom : Com :=
  .seq inputPrelude (.seq decodeOrder reductionAfterDecode)

/-! ### Arithmetic facts used by the execution proof -/

lemma pow_two_lt_sampleTarget_succ_iff (n bits : ℕ) :
    2 ^ bits < 100 * (n + 1) + 1 ↔ bits < executionSampleBits n := by
  rw [executionSampleBits, Nat.log2_eq_log_two]
  constructor
  · intro h
    by_contra hnot
    have hle : Nat.log 2 (100 * (n + 1)) + 1 ≤ bits := by omega
    have hpow : 2 ^ (Nat.log 2 (100 * (n + 1)) + 1) ≤ 2 ^ bits := by
      exact Nat.pow_le_pow_right (by omega) hle
    have htarget : 100 * (n + 1) <
        2 ^ (Nat.log 2 (100 * (n + 1)) + 1) :=
      Nat.lt_pow_succ_log_self (by omega) _
    omega
  · intro h
    have hle : bits ≤ Nat.log 2 (100 * (n + 1)) := by omega
    have hpow : 2 ^ bits ≤ 2 ^ Nat.log 2 (100 * (n + 1)) :=
      Nat.pow_le_pow_right (by omega) hle
    have htarget : 2 ^ Nat.log 2 (100 * (n + 1)) ≤ 100 * (n + 1) :=
      Nat.pow_log_le_self 2 (by omega)
    omega

/-! ### Specifications of the elementary phases -/

theorem edgeSlotCom_spec (B : ℕ) (left right destination : String) :
    Spec B
      (fun σ => σ.vars left < B ∧ σ.vars right < B ∧
        σ.vars blowupVar < B ∧
        σ.vars left * σ.vars blowupVar + σ.vars right < B ∧
        σ.vars right * σ.vars blowupVar + σ.vars left < B)
      (edgeSlotCom left right destination)
      (fun σ σ' => σ'.vars destination =
        if σ.vars left < σ.vars right then
          σ.vars left * σ.vars blowupVar + σ.vars right
        else σ.vars right * σ.vars blowupVar + σ.vars left) 20 := by
  unfold edgeSlotCom
  run_vcg <;> simp_all <;> omega

end Lax47Proofs.RamReduction
