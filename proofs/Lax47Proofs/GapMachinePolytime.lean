import Lax47Proofs.GapMachineBounded
import Lax51Proofs.TuringRamPolytimeEquivalence

/-!
Polynomial resource bounds and the final verified IMP+-to-RAM-to-finite-TM
bridge for the gap function.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Lax47Proofs.GapMachine

open Lax47.Machine Lax47.Complexity Lax47.Gap
open Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.OperationalReduction
open Lax47Proofs.FiniteExecution
open Lax47Proofs.RamReductionCorrectness
open Lax47Proofs.RamReductionSemantics Lax47Proofs.Redirect
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen
open Lax13Proofs.Compile Lax13Proofs.Simulation Lax13.Ram
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open Lax51Proofs.TMToRam
open Polynomial

lemma rawOrder_le_length (input : BitString) :
    rawOrder input ≤ input.length := by
  exact min_le_right _ _

lemma inputMax_lt_two_pow (input : BitString) :
    inputMax input < 2 ^ (bitSize input + 1) := by
  induction input with
  | nil => simp [inputMax]
  | cons head tail ih =>
      have headBound := Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one
        (x := head :: tail) (a := head) (by simp)
      have hsize : bitSize tail + 1 ≤ bitSize (head :: tail) + 1 := by
        rw [Lax51Proofs.Encoding.bitSize_cons]
        omega
      have tailBound : inputMax tail <
          2 ^ (bitSize (head :: tail) + 1) :=
        ih.trans_le (Nat.pow_le_pow_right (by omega) hsize)
      simpa [inputMax] using max_lt headBound tailBound

lemma bitSize_le_two_length_of_le_one (values : BitString)
    (hvalues : ∀ value ∈ values, value ≤ 1) :
    bitSize values ≤ 2 * values.length := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : head ≤ 1 := hvalues head (by simp)
      have htail : ∀ value ∈ tail, value ≤ 1 := by
        intro value membership
        exact hvalues value (by simp [membership])
      have ih' := ih htail
      interval_cases head <;>
        simp [Lax51Proofs.Encoding.bitSize_cons] at ih' ⊢ <;> omega

lemma nat_bits_length_le_add_one (value : ℕ) :
    value.bits.length ≤ value + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact (Nat.lt_two_pow_self (n := value)).trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))

lemma graph_bits_bitSize_le {order : ℕ} (graph : GraphCode order) :
    bitSize graph.bits ≤ 6 * (order + 1) ^ 2 := by
  let matrix : BitString := List.ofFn fun rank : Fin (order * order) =>
    let vertex := finProdFinEquiv.symm rank
    bitWord (graph.adjacent vertex.1 vertex.2)
  have matrixValues : ∀ value ∈ matrix, value ≤ 1 := by
    intro value membership
    simp only [matrix, List.mem_ofFn] at membership
    obtain ⟨index, rfl⟩ := membership
    simp [bitWord]
    split <;> omega
  have matrixSize := bitSize_le_two_length_of_le_one matrix matrixValues
  have matrixLength : matrix.length = order * order := by simp [matrix]
  have matrixSize' : bitSize matrix ≤ 2 * (order * order) := by
    simpa only [matrixLength] using matrixSize
  have orderBits := nat_bits_length_le_add_one order
  change bitSize (order :: matrix) ≤ _
  rw [Lax51Proofs.Encoding.bitSize_cons]
  have hbase : 1 ≤ order + 1 := by omega
  have horder : order ≤ (order + 1) ^ 2 := by
    calc
      order ≤ order + 1 := by omega
      _ = (order + 1) ^ 1 := by simp
      _ ≤ (order + 1) ^ 2 := pow_le_pow_right' hbase (by omega)
  have hsquare : order * order ≤ (order + 1) ^ 2 := by
    simpa only [pow_two] using pow_le_pow_left' (by omega : order ≤ order + 1) 2
  have hone : 1 ≤ (order + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

lemma reduction_graph_bitSize_le (input : BitString) :
    bitSize (rawReductionGraphBits input) ≤
      30 * (bitSize input + 1) ^ 4 := by
  let n := rawOrder input
  let target := executionOutput (rawGraphCodeAt n input)
    (executionSeedOfFlat (rawFlatSeedAt n input))
  have htarget := graph_bits_bitSize_le target
  have hn : n ≤ bitSize input :=
    (rawOrder_le_length input).trans
      (Lax51Proofs.Encoding.length_le_bitSize input)
  have hbase : n + 1 ≤ bitSize input + 1 := by omega
  have hpow : (n + 1) ^ 4 ≤ (bitSize input + 1) ^ 4 :=
    pow_le_pow_left' hbase 4
  change bitSize target.bits ≤ _
  have horder : n * n + 1 ≤ 2 * (n + 1) ^ 2 := by nlinarith
  calc
    bitSize target.bits ≤ 6 * (n * n + 1) ^ 2 := htarget
    _ ≤ 6 * (2 * (n + 1) ^ 2) ^ 2 := by gcongr
    _ = 24 * (n + 1) ^ 4 := by ring
    _ ≤ 24 * (bitSize input + 1) ^ 4 := by gcongr
    _ ≤ 30 * (bitSize input + 1) ^ 4 := by omega

/-- Coarse polynomial bound for the cost certified by the reduction's IMP+
semantics. -/
lemma reductionCostBound_polynomial (inputLength n size : ℕ)
    (hinput : inputLength ≤ size) (hn : n ≤ size) :
    reductionCostBound inputLength n ≤
      1000000 * (size + 1) ^ 20 := by
  let x := size + 1
  have hx : 1 ≤ x := by omega
  have hnx : n + 1 ≤ x := by omega
  have hsample : executionSampleBits n ≤ 101 * x := by
    exact (sampleBits_le_linear n).trans (Nat.mul_le_mul_left 101 hnx)
  have hbudget : executionBudget n ≤ 12 * x ^ 6 := by
    unfold executionBudget
    exact Nat.mul_le_mul_left 12 (pow_le_pow_left' hnx 6)
  have htriple : (n * n) * (n * n) * (n * n) ≤ x ^ 6 := by
    calc
      (n * n) * (n * n) * (n * n) = n ^ 6 := by ring
      _ ≤ x ^ 6 := pow_le_pow_left' (by omega : n ≤ x) 6
  have hcount : (n * n) * (n * n) ≤ x ^ 4 := by
    calc
      (n * n) * (n * n) = n ^ 4 := by ring
      _ ≤ x ^ 4 := pow_le_pow_left' (by omega : n ≤ x) 4
  let testCost := 2000 + 3 * ((200 + 4) * executionSampleBits n + 100)
  have htest : testCost ≤ 65000 * x := by
    dsimp [testCost]
    nlinarith
  let scanBodyCost := testCost + 200
  let scanCost := (scanBodyCost + 4) *
    ((n * n) * (n * n) * (n * n)) + 100
  have hscanFactor : scanBodyCost + 4 ≤ 65204 * x := by
    dsimp [scanBodyCost]
    nlinarith
  have hscan : scanCost ≤ 66000 * x ^ 7 := by
    calc
      scanCost ≤ (65204 * x) * x ^ 6 + 100 := by
        dsimp only [scanCost]
        gcongr
      _ = 65204 * x ^ 7 + 100 := by ring
      _ ≤ 66000 * x ^ 7 := by
        have hone : 1 ≤ x ^ 7 := Nat.one_le_pow _ _ hx
        nlinarith
  let roundCost := scanCost + 450
  let roundsCost := (roundCost + 4) * executionBudget n + 100
  have hroundFactor : roundCost + 4 ≤ 66500 * x ^ 7 := by
    dsimp [roundCost]
    have hone : 1 ≤ x ^ 7 := Nat.one_le_pow _ _ hx
    nlinarith
  have hrounds : roundsCost ≤ 800000 * x ^ 13 := by
    calc
      roundsCost ≤ (66500 * x ^ 7) * (12 * x ^ 6) + 100 := by
        dsimp only [roundsCost]
        gcongr
      _ = 798000 * x ^ 13 + 100 := by ring
      _ ≤ 800000 * x ^ 13 := by
        have hone : 1 ≤ x ^ 13 := Nat.one_le_pow _ _ hx
        nlinarith
  let outputBodyCost := 1000 + ((200 + 4) * executionSampleBits n + 100)
  let outputCost := (outputBodyCost + 4) * ((n * n) * (n * n)) + 100
  have houtputFactor : outputBodyCost + 4 ≤ 22000 * x := by
    dsimp [outputBodyCost]
    nlinarith
  have houtput : outputCost ≤ 23000 * x ^ 5 := by
    calc
      outputCost ≤ (22000 * x) * x ^ 4 + 100 := by
        dsimp only [outputCost]
        gcongr
      _ = 22000 * x ^ 5 + 100 := by ring
      _ ≤ 23000 * x ^ 5 := by
        have hone : 1 ≤ x ^ 5 := Nat.one_le_pow _ _ hx
        nlinarith
  let sampleComputeCost := 30 * (executionSampleBits n + 1) + 20
  have hsampleCompute : sampleComputeCost ≤ 3100 * x := by
    dsimp [sampleComputeCost]
    nlinarith
  let preludeCost := 1 + 12 * inputLength + 7
  have hprelude : preludeCost ≤ 20 * x := by
    dsimp [preludeCost, x]
    omega
  have hx1 : x ≤ x ^ 20 := by
    simpa only [pow_one] using pow_le_pow_right' hx (by omega : 1 ≤ 20)
  have hx5 : x ^ 5 ≤ x ^ 20 := pow_le_pow_right' hx (by omega)
  have hx7 : x ^ 7 ≤ x ^ 20 := pow_le_pow_right' hx (by omega)
  have hx13 : x ^ 13 ≤ x ^ 20 := pow_le_pow_right' hx (by omega)
  have hx20one : 1 ≤ x ^ 20 := Nat.one_le_pow _ _ hx
  dsimp [reductionCostBound]
  change preludeCost + 40 + 100 + sampleComputeCost + roundsCost +
    scanCost + 20 + outputCost + 100 ≤ 1000000 * x ^ 20
  nlinarith

/-- Polynomial upper bound for the bit-size of a generated reduction graph. -/
noncomputable def graphSizePolynomial : Polynomial ℕ :=
  C 30 * (X + C 1) ^ 4

@[simp] lemma graphSizePolynomial_eval (size : ℕ) :
    graphSizePolynomial.eval size = 30 * (size + 1) ^ 4 := by
  simp [graphSizePolynomial]

/-- Lax51's native approximation cost, with its input-size polynomial
composed with the polynomial size of the generated graph. -/
noncomputable def approximationCostPolynomial {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : Polynomial ℕ :=
  let H := approximationWitness algorithm
  let tm := H.tm
  let guardCost := 1 + Cond.size (.lt (.lit 0) (.var labelVar))
  let coreCoeff := guardCost + maxCost (FinTM2.compileDispatcher tm 0).com
  let push := FinTM2.machinePushBudget tm tm.k₁
  let constantCost := 22 +
    initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
    guardCost + 19 + 1
  (C constantCost + C 99 * X + C (coreCoeff + 29 * push) * H.time).comp
    graphSizePolynomial

theorem approximationNativeCost_polynomial {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString) :
    approximationNativeCost algorithm (rawReductionGraphBits input)
        (algorithm.program.output (rawReductionGraphBits input)) ≤
      (approximationCostPolynomial algorithm).eval (bitSize input) := by
  let H := approximationWitness algorithm
  let tm := H.tm
  let graphBits := rawReductionGraphBits input
  let outputBits := algorithm.program.output graphBits
  let graphSize := bitSize graphBits
  let guardCost := 1 + Cond.size (.lt (.lit 0) (.var labelVar))
  let coreCoeff := guardCost + maxCost (FinTM2.compileDispatcher tm 0).com
  let push := FinTM2.machinePushBudget tm tm.k₁
  let constantCost := 22 +
    initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
    guardCost + 19 + 1
  let sourcePolynomial : Polynomial ℕ :=
    C constantCost + C 99 * X + C (coreCoeff + 29 * push) * H.time
  have outputSize : bitSize outputBits ≤
      graphSize + H.time.eval graphSize * push := by
    have run := H.outputsFun graphBits
    have bound := FinTM2.output_length_le_of_outputsInTime tm
      (List.map H.inputAlphabet.invFun (encode graphBits))
      (List.map H.outputAlphabet.invFun (encode outputBits))
      (H.time.eval graphSize) run
    simpa [graphSize, outputBits, graphBits, bitSize, push] using bound
  have inputCost := encodeInputLoopCost_le graphBits
  have sourceBound : approximationNativeCost algorithm graphBits outputBits ≤
      sourcePolynomial.eval graphSize := by
    simp [approximationNativeCost, H, tm, sourcePolynomial, constantCost,
      coreCoeff, guardCost]
    dsimp [graphSize] at inputCost outputSize ⊢
    nlinarith
  have graphBound : graphSize ≤ graphSizePolynomial.eval (bitSize input) := by
    simpa [graphSize, graphBits] using reduction_graph_bitSize_le input
  have monotone := Lax51Proofs.RamToTM.polynomial_eval_mono
    sourcePolynomial graphBound
  calc
    approximationNativeCost algorithm (rawReductionGraphBits input)
          (algorithm.program.output (rawReductionGraphBits input)) =
        approximationNativeCost algorithm graphBits outputBits := by rfl
    _ ≤ sourcePolynomial.eval graphSize := sourceBound
    _ ≤ sourcePolynomial.eval (graphSizePolynomial.eval (bitSize input)) :=
      monotone
    _ = (approximationCostPolynomial algorithm).eval (bitSize input) := by
      dsimp [approximationCostPolynomial, sourcePolynomial, H, tm,
        constantCost, coreCoeff, guardCost, push]
      simp [Polynomial.eval_comp]

/-- A polynomial bounding the exact IMP+ cost of the complete gap program. -/
noncomputable def gapTimePolynomial (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : Polynomial ℕ :=
  C 12 * X + C 200 + C 1000000 * (X + C 1) ^ 20 +
    C 20 * approximationCostPolynomial algorithm +
    C 40 * (X + C 1) ^ 2 + C (10 * (q + 5) + 100)

theorem gapCom_cost_polynomial (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString) :
    ∃ ext final cost,
      BigStep (gapCom q algorithm) (initEnv ext (input.length :: input))
        final cost ∧ final.out = gapFunction q algorithm input ∧
      cost ≤ (gapTimePolynomial q algorithm).eval (bitSize input) := by
  obtain ⟨ext, final, cost, run, output, costBound⟩ :=
    gapCom_bigStep q algorithm input
  have hlength := Lax51Proofs.Encoding.length_le_bitSize input
  have horder : rawOrder input ≤ bitSize input :=
    (rawOrder_le_length input).trans hlength
  have hreduction := reductionCostBound_polynomial input.length
    (rawOrder input) (bitSize input) hlength horder
  have hnative := approximationNativeCost_polynomial algorithm input
  have hsquare : rawOrder input * rawOrder input ≤
      (bitSize input + 1) ^ 2 := by
    calc
      rawOrder input * rawOrder input = rawOrder input ^ 2 := by ring
      _ ≤ bitSize input ^ 2 := pow_le_pow_left' horder 2
      _ ≤ (bitSize input + 1) ^ 2 :=
        pow_le_pow_left' (by omega : bitSize input ≤ bitSize input + 1) 2
  refine ⟨ext, final, cost, run, output, ?_⟩
  simp [gapTimePolynomial]
  omega

/-- Polynomial exponent sufficient for all values produced by the reduction
before the native approximation phase. -/
noncomputable def reductionWordPolynomial : Polynomial ℕ :=
  X + C 4 + C 2000000 * (X + C 1) ^ 20

@[simp] lemma reductionWordPolynomial_eval (size : ℕ) :
    reductionWordPolynomial.eval size =
      size + 4 + 2000000 * (size + 1) ^ 20 := by
  simp [reductionWordPolynomial]

lemma input_getD_one_lt_two_pow (input : BitString) :
    input.getD 1 0 < 2 ^ (bitSize input + 1) := by
  by_cases hindex : 1 < input.length
  · rw [List.getD_eq_getElem input 0 hindex]
    exact Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one
      (List.getElem_mem hindex)
  · rw [List.getD_eq_default input 0 (by omega : input.length ≤ 1)]
    positivity

lemma reductionValueBound_le_two_pow (input : BitString) :
    reductionValueBound input (rawOrder input) ≤
      2 ^ (reductionWordPolynomial.eval (bitSize input)) := by
  let size := bitSize input
  let n := rawOrder input
  let x := size + 1
  let poly := 2000000 * x ^ 20
  let inputPower := 2 ^ (size + 1)
  have hx : 1 ≤ x := by omega
  have hn : n ≤ size :=
    (rawOrder_le_length input).trans
      (Lax51Proofs.Encoding.length_le_bitSize input)
  have hnx : n + 1 ≤ x := by omega
  have hflat : flatRandomBitCount n ≤ 1400 * x ^ 12 := by
    exact (flatRandomBitCount_polynomial n).trans
      (Nat.mul_le_mul_left 1400 (pow_le_pow_left' hnx 12))
  have hsample : executionSampleBits n ≤ 101 * x := by
    exact (sampleBits_le_linear n).trans (Nat.mul_le_mul_left 101 hnx)
  have hbudget : executionBudget n + 1 ≤ 13 * x ^ 6 := by
    unfold executionBudget
    have hpow := pow_le_pow_left' hnx 6
    have hone : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ hx
    nlinarith
  have hn2 : n * n ≤ x ^ 2 := by
    calc
      n * n = n ^ 2 := by ring
      _ ≤ x ^ 2 := pow_le_pow_left' (by omega : n ≤ x) 2
  have hn4 : (n * n) * (n * n) ≤ x ^ 4 := by
    calc
      (n * n) * (n * n) = n ^ 4 := by ring
      _ ≤ x ^ 4 := pow_le_pow_left' (by omega : n ≤ x) 4
  have hn6 : (n * n) * (n * n) * (n * n) ≤ x ^ 6 := by
    calc
      (n * n) * (n * n) * (n * n) = n ^ 6 := by ring
      _ ≤ x ^ 6 := pow_le_pow_left' (by omega : n ≤ x) 6
  have hx1 : x ≤ x ^ 20 := by
    simpa only [pow_one] using pow_le_pow_right' hx (by omega : 1 ≤ 20)
  have hx2 : x ^ 2 ≤ x ^ 20 := pow_le_pow_right' hx (by omega)
  have hx4 : x ^ 4 ≤ x ^ 20 := pow_le_pow_right' hx (by omega)
  have hx6 : x ^ 6 ≤ x ^ 20 := pow_le_pow_right' hx (by omega)
  have hx12 : x ^ 12 ≤ x ^ 20 := pow_le_pow_right' hx (by omega)
  have hx20one : 1 ≤ x ^ 20 := Nat.one_le_pow _ _ hx
  let rest := 1 +
    (2 + n * n + flatRandomBitCount n) +
    ((n * n) * (n * n) * (n * n) + 1) +
    (executionBudget n + 1) + executionSampleBits n +
    ((n * n) * (n * n)) +
    (2 * (100 * (n + 1) + 1)) +
    (12 * (n + 1) ^ 6) + (executionSampleBits n + 1)
  have hrest : rest ≤ poly := by
    dsimp [rest, poly]
    have hpowSix := pow_le_pow_left' hnx 6
    nlinarith
  have hmax : inputMax input ≤ inputPower := by
    exact Nat.le_of_lt (by simpa [inputPower, size] using inputMax_lt_two_pow input)
  have hlength : input.length ≤ inputPower := by
    have := Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one input
    exact Nat.le_of_lt (by simpa [inputPower, size] using this)
  have hclaimed : input.getD 1 0 ≤ inputPower := by
    exact Nat.le_of_lt (by simpa [inputPower, size] using
      input_getD_one_lt_two_pow input)
  have hvalue : reductionValueBound input n ≤ 3 * inputPower + poly := by
    change 1 + inputMax input + input.length + input.getD 1 0 +
      (2 + n * n + flatRandomBitCount n) +
      ((n * n) * (n * n) * (n * n) + 1) +
      (executionBudget n + 1) + executionSampleBits n +
      ((n * n) * (n * n)) +
      (2 * (100 * (n + 1) + 1)) +
      (12 * (n + 1) ^ 6) + (executionSampleBits n + 1) ≤ _
    dsimp [rest] at hrest
    omega
  let commonPower := 2 ^ (size + poly + 2)
  have hinputPower : inputPower ≤ commonPower := by
    apply Nat.pow_le_pow_right (by omega)
    dsimp [inputPower, commonPower]
    omega
  have hpolyPower : poly ≤ commonPower := by
    have hself : poly ≤ 2 ^ poly :=
      Nat.le_of_lt (Nat.lt_two_pow_self (n := poly))
    have hexponent : poly ≤ size + poly + 2 := by omega
    exact hself.trans (by
      simpa [commonPower] using Nat.pow_le_pow_right (by omega) hexponent)
  calc
    reductionValueBound input (rawOrder input) =
        reductionValueBound input n := by rfl
    _ ≤ 3 * inputPower + poly := hvalue
    _ ≤ 4 * commonPower := by omega
    _ = 2 ^ (size + poly + 4) := by
      dsimp [commonPower]
      rw [show size + poly + 4 = (size + poly + 2) + 2 by omega,
        pow_add]
      norm_num
      ring_nf
    _ = 2 ^ (reductionWordPolynomial.eval (bitSize input)) := by
      congr 1
      simp [size, poly, x]
      omega

/-- Polynomial word exponent for the complete composed command. -/
noncomputable def gapWordPolynomial (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : Polynomial ℕ :=
  reductionWordPolynomial +
    C (redirectedApproximationGrowth algorithm) * gapTimePolynomial q algorithm +
    C countGrowth * gapTimePolynomial q algorithm +
    C (2 * q + 10) * (X + C 1) + C 10

@[simp] lemma gapWordPolynomial_eval (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (size : ℕ) :
    (gapWordPolynomial q algorithm).eval size =
      reductionWordPolynomial.eval size +
        redirectedApproximationGrowth algorithm *
          (gapTimePolynomial q algorithm).eval size +
        countGrowth * (gapTimePolynomial q algorithm).eval size +
        (2 * q + 10) * (size + 1) + 10 := by
  simp [gapWordPolynomial]

/-- Bounded end-to-end execution on the positive-order branch. -/
theorem gapCom_positive_bigStepB (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString)
    (hn : 0 < rawOrder input) :
    let exponent := (gapWordPolynomial q algorithm).eval (bitSize input)
    ∃ ext final cost,
      BigStepB (2 ^ exponent) (gapCom q algorithm)
        (initEnv ext (input.length :: input)) final cost ∧
      final.out = gapFunction q algorithm input ∧
      cost ≤ (gapTimePolynomial q algorithm).eval (bitSize input) := by
  dsimp only
  let n := rawOrder input
  let graph := rawGraphCodeAt n input
  let flatSeed := rawFlatSeedAt n input
  let target := executionOutput graph (executionSeedOfFlat flatSeed)
  let outputBits := algorithm.program.output target.bits
  let size := bitSize input
  let baseExponent := reductionWordPolynomial.eval size
  let timeBound := (gapTimePolynomial q algorithm).eval size
  let exponent := (gapWordPolynomial q algorithm).eval size
  obtain ⟨sourceExt, sourceFinal, sourceCost, sourceRun, sourceOut,
    sourceCostBound⟩ := approximationNativeCom_bigStep algorithm target.bits
  let capacity := outputBits.length + n * n
  let ext := combinedExt sourceExt input ((n * n) * (n * n))
    target.bits.length capacity
  obtain ⟨afterReduction, reductionCost, reductionBounded,
      reductionContext, reductionGraph, reductionCostLe⟩ :=
    reductionCom_raw_bigStepB sourceExt input n (by simpa [n] using hn)
      (by rfl) capacity
  have reductionValueLe : reductionValueBound input n ≤ 2 ^ baseExponent := by
    simpa [n, baseExponent, size] using reductionValueBound_le_two_pow input
  have reductionAtBase := bigStepBMono reductionValueLe reductionBounded
  change BigStepB (2 ^ baseExponent)
    (.seq inputPrelude (.seq decodeOrder reductionAfterDecode))
    (initEnv ext (input.length :: input)) afterReduction reductionCost at reductionAtBase
  cases reductionAtBase with
  | seq preludeBounded decodedBounded =>
    cases decodedBounded with
    | seq decodeBounded reductionTailBounded =>
      rename_i afterPrelude preludeCost afterDecode decodeCost reductionTailCost
      have preludeRun := preludeBounded.bigStep
      have decodeRun := decodeBounded.bigStep
      have reductionTailRun := reductionTailBounded.bigStep
      have wholeReductionRun : BigStep reductionCom
          (initEnv ext (input.length :: input)) afterReduction
          (preludeCost + (decodeCost + reductionTailCost)) := by
        simpa [reductionCom] using BigStep.seq preludeRun
          (BigStep.seq decodeRun reductionTailRun)
      have initialRelation : Rel target.bits capacity
          (initEnv sourceExt (target.bits.length :: target.bits))
          afterReduction := by
        constructor
        · intro name
          rw [wholeReductionRun.vars_eq
            (algorithmName_not_mem_reduction_wvars name)]
          simp [initEnv]
        · intro name
          rw [wholeReductionRun.arrs_eq
            (algorithmName_not_mem_reduction_warrs name)]
          simp [initEnv, ext, combinedExt_algorithmName]
        · have hcursor : afterReduction.vars inputCursor = 0 := by
            rw [wholeReductionRun.vars_eq (by decide)]
            simp [initEnv]
          simp [hcursor, virtualInput]
        · have hcursor : afterReduction.vars inputCursor = 0 := by
            rw [wholeReductionRun.vars_eq (by decide)]
            simp [initEnv]
          simp [initEnv, virtualInput, hcursor]
        · simp [initEnv, capacity]
        · have hcursor : afterReduction.vars outputCursor = 0 := by
            rw [wholeReductionRun.vars_eq (by decide)]
            simp [initEnv]
          simp [initEnv, hcursor]
        · have harray : afterReduction.arrs algorithmOutputArray =
              List.replicate capacity 0 := by
            rw [wholeReductionRun.arrs_eq (by decide)]
            simp [initEnv, ext]
          simpa [initEnv, harray]
        · exact reductionGraph
        · have hcount := reductionContext.2.1.2.2.1
          rw [hcount, graphCode_bits_length]
          omega
      have sourceCapacity : sourceFinal.out.length ≤ capacity := by
        rw [sourceOut]
        simp [outputBits, capacity]
      obtain ⟨afterAlgorithm, redirectedCost, redirectedRun,
          redirectedRelation, redirectedCostBound⟩ :=
        redirectCom_bigStep sourceRun initialRelation sourceCapacity
      have redirectedBlowup : afterAlgorithm.vars blowupVar = n * n := by
        rw [redirectCom_var_eq redirectedRun blowupVar (by decide)
          (by decide) (by decide)]
        exact reductionContext.2.1.2.1
      have redirectedOrder : afterAlgorithm.vars orderVar = n := by
        rw [redirectCom_var_eq redirectedRun orderVar (by decide)
          (by decide) (by decide)]
        exact reductionContext.2.1.1
      have redirectedArray : afterAlgorithm.arrs algorithmOutputArray =
          outputBits ++ List.replicate (n * n) 0 := by
        rw [redirectedRelation.output_array, sourceOut]
        simp [outputBits, capacity]
      have reductionOut : afterReduction.out = [] := by
        simpa [initEnv] using wholeReductionRun.out_eq
          (show reductionCom.NoWrite by decide)
      have redirectedOut : afterAlgorithm.out = [] := by
        rw [redirectedRun.out_eq (redirectCom_noWrite _)]
        exact reductionOut
      obtain ⟨afterCount, countCost, countRun, countCard, _countIndex,
          _countArray, countCostBound⟩ :=
        countAlgorithmOutput_bigStep outputBits (n * n) afterAlgorithm
          redirectedBlowup redirectedArray
      have countOrder : afterCount.vars orderVar = n := by
        rw [countRun.vars_eq (by decide)]
        exact redirectedOrder
      have countOut : afterCount.out = [] := by
        rw [countRun.out_eq (by decide)]
        exact redirectedOut
      let card := (decodeVertexSet (n * n) outputBits).card
      have countCardDecoded : afterCount.vars outputCardVar = card := by
        dsimp only [card]
        rw [countCard, oneCount_eq_decodeVertexSet_card]
      have initialBits := initEnv_bitBounded ext input
      have baseLarge : size + 1 ≤ baseExponent := by
        simp [size, baseExponent]
        omega
      have initialAtBase : EnvBitBounded
          (initEnv ext (input.length :: input)) baseExponent :=
        initialBits.mono (by simpa [size] using baseLarge)
      have wholeReductionBounded : BigStepB (2 ^ baseExponent) reductionCom
          (initEnv ext (input.length :: input)) afterReduction
          (preludeCost + (decodeCost + reductionTailCost)) := by
        simpa [reductionCom] using BigStepB.seq preludeBounded
          (BigStepB.seq decodeBounded reductionTailBounded)
      have reductionStateBounded : EnvBitBounded afterReduction baseExponent :=
        BigStepB.envBitBounded wholeReductionBounded le_rfl initialAtBase
      obtain ⟨redirectedBounded, algorithmStateBounded⟩ :=
        bigStepBigStepBOfBitGrowth redirectedRun reductionStateBounded
          (redirectedApproximation_bitGrowth algorithm) le_rfl
      let algorithmExponent := baseExponent + redirectedCost *
        redirectedApproximationGrowth algorithm
      have algorithmStateBounded' : EnvBitBounded afterAlgorithm
          algorithmExponent := by
        simpa [algorithmExponent] using algorithmStateBounded
      obtain ⟨countBounded, countStateBounded⟩ :=
        bigStepBigStepBOfBitGrowth countRun algorithmStateBounded'
          countAlgorithmOutput_bitGrowth le_rfl
      let countExponent := algorithmExponent + countCost * countGrowth
      have sourceCostBound' : sourceCost ≤
          approximationNativeCost algorithm target.bits outputBits := by
        simpa [outputBits] using sourceCostBound
      have targetRaw : target.bits = rawReductionGraphBits input := by rfl
      have nativePolynomial : approximationNativeCost algorithm target.bits
          outputBits ≤ (approximationCostPolynomial algorithm).eval size := by
        rw [targetRaw]
        simpa [outputBits, size] using
          approximationNativeCost_polynomial algorithm input
      have redirectTime : redirectedCost ≤ timeBound := by
        have nativePart : 20 * (approximationCostPolynomial algorithm).eval size ≤
            timeBound := by
          simp [timeBound, gapTimePolynomial]
          omega
        exact redirectedCostBound.trans
          (Nat.mul_le_mul_left 20 sourceCostBound' |>.trans
            ((Nat.mul_le_mul_left 20 nativePolynomial).trans nativePart))
      have countTime : countCost ≤ timeBound := by
        have horderSize : n ≤ size :=
          (rawOrder_le_length input).trans
            (Lax51Proofs.Encoding.length_le_bitSize input)
        have hsquare : n * n ≤ (size + 1) ^ 2 := by
          calc
            n * n = n ^ 2 := by ring
            _ ≤ size ^ 2 := pow_le_pow_left' horderSize 2
            _ ≤ (size + 1) ^ 2 := pow_le_pow_left'
              (by omega : size ≤ size + 1) 2
        have countPart : 40 * (size + 1) ^ 2 + 30 ≤ timeBound := by
          simp [timeBound, gapTimePolynomial]
          omega
        exact countCostBound.trans ((Nat.add_le_add_right
          (Nat.mul_le_mul_left 40 hsquare) 30).trans countPart)
      have exponentFormula : exponent = baseExponent +
          redirectedApproximationGrowth algorithm * timeBound +
          countGrowth * timeBound + (2 * q + 10) * (size + 1) + 10 := by
        simp [exponent, baseExponent, timeBound, size]
      have algorithmExponentLe : algorithmExponent ≤ exponent := by
        have hredirect : redirectedCost * redirectedApproximationGrowth algorithm ≤
            redirectedApproximationGrowth algorithm * timeBound := by
          calc
            redirectedCost * redirectedApproximationGrowth algorithm ≤
                timeBound * redirectedApproximationGrowth algorithm :=
              Nat.mul_le_mul_right _ redirectTime
            _ = redirectedApproximationGrowth algorithm * timeBound :=
              Nat.mul_comm _ _
        rw [exponentFormula]
        dsimp [algorithmExponent]
        omega
      have countExponentLe : countExponent ≤ exponent := by
        have hredirect : redirectedCost * redirectedApproximationGrowth algorithm ≤
            redirectedApproximationGrowth algorithm * timeBound := by
          calc
            redirectedCost * redirectedApproximationGrowth algorithm ≤
                timeBound * redirectedApproximationGrowth algorithm :=
              Nat.mul_le_mul_right _ redirectTime
            _ = redirectedApproximationGrowth algorithm * timeBound :=
              Nat.mul_comm _ _
        have hcount : countCost * countGrowth ≤ countGrowth * timeBound := by
          calc
            countCost * countGrowth ≤ timeBound * countGrowth :=
              Nat.mul_le_mul_right _ countTime
            _ = countGrowth * timeBound := Nat.mul_comm _ _
        rw [exponentFormula]
        dsimp [countExponent, algorithmExponent]
        omega
      have nSize : n < 2 ^ (size + 1) := by
        have nle : n ≤ size :=
          (rawOrder_le_length input).trans
            (Lax51Proofs.Encoding.length_le_bitSize input)
        exact nle.trans_lt (size.lt_two_pow_self.trans_le
          (Nat.pow_le_pow_right (by omega) (by omega)))
      have cardLe : card ≤ n * n := by
        dsimp [card]
        simpa using Finset.card_le_card
          (Finset.subset_univ (decodeVertexSet (n * n) outputBits))
      have cardPowerBase : card ≤ 2 ^ (2 * (size + 1)) := by
        have nle := Nat.le_of_lt nSize
        calc
          card ≤ n * n := cardLe
          _ ≤ 2 ^ (size + 1) * 2 ^ (size + 1) :=
            Nat.mul_le_mul nle nle
          _ = 2 ^ (2 * (size + 1)) := by rw [← pow_add]; congr 1 <;> omega
      have leftPowers : ∀ power ≤ q + 3, n ^ power < 2 ^ exponent := by
        intro power hpower
        have hpow : n ^ power ≤ 2 ^ ((size + 1) * power) := by
          calc
            n ^ power ≤ (2 ^ (size + 1)) ^ power :=
              pow_le_pow_left' (Nat.le_of_lt nSize) power
            _ = 2 ^ ((size + 1) * power) := by rw [← pow_mul]
        have hexp : (size + 1) * power < exponent := by
          rw [exponentFormula]
          nlinarith
        exact hpow.trans_lt (Nat.pow_lt_pow_right (by omega) hexp)
      have rightPowers : ∀ power ≤ q, card ^ power < 2 ^ exponent := by
        intro power hpower
        have hpow : card ^ power ≤ 2 ^ ((2 * (size + 1)) * power) := by
          calc
            card ^ power ≤ (2 ^ (2 * (size + 1))) ^ power :=
              pow_le_pow_left' cardPowerBase power
            _ = 2 ^ ((2 * (size + 1)) * power) := by rw [← pow_mul]
        have hexp : (2 * (size + 1)) * power < exponent := by
          rw [exponentFormula]
          nlinarith
        exact hpow.trans_lt (Nat.pow_lt_pow_right (by omega) hexp)
      have exponentPositive : 0 < exponent := by
        rw [exponentFormula]
        omega
      have nGlobal : n < 2 ^ exponent := by
        simpa using leftPowers 1 (by omega)
      have cardGlobal : card < 2 ^ exponent := by
        have hexp : 2 * (size + 1) < exponent := by
          rw [exponentFormula]
          nlinarith
        exact cardPowerBase.trans_lt
          (Nat.pow_lt_pow_right (by omega) hexp)
      obtain ⟨final, decisionCost, decisionBounded, decisionOut,
          decisionCostBound⟩ := writeGapDecision_bigStepB (2 ^ exponent)
        q n card afterCount countOrder countCardDecoded countOut
        nGlobal cardGlobal leftPowers rightPowers
        (by positivity) (Nat.one_lt_two_pow exponentPositive.ne')
      have baseExponentLe : baseExponent ≤ exponent := by
        rw [exponentFormula]
        omega
      have preludeGlobal := bigStepBMono
        (Nat.pow_le_pow_right (by omega) baseExponentLe) preludeBounded
      have decodeGlobal := bigStepBMono
        (Nat.pow_le_pow_right (by omega) baseExponentLe) decodeBounded
      have tailGlobal := bigStepBMono
        (Nat.pow_le_pow_right (by omega) (by
          rw [exponentFormula]
          omega : baseExponent ≤ exponent)) reductionTailBounded
      have redirectGlobal := bigStepBMono
        (Nat.pow_le_pow_right (by omega) algorithmExponentLe) redirectedBounded
      have countGlobal := bigStepBMono
        (Nat.pow_le_pow_right (by omega) countExponentLe) countBounded
      have positiveBounded : BigStepB (2 ^ exponent)
          (positiveGapCom q algorithm) afterDecode final
          (reductionTailCost +
            (redirectedCost + (countCost + (decisionCost + 1)))) := by
        simpa [positiveGapCom, Com.block] using
          BigStepB.seq tailGlobal
            (BigStepB.seq redirectGlobal
              (BigStepB.seq countGlobal
                (BigStepB.seq decisionBounded BigStepB.skip)))
      have decodeOrderValue : afterDecode.vars orderVar = n := by
        rw [← reductionTailRun.vars_eq (by decide)]
        exact reductionContext.2.1.1
      have conditionFalse :
          (Cond.eq (.var orderVar) (.lit 0)).evalB
            (2 ^ exponent) afterDecode = some false := by
        have orderEval : (Expr.var orderVar).evalB (2 ^ exponent)
            afterDecode = some n := by
          rw [Expr.evalB, decodeOrderValue]
          exact fit_self nGlobal
        have zeroEval : (Expr.lit 0).evalB (2 ^ exponent)
            afterDecode = some 0 := by
          exact fit_self (by positivity)
        rw [Cond.evalB, orderEval, zeroEval]
        simp
        omega
      let totalCost := preludeCost + (decodeCost +
        (1 + (Cond.eq (.var orderVar) (.lit 0)).size +
          (reductionTailCost +
            (redirectedCost + (countCost + (decisionCost + 1))))))
      have wholeBounded : BigStepB (2 ^ exponent) (gapCom q algorithm)
          (initEnv ext (input.length :: input)) final totalCost := by
        dsimp only [totalCost]
        exact BigStepB.seq preludeGlobal (BigStepB.seq decodeGlobal
          (BigStepB.ite_false conditionFalse positiveBounded))
      have totalTime : totalCost ≤ timeBound := by
        have hlength := Lax51Proofs.Encoding.length_le_bitSize input
        have horderSize : n ≤ size :=
          (rawOrder_le_length input).trans hlength
        have redPoly := reductionCostBound_polynomial input.length n size
          hlength horderSize
        have nativePoly := nativePolynomial
        have hsquare : n * n ≤ (size + 1) ^ 2 := by
          calc
            n * n = n ^ 2 := by ring
            _ ≤ size ^ 2 := pow_le_pow_left' horderSize 2
            _ ≤ (size + 1) ^ 2 := pow_le_pow_left'
              (by omega : size ≤ size + 1) 2
        have localCost : totalCost ≤ reductionCostBound input.length n +
            20 * approximationNativeCost algorithm target.bits outputBits +
            40 * (n * n) + 10 * (q + 5) + 100 := by
          dsimp only [totalCost]
          simp only [Cond.size, Expr.size]
          omega
        apply localCost.trans
        simp [timeBound, gapTimePolynomial]
        omega
      refine ⟨ext, final, totalCost, wholeBounded, ?_, totalTime⟩
      simpa [gapFunction, n, graph, flatSeed, target, outputBits,
        show n ≠ 0 by omega] using decisionOut

/-- Bounded end-to-end execution on the zero-order cutoff branch. -/
theorem gapCom_zero_bigStepB (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString)
    (hzero : rawOrder input = 0) :
    let exponent := (gapWordPolynomial q algorithm).eval (bitSize input)
    ∃ ext final cost,
      BigStepB (2 ^ exponent) (gapCom q algorithm)
        (initEnv ext (input.length :: input)) final cost ∧
      final.out = gapFunction q algorithm input ∧
      cost ≤ (gapTimePolynomial q algorithm).eval (bitSize input) := by
  dsimp only
  let ext := combinedExt (fun _ => 0) input 0 0 0
  let B := reductionValueBound input 0
  let exponent := (gapWordPolynomial q algorithm).eval (bitSize input)
  have hB : 1 < B := by
    dsimp [B, reductionValueBound]
    omega
  have hvalue (value : ℕ) (membership : value ∈ input) : value < B := by
    have hmax := mem_le_inputMax membership
    dsimp [B, reductionValueBound]
    omega
  have hpreludeBase := readScalarsThenArr_spec B ext [rawLenVar]
    rawArray loadIndexVar rawLenVar RamReduction.tempVar [input.length] input
    (by simp) (by simp) (by simp) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp [ext])
    (by dsimp [B, reductionValueBound]; omega) hvalue
  have hprelude : Spec B
      (fun state => state = initEnv ext (input.length :: input)) inputPrelude
      (fun _ final => ScalarsArrIn ext [rawLenVar] rawArray loadIndexVar
        RamReduction.tempVar [input.length] input final)
      (1 + 12 * input.length + 7) := by
    simpa [inputPrelude] using hpreludeBase
  obtain ⟨afterPrelude, preludeRun, preludePost⟩ :=
    hprelude.run (by rfl)
  have rawPrelude : HasRawInput input afterPrelude :=
    ⟨preludePost.cells (rawLenVar, input.length) (by simp), preludePost.arr⟩
  obtain ⟨afterDecode, decodeRun, _rawDecode, orderDecode⟩ :=
    (decodeOrder_spec B input).run
      ⟨rawPrelude,
        by dsimp [B, reductionValueBound]; omega,
        by dsimp [B, reductionValueBound]; omega,
        by rw [hzero]; dsimp [B, reductionValueBound]; omega,
        by dsimp [B, reductionValueBound]; omega⟩
  have orderZero : afterDecode.vars orderVar = 0 := by
    rw [orderDecode, hzero]
  have orderEval : (Expr.var orderVar).evalB B afterDecode = some 0 := by
    rw [Expr.evalB, orderZero]
    exact fit_self (by omega)
  have zeroEval : (Expr.lit 0).evalB B afterDecode = some 0 :=
    fit_self (by omega)
  have conditionTrue :
      (Cond.eq (.var orderVar) (.lit 0)).evalB B afterDecode = some true := by
    rw [Cond.evalB, orderEval, zeroEval]
    simp
  let final : Env := { afterDecode with out := afterDecode.out ++ [0] }
  have decodeOut : afterDecode.out = [] := by
    obtain ⟨_, _, decodeBig⟩ := decodeRun
    obtain ⟨_, _, preludeBig⟩ := preludeRun
    rw [decodeBig.bigStep.out_eq (by decide)]
    rw [preludeBig.bigStep.out_eq (by decide)]
    simp [initEnv]
  have writeBounded : BigStepB B (.write (.lit 0)) afterDecode final 2 := by
    exact BigStepB.write (fit_self (by omega))
  obtain ⟨preludeCost, preludeCostBound, preludeBounded⟩ := preludeRun
  obtain ⟨decodeCost, decodeCostBound, decodeBounded⟩ := decodeRun
  let totalCost := preludeCost + (decodeCost +
    (1 + (Cond.eq (.var orderVar) (.lit 0)).size + 2))
  have wholeAtB : BigStepB B (gapCom q algorithm)
      (initEnv ext (input.length :: input)) final totalCost := by
    dsimp only [totalCost]
    simpa [gapCom] using BigStepB.seq preludeBounded
      (BigStepB.seq decodeBounded
        (BigStepB.ite_true conditionTrue writeBounded))
  have Bbase : B ≤ 2 ^ reductionWordPolynomial.eval (bitSize input) := by
    simpa [B, hzero] using reductionValueBound_le_two_pow input
  have baseExponentLe : reductionWordPolynomial.eval (bitSize input) ≤
      exponent := by
    simp [exponent]
    omega
  have Bglobal : B ≤ 2 ^ exponent :=
    Bbase.trans (Nat.pow_le_pow_right (by omega) baseExponentLe)
  have wholeBounded := bigStepBMono Bglobal wholeAtB
  refine ⟨ext, final, totalCost, wholeBounded, ?_, ?_⟩
  · simp [final, decodeOut, gapFunction, hzero]
  · have hlength := Lax51Proofs.Encoding.length_le_bitSize input
    have localCost : totalCost ≤ 12 * input.length + 100 := by
      dsimp only [totalCost]
      simp only [Cond.size, Expr.size]
      omega
    apply localCost.trans
    simp [gapTimePolynomial]
    omega

/-- The one fixed IMP+ command computes the gap function with simultaneous
polynomial time and word-value bounds on every input. -/
theorem gapCom_bigStepB (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString) :
    let exponent := (gapWordPolynomial q algorithm).eval (bitSize input)
    ∃ ext final cost,
      BigStepB (2 ^ exponent) (gapCom q algorithm)
        (initEnv ext (input.length :: input)) final cost ∧
      final.out = gapFunction q algorithm input ∧
      cost ≤ (gapTimePolynomial q algorithm).eval (bitSize input) := by
  by_cases hzero : rawOrder input = 0
  · exact gapCom_zero_bigStepB q algorithm input hzero
  · exact gapCom_positive_bigStepB q algorithm input
      (Nat.pos_of_ne_zero hzero)

lemma gapFunction_mem_le_one (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) (input : BitString)
    {value : ℕ} (membership : value ∈ gapFunction q algorithm input) :
    value ≤ 1 := by
  unfold gapFunction at membership
  dsimp only at membership
  split at membership
  · simp_all
  · split at membership <;> simp_all

/-- The verified IMP+ implementation compiles to one uniform word-RAM
program with polynomial resources.  The RAM is used only as Lax51's grounded
intermediate machine model. -/
theorem gapFunction_ramPolytime (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) :
    RamPolytime (gapFunction q algorithm) := by
  let cmd := gapCom q algorithm
  let layout := comCanonicalLayout cmd
  let exponentPoly := gapWordPolynomial q algorithm
  let wordPoly : Polynomial ℕ :=
    exponentPoly + C (layoutBitOverhead layout)
  let timePoly : Polynomial ℕ :=
    C layout.const * gapTimePolynomial q algorithm
  refine ⟨compileProgram layout cmd, wordPoly, timePoly, ?_⟩
  intro input
  let size := bitSize input
  let exponent := exponentPoly.eval size
  have exponentLarge : size + 1 ≤ exponent := by
    dsimp [exponent, exponentPoly, size]
    simp
    omega
  have exponentPositive : 0 < exponent := by omega
  have wordEval : wordPoly.eval size =
      exponent + layoutBitOverhead layout := by
    simp [wordPoly, exponent, exponentPoly]
  have exponentWord : exponent ≤ wordPoly.eval size := by
    rw [wordEval]
    omega
  constructor
  · intro value membership
    rw [List.mem_append] at membership
    rcases membership with inputMembership | outputMembership
    · rcases List.mem_cons.mp inputMembership with rfl | inputMembership
      · have bound :=
          Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one input
        exact bound.trans_le (Nat.pow_le_pow_right (by omega)
          (exponentLarge.trans exponentWord))
      · have bound :=
          Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one inputMembership
        exact bound.trans_le (Nat.pow_le_pow_right (by omega)
          (exponentLarge.trans exponentWord))
    · have valueLe := gapFunction_mem_le_one q algorithm input outputMembership
      have wordPositive : 0 < wordPoly.eval size :=
        exponentPositive.trans_le exponentWord
      exact valueLe.trans_lt (Nat.one_lt_two_pow wordPositive.ne')
  · intro wordLength wordLarge
    have layoutLarge : exponent + layoutBitOverhead layout ≤ wordLength := by
      rw [← wordEval]
      simpa [size] using wordLarge
    obtain ⟨ext, final, cost, bounded, output, costBound⟩ :=
      gapCom_bigStepB q algorithm input
    have layoutFits : layout.FitsWords (2 ^ exponent) wordLength :=
      layoutFitsWordsTwoPow layout exponentPositive layoutLarge
    have physicalInputFits : ∀ value ∈ input.length :: input,
        value < 2 ^ exponent := by
      intro value membership
      rcases List.mem_cons.mp membership with rfl | membership
      · exact (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one input).trans_le
          (Nat.pow_le_pow_right (by omega) exponentLarge)
      · exact (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one membership).trans_le
          (Nat.pow_le_pow_right (by omega) exponentLarge)
    obtain ⟨time, timeCost, ramRun⟩ := compileProgram_runsTo layoutFits
      (by simpa [layout, cmd] using comCanonicalLayoutOk cmd)
      physicalInputFits bounded
    refine ⟨time, ?_, ?_⟩
    · calc
        time ≤ layout.const * cost := timeCost
        _ ≤ layout.const * (gapTimePolynomial q algorithm).eval size :=
          Nat.mul_le_mul_left _ costBound
        _ = timePoly.eval size := by simp [timePoly]
    · simpa [cmd, output] using ramRun

/-- The gap function is computed by an actual finite Turing machine with a
polynomial transition bound, via Lax51's verified machine equivalence. -/
theorem gapFunction_turingPolytime (q : ℕ) {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) :
    TuringPolytime (gapFunction q algorithm) :=
  (Lax51Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime
    (gapFunction q algorithm)).mp (gapFunction_ramPolytime q algorithm)

end Lax47Proofs.GapMachine
