import Lax47Proofs.GapMachineRun
import Lax51Proofs.TMToRam.InterpreterTame

/-!
Word bounds for the composed IMP+ program.  The reduction already carries
bounded semantics.  Only the redirected native interpreter and the final
linear scan use Lax51's generic bit-growth theorem; the fixed power test is
bounded directly.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Lax47Proofs.GapMachine

open Lax47.Machine Lax47.Complexity Lax47.Gap
open Lax47Proofs Lax47Proofs.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax47Proofs.RamReductionSemantics Lax47Proofs.Redirect
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen
open Lax51.BinaryWordEncoding
open Lax51Proofs.TMToRam

/-- Bounded IMP+ execution preserves a common strict bound on all values in
the environment. -/
theorem BigStepB.envBitBounded {bound exponent : ℕ} {command : Com}
    {initial final : Env} {cost : ℕ}
    (run : BigStepB bound command initial final cost)
    (hbound : bound ≤ 2 ^ exponent)
    (initialBounded : EnvBitBounded initial exponent) :
    EnvBitBounded final exponent := by
  induction run with
  | skip => exact initialBounded
  | @assign state name expression value evaluation =>
      exact initialBounded.setVar name
        ((Expr.lt_of_evalB evaluation).trans_le hbound)
  | @store state name index expression position value indexEval valueEval hposition =>
      exact initialBounded.setArr name
        ((Expr.lt_of_evalB valueEval).trans_le hbound)
  | seq first second firstIH secondIH =>
      exact secondIH (firstIH initialBounded)
  | ite_true condition branch branchIH => exact branchIH initialBounded
  | ite_false condition branch branchIH => exact branchIH initialBounded
  | while_true condition body loop bodyIH loopIH =>
      exact loopIH (bodyIH initialBounded)
  | while_false => exact initialBounded
  | @read state name value rest inputEq =>
      let after : Env := { state.setVar name value with inp := rest }
      have hvalue : value < 2 ^ exponent := by
        apply initialBounded.inp value
        rw [inputEq]
        simp
      have hset := initialBounded.setVar name hvalue
      refine ⟨hset.vars, hset.arrs, ?_, hset.out⟩
      intro queried membership
      apply initialBounded.inp queried
      rw [inputEq]
      exact List.mem_cons_of_mem value membership
  | @write state expression value evaluation =>
      exact initialBounded.write
        ((Expr.lt_of_evalB evaluation).trans_le hbound)

@[simp] theorem redirectExpr_bitGrowth (expression : Expr) :
    exprBitGrowth (redirectExpr expression) = exprBitGrowth expression := by
  induction expression with
  | lit => rfl
  | var => rfl
  | get name index ih => simp [redirectExpr, exprBitGrowth, ih]
  | bin operator left right leftIH rightIH =>
      cases operator with
      | mul =>
          cases left <;> cases right <;>
            simp_all [redirectExpr, exprBitGrowth]
      | add | sub | div | and | or | xor | shiftl | shiftr =>
          simp [redirectExpr, exprBitGrowth, leftIH, rightIH]

@[simp] theorem redirectCond_bitGrowth (condition : Cond) :
    condBitGrowth (redirectCond condition) = condBitGrowth condition := by
  cases condition <;> simp [redirectCond, condBitGrowth]

theorem redirectCom_tame {command : Com} (tame : comTame command) :
    comTame (redirectCom command) := by
  induction command with
  | skip => exact ComTame.skip
  | assign name expression =>
      obtain ⟨growth, growthEq⟩ := tame
      cases expressionGrowth : exprBitGrowth expression <;>
        simp [comBitGrowth, expressionGrowth] at growthEq
      exact ComTame.assign _ ⟨_, by simpa using expressionGrowth⟩
  | store name index expression =>
      simp only [comTameIffExistsBitGrowth] at tame ⊢
      obtain ⟨growth, growthEq⟩ := tame
      cases indexGrowth : exprBitGrowth index <;>
        cases expressionGrowth : exprBitGrowth expression <;>
        simp [comBitGrowth, indexGrowth, expressionGrowth] at growthEq
      exact ComTame.store _ ⟨_, by simpa using indexGrowth⟩
        ⟨_, by simpa using expressionGrowth⟩
  | seq first second firstIH secondIH =>
      obtain ⟨growth, growthEq⟩ := tame
      cases firstGrowth : comBitGrowth first <;>
        cases secondGrowth : comBitGrowth second <;>
        simp [comBitGrowth, firstGrowth, secondGrowth] at growthEq
      exact ComTame.seq (firstIH ⟨_, firstGrowth⟩)
        (secondIH ⟨_, secondGrowth⟩)
  | ite condition yes no yesIH noIH =>
      obtain ⟨growth, growthEq⟩ := tame
      cases conditionGrowth : condBitGrowth condition <;>
        cases yesGrowth : comBitGrowth yes <;>
        cases noGrowth : comBitGrowth no <;>
        simp [comBitGrowth, conditionGrowth, yesGrowth, noGrowth] at growthEq
      exact ComTame.ite ⟨_, by simpa using conditionGrowth⟩
        (yesIH ⟨_, yesGrowth⟩) (noIH ⟨_, noGrowth⟩)
  | «while» condition body bodyIH =>
      obtain ⟨growth, growthEq⟩ := tame
      cases conditionGrowth : condBitGrowth condition <;>
        cases bodyGrowth : comBitGrowth body <;>
        simp [comBitGrowth, conditionGrowth, bodyGrowth] at growthEq
      exact ComTame.«while» ⟨_, by simpa using conditionGrowth⟩
        (bodyIH ⟨_, bodyGrowth⟩)
  | read name =>
      unfold redirectCom redirectRead increment
      exact ComTame.seq
        (ComTame.ite
          (CondTame.eq (ExprTame.var _) (ExprTame.lit 0))
          (ComTame.assign _
            (ExprTame.add (ExprTame.var _) (ExprTame.lit 1)))
          (ComTame.assign _
            (ExprTame.get
              (ExprTame.sub (ExprTame.var _) (ExprTame.lit 1)) _)))
        (ComTame.assign _
          (ExprTame.add (ExprTame.var _) (ExprTame.lit 1)))
  | write expression =>
      obtain ⟨growth, growthEq⟩ := tame
      cases expressionGrowth : exprBitGrowth expression <;>
        simp [comBitGrowth, expressionGrowth] at growthEq
      unfold redirectCom redirectWrite increment
      exact ComTame.seq
        (ComTame.store _ (ExprTame.var _)
          ⟨_, by simpa using expressionGrowth⟩)
        (ComTame.assign _
          (ExprTame.add (ExprTame.var _) (ExprTame.lit 1)))

theorem approximationNativeCom_tame {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) :
    comTame (approximationNativeCom algorithm) := by
  let H := approximationWitness algorithm
  let tm := H.tm
  dsimp [approximationNativeCom]
  exact FinTM2.compileNativeMachine_tame tm _ _ _ _ _ _ _ _ _ _

noncomputable def redirectedApproximationGrowth {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) : ℕ :=
  Classical.choose (redirectCom_tame (approximationNativeCom_tame algorithm))

theorem redirectedApproximation_bitGrowth {ε : ℝ}
    (algorithm : TriangleFreeMISApproximation ε) :
    comBitGrowth (redirectCom (approximationNativeCom algorithm)) =
      some (redirectedApproximationGrowth algorithm) :=
  Classical.choose_spec
    (redirectCom_tame (approximationNativeCom_tame algorithm))

def countGrowth : ℕ := (comBitGrowth countAlgorithmOutput).getD 1

theorem countAlgorithmOutput_bitGrowth :
    comBitGrowth countAlgorithmOutput = some countGrowth := by
  decide

/-- Bounded version of the already packaged raw reduction run. -/
theorem reductionCom_raw_bigStepB (sourceExt : String → ℕ)
    (input : BitString) (n : ℕ) (hn : 0 < n)
    (horder : rawOrder input = n) (outputCapacity : ℕ) :
    let graph := rawGraphCodeAt n input
    let flatSeed := rawFlatSeedAt n input
    let target := executionOutput graph (executionSeedOfFlat flatSeed)
    let ext := combinedExt sourceExt input ((n * n) * (n * n))
      target.bits.length outputCapacity
    ∃ final cost,
      BigStepB (reductionValueBound input n) reductionCom
        (initEnv ext (input.length :: input)) final cost ∧
      ExecutionContext n input
        (executionCounts graph (executionSeedOfFlat flatSeed)) final ∧
      final.arrs graphArray = target.bits ∧
      cost ≤ reductionCostBound input.length n := by
  dsimp only
  let graph := rawGraphCodeAt n input
  let flatSeed := rawFlatSeedAt n input
  let target := executionOutput graph (executionSeedOfFlat flatSeed)
  let ext := combinedExt sourceExt input ((n * n) * (n * n))
    target.bits.length outputCapacity
  let B := reductionValueBound input n
  have hvalue (value : ℕ) (membership : value ∈ input) : value < B := by
    have := mem_le_inputMax membership
    dsimp [B, reductionValueBound]
    omega
  have hspec := reductionCom_model_spec B ext input graph flatSeed
    (ModelsReductionInput.raw n input) horder hn
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    hvalue
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by dsimp [B, reductionValueBound]; omega)
    (by simp [ext]) (by simp [ext]) (by simp [ext, target])
  obtain ⟨final, run, context, _halted, graphOutput⟩ :=
    hspec.run (by rfl)
  obtain ⟨cost, hcost, bounded⟩ := run
  refine ⟨final, cost, bounded, context, graphOutput, ?_⟩
  simpa [reductionCostBound] using hcost

lemma natPowExpr_evalB (bound : ℕ) (base : Expr) (state : Env)
    (exponent value : ℕ) (baseEval : base.evalB bound state = some value)
    (powersBound : ∀ power ≤ exponent, value ^ power < bound) :
    (natPowExpr base exponent).evalB bound state = some (value ^ exponent) := by
  induction exponent with
  | zero =>
      change fit bound 1 = some 1
      exact fit_self (powersBound 0 (by omega))
  | succ exponent ih =>
      have priorBound : ∀ power ≤ exponent, value ^ power < bound := by
        intro power hpower
        exact powersBound power (by omega)
      have productBound := powersBound (exponent + 1) (by omega)
      rw [natPowExpr, Expr.evalB, ih priorBound, baseEval]
      exact fit_self (by simpa [Nat.pow_succ] using productBound)

/-- Direct bounded semantics for the fixed-exponent threshold test. -/
theorem writeGapDecision_bigStepB (bound q n card : ℕ) (initial : Env)
    (horder : initial.vars orderVar = n)
    (hcard : initial.vars outputCardVar = card)
    (hout : initial.out = [])
    (hn : n < bound) (hcardBound : card < bound)
    (hleftPowers : ∀ power ≤ q + 3, n ^ power < bound)
    (hrightPowers : ∀ power ≤ q, card ^ power < bound)
    (hzero : 0 < bound) (hone : 1 < bound) :
    ∃ final cost,
      BigStepB bound (writeGapDecision q) initial final cost ∧
      final.out = (if n ^ (q + 3) ≤ card ^ q then [1] else [0]) ∧
      cost ≤ 10 * (q + 5) := by
  let left := n ^ (q + 3)
  let right := card ^ q
  let afterLeft := initial.setVar decisionLeftVar left
  let afterRight := afterLeft.setVar decisionRightVar right
  have orderEval : (Expr.var orderVar).evalB bound initial = some n := by
    simp [Expr.evalB, horder, fit_self hn]
  have leftEval :
      (natPowExpr (.var orderVar) (q + 3)).evalB bound initial =
        some left := natPowExpr_evalB bound _ _ _ _ orderEval hleftPowers
  have cardState : afterLeft.vars outputCardVar = card := by
    simpa [afterLeft, Env.setVar, outputCardVar, decisionLeftVar] using hcard
  have cardEval : (Expr.var outputCardVar).evalB bound afterLeft = some card := by
    simp [Expr.evalB, cardState, fit_self hcardBound]
  have rightEval :
      (natPowExpr (.var outputCardVar) q).evalB bound afterLeft =
        some right := natPowExpr_evalB bound _ _ _ _ cardEval hrightPowers
  have runLeft : BigStepB bound
      (.assign decisionLeftVar (natPowExpr (.var orderVar) (q + 3)))
      initial afterLeft (1 + ((q + 3) * 2 + 1)) := by
    simpa [afterLeft, Expr.size] using BigStepB.assign leftEval
  have runRight : BigStepB bound
      (.assign decisionRightVar (natPowExpr (.var outputCardVar) q))
      afterLeft afterRight (1 + (q * 2 + 1)) := by
    simpa [afterRight, Expr.size] using BigStepB.assign rightEval
  have leftVar : afterRight.vars decisionLeftVar = left := by
    simp [afterRight, afterLeft, Env.setVar, decisionLeftVar, decisionRightVar]
  have rightVar : afterRight.vars decisionRightVar = right := by
    simp [afterRight, Env.setVar]
  have leftBound := hleftPowers (q + 3) (by omega)
  have rightBound := hrightPowers q (by omega)
  have leftFit : (Expr.var decisionLeftVar).evalB bound afterRight =
      some left := by
    rw [Expr.evalB, leftVar]
    exact fit_self (by simpa [left] using leftBound)
  have rightFit : (Expr.var decisionRightVar).evalB bound afterRight =
      some right := by
    rw [Expr.evalB, rightVar]
    exact fit_self (by simpa [right] using rightBound)
  by_cases accept : left ≤ right
  · let final : Env := { afterRight with out := afterRight.out ++ [1] }
    have condition :
        (Cond.lt (.var decisionRightVar) (.var decisionLeftVar)).evalB
          bound afterRight = some false := by
      rw [Cond.evalB, rightFit, leftFit]
      simp
      omega
    have branch : BigStepB bound
        (.ite (.lt (.var decisionRightVar) (.var decisionLeftVar))
          (.write (.lit 0)) (.write (.lit 1))) afterRight final 6 := by
      exact BigStepB.ite_false condition
        (BigStepB.write (by simp [Expr.evalB, fit_self hone]))
    refine ⟨final, (1 + ((q + 3) * 2 + 1)) +
      ((1 + (q * 2 + 1)) + (6 + 1)), ?_, ?_, by omega⟩
    · exact BigStepB.seq runLeft (BigStepB.seq runRight
        (BigStepB.seq branch BigStepB.skip))
    · simp [final, afterRight, afterLeft, Env.setVar, hout, left, right,
        accept]
  · let final : Env := { afterRight with out := afterRight.out ++ [0] }
    have condition :
        (Cond.lt (.var decisionRightVar) (.var decisionLeftVar)).evalB
          bound afterRight = some true := by
      rw [Cond.evalB, rightFit, leftFit]
      simp
      omega
    have branch : BigStepB bound
        (.ite (.lt (.var decisionRightVar) (.var decisionLeftVar))
          (.write (.lit 0)) (.write (.lit 1))) afterRight final 6 := by
      exact BigStepB.ite_true condition
        (BigStepB.write (by simp [Expr.evalB, fit_self hzero]))
    refine ⟨final, (1 + ((q + 3) * 2 + 1)) +
      ((1 + (q * 2 + 1)) + (6 + 1)), ?_, ?_, by omega⟩
    · exact BigStepB.seq runLeft (BigStepB.seq runRight
        (BigStepB.seq branch BigStepB.skip))
    · simp [final, afterRight, afterLeft, Env.setVar, hout, left, right,
        accept]

end Lax47Proofs.GapMachine
