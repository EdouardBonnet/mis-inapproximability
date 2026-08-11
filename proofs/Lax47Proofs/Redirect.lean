import Lax47Proofs.RamReduction

/-!
Lax51 compiles any supplied finite Turing machine to a native IMP+ command.
This file gives a transparent syntactic adapter for that command.  Reads are
served from the generated graph array and writes are captured in another
array; all of the native command's names are prefixed.  The simulation theorem
below is structural on the actual IMP+ big-step derivation.
-/

set_option autoImplicit false

namespace Lax47Proofs.Redirect

open Lax13Proofs.Imp
open Lax47Proofs.RamReduction

def algorithmPrefix : String := "a."
def algorithmName (name : String) : String := algorithmPrefix ++ name

def inputCursor : String := "r.algorithmInputCursor"
def outputCursor : String := "r.algorithmOutputCursor"
def algorithmOutputArray : String := "r.algorithmOutput"

lemma algorithmName_injective : Function.Injective algorithmName := by
  intro left right h
  exact String.append_right_inj algorithmPrefix |>.mp h

lemma algorithmName_ne_inputCursor (name : String) :
    algorithmName name ≠ inputCursor := by
  intro h
  have hlist := congrArg String.toList h
  simp [algorithmName, algorithmPrefix, inputCursor] at hlist

lemma algorithmName_ne_outputCursor (name : String) :
    algorithmName name ≠ outputCursor := by
  intro h
  have hlist := congrArg String.toList h
  simp [algorithmName, algorithmPrefix, outputCursor] at hlist

lemma algorithmName_ne_rawArray (name : String) :
    algorithmName name ≠ rawArray := by
  intro h
  have hlist := congrArg String.toList h
  simp [algorithmName, algorithmPrefix, rawArray] at hlist

lemma algorithmName_ne_countsArray (name : String) :
    algorithmName name ≠ countsArray := by
  intro h
  have hlist := congrArg String.toList h
  simp [algorithmName, algorithmPrefix, countsArray] at hlist

lemma algorithmName_ne_graphArray (name : String) :
    algorithmName name ≠ graphArray := by
  intro h
  have hlist := congrArg String.toList h
  simp [algorithmName, algorithmPrefix, graphArray] at hlist

lemma algorithmName_ne_algorithmOutputArray (name : String) :
    algorithmName name ≠ algorithmOutputArray := by
  intro h
  have hlist := congrArg String.toList h
  simp [algorithmName, algorithmPrefix, algorithmOutputArray] at hlist

lemma algorithmName_ne_countLenVar (name : String) :
    algorithmName name ≠ countLenVar := by
  intro h
  have hlist := congrArg String.toList h
  simp [algorithmName, algorithmPrefix, countLenVar] at hlist

def redirectExpr : Expr → Expr
  | .lit value => .lit value
  | .var name => .var (algorithmName name)
  | .get name index => .get (algorithmName name) (redirectExpr index)
  | .bin operator left right =>
      .bin operator (redirectExpr left) (redirectExpr right)

def redirectCond : Cond → Cond
  | .eq left right => .eq (redirectExpr left) (redirectExpr right)
  | .lt left right => .lt (redirectExpr left) (redirectExpr right)

/-- Virtual physical input expected by Lax51's native codec. -/
def virtualInput (graph : List ℕ) : List ℕ := graph.length :: graph

/-- One virtualized read.  Cursor zero yields the physical length prefix;
subsequent positions come from the generated graph word. -/
def redirectRead (name : String) : Com :=
  .seq
    (.ite (.eq (.var inputCursor) (.lit 0))
      (.assign (algorithmName name) (.add (.var countLenVar) (.lit 1)))
      (.assign (algorithmName name)
        (.get graphArray (.sub (.var inputCursor) (.lit 1)))))
    (increment inputCursor)

/-- One virtualized write into the pre-sized capture array. -/
def redirectWrite (expression : Expr) : Com :=
  .seq
    (.store algorithmOutputArray (.var outputCursor)
      (redirectExpr expression))
    (increment outputCursor)

def redirectCom : Com → Com
  | .skip => .skip
  | .assign name expression =>
      .assign (algorithmName name) (redirectExpr expression)
  | .store name index expression =>
      .store (algorithmName name) (redirectExpr index)
        (redirectExpr expression)
  | .seq first second => .seq (redirectCom first) (redirectCom second)
  | .ite condition yes no =>
      .ite (redirectCond condition) (redirectCom yes) (redirectCom no)
  | .while condition body =>
      .while (redirectCond condition) (redirectCom body)
  | .read name => redirectRead name
  | .write expression => redirectWrite expression

@[simp] lemma redirectExpr_size (expression : Expr) :
    (redirectExpr expression).size = expression.size := by
  induction expression <;> simp [redirectExpr, Expr.size, *]

@[simp] lemma redirectCond_size (condition : Cond) :
    (redirectCond condition).size = condition.size := by
  cases condition <;> simp [redirectCond, Cond.size]

/-! ### State relation -/

/-- The target state mirrors every source scalar and array under the prefix.
The remaining conjuncts describe the virtual input and captured output. -/
structure Rel (graph : List ℕ) (capacity : ℕ) (source target : Env) : Prop where
  vars : ∀ name, target.vars (algorithmName name) = source.vars name
  arrs : ∀ name, target.arrs (algorithmName name) = source.arrs name
  input_le : target.vars inputCursor ≤ (virtualInput graph).length
  input_tape : source.inp =
    (virtualInput graph).drop (target.vars inputCursor)
  output_le : source.out.length ≤ capacity
  output_cursor : target.vars outputCursor = source.out.length
  output_array : target.arrs algorithmOutputArray =
    source.out ++ List.replicate (capacity - source.out.length) 0
  graph_array : target.arrs graphArray = graph
  graph_length : target.vars countLenVar + 1 = graph.length

lemma Rel.setVar {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    (name : String) (value : ℕ) :
    Rel graph capacity (source.setVar name value)
      (target.setVar (algorithmName name) value) := by
  constructor
  · intro queried
    simp only [Env.setVar]
    by_cases h : queried = name
    · subst queried
      simp
    · have hren : algorithmName queried ≠ algorithmName name :=
        fun heq => h (algorithmName_injective heq)
      simp [h, hren, relation.vars]
  · intro queried
    simp [Env.setVar, relation.arrs]
  · simpa [Env.setVar, Ne.symm (algorithmName_ne_inputCursor name)] using
      relation.input_le
  · simpa [Env.setVar] using relation.input_tape
  · simpa [Env.setVar] using relation.output_le
  · simpa [Env.setVar, Ne.symm (algorithmName_ne_outputCursor name)] using
      relation.output_cursor
  · simpa [Env.setVar] using relation.output_array
  · simpa [Env.setVar] using relation.graph_array
  · simpa [Env.setVar, Ne.symm (algorithmName_ne_countLenVar name)] using
      relation.graph_length

lemma Rel.setArr {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    (name : String) (index value : ℕ) :
    Rel graph capacity (source.setArr name index value)
      (target.setArr (algorithmName name) index value) := by
  constructor
  · intro queried
    simp [Env.setArr, relation.vars]
  · intro queried
    simp only [Env.setArr]
    by_cases h : queried = name
    · subst queried
      simp [relation.arrs]
    · have hren : algorithmName queried ≠ algorithmName name :=
        fun heq => h (algorithmName_injective heq)
      simp [h, hren, relation.arrs]
  · simpa [Env.setArr] using relation.input_le
  · simpa [Env.setArr] using relation.input_tape
  · simpa [Env.setArr] using relation.output_le
  · simpa [Env.setArr] using relation.output_cursor
  · simpa [Env.setArr,
      Ne.symm (algorithmName_ne_algorithmOutputArray name)] using
      relation.output_array
  · simpa [Env.setArr, Ne.symm (algorithmName_ne_graphArray name)] using
      relation.graph_array
  · simpa [Env.setArr] using relation.graph_length

lemma redirectExpr_eval {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    (expression : Expr) :
    (redirectExpr expression).eval target = expression.eval source := by
  induction expression with
  | lit value => rfl
  | var name => simp [redirectExpr, relation.vars]
  | get name index ih =>
      simp only [redirectExpr, Expr.eval, ih, relation.arrs]
  | bin operator left right ihLeft ihRight =>
      simp only [redirectExpr, Expr.eval, ihLeft, ihRight]

lemma redirectCond_eval {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    (condition : Cond) :
    (redirectCond condition).eval target = condition.eval source := by
  cases condition <;> simp [redirectCond, Cond.eval,
    redirectExpr_eval relation]

lemma BigStep.out_length_le {command : Com} {source target : Env} {cost : ℕ}
    (run : BigStep command source target cost) :
    source.out.length ≤ target.out.length := by
  induction run with
  | skip => exact le_rfl
  | assign => exact le_rfl
  | store => exact le_rfl
  | seq _ _ first second => exact first.trans second
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ body loop => exact body.trans loop
  | while_false => exact le_rfl
  | read => exact le_rfl
  | write => simp

lemma drop_eq_cons_info {α : Type} {values : List α} {position : ℕ}
    {value : α} {rest : List α}
    (h : values.drop position = value :: rest) :
    position < values.length ∧ rest = values.drop (position + 1) := by
  have hposition : position < values.length := by
    by_contra hnot
    have hle : values.length ≤ position := by omega
    rw [List.drop_eq_nil_of_le hle] at h
    simp at h
  rw [List.drop_eq_getElem_cons hposition] at h
  injection h with hvalue hrest
  exact ⟨hposition, hrest.symm⟩

def afterReadSource (source : Env) (name : String) (value : ℕ)
    (rest : List ℕ) : Env :=
  { source.setVar name value with inp := rest }

def afterReadTarget (target : Env) (name : String) (value : ℕ) : Env :=
  (target.setVar (algorithmName name) value).setVar inputCursor
    (target.vars inputCursor + 1)

lemma Rel.afterRead {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    {name : String} {value : ℕ} {rest : List ℕ}
    (hread : source.inp = value :: rest) :
    Rel graph capacity (afterReadSource source name value rest)
      (afterReadTarget target name value) := by
  let position := target.vars inputCursor
  have hdrop : (virtualInput graph).drop position = value :: rest := by
    rw [← relation.input_tape]
    exact hread
  obtain ⟨hposition, hrest⟩ := drop_eq_cons_info hdrop
  have base := relation.setVar name value
  constructor
  · intro queried
    simp only [afterReadTarget, afterReadSource, Env.setVar]
    have hspecial : algorithmName queried ≠ inputCursor :=
      algorithmName_ne_inputCursor queried
    rw [if_neg hspecial]
    exact base.vars queried
  · intro queried
    simpa [afterReadTarget, afterReadSource, Env.setVar] using
      base.arrs queried
  · simp only [afterReadTarget, Env.setVar]
    simp only [ite_true]
    exact Nat.succ_le_iff.mpr hposition
  · dsimp only [position] at hrest
    simpa [afterReadSource, afterReadTarget, Env.setVar] using hrest
  · simpa [afterReadSource, afterReadTarget, Env.setVar] using
      base.output_le
  · simpa [afterReadSource, afterReadTarget, Env.setVar,
      inputCursor, outputCursor] using base.output_cursor
  · simpa [afterReadSource, afterReadTarget, Env.setVar] using
      base.output_array
  · simpa [afterReadSource, afterReadTarget, Env.setVar] using
      base.graph_array
  · simpa [afterReadSource, afterReadTarget, Env.setVar,
      inputCursor, countLenVar] using base.graph_length

def afterWriteSource (source : Env) (value : ℕ) : Env :=
  { source with out := source.out ++ [value] }

def afterWriteTarget (target : Env) (value : ℕ) : Env :=
  (target.setArr algorithmOutputArray (target.vars outputCursor) value).setVar
    outputCursor (target.vars outputCursor + 1)

lemma capture_set (values : List ℕ) (capacity value : ℕ)
    (hroom : values.length + 1 ≤ capacity) :
    (values ++ List.replicate (capacity - values.length) 0).set
        values.length value =
      (values ++ [value]) ++
        List.replicate (capacity - (values ++ [value]).length) 0 := by
  have hsplit : capacity - values.length =
      (capacity - (values.length + 1)) + 1 := by omega
  rw [List.set_append_right]
  · simp only [Nat.sub_self]
    rw [hsplit, List.replicate_succ]
    simp [List.append_assoc]
  · exact le_rfl

lemma Rel.afterWrite {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    (value : ℕ) (hroom : source.out.length + 1 ≤ capacity) :
    Rel graph capacity (afterWriteSource source value)
      (afterWriteTarget target value) := by
  constructor
  · intro queried
    simp only [afterWriteTarget, afterWriteSource, Env.setVar, Env.setArr]
    by_cases h : algorithmName queried = outputCursor
    · exact absurd h (algorithmName_ne_outputCursor queried)
    · rw [if_neg h]
      exact relation.vars queried
  · intro queried
    simp [afterWriteTarget, afterWriteSource, Env.setVar, Env.setArr,
      algorithmName_ne_algorithmOutputArray queried, relation.arrs]
  · simpa [afterWriteTarget, Env.setVar, Env.setArr,
      inputCursor, outputCursor] using relation.input_le
  · simpa [afterWriteTarget, afterWriteSource, Env.setVar, Env.setArr] using
      relation.input_tape
  · simpa [afterWriteSource] using hroom
  · simp [afterWriteTarget, afterWriteSource, Env.setVar,
      relation.output_cursor]
  · simp only [afterWriteTarget, afterWriteSource, Env.setVar]
    change (target.arrs algorithmOutputArray).set
      (target.vars outputCursor) value = _
    rw [relation.output_cursor, relation.output_array,
      capture_set source.out capacity value hroom]
  · simpa [afterWriteTarget, Env.setVar, Env.setArr,
      graphArray, algorithmOutputArray] using relation.graph_array
  · simpa [afterWriteTarget, Env.setVar, Env.setArr,
      outputCursor, countLenVar] using relation.graph_length

lemma read_value_zero {graph : List ℕ} {value : ℕ} {rest : List ℕ}
    (h : (virtualInput graph).drop 0 = value :: rest) :
    value = graph.length := by
  simp only [List.drop_zero, virtualInput] at h
  injection h
  symm
  assumption

lemma read_value_succ {graph : List ℕ} {position value : ℕ}
    {rest : List ℕ}
    (hposition : position + 1 < (virtualInput graph).length)
    (h : (virtualInput graph).drop (position + 1) = value :: rest) :
    position < graph.length ∧ graph[position]? = some value := by
  have hp : position < graph.length := by
    simpa [virtualInput] using hposition
  change graph.drop position = value :: rest at h
  rw [List.drop_eq_getElem_cons hp] at h
  injection h with hvalue _
  refine ⟨hp, ?_⟩
  rw [List.getElem?_eq_getElem hp, hvalue]

lemma redirectRead_bigStep {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    {name : String} {value : ℕ} {rest : List ℕ}
    (hread : source.inp = value :: rest) :
    ∃ cost, BigStep (redirectRead name) target
      (afterReadTarget target name value) cost ∧ cost ≤ 20 := by
  let position := target.vars inputCursor
  have hdrop : (virtualInput graph).drop position = value :: rest := by
    rw [← relation.input_tape]
    exact hread
  by_cases hzero : position = 0
  · have hvalue : value = graph.length := by
      apply read_value_zero
      simpa [hzero] using hdrop
    have hcount : target.vars countLenVar + 1 = value := by
      rw [hvalue]
      exact relation.graph_length
    let middle := target.setVar (algorithmName name) value
    have hcondition :
        (Cond.eq (.var inputCursor) (.lit 0)).eval target = some true := by
      simp [Cond.eval, Expr.eval, position, hzero]
    have hassign :
        (Expr.add (.var countLenVar) (.lit 1)).eval target = some value := by
      simp [Expr.eval, hcount]
    have hcursor : middle.vars inputCursor = position := by
      simp [middle, Env.setVar, Ne.symm (algorithmName_ne_inputCursor name),
        position]
    have hinc :
        (Expr.add (.var inputCursor) (.lit 1)).eval middle =
          some (position + 1) := by simp [Expr.eval, hcursor]
    refine ⟨_, BigStep.seq (BigStep.ite_true hcondition
      (BigStep.assign hassign)) (BigStep.assign hinc), ?_⟩
    decide
  · obtain ⟨prior, hposition⟩ : ∃ prior, position = prior + 1 := by
      exact ⟨position - 1, by omega⟩
    have hpositionLt : position < (virtualInput graph).length := by
      have hinfo := drop_eq_cons_info hdrop
      exact hinfo.1
    have hdrop' : (virtualInput graph).drop (prior + 1) = value :: rest := by
      simpa [hposition] using hdrop
    rw [hposition] at hpositionLt
    obtain ⟨hprior, hvalue⟩ :=
      read_value_succ hpositionLt hdrop'
    let middle := target.setVar (algorithmName name) value
    have hcondition :
        (Cond.eq (.var inputCursor) (.lit 0)).eval target = some false := by
      simp [Cond.eval, Expr.eval, position, hzero]
    have hassign :
        (Expr.get graphArray (.sub (.var inputCursor) (.lit 1))).eval target =
          some value := by
      simp only [Expr.eval, Option.bind_eq_bind, Bop.apply_sub]
      simp [position, hposition, relation.graph_array, hvalue]
    have hcursor : middle.vars inputCursor = position := by
      simp [middle, Env.setVar, Ne.symm (algorithmName_ne_inputCursor name),
        position]
    have hinc :
        (Expr.add (.var inputCursor) (.lit 1)).eval middle =
          some (position + 1) := by simp [Expr.eval, hcursor]
    refine ⟨_, BigStep.seq (BigStep.ite_false hcondition
      (BigStep.assign hassign)) (BigStep.assign hinc), ?_⟩
    decide

lemma redirectWrite_bigStep {graph : List ℕ} {capacity : ℕ}
    {source target : Env} (relation : Rel graph capacity source target)
    {expression : Expr} {value : ℕ}
    (heval : expression.eval source = some value)
    (hroom : source.out.length + 1 ≤ capacity) :
    ∃ cost, BigStep (redirectWrite expression) target
      (afterWriteTarget target value) cost ∧
        cost ≤ 20 * (1 + expression.size) := by
  let position := target.vars outputCursor
  have hposition : position = source.out.length := relation.output_cursor
  have hlength : (target.arrs algorithmOutputArray).length = capacity := by
    rw [relation.output_array]
    simp
    omega
  have hindex : position < (target.arrs algorithmOutputArray).length := by
    rw [hlength, hposition]
    omega
  have hindexEval : (Expr.var outputCursor).eval target = some position := rfl
  have hvalueEval : (redirectExpr expression).eval target = some value := by
    rw [redirectExpr_eval relation]
    exact heval
  let middle := target.setArr algorithmOutputArray position value
  have hcursor : middle.vars outputCursor = position := rfl
  have hinc : (Expr.add (.var outputCursor) (.lit 1)).eval middle =
      some (position + 1) := by simp [Expr.eval, hcursor]
  refine ⟨_, BigStep.seq (BigStep.store hindexEval hvalueEval hindex)
    (BigStep.assign hinc), ?_⟩
  simp only [redirectExpr_size, Expr.size]
  omega

/-! ### Structural simulation -/

/-- Redirecting a terminating IMP+ run preserves its exact source state under
the prefixing relation.  The redirected run costs at most a fixed factor of
the source run; in particular, virtual tape access is charged rather than
treated as a free oracle operation. -/
theorem redirectCom_bigStep {graph : List ℕ} {capacity : ℕ}
    {command : Com} {source final target : Env} {cost : ℕ}
    (run : BigStep command source final cost)
    (relation : Rel graph capacity source target)
    (hcapacity : final.out.length ≤ capacity) :
    ∃ targetFinal targetCost,
      BigStep (redirectCom command) target targetFinal targetCost ∧
      Rel graph capacity final targetFinal ∧
      targetCost ≤ 20 * cost := by
  induction run generalizing target with
  | skip =>
      exact ⟨target, 1, BigStep.skip, relation, by omega⟩
  | @assign source name expression value heval =>
      refine ⟨target.setVar (algorithmName name) value,
        1 + expression.size, ?_, relation.setVar name value, ?_⟩
      · change BigStep (.assign (algorithmName name)
          (redirectExpr expression)) target _ _
        rw [← redirectExpr_size expression]
        exact BigStep.assign (x := algorithmName name) (by
          rw [redirectExpr_eval relation]
          exact heval)
      · omega
  | @store source array index expression position value hindex hvalue hbound =>
      refine ⟨target.setArr (algorithmName array) position value,
        1 + index.size + expression.size, ?_,
        relation.setArr array position value, ?_⟩
      · change BigStep (.store (algorithmName array)
          (redirectExpr index) (redirectExpr expression)) target _ _
        rw [← redirectExpr_size index, ← redirectExpr_size expression]
        exact BigStep.store
          (by rw [redirectExpr_eval relation]; exact hindex)
          (by rw [redirectExpr_eval relation]; exact hvalue)
          (by simpa [relation.arrs])
      · omega
  | seq firstRun secondRun firstIH secondIH =>
      have hmiddle : _ :=
        (BigStep.out_length_le secondRun).trans hcapacity
      obtain ⟨targetMiddle, firstCost, firstTargetRun, middleRelation,
        firstBound⟩ := firstIH relation hmiddle
      obtain ⟨targetFinal, secondCost, secondTargetRun, finalRelation,
        secondBound⟩ := secondIH middleRelation hcapacity
      refine ⟨targetFinal, firstCost + secondCost,
        BigStep.seq firstTargetRun secondTargetRun, finalRelation, ?_⟩
      omega
  | ite_true hcondition branchRun branchIH =>
      obtain ⟨targetFinal, targetCost, targetRun, finalRelation,
        costBound⟩ := branchIH relation hcapacity
      refine ⟨targetFinal, 1 + (redirectCond _).size + targetCost,
        BigStep.ite_true ?_ targetRun, finalRelation, ?_⟩
      · rw [redirectCond_eval relation]
        exact hcondition
      · simp only [redirectCond_size]
        omega
  | ite_false hcondition branchRun branchIH =>
      obtain ⟨targetFinal, targetCost, targetRun, finalRelation,
        costBound⟩ := branchIH relation hcapacity
      refine ⟨targetFinal, 1 + (redirectCond _).size + targetCost,
        BigStep.ite_false ?_ targetRun, finalRelation, ?_⟩
      · rw [redirectCond_eval relation]
        exact hcondition
      · simp only [redirectCond_size]
        omega
  | while_true hcondition bodyRun loopRun bodyIH loopIH =>
      have hmiddle : _ :=
        (BigStep.out_length_le loopRun).trans hcapacity
      obtain ⟨targetMiddle, bodyCost, targetBodyRun, middleRelation,
        bodyBound⟩ := bodyIH relation hmiddle
      obtain ⟨targetFinal, loopCost, targetLoopRun, finalRelation,
        loopBound⟩ := loopIH middleRelation hcapacity
      refine ⟨targetFinal,
        1 + (redirectCond _).size + bodyCost + loopCost,
        BigStep.while_true ?_ targetBodyRun targetLoopRun,
        finalRelation, ?_⟩
      · rw [redirectCond_eval relation]
        exact hcondition
      · simp only [redirectCond_size]
        omega
  | while_false hcondition =>
      refine ⟨target, 1 + (redirectCond _).size,
        BigStep.while_false ?_, relation, ?_⟩
      · rw [redirectCond_eval relation]
        exact hcondition
      · simp only [redirectCond_size]
        omega
  | read hread =>
      obtain ⟨targetCost, targetRun, costBound⟩ :=
        redirectRead_bigStep relation hread
      refine ⟨afterReadTarget target _ _, targetCost,
        by simpa [redirectCom] using targetRun, ?_, by omega⟩
      simpa [afterReadSource] using relation.afterRead hread
  | @write source expression value heval =>
      have hroom : source.out.length + 1 ≤ capacity := by
        simpa [afterWriteSource] using hcapacity
      obtain ⟨targetCost, targetRun, costBound⟩ :=
        redirectWrite_bigStep relation heval hroom
      refine ⟨afterWriteTarget target _, targetCost,
        by simpa [redirectCom] using targetRun, ?_, ?_⟩
      · simpa [afterWriteSource] using relation.afterWrite _ hroom
      · simpa using costBound

end Lax47Proofs.Redirect
