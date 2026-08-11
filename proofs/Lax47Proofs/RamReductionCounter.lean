import Lax47Proofs.RamReductionScan

/-!
The counter-table update performed after a selected violating triple.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Lax47Proofs.RamReductionSemantics

open Lax47.Machine Lax47.Complexity Lax47.Reduction
open Lax47Proofs.FlatReduction Lax47Proofs.RamReduction
open Lax47Proofs.RamReductionCorrectness
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen

def incrementTriangleCounts {n : ℕ} (counts : EdgeVariable n → ℕ)
    (triple : ExecutionTriple n) : EdgeVariable n → ℕ :=
  let edgeOne := s(executionFirstVertex triple, executionSecondVertex triple)
  let edgeTwo := s(executionFirstVertex triple, executionThirdVertex triple)
  let edgeThree := s(executionSecondVertex triple, executionThirdVertex triple)
  let afterOne := incrementEdgeCount counts edgeOne
  let afterTwo := if edgeTwo = edgeOne then afterOne
    else incrementEdgeCount afterOne edgeTwo
  if edgeThree = edgeOne then afterTwo
  else if edgeThree = edgeTwo then afterTwo
  else incrementEdgeCount afterTwo edgeThree

lemma incrementTriangleCounts_eq_advance {n : ℕ}
    (counts : EdgeVariable n → ℕ) (triple : ExecutionTriple n) :
    incrementTriangleCounts counts triple =
      advanceExecutionCounts counts (some triple) := by
  classical
  funext edge
  let edgeOne := s(executionFirstVertex triple, executionSecondVertex triple)
  let edgeTwo := s(executionFirstVertex triple, executionThirdVertex triple)
  let edgeThree := s(executionSecondVertex triple, executionThirdVertex triple)
  by_cases h21 : edgeTwo = edgeOne <;>
    by_cases h31 : edgeThree = edgeOne <;>
    by_cases h32 : edgeThree = edgeTwo <;>
    by_cases h1 : edge = edgeOne <;>
    by_cases h2 : edge = edgeTwo <;>
    by_cases h3 : edge = edgeThree <;>
    simp_all [incrementTriangleCounts, incrementEdgeCount,
      advanceExecutionCounts, executionTriangleVariables, edgeOne, edgeTwo,
      edgeThree]

/-- One concrete counter-table store, with its cost attached to the actual
bounded IMP+ run. -/
theorem incrementCountAt_spec (B : ℕ) {n : ℕ} (input : BitString)
    (counts : EdgeVariable n → ℕ) (edge : EdgeVariable n)
    (edgeName : String) (hOneB : 1 < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hvalueB : counts edge + 1 < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        state.vars edgeName = edgeSlot edge)
      (.store countsArray (.var edgeName)
        (.add (.get countsArray (.var edgeName)) (.lit 1)))
      (fun initial final =>
        ExecutionContext n input (incrementEdgeCount counts edge) final ∧
        final.vars = initial.vars)
      10 := by
  unfold Spec
  intro state hstate
  rcases hstate with ⟨hcontext, hedgeName⟩
  rcases hcontext with ⟨hraw, hparameters, hsampleBits, hcounts⟩
  have hslotB : edgeSlot edge < B :=
    (edgeSlot_lt edge).trans hcountLenB
  have hedgeNameB : state.vars edgeName < B := by
    rw [hedgeName]
    exact hslotB
  have hindex :
      (Expr.var edgeName).evalB B state = some (edgeSlot edge) := by
    simpa [hedgeName] using evalB_var hedgeNameB
  have hcountB : counts edge < B := by omega
  have hget :
      (Expr.get countsArray (.var edgeName)).evalB B state =
        some (counts edge) :=
    evalB_get hindex (hcounts.getElem? edge) hcountB
  have hvalue :
      (Expr.add (.get countsArray (.var edgeName)) (.lit 1)).evalB B state =
        some (counts edge + 1) := by
    exact evalB_bin hget (evalB_lit hOneB) (by simpa using hvalueB)
  refine ⟨state.setArr countsArray (edgeSlot edge) (counts edge + 1),
    (Run.store hindex hvalue (hcounts.index_lt edge)).mono
      (by simp [Expr.size]), ?_, rfl⟩
  refine ⟨?_, ?_, ?_, hcounts.increment edge⟩
  · simpa [HasRawInput, Env.setArr, countsArray, rawArray] using hraw
  · simpa [HasParameters, Env.setArr] using hparameters
  · simpa [Env.setArr] using hsampleBits

/-- Increment the candidate unless its edge slot is the preceding slot. -/
theorem incrementUnlessEqual_spec (B : ℕ) {n : ℕ} (input : BitString)
    (counts : EdgeVariable n → ℕ)
    (candidate prior : EdgeVariable n) (candidateName priorName : String)
    (hOneB : 1 < B) (hcountLenB : (n * n) * (n * n) < B)
    (hvalueB : candidate ≠ prior → counts candidate + 1 < B) :
    let finalCounts := if candidate = prior then counts
      else incrementEdgeCount counts candidate
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        state.vars candidateName = edgeSlot candidate ∧
        state.vars priorName = edgeSlot prior)
      (.ite (.eq (.var candidateName) (.var priorName)) .skip
        (.store countsArray (.var candidateName)
          (.add (.get countsArray (.var candidateName)) (.lit 1))))
      (fun initial final => ExecutionContext n input finalCounts final ∧
        final.vars = initial.vars)
      30 := by
  dsimp only
  unfold Spec
  intro state hstate
  rcases hstate with ⟨hcontext, hcandidate, hprior⟩
  have hcandidateB : state.vars candidateName < B := by
    rw [hcandidate]
    exact (edgeSlot_lt candidate).trans hcountLenB
  have hpriorB : state.vars priorName < B := by
    rw [hprior]
    exact (edgeSlot_lt prior).trans hcountLenB
  by_cases heq : candidate = prior
  · have hcondition :
        (Cond.eq (.var candidateName) (.var priorName)).evalB B state =
          some true :=
      (evalB_condEq (evalB_var hcandidateB) (evalB_var hpriorB)).trans
        (by simp [hcandidate, hprior, heq])
    refine ⟨state, (Run.ite_true hcondition Run.skip).mono
      (by simp [Cond.size, Expr.size]), ?_, rfl⟩
    simpa [heq] using hcontext
  · have hslots : edgeSlot candidate ≠ edgeSlot prior :=
      fun h => heq (edgeSlot_injective h)
    have hcondition :
        (Cond.eq (.var candidateName) (.var priorName)).evalB B state =
          some false :=
      (evalB_condEq (evalB_var hcandidateB) (evalB_var hpriorB)).trans
        (by simp [hcandidate, hprior, hslots])
    obtain ⟨final, hrun, hfinalContext, hfinalVars⟩ :=
      (incrementCountAt_spec B input counts candidate candidateName hOneB
        hcountLenB (hvalueB heq)).run ⟨hcontext, hcandidate⟩
    refine ⟨final, (Run.ite_false hcondition hrun).mono
      (by simp [Cond.size, Expr.size]), ?_, hfinalVars⟩
    simpa [heq] using hfinalContext

/-- Increment the candidate unless it equals either of two preceding slots. -/
theorem incrementUnlessEqualTwo_spec (B : ℕ) {n : ℕ}
    (input : BitString) (counts : EdgeVariable n → ℕ)
    (candidate first second : EdgeVariable n)
    (candidateName firstName secondName : String)
    (hOneB : 1 < B) (hcountLenB : (n * n) * (n * n) < B)
    (hvalueB : candidate ≠ first → candidate ≠ second →
      counts candidate + 1 < B) :
    let finalCounts := if candidate = first then counts
      else if candidate = second then counts
      else incrementEdgeCount counts candidate
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        state.vars candidateName = edgeSlot candidate ∧
        state.vars firstName = edgeSlot first ∧
        state.vars secondName = edgeSlot second)
      (.ite (.eq (.var candidateName) (.var firstName)) .skip
        (.ite (.eq (.var candidateName) (.var secondName)) .skip
          (.store countsArray (.var candidateName)
            (.add (.get countsArray (.var candidateName)) (.lit 1)))))
      (fun initial final => ExecutionContext n input finalCounts final ∧
        final.vars = initial.vars)
      60 := by
  dsimp only
  unfold Spec
  intro state hstate
  rcases hstate with ⟨hcontext, hcandidate, hfirst, hsecond⟩
  have hcandidateB : state.vars candidateName < B := by
    rw [hcandidate]
    exact (edgeSlot_lt candidate).trans hcountLenB
  have hfirstB : state.vars firstName < B := by
    rw [hfirst]
    exact (edgeSlot_lt first).trans hcountLenB
  by_cases hEqFirst : candidate = first
  · have hcondition :
        (Cond.eq (.var candidateName) (.var firstName)).evalB B state =
          some true :=
      (evalB_condEq (evalB_var hcandidateB) (evalB_var hfirstB)).trans
        (by simp [hcandidate, hfirst, hEqFirst])
    refine ⟨state, (Run.ite_true hcondition Run.skip).mono
      (by simp [Cond.size, Expr.size]), ?_, rfl⟩
    simpa [hEqFirst] using hcontext
  · have hslots : edgeSlot candidate ≠ edgeSlot first :=
      fun h => hEqFirst (edgeSlot_injective h)
    have hcondition :
        (Cond.eq (.var candidateName) (.var firstName)).evalB B state =
          some false :=
      (evalB_condEq (evalB_var hcandidateB) (evalB_var hfirstB)).trans
        (by simp [hcandidate, hfirst, hslots])
    obtain ⟨final, hrun, hfinalContext, hfinalVars⟩ :=
      (incrementUnlessEqual_spec B input counts candidate second
        candidateName secondName hOneB hcountLenB
        (hvalueB hEqFirst)).run ⟨hcontext, hcandidate, hsecond⟩
    refine ⟨final, (Run.ite_false hcondition hrun).mono
      (by simp [Cond.size, Expr.size]), ?_,
      hfinalVars⟩
    simpa [hEqFirst] using hfinalContext

theorem advanceCounters_spec (B : ℕ) {n : ℕ} (input : BitString)
    (counts : EdgeVariable n → ℕ) (selection : Option (ExecutionTriple n))
    (hOneB : 1 < B)
    (hcountLenB : (n * n) * (n * n) < B)
    (hcountsSuccB : ∀ edge, counts edge + 1 < B) :
    Spec B
      (fun state => ExecutionContext n input counts state ∧
        SelectionRepresent selection state)
      advanceCounters
      (fun _ final => ExecutionContext n input
        (advanceExecutionCounts counts selection) final)
      200 := by
  unfold Spec
  intro initial hstate
  rcases hstate with ⟨hcontext, hselection⟩
  cases selection with
  | none =>
      have hfound : initial.vars foundVar = 0 := by
        simpa [SelectionRepresent] using hselection
      have hcondition :
          (Cond.eq (.var foundVar) (.lit 1)).evalB B initial = some false :=
        (evalB_condEq (evalB_var (by omega)) (evalB_lit hOneB)).trans
          (by simp [hfound])
      have hrun := Run.seq
        (Run.ite_false
          (c := Com.block [
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
                  (.add (.get countsArray (.var selectedEdgeThreeVar))
                    (.lit 1))))])
          hcondition Run.skip) Run.skip
      refine ⟨initial, ?_, ?_⟩
      · simpa [advanceCounters] using hrun.mono (K' := 200)
          (by simp [Cond.size, Expr.size])
      · simpa [advanceExecutionCounts] using hcontext
  | some triple =>
      let edgeOne : EdgeVariable n :=
        s(executionFirstVertex triple, executionSecondVertex triple)
      let edgeTwo : EdgeVariable n :=
        s(executionFirstVertex triple, executionThirdVertex triple)
      let edgeThree : EdgeVariable n :=
        s(executionSecondVertex triple, executionThirdVertex triple)
      let countsOne := incrementEdgeCount counts edgeOne
      let countsTwo := if edgeTwo = edgeOne then countsOne
        else incrementEdgeCount countsOne edgeTwo
      let countsThree := if edgeThree = edgeOne then countsTwo
        else if edgeThree = edgeTwo then countsTwo
        else incrementEdgeCount countsTwo edgeThree
      have hvalueOne : counts edgeOne + 1 < B := hcountsSuccB edgeOne
      have hvalueTwo (hNe : edgeTwo ≠ edgeOne) :
          countsOne edgeTwo + 1 < B := by
        simpa [countsOne, incrementEdgeCount, hNe] using hcountsSuccB edgeTwo
      have hvalueThree (hNeOne : edgeThree ≠ edgeOne)
          (hNeTwo : edgeThree ≠ edgeTwo) : countsTwo edgeThree + 1 < B := by
        by_cases hEq : edgeTwo = edgeOne
        · simp [countsTwo, hEq, countsOne, incrementEdgeCount, hNeOne]
          exact hcountsSuccB edgeThree
        · simp [countsTwo, hEq, countsOne, incrementEdgeCount, hNeOne,
            hNeTwo]
          exact hcountsSuccB edgeThree
      have hfinalCounts : countsThree = incrementTriangleCounts counts triple := by
        rfl
      have hadvance : countsThree = advanceExecutionCounts counts (some triple) := by
        rw [hfinalCounts, incrementTriangleCounts_eq_advance]
      rcases hselection with ⟨hfound, hselectedOne, hselectedTwo,
        hselectedThree⟩
      obtain ⟨stateOne, hrunOne, hcontextOne, hvarsOne⟩ :=
        (incrementCountAt_spec B input counts edgeOne selectedEdgeOneVar
          hOneB hcountLenB hvalueOne).run ⟨hcontext, hselectedOne⟩
      have hselectedTwoOne :
          stateOne.vars selectedEdgeTwoVar = edgeSlot edgeTwo := by
        rw [hvarsOne]
        exact hselectedTwo
      have hselectedOneOne :
          stateOne.vars selectedEdgeOneVar = edgeSlot edgeOne := by
        rw [hvarsOne]
        exact hselectedOne
      obtain ⟨stateTwo, hrunTwo, hcontextTwo, hvarsTwo⟩ :=
        (incrementUnlessEqual_spec B input countsOne edgeTwo edgeOne
          selectedEdgeTwoVar selectedEdgeOneVar hOneB hcountLenB
          hvalueTwo).run ⟨hcontextOne, hselectedTwoOne, hselectedOneOne⟩
      have hselectedThreeTwo :
          stateTwo.vars selectedEdgeThreeVar = edgeSlot edgeThree := by
        rw [hvarsTwo, hvarsOne]
        exact hselectedThree
      have hselectedOneTwo :
          stateTwo.vars selectedEdgeOneVar = edgeSlot edgeOne := by
        rw [hvarsTwo, hvarsOne]
        exact hselectedOne
      have hselectedTwoTwo :
          stateTwo.vars selectedEdgeTwoVar = edgeSlot edgeTwo := by
        rw [hvarsTwo, hvarsOne]
        exact hselectedTwo
      obtain ⟨stateThree, hrunThree, hcontextThree, _hvarsThree⟩ :=
        (incrementUnlessEqualTwo_spec B input countsTwo edgeThree edgeOne
          edgeTwo selectedEdgeThreeVar selectedEdgeOneVar selectedEdgeTwoVar
          hOneB hcountLenB hvalueThree).run
            ⟨hcontextTwo, hselectedThreeTwo, hselectedOneTwo,
              hselectedTwoTwo⟩
      have hfoundB : initial.vars foundVar < B := by rw [hfound]; exact hOneB
      have hcondition :
          (Cond.eq (.var foundVar) (.lit 1)).evalB B initial = some true :=
        (evalB_condEq (evalB_var hfoundB) (evalB_lit hOneB)).trans
          (by simp [hfound])
      have hbranchRun :=
        Run.seq hrunOne (Run.seq hrunTwo (Run.seq hrunThree Run.skip))
      have hrun := Run.seq (Run.ite_true (d := .skip) hcondition hbranchRun)
        Run.skip
      refine ⟨stateThree, ?_, ?_⟩
      · simpa [advanceCounters] using hrun.mono (K' := 200)
          (by simp [Cond.size, Expr.size])
      · rw [← hadvance]
        exact hcontextThree

end Lax47Proofs.RamReductionSemantics
