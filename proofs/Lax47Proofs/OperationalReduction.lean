import Lax47Proofs.FiniteExecution

/-!
This module connects the fixed finite-bit implementation in the concept
package to the Moser--Tardos process analyzed in $Construction$.  In
particular, it proves that the executable counter loop, halt test, and encoded
output graph are the same objects whose probability bounds were proved using
the imported resampling and distributional theorems.
-/

set_option autoImplicit false

namespace Lax47Proofs.OperationalReduction

open Lax47.Complexity Lax47.Reduction
open Lax41.MoserTardosDefinitions
open Lax41.HaeuplerSahaSrinivasanDefinitions
open Lax47Proofs.Construction Lax47Proofs.FiniteExecution

/-! ### The finite seed used by the implementation -/

/-- Reindex the structured finite seed as the input expected by the executable loop. -/
def executionSeedOfFinite {n : ℕ} (seed : FiniteSeed n) : ExecutionSeed n :=
  fun edge row bit ↦
    seed ⟨⟨edge, row.1⟩, by
      simpa [prefixIndices, executionBudget, cutoffBudget] using row.2⟩
      (Fin.cast (by rfl) bit)

/-- Inverse reindexing from the executable seed to the finite-prefix seed. -/
def finiteSeedOfExecution {n : ℕ} (seed : ExecutionSeed n) : FiniteSeed n :=
  fun index bit ↦
    seed index.1.1
      ⟨index.1.2, by
        have hrow : index.1.2 < cutoffBudget n + 1 := by
          exact (Lax47Proofs.FiniteExecution.mem_prefixIndices
            (j := index.1)).mp index.2
        simpa [executionBudget, cutoffBudget] using hrow⟩
      (Fin.cast (by rfl) bit)

/-- The two structured presentations contain exactly the same fair bits. -/
def finiteSeedEquivExecution (n : ℕ) : FiniteSeed n ≃ ExecutionSeed n where
  toFun := executionSeedOfFinite
  invFun := finiteSeedOfExecution
  left_inv := by
    intro seed
    funext index bit
    rfl
  right_inv := by
    intro seed
    funext edge row bit
    rfl

@[simp] lemma executionCell_seedOfFinite {n : ℕ} (seed : FiniteSeed n)
    (edge : EdgeVariable n) (row : ℕ) :
    executionCell (executionSeedOfFinite seed) edge row =
      extendFiniteTable (seedFiniteTable seed) ⟨edge, row⟩ := by
  by_cases hrow : row < executionBudget n + 1
  · have hmem : (⟨edge, row⟩ : TableIndex (Variable := EdgeVariable n)) ∈
        prefixIndices n := by
      simpa [executionBudget, cutoffBudget] using hrow
    rw [executionCell, dif_pos hrow, extendFiniteTable, dif_pos hmem]
    rfl
  · have hmem : (⟨edge, row⟩ : TableIndex (Variable := EdgeVariable n)) ∉
        prefixIndices n := by
      simpa [executionBudget, cutoffBudget] using hrow
    rw [executionCell, dif_neg hrow, extendFiniteTable, dif_neg hmem]

/-! ### One executable scan is one Moser--Tardos selection -/

/-- The infinite table used only to analyze a concrete finite seed. -/
abbrev analysisTable {n : ℕ} (seed : FiniteSeed n) : SampleTable n :=
  extendFiniteTable (seedFiniteTable seed)

lemma executionViolates_iff {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) (counts : EdgeVariable n → ℕ)
    (triple : ExecutionTriple n) :
    executionViolates input (executionSeedOfFinite seed) counts triple = true ↔
      IsBlowupTriangle input.graph triple ∧
        ∀ edge ∈ triangleVariables triple,
          currentAssignment (fun _ : EdgeVariable n ↦ Bool)
            (analysisTable seed) counts edge = true := by
  rcases triple with ⟨⟨a, a'⟩, ⟨⟨b, b'⟩, ⟨c, c'⟩⟩⟩
  simp [executionViolates, executionBlowupAdjacent, IsBlowupTriangle,
    blowup, triangleVariables, currentAssignment, executionFirstVertex,
    executionSecondVertex, executionThirdVertex]
  tauto

@[simp] lemma badVariables_triangleBadIndex {n : ℕ} (H : SimpleGraph (Fin n))
    (triple : VertexTriple n) (htriangle : IsBlowupTriangle H triple) :
    badVariables H (triangleBadIndex H triple htriangle) =
      triangleVariables triple := by
  rfl

@[simp] lemma executionTriangleVariables_eq {n : ℕ}
    (triple : ExecutionTriple n) :
    executionTriangleVariables triple = triangleVariables triple := by
  rfl

lemma violates_triangleBadIndex_iff {n : ℕ} (H : SimpleGraph (Fin n))
    (assignment : EdgeVariable n → Bool) (triple : VertexTriple n)
    (htriangle : IsBlowupTriangle H triple) :
    violates (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) assignment
        (triangleBadIndex H triple htriangle) ↔
      ∀ edge ∈ triangleVariables triple, assignment edge = true := by
  change (∀ edge : triangleVariables triple, assignment edge.1 = true) ↔ _
  simp

lemma executionViolates_iff_candidate {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) (counts : EdgeVariable n → ℕ)
    (triple : ExecutionTriple n) :
    executionViolates input (executionSeedOfFinite seed) counts triple = true ↔
      (triangleCandidate input.graph
        (currentAssignment (fun _ : EdgeVariable n ↦ Bool)
          (analysisTable seed) counts) triple).isSome := by
  rw [executionViolates_iff]
  classical
  by_cases htriangle : IsBlowupTriangle input.graph triple
  · rw [and_iff_right htriangle]
    rw [← (violates_triangleBadIndex_iff input.graph
      (currentAssignment (fun _ : EdgeVariable n ↦ Bool)
        (analysisTable seed) counts) triple htriangle)]
    by_cases hviolates : violates (fun _ : EdgeVariable n ↦ Bool)
        (badVariables input.graph) (badSet input.graph)
        (currentAssignment (fun _ : EdgeVariable n ↦ Bool)
          (analysisTable seed) counts)
        (triangleBadIndex input.graph triple htriangle)
    · simp [triangleCandidate, htriangle, hviolates]
    · simp [triangleCandidate, htriangle, hviolates]
  · simp [htriangle, triangleCandidate]

lemma candidateScope_eq {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) (counts : EdgeVariable n → ℕ)
    (triple : ExecutionTriple n) :
    Option.map (badVariables input.graph)
        (triangleCandidate input.graph
          (currentAssignment (fun _ : EdgeVariable n ↦ Bool)
            (analysisTable seed) counts) triple) =
      if executionViolates input (executionSeedOfFinite seed) counts triple then
        some (executionTriangleVariables triple)
      else none := by
  classical
  let assignment := currentAssignment (fun _ : EdgeVariable n ↦ Bool)
    (analysisTable seed) counts
  by_cases htriangle : IsBlowupTriangle input.graph triple
  · by_cases hviolates : violates (fun _ : EdgeVariable n ↦ Bool)
        (badVariables input.graph) (badSet input.graph) assignment
        (triangleBadIndex input.graph triple htriangle)
    · have hcandidate : triangleCandidate input.graph assignment triple =
          some (triangleBadIndex input.graph triple htriangle) := by
        simp [triangleCandidate, htriangle, hviolates]
      have hexec : executionViolates input (executionSeedOfFinite seed)
          counts triple = true :=
        (executionViolates_iff_candidate input seed counts triple).2 (by
          simp [assignment, hcandidate])
      simp [assignment, hcandidate, hexec]
    · have hcandidate : triangleCandidate input.graph assignment triple = none := by
        simp [triangleCandidate, htriangle, hviolates]
      have hnot : ¬executionViolates input (executionSeedOfFinite seed)
          counts triple = true := by
        intro hexec
        have := (executionViolates_iff_candidate input seed counts triple).1 hexec
        simpa [assignment, hcandidate] using this
      have hexec : executionViolates input (executionSeedOfFinite seed)
          counts triple = false := Bool.eq_false_of_not_eq_true hnot
      simp [assignment, hcandidate, hexec]
  · have hcandidate : triangleCandidate input.graph assignment triple = none := by
      simp [triangleCandidate, htriangle]
    have hnot : ¬executionViolates input (executionSeedOfFinite seed)
        counts triple = true := by
      intro hexec
      have := (executionViolates_iff_candidate input seed counts triple).1 hexec
      simpa [assignment, hcandidate] using this
    have hexec : executionViolates input (executionSeedOfFinite seed)
        counts triple = false := Bool.eq_false_of_not_eq_true hnot
    simp [assignment, hcandidate, hexec]

/-- Both scanners select exactly the same three counters, in the same order. -/
lemma selectedScope_eq_scan {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) (counts : EdgeVariable n → ℕ)
    (order : List (ExecutionTriple n)) :
    Option.map (badVariables input.graph)
        (chooseTriangleEvent input.graph
          (currentAssignment (fun _ : EdgeVariable n ↦ Bool)
            (analysisTable seed) counts) order) =
      Option.map executionTriangleVariables
        (scanExecutionTriples input (executionSeedOfFinite seed) counts order).1 := by
  classical
  induction order with
  | nil => simp [chooseTriangleEvent, scanExecutionTriples]
  | cons triple rest ih =>
      let assignment := currentAssignment (fun _ : EdgeVariable n ↦ Bool)
        (analysisTable seed) counts
      cases hcandidate : triangleCandidate input.graph assignment triple with
      | none =>
          have hscope := candidateScope_eq input seed counts triple
          rw [show currentAssignment (fun _ : EdgeVariable n ↦ Bool)
              (analysisTable seed) counts = assignment by rfl,
            hcandidate] at hscope
          have hnot : ¬executionViolates input (executionSeedOfFinite seed)
              counts triple = true := by
            intro hexec
            simp [hexec] at hscope
          have hexec : executionViolates input (executionSeedOfFinite seed)
              counts triple = false := Bool.eq_false_of_not_eq_true hnot
          simpa [chooseTriangleEvent, List.findSome?_cons, assignment,
            hcandidate, scanExecutionTriples, hexec] using ih
      | some A =>
          have hscope := candidateScope_eq input seed counts triple
          rw [show currentAssignment (fun _ : EdgeVariable n ↦ Bool)
              (analysisTable seed) counts = assignment by rfl,
            hcandidate] at hscope
          have hexec : executionViolates input (executionSeedOfFinite seed)
              counts triple = true := by
            by_contra hnot
            have hfalse : executionViolates input (executionSeedOfFinite seed)
                counts triple = false := Bool.eq_false_of_not_eq_true hnot
            simp [hfalse] at hscope
          have hscope' : badVariables input.graph A =
              executionTriangleVariables triple := by
            simpa [hexec] using hscope
          simp [chooseTriangleEvent, List.findSome?_cons, assignment,
            hcandidate, scanExecutionTriples, hexec, hscope']

lemma advanceCounts_eq_of_selectedScope_eq {n : ℕ}
    (H : SimpleGraph (Fin n)) (counts : EdgeVariable n → ℕ)
    (selected : Option (BadEventIndex (badEvents H)))
    (triple : Option (ExecutionTriple n))
    (hscope : Option.map (badVariables H) selected =
      Option.map executionTriangleVariables triple) :
    advanceCounts (badVariables H) counts selected =
      advanceExecutionCounts counts triple := by
  cases selected with
  | none =>
      cases triple with
      | none => rfl
      | some triple => simp at hscope
  | some A =>
      cases triple with
      | none => simp at hscope
      | some triple =>
          simp only [Option.map_some, Option.some.injEq] at hscope
          funext edge
          simp [advanceCounts, advanceExecutionCounts, hscope]

lemma advanceCounts_eq_execution {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) (counts : EdgeVariable n → ℕ) :
    advanceCounts (badVariables input.graph) counts
        ((selectionRule input.graph).choose
          (currentAssignment (fun _ : EdgeVariable n ↦ Bool)
            (analysisTable seed) counts)) =
      advanceExecutionCounts counts
        (findExecutionViolation input (executionSeedOfFinite seed) counts).1 := by
  apply advanceCounts_eq_of_selectedScope_eq
  simpa only [selectionRule, findExecutionViolation] using
    selectedScope_eq_scan input seed counts (executionTriples n)

/-- The concrete recursive loop has exactly the analyzed counter state at every round. -/
lemma executeRounds_counts_eq_runCounts {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) (round : ℕ) :
    (executeRounds input (executionSeedOfFinite seed) round (fun _ ↦ 0)).1 =
      runCounts (fun _ : EdgeVariable n ↦ Bool)
        (badVariables input.graph) (badSet input.graph)
        (selectionRule input.graph) (analysisTable seed) round := by
  classical
  induction round with
  | zero => rfl
  | succ round ih =>
      rw [Lax41Proofs.runCounts_succ]
      simp only [executeRounds]
      rw [ih]
      exact advanceCounts_eq_execution input seed _ |>.symm

lemma executionCounts_eq_runCounts {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) :
    executionCounts input (executionSeedOfFinite seed) =
      runCounts (fun _ : EdgeVariable n ↦ Bool)
        (badVariables input.graph) (badSet input.graph)
        (selectionRule input.graph) (analysisTable seed) (cutoffBudget n) := by
  simpa [executionCounts, executionBudget, cutoffBudget] using
    executeRounds_counts_eq_runCounts input seed (cutoffBudget n)

lemma option_isNone_eq_of_map_eq {A B C : Type} (f : A → B) (g : C → B)
    (left : Option A) (right : Option C)
    (hmap : Option.map f left = Option.map g right) :
    left.isNone = right.isNone := by
  cases left <;> cases right <;> simp_all

lemma selection_isNone_eq_scan {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) (counts : EdgeVariable n → ℕ) :
    ((selectionRule input.graph).choose
        (currentAssignment (fun _ : EdgeVariable n ↦ Bool)
          (analysisTable seed) counts)).isNone =
      (findExecutionViolation input (executionSeedOfFinite seed) counts).1.isNone := by
  apply option_isNone_eq_of_map_eq (badVariables input.graph)
    executionTriangleVariables
  simpa only [selectionRule, findExecutionViolation] using
    selectedScope_eq_scan input seed counts (executionTriples n)

lemma executionHalted_iff {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) :
    executionHalted input (executionSeedOfFinite seed) = true ↔
      haltedAtCutoff input.graph (analysisTable seed) := by
  unfold executionHalted haltedAtCutoff resamplingLog
  rw [executionCounts_eq_runCounts]
  rw [← selection_isNone_eq_scan input seed]
  simp

lemma cutoffOutputGraph_adj_iff {n : ℕ} {H : SimpleGraph (Fin n)}
    {table : SampleTable n} {left right : BlowupVertex n} :
    (cutoffOutputGraph H table).Adj left right ↔
      (blowup H).Adj left right ∧
        cutoffAssignment H table s(left, right) = true := by
  constructor
  · intro hadj
    rcases (SimpleGraph.fromEdgeSet_adj _).mp hadj with ⟨⟨hedge, hvalue⟩, _⟩
    exact ⟨(SimpleGraph.mem_edgeSet (blowup H)).mp hedge, hvalue⟩
  · rintro ⟨hadj, hvalue⟩
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    exact ⟨⟨(SimpleGraph.mem_edgeSet (blowup H)).mpr hadj, hvalue⟩,
      (blowup H).ne_of_adj hadj⟩

/-- The encoded executable output is the analyzed truncated graph, up to pair encoding. -/
theorem executionOutput_comap_eq {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) :
    (executionOutput input (executionSeedOfFinite seed)).graph.comap
        (finProdFinEquiv : BlowupVertex n ≃ Fin (n * n)) =
      truncatedGraph input.graph (analysisTable seed) := by
  ext left right
  by_cases hhalt : haltedAtCutoff input.graph (analysisTable seed)
  · have hexec : executionHalted input (executionSeedOfFinite seed) = true :=
      (executionHalted_iff input seed).2 hhalt
    have hdecodeLeft : decodeBlowupVertex (finProdFinEquiv left) = left :=
      finProdFinEquiv.symm_apply_apply left
    have hdecodeRight : decodeBlowupVertex (finProdFinEquiv right) = right :=
      finProdFinEquiv.symm_apply_apply right
    rw [truncatedGraph, if_pos hhalt, cutoffOutputGraph_adj_iff]
    simp only [SimpleGraph.comap_adj, GraphCode.graph_adj, executionOutput,
      hexec, if_true, Bool.and_eq_true, decodeBlowupVertex_encode,
      executionCell_seedOfFinite, executionCounts_eq_runCounts, blowup,
      cutoffAssignment, currentAssignment]
    rw [hdecodeLeft, hdecodeRight]
  · have hexec : executionHalted input (executionSeedOfFinite seed) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hhalt ((executionHalted_iff input seed).1 htrue)
    rw [truncatedGraph, if_neg hhalt]
    simp [executionOutput, hexec]

/-! ### Transfer through the pair encoding -/

lemma indepNum_comap_equiv_le {A B : Type} [Fintype A] [Fintype B]
    (graph : SimpleGraph B) (equiv : A ≃ B) :
    (graph.comap equiv).indepNum ≤ graph.indepNum := by
  classical
  obtain ⟨set, hset⟩ := (graph.comap equiv).exists_isNIndepSet_indepNum
  have hmapped : graph.IsIndepSet (set.map equiv.toEmbedding) := by
    intro left hleft right hright hne
    change left ∈ set.map equiv.toEmbedding at hleft
    change right ∈ set.map equiv.toEmbedding at hright
    rw [Finset.mem_map] at hleft hright
    obtain ⟨left, hleft, rfl⟩ := hleft
    obtain ⟨right, hright, rfl⟩ := hright
    have hne' : left ≠ right := fun heq ↦ hne (congrArg equiv heq)
    exact hset.1 hleft hright hne'
  calc
    (graph.comap equiv).indepNum = set.card := hset.2.symm
    _ = (set.map equiv.toEmbedding).card := by simp
    _ ≤ graph.indepNum := hmapped.card_le_indepNum

lemma indepNum_comap_equiv {A B : Type} [Fintype A] [Fintype B]
    (graph : SimpleGraph B) (equiv : A ≃ B) :
    (graph.comap equiv).indepNum = graph.indepNum := by
  apply le_antisymm (indepNum_comap_equiv_le graph equiv)
  have hinverse := indepNum_comap_equiv_le (graph.comap equiv) equiv.symm
  have hgraph : (graph.comap equiv).comap equiv.symm = graph := by
    ext left right
    simp
  rw [hgraph] at hinverse
  exact hinverse

lemma cliqueFree_of_comap_equiv {A B : Type} [Fintype A] [Fintype B]
    {graph : SimpleGraph B} (equiv : A ≃ B) {size : ℕ}
    (hfree : (graph.comap equiv).CliqueFree size) : graph.CliqueFree size := by
  classical
  intro set hclique
  let preimage : Finset A := set.map equiv.symm.toEmbedding
  have hpreimage : (graph.comap equiv).IsNClique size preimage := by
    constructor
    · intro left hleft right hright hne
      change left ∈ preimage at hleft
      change right ∈ preimage at hright
      simp only [preimage] at hleft hright
      rw [Finset.mem_map] at hleft hright
      obtain ⟨left, hleft, rfl⟩ := hleft
      obtain ⟨right, hright, rfl⟩ := hright
      change graph.Adj (equiv (equiv.symm left)) (equiv (equiv.symm right))
      rw [equiv.apply_symm_apply, equiv.apply_symm_apply]
      exact hclique.1 hleft hright
        (fun heq ↦ hne (congrArg equiv.symm heq))
    · simp [preimage, hclique.2]
  exact hfree preimage hpreimage

theorem executionOutput_triangleFree {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) :
    (executionOutput input (executionSeedOfFinite seed)).graph.CliqueFree 3 := by
  apply cliqueFree_of_comap_equiv
    (finProdFinEquiv : BlowupVertex n ≃ Fin (n * n))
  rw [executionOutput_comap_eq]
  exact truncatedGraph_triangleFree input.graph (analysisTable seed)

lemma executionOutput_indepNum {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) :
    (executionOutput input (executionSeedOfFinite seed)).graph.indepNum =
      (truncatedGraph input.graph (analysisTable seed)).indepNum := by
  rw [← executionOutput_comap_eq input seed]
  exact (indepNum_comap_equiv
    (executionOutput input (executionSeedOfFinite seed)).graph
    (finProdFinEquiv : BlowupVertex n ≃ Fin (n * n))).symm

theorem executionOutput_completeness {n : ℕ} (input : GraphCode n)
    (seed : FiniteSeed n) :
    input.graph.indepNum * n ≤
      (executionOutput input (executionSeedOfFinite seed)).graph.indepNum := by
  rw [executionOutput_indepNum]
  exact truncatedGraph_completeness input.graph (analysisTable seed)

/-- Triangle-freeness stated directly for the implementation's seed type. -/
theorem executionOutput_triangleFree_of_executionSeed {n : ℕ}
    (input : GraphCode n) (seed : ExecutionSeed n) :
    (executionOutput input seed).graph.CliqueFree 3 := by
  have hseed := (finiteSeedEquivExecution n).apply_symm_apply seed
  rw [← hseed]
  exact executionOutput_triangleFree input (finiteSeedOfExecution seed)

/-- Completeness stated directly for the implementation's seed type. -/
theorem executionOutput_completeness_of_executionSeed {n : ℕ}
    (input : GraphCode n) (seed : ExecutionSeed n) :
    input.graph.indepNum * n ≤ (executionOutput input seed).graph.indepNum := by
  have hseed := (finiteSeedEquivExecution n).apply_symm_apply seed
  rw [← hseed]
  exact executionOutput_completeness input (finiteSeedOfExecution seed)

theorem executionOutput_soundness_failure_card_le_third
    (n : ℕ) (hn : 3 ≤ n) (input : GraphCode n) :
    3 * ((Finset.univ : Finset (FiniteSeed n)).filter fun seed ↦
      40000 * input.graph.indepNum * n * Real.log n <
        ((executionOutput input
          (executionSeedOfFinite seed)).graph.indepNum : ℝ)).card ≤
      (Finset.univ : Finset (FiniteSeed n)).card := by
  classical
  apply filter_card_le_third_of_measure_le
  simpa only [executionOutput_indepNum] using
    finiteSeed_truncatedGraph_soundness_failure_le_third n hn input.graph

/-! ### Polynomial bounds for the counted execution -/

@[simp] lemma executionTriples_length (n : ℕ) :
    (executionTriples n).length = n ^ 6 := by
  simp [executionTriples]
  ring

lemma scanExecutionTriples_steps_le {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ)
    (order : List (ExecutionTriple n)) :
    (scanExecutionTriples input seed counts order).2 ≤
      executionTestSteps n * order.length + 1 := by
  induction order with
  | nil => simp [scanExecutionTriples]
  | cons triple rest ih =>
      rw [scanExecutionTriples]
      split
      · simp only [List.length_cons]
        rw [Nat.mul_succ]
        omega
      · simp only [List.length_cons]
        rw [Nat.mul_succ]
        omega

lemma findExecutionViolation_steps_le {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) (counts : EdgeVariable n → ℕ) :
    (findExecutionViolation input seed counts).2 ≤
      executionTestSteps n * n ^ 6 + 1 := by
  have h := scanExecutionTriples_steps_le input seed counts (executionTriples n)
  simpa only [findExecutionViolation, executionTriples_length,
    show (n * n) * (n * n) * (n * n) = n ^ 6 by ring] using h

lemma executeRounds_steps_le {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) (rounds : ℕ) (counts : EdgeVariable n → ℕ) :
    (executeRounds input seed rounds counts).2 ≤
      1 + rounds * (executionTestSteps n * n ^ 6 + 2) := by
  induction rounds with
  | zero => simp [executeRounds]
  | succ rounds ih =>
      simp only [executeRounds]
      have hscan := findExecutionViolation_steps_le input seed
        (executeRounds input seed rounds counts).1
      rw [Nat.add_mul]
      omega

lemma executionSampleBits_le_linear (n : ℕ) :
    executionSampleBits n ≤ 101 * (n + 1) := by
  simpa only [executionSampleBits, sampleBits] using sampleBits_le_linear n

lemma executionTestSteps_polynomial (n : ℕ) :
    executionTestSteps n ≤ 26520 * (n + 1) ^ 7 := by
  have hbudget : executionBudget n + 1 ≤ 13 * (n + 1) ^ 6 := by
    simp only [executionBudget]
    have hbase : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have hbits : executionSampleBits n + 1 ≤ 102 * (n + 1) := by
    have := executionSampleBits_le_linear n
    omega
  unfold executionTestSteps
  calc
    20 * (executionBudget n + 1) * (executionSampleBits n + 1) ≤
        20 * (13 * (n + 1) ^ 6) * (102 * (n + 1)) := by
      gcongr
    _ = 26520 * (n + 1) ^ 7 := by ring

/-- Every counted transition of the fixed reduction fits one explicit polynomial. -/
theorem executionSteps_polynomial {n : ℕ} (input : GraphCode n)
    (seed : ExecutionSeed n) :
    executionSteps input seed ≤ 400000 * (n + 1) ^ 20 := by
  let base := n + 1
  have hbase : 1 ≤ base := by omega
  have htest : executionTestSteps n ≤ 26520 * base ^ 7 := by
    simpa only [base] using executionTestSteps_polynomial n
  have hn6 : n ^ 6 ≤ base ^ 6 := by gcongr <;> omega
  have hscanCore : executionTestSteps n * n ^ 6 + 2 ≤
      26522 * base ^ 13 := by
    calc
      executionTestSteps n * n ^ 6 + 2 ≤
          (26520 * base ^ 7) * base ^ 6 + 2 := by gcongr
      _ = 26520 * base ^ 13 + 2 := by ring
      _ ≤ 26522 * base ^ 13 := by
        have hone : 1 ≤ base ^ 13 := Nat.one_le_pow _ _ hbase
        nlinarith
  have hrounds := executeRounds_steps_le input seed (executionBudget n)
    (fun _ ↦ 0)
  have hfinal := findExecutionViolation_steps_le input seed
    (executionCounts input seed)
  have hbudget : executionBudget n ≤ 12 * base ^ 6 := by
    simp [executionBudget, base]
  unfold executionSteps
  calc
    (executeRounds input seed (executionBudget n) (fun _ ↦ 0)).2 +
          (findExecutionViolation input seed (executionCounts input seed)).2 +
          (n + 1) ^ 4 ≤
        (1 + executionBudget n *
          (executionTestSteps n * n ^ 6 + 2)) +
          (executionTestSteps n * n ^ 6 + 1) + base ^ 4 := by
      gcongr
    _ ≤ (1 + (12 * base ^ 6) * (26522 * base ^ 13)) +
          (26520 * base ^ 7 * base ^ 6 + 1) + base ^ 4 := by
      gcongr
    _ = 318264 * base ^ 19 + 26520 * base ^ 13 + base ^ 4 + 2 := by ring
    _ ≤ 400000 * base ^ 20 := by
      have h4 : base ^ 4 ≤ base ^ 20 := pow_le_pow_right' hbase (by omega)
      have h13 : base ^ 13 ≤ base ^ 20 := pow_le_pow_right' hbase (by omega)
      have h19 : base ^ 19 ≤ base ^ 20 := pow_le_pow_right' hbase (by omega)
      have hone : 1 ≤ base ^ 20 := Nat.one_le_pow _ _ hbase
      nlinarith

end Lax47Proofs.OperationalReduction
