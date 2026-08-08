import Lax47.Reduction
import Lax41Proofs.MoserTardos
import Lax41Proofs.HaeuplerSahaSrinivasanTheorem22
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false

namespace Lax47Proofs.Construction

open scoped ENNReal BigOperators
open Lax47.Reduction
open Lax41.MoserTardosDefinitions
open Lax41.HaeuplerSahaSrinivasanDefinitions

noncomputable section

/-! ### The resampling instance -/

/-- The complete blow-up of $H$: each input vertex is replaced by $n$ twins. -/
def blowup {n : ℕ} (H : SimpleGraph (Fin n)) :
    SimpleGraph (BlowupVertex n) :=
  H.comap Prod.fst

/-- Ordered triples are used as triangle-event names.  The six names of a
triangle are harmless and make the event type independent of $H$. -/
abbrev VertexTriple (n : ℕ) :=
  BlowupVertex n × BlowupVertex n × BlowupVertex n

/-- In addition to triangle events, the common event universe contains one
query event for every prospective independent set. -/
abbrev ReductionEvent (n : ℕ) :=
  VertexTriple n ⊕ Finset (BlowupVertex n)

private def firstVertex {n : ℕ} (t : VertexTriple n) : BlowupVertex n := t.1
private def secondVertex {n : ℕ} (t : VertexTriple n) : BlowupVertex n := t.2.1
private def thirdVertex {n : ℕ} (t : VertexTriple n) : BlowupVertex n := t.2.2

/-- The three edge variables on an ordered triple. -/
def triangleVariables {n : ℕ} (t : VertexTriple n) :
    Finset (EdgeVariable n) := by
  classical
  exact {s(firstVertex t, secondVertex t),
    s(firstVertex t, thirdVertex t), s(secondVertex t, thirdVertex t)}

/-- Whether an ordered triple names a triangle of the complete blow-up. -/
def IsBlowupTriangle {n : ℕ} (H : SimpleGraph (Fin n))
    (t : VertexTriple n) : Prop :=
  (blowup H).Adj (firstVertex t) (secondVertex t) ∧
    (blowup H).Adj (firstVertex t) (thirdVertex t) ∧
    (blowup H).Adj (secondVertex t) (thirdVertex t)

/-- The triangle events on which Moser--Tardos runs. -/
def badEvents {n : ℕ} (H : SimpleGraph (Fin n)) :
    Finset (ReductionEvent n) := by
  classical
  exact Finset.univ.filter fun A ↦ match A with
    | Sum.inl t => IsBlowupTriangle H t
    | Sum.inr _ => False

/-- Variables determining either a bad triangle or an independent-set query. -/
noncomputable def variablesOf {n : ℕ} (H : SimpleGraph (Fin n)) :
    ReductionEvent n → Finset (EdgeVariable n) := by
  classical
  exact fun
    | Sum.inl t => triangleVariables t
    | Sum.inr S => (blowup H).edgeFinset ∩ S.sym2

/-- A triangle event says that its three edges are present; a query event says
that all blow-up edges induced by the queried set are absent. -/
noncomputable def eventSet {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∀ A : ReductionEvent n,
      Set (LocalAssignment (fun _ : EdgeVariable n ↦ Bool) (variablesOf H A)) := by
  classical
  exact fun
    | Sum.inl _ => {a | ∀ e, a e = true}
    | Sum.inr _ => {a | ∀ e, a e = false}

/-- On a finite Boolean assignment space, choosing an arbitrary currently true
event is a measurable resampling rule. -/
noncomputable def chooseViolation
    {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (scope : E → Finset I)
    (bad : ∀ e, Set (LocalAssignment (fun _ : I ↦ Bool) (scope e))) :
    ResamplingRule (fun _ : I ↦ Bool) scope bad := by
  classical
  let pick (assignment : Assignment (fun _ : I ↦ Bool)) : Option E :=
    if h : ∃ e, violates (fun _ : I ↦ Bool) scope bad assignment e
      then some (Classical.choose h) else none
  refine
    { choose := pick
      measurable_fiber := fun _ ↦ Set.toFinite _ |>.measurableSet
      sound := ?_
      complete := ?_ }
  · intro assignment A hchoose
    dsimp only [pick] at hchoose
    split at hchoose
    next h =>
      have hA : Classical.choose h = A := Option.some.inj hchoose
      rw [← hA]
      exact Classical.choose_spec h
    next => simp at hchoose
  · intro assignment hchoose
    dsimp only [pick] at hchoose
    split at hchoose
    next => simp at hchoose
    next h => simpa only [not_exists] using h

/-- Bad-event scopes, in the notation of the HSS theorem. -/
abbrev badVariables {n : ℕ} (H : SimpleGraph (Fin n)) :=
  badEventVariables (badEvents H) (variablesOf H)

/-- Bad-event sets, in the notation of the HSS theorem. -/
abbrev badSet {n : ℕ} (H : SimpleGraph (Fin n)) :=
  badEventSet (fun _ : EdgeVariable n ↦ Bool)
    (badEvents H) (variablesOf H) (eventSet H)

/-- The fixed deterministic rule used by the reduction. -/
noncomputable def selectionRule {n : ℕ} (H : SimpleGraph (Fin n)) :
    ResamplingRule (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) := by
  classical
  exact chooseViolation (badVariables H) (badSet H)

/-- Sampling probability $1/(100(n+1))$. The extra slack absorbs the six
ordered names of every triangle. -/
def edgeChance (n : ℕ) : NNReal :=
  (100 * ((n + 1 : ℕ) : NNReal))⁻¹

lemma edgeChance_le_one (n : ℕ) : edgeChance n ≤ 1 := by
  rw [edgeChance, inv_le_one₀]
  · calc
      (1 : NNReal) ≤ 100 := by norm_num
      _ ≤ 100 * ((n + 1 : ℕ) : NNReal) := by
        have hn : (1 : NNReal) ≤ ((n + 1 : ℕ) : NNReal) := by
          exact_mod_cast Nat.succ_pos n
        simpa only [mul_one] using mul_le_mul_left' hn (100 : NNReal)
  · positivity

/-- Every edge variable is an independent Bernoulli sample. -/
noncomputable def distribution (n : ℕ) (_ : EdgeVariable n) :
    MeasureTheory.Measure Bool :=
  (PMF.bernoulli (edgeChance n) (edgeChance_le_one n)).toMeasure

instance distribution_isProbabilityMeasure (n : ℕ) (e : EdgeVariable n) :
    MeasureTheory.IsProbabilityMeasure (distribution n e) := by
  unfold distribution
  infer_instance

/-- The product distribution on infinite resampling tables. -/
noncomputable def sampleMeasure (n : ℕ) :
    MeasureTheory.Measure (SampleTable n) :=
  tableMeasure (fun _ : EdgeVariable n ↦ Bool) (distribution n)

/-- The local-lemma charge assigned to each ordered triangle event. -/
def charge {n : ℕ} (H : SimpleGraph (Fin n))
    (_ : BadEventIndex (badEvents H)) : NNReal :=
  2 * edgeChance n ^ 3

/-- The assignment returned at the first terminating stage. -/
noncomputable def finalAssignment {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) : EdgeVariable n → Bool :=
  outputAssignment (fun _ : EdgeVariable n ↦ Bool)
    (badEvents H) (variablesOf H) (eventSet H) (selectionRule H) table

/-- Keep precisely the sampled edges of the complete blow-up. -/
noncomputable def outputGraph {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) : SimpleGraph (BlowupVertex n) :=
  SimpleGraph.fromEdgeSet
    {e | e ∈ (blowup H).edgeSet ∧ finalAssignment H table e = true}

/-- Total number of resampling steps, one for each resampled ordered triangle. -/
noncomputable def resamplingSteps {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) : ℝ≥0∞ :=
  ∑ A : BadEventIndex (badEvents H),
    resamplingCount (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table A

/-! ### Product probabilities -/

lemma localMeasure_all_true {n : ℕ} (S : Finset (EdgeVariable n)) :
    localMeasure (fun _ : EdgeVariable n ↦ Bool) (distribution n) S
        {a | ∀ e, a e = true} =
      (edgeChance n : ℝ≥0∞) ^ S.card := by
  classical
  rw [localMeasure]
  have hset :
      {a : (∀ _ : S, Bool) | ∀ e, a e = true} =
        Set.pi (Finset.univ : Finset S) (fun _ ↦ ({true} : Set Bool)) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_univ,
      Set.mem_singleton_iff, forall_const]
  rw [hset, MeasureTheory.Measure.infinitePi_pi]
  all_goals simp [distribution, PMF.bernoulli_apply]

lemma localMeasure_all_false {n : ℕ} (S : Finset (EdgeVariable n)) :
    localMeasure (fun _ : EdgeVariable n ↦ Bool) (distribution n) S
        {a | ∀ e, a e = false} =
      ((1 - edgeChance n : NNReal) : ℝ≥0∞) ^ S.card := by
  classical
  rw [localMeasure]
  have hset :
      {a : (∀ _ : S, Bool) | ∀ e, a e = false} =
        Set.pi (Finset.univ : Finset S) (fun _ ↦ ({false} : Set Bool)) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_univ,
      Set.mem_singleton_iff, forall_const]
  rw [hset, MeasureTheory.Measure.infinitePi_pi]
  all_goals simp [distribution, PMF.bernoulli_apply]

/-! ### Triangle-event facts -/

lemma triangleVariables_card {n : ℕ} {H : SimpleGraph (Fin n)}
    {t : VertexTriple n} (ht : IsBlowupTriangle H t) :
    (triangleVariables t).card = 3 := by
  rcases ht with ⟨hab, hac, hbc⟩
  have hab' := (blowup H).ne_of_adj hab
  have hac' := (blowup H).ne_of_adj hac
  have hbc' := (blowup H).ne_of_adj hbc
  have eab_ne_eac :
      s(firstVertex t, secondVertex t) ≠ s(firstVertex t, thirdVertex t) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hbc' h.2
    · exact hac' h.1
  have eab_ne_ebc :
      s(firstVertex t, secondVertex t) ≠ s(secondVertex t, thirdVertex t) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hab' h.1
    · exact hac' h.1
  have eac_ne_ebc :
      s(firstVertex t, thirdVertex t) ≠ s(secondVertex t, thirdVertex t) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hab' h.1
    · exact hac' h.1
  simp [triangleVariables, eab_ne_eac, eab_ne_ebc, eac_ne_ebc]

lemma badIndex_spec {n : ℕ} {H : SimpleGraph (Fin n)}
    (A : BadEventIndex (badEvents H)) :
    ∃ t : VertexTriple n, A.1 = Sum.inl t ∧ IsBlowupTriangle H t := by
  rcases A with ⟨A, hA⟩
  simp only [badEvents, Finset.mem_filter, Finset.mem_univ, true_and] at hA
  cases A with
  | inl t => exact ⟨t, rfl, hA⟩
  | inr S => exact False.elim hA

lemma bad_event_measurable {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∀ A : ReductionEvent n, MeasurableSet (eventSet H A) := by
  intro A
  exact Set.toFinite _ |>.measurableSet

lemma bad_event_probability {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) :
    eventProbability (fun _ : EdgeVariable n ↦ Bool) (distribution n)
        (badVariables H) (badSet H) A =
      (edgeChance n : ℝ≥0∞) ^ 3 := by
  obtain ⟨t, hAt, ht⟩ := badIndex_spec A
  rcases A with ⟨A, hA⟩
  dsimp only at hAt ⊢
  subst A
  rw [eventProbability]
  change localMeasure (fun _ : EdgeVariable n ↦ Bool) (distribution n)
      (variablesOf H (Sum.inl t)) (eventSet H (Sum.inl t)) = _
  simpa only [variablesOf, eventSet, triangleVariables_card ht] using
    localMeasure_all_true (n := n) (triangleVariables t)

lemma query_event_probability {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) :
    eventProbability (fun _ : EdgeVariable n ↦ Bool) (distribution n)
        (variablesOf H) (eventSet H) (Sum.inr S) =
      ((1 - edgeChance n : NNReal) : ℝ≥0∞) ^
        (variablesOf H (Sum.inr S)).card := by
  rw [eventProbability]
  change localMeasure (fun _ : EdgeVariable n ↦ Bool) (distribution n)
      (variablesOf H (Sum.inr S)) (eventSet H (Sum.inr S)) = _
  simpa only [eventSet] using
    localMeasure_all_false (n := n) (variablesOf H (Sum.inr S))

/-! ### Dependency-degree bound -/

/-- The six possible positions and orientations of a fixed unordered edge in
an ordered triple. -/
def triplesWithEdge {n : ℕ} (u v : BlowupVertex n) :
    Finset (VertexTriple n) := by
  classical
  exact
    (Finset.univ.image fun w ↦ (u, v, w)) ∪
    (Finset.univ.image fun w ↦ (v, u, w)) ∪
    (Finset.univ.image fun w ↦ (u, w, v)) ∪
    (Finset.univ.image fun w ↦ (v, w, u)) ∪
    (Finset.univ.image fun w ↦ (w, u, v)) ∪
    (Finset.univ.image fun w ↦ (w, v, u))

lemma mem_triplesWithEdge_of_mem_triangleVariables {n : ℕ}
    {u v : BlowupVertex n} {t : VertexTriple n}
    (h : s(u, v) ∈ triangleVariables t) :
    t ∈ triplesWithEdge u v := by
  classical
  rcases t with ⟨a, b, c⟩
  simp_all [triangleVariables, triplesWithEdge, firstVertex, secondVertex,
    thirdVertex, Sym2.eq_iff]
  aesop

lemma card_triplesWithEdge_le {n : ℕ} (u v : BlowupVertex n) :
    (triplesWithEdge u v).card ≤ 6 * n ^ 2 := by
  classical
  let S₁ : Finset (VertexTriple n) := Finset.univ.image fun w ↦ (u, v, w)
  let S₂ : Finset (VertexTriple n) := Finset.univ.image fun w ↦ (v, u, w)
  let S₃ : Finset (VertexTriple n) := Finset.univ.image fun w ↦ (u, w, v)
  let S₄ : Finset (VertexTriple n) := Finset.univ.image fun w ↦ (v, w, u)
  let S₅ : Finset (VertexTriple n) := Finset.univ.image fun w ↦ (w, u, v)
  let S₆ : Finset (VertexTriple n) := Finset.univ.image fun w ↦ (w, v, u)
  have h₁ : S₁.card ≤ n ^ 2 := by
    calc S₁.card ≤ Finset.univ.card := Finset.card_image_le
      _ = n ^ 2 := by simp [Fintype.card_prod, pow_two]
  have h₂ : S₂.card ≤ n ^ 2 := by
    calc S₂.card ≤ Finset.univ.card := Finset.card_image_le
      _ = n ^ 2 := by simp [Fintype.card_prod, pow_two]
  have h₃ : S₃.card ≤ n ^ 2 := by
    calc S₃.card ≤ Finset.univ.card := Finset.card_image_le
      _ = n ^ 2 := by simp [Fintype.card_prod, pow_two]
  have h₄ : S₄.card ≤ n ^ 2 := by
    calc S₄.card ≤ Finset.univ.card := Finset.card_image_le
      _ = n ^ 2 := by simp [Fintype.card_prod, pow_two]
  have h₅ : S₅.card ≤ n ^ 2 := by
    calc S₅.card ≤ Finset.univ.card := Finset.card_image_le
      _ = n ^ 2 := by simp [Fintype.card_prod, pow_two]
  have h₆ : S₆.card ≤ n ^ 2 := by
    calc S₆.card ≤ Finset.univ.card := Finset.card_image_le
      _ = n ^ 2 := by simp [Fintype.card_prod, pow_two]
  have h₁₂ := Finset.card_union_le S₁ S₂
  have h₁₂₃ := Finset.card_union_le (S₁ ∪ S₂) S₃
  have h₁₂₃₄ := Finset.card_union_le (S₁ ∪ S₂ ∪ S₃) S₄
  have h₁₂₃₄₅ := Finset.card_union_le (S₁ ∪ S₂ ∪ S₃ ∪ S₄) S₅
  have h₁₂₃₄₅₆ :=
    Finset.card_union_le (S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅) S₆
  change (S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅ ∪ S₆).card ≤ 6 * n ^ 2
  omega

/-- Ordered triples whose three-edge scope contains $e$. -/
def triplesUsing {n : ℕ} (e : EdgeVariable n) : Finset (VertexTriple n) := by
  classical
  exact Finset.univ.filter fun t ↦ e ∈ triangleVariables t

lemma card_triplesUsing_le {n : ℕ} (e : EdgeVariable n) :
    (triplesUsing e).card ≤ 6 * n ^ 2 := by
  classical
  induction e using Sym2.ind with
  | _ u v =>
      calc
        (triplesUsing s(u, v)).card ≤ (triplesWithEdge u v).card := by
          apply Finset.card_le_card
          intro t ht
          simp only [triplesUsing, Finset.mem_filter, Finset.mem_univ,
            true_and] at ht
          exact mem_triplesWithEdge_of_mem_triangleVariables ht
        _ ≤ 6 * n ^ 2 := card_triplesWithEdge_le u v

/-- Recover the ordered triple underlying a bad-event index. -/
noncomputable def badTriple {n : ℕ} {H : SimpleGraph (Fin n)}
    (A : BadEventIndex (badEvents H)) : VertexTriple n :=
  Classical.choose (badIndex_spec A)

lemma badTriple_spec {n : ℕ} {H : SimpleGraph (Fin n)}
    (A : BadEventIndex (badEvents H)) :
    A.1 = Sum.inl (badTriple A) ∧ IsBlowupTriangle H (badTriple A) :=
  Classical.choose_spec (badIndex_spec A)

lemma badTriple_injective {n : ℕ} {H : SimpleGraph (Fin n)} :
    Function.Injective (badTriple (H := H)) := by
  intro A B hAB
  apply Subtype.ext
  calc
    A.1 = Sum.inl (badTriple A) := (badTriple_spec A).1
    _ = Sum.inl (badTriple B) := congrArg Sum.inl hAB
    _ = B.1 := (badTriple_spec B).1.symm

/-- The embedding of bad-event indices into their ordered triples. -/
noncomputable def badTripleEmbedding {n : ℕ} (H : SimpleGraph (Fin n)) :
    BadEventIndex (badEvents H) ↪ VertexTriple n :=
  ⟨badTriple, badTriple_injective⟩

local instance badEventIndexDecidableEq {n : ℕ} {H : SimpleGraph (Fin n)} :
    DecidableEq (BadEventIndex (badEvents H)) :=
  Classical.decEq _

lemma badVariables_eq_triangleVariables {n : ℕ} {H : SimpleGraph (Fin n)}
    (A : BadEventIndex (badEvents H)) :
    badVariables H A = triangleVariables (badTriple A) := by
  change variablesOf H A.1 = _
  rw [(badTriple_spec A).1]
  rfl

/-- Every dependent bad event uses one of the three variables of $A$, and
each variable occurs in at most $6n^2$ ordered triples. -/
lemma dependency_card_le {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) :
    (Lax41.MoserTardosDefinitions.dependencyNeighborhood
      (badVariables H) A).card ≤ 18 * n ^ 2 := by
  classical
  let D := Lax41.MoserTardosDefinitions.dependencyNeighborhood
    (badVariables H) A
  let candidates := (triangleVariables (badTriple A)).biUnion triplesUsing
  have hcandidates : candidates.card ≤ 18 * n ^ 2 := by
    calc
      candidates.card ≤ (triangleVariables (badTriple A)).card * (6 * n ^ 2) := by
        exact Finset.card_biUnion_le_card_mul _ _ _ fun e _ ↦ card_triplesUsing_le e
      _ = 18 * n ^ 2 := by
        rw [triangleVariables_card (badTriple_spec A).2]
        omega
  have hsubset : D.map (badTripleEmbedding H) ⊆ candidates := by
    intro t ht
    simp only [Finset.mem_map] at ht
    obtain ⟨C, hCD, rfl⟩ := ht
    have hoverlap : ¬Disjoint (badVariables H A) (badVariables H C) := by
      have hCD' : C ≠ A ∧ ¬Disjoint (badVariables H A) (badVariables H C) := by
        simpa only [D, Lax41.MoserTardosDefinitions.dependencyNeighborhood,
          Finset.mem_filter, Finset.mem_univ, true_and] using hCD
      exact hCD'.2
    rw [badVariables_eq_triangleVariables,
      badVariables_eq_triangleVariables] at hoverlap
    obtain ⟨e, heA, heC⟩ := Finset.not_disjoint_iff.mp hoverlap
    simp only [candidates, Finset.mem_biUnion]
    refine ⟨e, heA, ?_⟩
    change badTriple C ∈ triplesUsing e
    simp [triplesUsing, heC]
  calc
    D.card = (D.map (badTripleEmbedding H)).card :=
      (Finset.card_map (badTripleEmbedding H)).symm
    _ ≤ candidates.card := Finset.card_le_card hsubset
    _ ≤ 18 * n ^ 2 := hcandidates

/-- A query depending on $m$ edge variables can overlap at most $6n^2m$
ordered triangle events. -/
lemma query_dependency_card_le {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) :
    (Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
      (badEvents H) (variablesOf H) (Sum.inr S)).card ≤
        (variablesOf H (Sum.inr S)).card * (6 * n ^ 2) := by
  classical
  let D := Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
    (badEvents H) (variablesOf H) (Sum.inr S)
  let candidates := (variablesOf H (Sum.inr S)).biUnion triplesUsing
  have hcandidates : candidates.card ≤
      (variablesOf H (Sum.inr S)).card * (6 * n ^ 2) := by
    exact Finset.card_biUnion_le_card_mul _ _ _ fun e _ ↦ card_triplesUsing_le e
  have hsubset : D.map (badTripleEmbedding H) ⊆ candidates := by
    intro t ht
    simp only [Finset.mem_map] at ht
    obtain ⟨A, hAD, rfl⟩ := ht
    have hoverlap : ¬Disjoint (variablesOf H A.1)
        (variablesOf H (Sum.inr S)) := by
      have hAD' := hAD
      simp only [D,
        Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood,
        Finset.mem_filter, Finset.mem_univ, true_and] at hAD'
      exact hAD'.2
    rw [show variablesOf H A.1 = triangleVariables (badTriple A) by
      exact badVariables_eq_triangleVariables A] at hoverlap
    obtain ⟨e, heA, heS⟩ := Finset.not_disjoint_iff.mp hoverlap
    simp only [candidates, Finset.mem_biUnion]
    refine ⟨e, heS, ?_⟩
    change badTriple A ∈ triplesUsing e
    simp [triplesUsing, heA]
  calc
    D.card = (D.map (badTripleEmbedding H)).card :=
      (Finset.card_map (badTripleEmbedding H)).symm
    _ ≤ candidates.card := Finset.card_le_card hsubset
    _ ≤ (variablesOf H (Sum.inr S)).card * (6 * n ^ 2) := hcandidates

/-! ### The local-lemma inequalities -/

lemma edgeChance_pos (n : ℕ) : 0 < edgeChance n := by
  unfold edgeChance
  positivity

lemma edgeChance_le_hundredth (n : ℕ) :
    edgeChance n ≤ (1 / 100 : NNReal) := by
  unfold edgeChance
  rw [one_div]
  rw [inv_le_inv₀ (by positivity) (by norm_num)]
  calc
    (100 : NNReal) = 100 * 1 := by norm_num
    _ ≤ 100 * ((n + 1 : ℕ) : NNReal) := by
      have hn : (1 : NNReal) ≤ ((n + 1 : ℕ) : NNReal) := by
        exact_mod_cast Nat.succ_pos n
      exact mul_le_mul_left' hn 100

lemma charge_pos {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) : 0 < charge H A := by
  simp only [charge]
  exact mul_pos (by norm_num) (pow_pos (edgeChance_pos n) 3)

lemma charge_lt_one {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) : charge H A < 1 := by
  have hp := edgeChance_le_hundredth n
  simp only [charge]
  calc
    2 * edgeChance n ^ 3 ≤ 2 * (1 / 100 : NNReal) ^ 3 := by gcongr
    _ < 1 := by norm_num

lemma charge_mul_dependency_card_le_half {n d : ℕ}
    (hd : d ≤ 18 * n ^ 2) :
    (d : ℝ) * (2 * ((edgeChance n : NNReal) : ℝ) ^ 3) ≤ 1 / 2 := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd' : (d : ℝ) ≤ 18 * (n : ℝ) ^ 2 := by exact_mod_cast hd
  have hpoly : (n : ℝ) ^ 2 ≤ (n + 1) ^ 3 := by
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg hn (sq_nonneg (n : ℝ))]
  have hden : (0 : ℝ) < (100 * (n + 1)) ^ 3 := by positivity
  rw [edgeChance]
  push_cast
  change (d : ℝ) * (2 * ((100 * ((n : ℝ) + 1))⁻¹) ^ 3) ≤ 1 / 2
  rw [inv_pow, ← div_eq_mul_inv]
  rw [show (d : ℝ) * (2 / (100 * ((n : ℝ) + 1)) ^ 3) =
      ((d : ℝ) * 2) / (100 * ((n : ℝ) + 1)) ^ 3 by ring]
  rw [div_le_iff₀ hden]
  nlinarith

/-- One block of at most $6n^2$ triangle dependencies consumes at most a
quarter of the raw edge-deletion probability. -/
lemma query_charge_block_mul_le_quarter (n : ℕ) :
    ((6 * n ^ 2 : ℕ) : ℝ) *
        (2 * ((edgeChance n : NNReal) : ℝ) ^ 3) ≤
      (edgeChance n : ℝ) / 4 := by
  have hn : (0 : ℝ) ≤ n := by positivity
  rw [edgeChance]
  push_cast
  change (6 * (n : ℝ) ^ 2) *
      (2 * ((100 * ((n : ℝ) + 1))⁻¹) ^ 3) ≤
        (100 * ((n : ℝ) + 1))⁻¹ / 4
  have hden : (0 : ℝ) < 100 * (n + 1) := by positivity
  field_simp
  nlinarith [sq_nonneg (n : ℝ)]

lemma query_block_survival_lower (n : ℕ) :
    (1 - edgeChance n / 4 : NNReal) ≤
      (1 - 2 * edgeChance n ^ 3 : NNReal) ^ (6 * n ^ 2) := by
  have hp : (edgeChance n : ℝ) ≤ 1 := by
    exact_mod_cast edgeChance_le_one n
  have hx : (2 * edgeChance n ^ 3 : NNReal) < 1 := by
    have hp100 := edgeChance_le_hundredth n
    calc
      2 * edgeChance n ^ 3 ≤ 2 * (1 / 100 : NNReal) ^ 3 := by gcongr
      _ < 1 := by norm_num
  have hmul := query_charge_block_mul_le_quarter n
  have hbern :
      (1 : ℝ) + (6 * n ^ 2 : ℕ) *
          (((1 : ℝ) - 2 * (edgeChance n : ℝ) ^ 3) - 1) ≤
        ((1 : ℝ) - 2 * (edgeChance n : ℝ) ^ 3) ^ (6 * n ^ 2) := by
    exact one_add_mul_sub_le_pow (by
      have hx' : (2 * (edgeChance n : ℝ) ^ 3) ≤ 1 := by exact_mod_cast hx.le
      nlinarith) _
  have hp4le : edgeChance n / 4 ≤ (1 : NNReal) := by
    apply (div_le_one (by norm_num)).2
    exact (edgeChance_le_one n).trans (by norm_num)
  have hp4cast :
      ((1 - edgeChance n / 4 : NNReal) : ℝ) =
        1 - (edgeChance n : ℝ) / 4 := by
    rw [NNReal.coe_sub hp4le, NNReal.coe_div]
    norm_num
  have hxcast :
      ((1 - 2 * edgeChance n ^ 3 : NNReal) : ℝ) =
        1 - 2 * (edgeChance n : ℝ) ^ 3 := by
    rw [NNReal.coe_sub hx.le]
    norm_num
  have hreal :
      (1 : ℝ) - (edgeChance n : ℝ) / 4 ≤
        (1 - 2 * (edgeChance n : ℝ) ^ 3) ^ (6 * n ^ 2) := by
    nlinarith
  rw [← NNReal.coe_le_coe]
  rw [hp4cast, NNReal.coe_pow, hxcast]
  exact hreal

lemma query_correction_block_le (n : ℕ) :
    ((1 - 2 * edgeChance n ^ 3 : NNReal)⁻¹) ^ (6 * n ^ 2) ≤
      (1 - edgeChance n / 4 : NNReal)⁻¹ := by
  have hx : (2 * edgeChance n ^ 3 : NNReal) < 1 := by
    have hp100 := edgeChance_le_hundredth n
    calc
      2 * edgeChance n ^ 3 ≤ 2 * (1 / 100 : NNReal) ^ 3 := by gcongr
      _ < 1 := by norm_num
  have hp4 : edgeChance n / 4 < (1 : NNReal) := by
    calc
      edgeChance n / 4 ≤ (1 : NNReal) / 4 := by gcongr; exact edgeChance_le_one n
      _ < 1 := by norm_num
  rw [inv_pow]
  exact (inv_le_inv₀ (pow_pos (tsub_pos_of_lt hx) _)
    (tsub_pos_of_lt hp4)).2 (query_block_survival_lower n)

lemma query_base_after_correction_le (n : ℕ) :
    (1 - edgeChance n : NNReal) *
        (1 - edgeChance n / 4 : NNReal)⁻¹ ≤
      (1 - edgeChance n / 2 : NNReal) := by
  have hp := edgeChance_le_one n
  have hp2 : edgeChance n / 2 ≤ (1 : NNReal) := by
    apply (div_le_one (by norm_num)).2
    exact hp.trans (by norm_num)
  have hp4 : edgeChance n / 4 < (1 : NNReal) := by
    calc
      edgeChance n / 4 ≤ (1 : NNReal) / 4 := by gcongr
      _ < 1 := by norm_num
  have hp4le : edgeChance n / 4 ≤ (1 : NNReal) := hp4.le
  have hpcast :
      ((1 - edgeChance n : NNReal) : ℝ) = 1 - edgeChance n := by
    rw [NNReal.coe_sub hp]
    norm_num
  have hp2cast :
      ((1 - edgeChance n / 2 : NNReal) : ℝ) =
        1 - (edgeChance n : ℝ) / 2 := by
    rw [NNReal.coe_sub hp2, NNReal.coe_div]
    norm_num
  have hp4cast :
      ((1 - edgeChance n / 4 : NNReal) : ℝ) =
        1 - (edgeChance n : ℝ) / 4 := by
    rw [NNReal.coe_sub hp4le, NNReal.coe_div]
    norm_num
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_mul, NNReal.coe_inv, hpcast, hp4cast, hp2cast]
  have hp4' : (edgeChance n : ℝ) / 4 < 1 := by
    have hcast : ((edgeChance n / 4 : NNReal) : ℝ) < 1 := by
      exact_mod_cast hp4
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one] using hcast
  rw [← div_eq_mul_inv, div_le_iff₀ (sub_pos.mpr hp4')]
  nlinarith [sq_nonneg (edgeChance n : ℝ)]

lemma query_correction_le {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) :
    (∏ A ∈
        Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
          (badEvents H) (variablesOf H) (Sum.inr S),
        (1 - charge H A)⁻¹ : NNReal) ≤
      (1 - edgeChance n / 4 : NNReal)⁻¹ ^
        (variablesOf H (Sum.inr S)).card := by
  let D := Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
    (badEvents H) (variablesOf H) (Sum.inr S)
  have hD := query_dependency_card_le H S
  have hx : (2 * edgeChance n ^ 3 : NNReal) < 1 := by
    have hp100 := edgeChance_le_hundredth n
    calc
      2 * edgeChance n ^ 3 ≤ 2 * (1 / 100 : NNReal) ^ 3 := by gcongr
      _ < 1 := by norm_num
  have hone : (1 : NNReal) ≤ (1 - 2 * edgeChance n ^ 3 : NNReal)⁻¹ := by
    exact (one_le_inv₀ (tsub_pos_of_lt hx)).2 tsub_le_self
  rw [show (∏ A ∈ D, (1 - charge H A)⁻¹ : NNReal) =
      ((1 - 2 * edgeChance n ^ 3 : NNReal)⁻¹) ^ D.card by
        simp [charge]]
  calc
    ((1 - 2 * edgeChance n ^ 3 : NNReal)⁻¹) ^ D.card ≤
        ((1 - 2 * edgeChance n ^ 3 : NNReal)⁻¹) ^
          ((variablesOf H (Sum.inr S)).card * (6 * n ^ 2)) :=
      pow_le_pow_right' hone hD
    _ = (((1 - 2 * edgeChance n ^ 3 : NNReal)⁻¹) ^ (6 * n ^ 2)) ^
        (variablesOf H (Sum.inr S)).card := by
      rw [Nat.mul_comm, pow_mul]
    _ ≤ ((1 - edgeChance n / 4 : NNReal)⁻¹) ^
        (variablesOf H (Sum.inr S)).card :=
      pow_le_pow_left' (query_correction_block_le n) _

lemma query_hss_upper_nnreal {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) :
    (1 - edgeChance n : NNReal) ^ (variablesOf H (Sum.inr S)).card *
        (∏ A ∈
          Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
            (badEvents H) (variablesOf H) (Sum.inr S),
          (1 - charge H A)⁻¹ : NNReal) ≤
      (1 - edgeChance n / 2 : NNReal) ^
        (variablesOf H (Sum.inr S)).card := by
  calc
    (1 - edgeChance n : NNReal) ^ (variablesOf H (Sum.inr S)).card *
        (∏ A ∈
          Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
            (badEvents H) (variablesOf H) (Sum.inr S),
          (1 - charge H A)⁻¹ : NNReal) ≤
        (1 - edgeChance n : NNReal) ^ (variablesOf H (Sum.inr S)).card *
          (1 - edgeChance n / 4 : NNReal)⁻¹ ^
            (variablesOf H (Sum.inr S)).card := by
      exact mul_le_mul_left' (query_correction_le H S) _
    _ = ((1 - edgeChance n : NNReal) *
        (1 - edgeChance n / 4 : NNReal)⁻¹) ^
          (variablesOf H (Sum.inr S)).card := by rw [mul_pow]
    _ ≤ (1 - edgeChance n / 2 : NNReal) ^
        (variablesOf H (Sum.inr S)).card :=
      pow_le_pow_left' (query_base_after_correction_le n) _

lemma half_le_dependency_product {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) :
    (1 / 2 : NNReal) ≤
      ∏ B ∈ Lax41.MoserTardosDefinitions.dependencyNeighborhood
        (badVariables H) A, (1 - charge H B : NNReal) := by
  let D := Lax41.MoserTardosDefinitions.dependencyNeighborhood
    (badVariables H) A
  have hcard := charge_mul_dependency_card_le_half (dependency_card_le H A)
  have hcard' : (D.card : ℝ) * (charge H A : ℝ) ≤ 1 / 2 := by
    simpa only [D, charge, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow] using hcard
  have hxle : (charge H A : ℝ) ≤ 1 := (charge_lt_one H A).le
  have hbern :
      (1 : ℝ) + D.card * (((1 : ℝ) - charge H A) - 1) ≤
        ((1 : ℝ) - charge H A) ^ D.card := by
    exact one_add_mul_sub_le_pow (by nlinarith) D.card
  have hreal : (1 / 2 : ℝ) ≤ ((1 : ℝ) - charge H A) ^ D.card := by
    nlinarith
  rw [show (∏ B ∈ D, (1 - charge H B : NNReal)) =
      (1 - charge H A : NNReal) ^ D.card by simp [charge]]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    NNReal.coe_pow, NNReal.coe_sub (charge_lt_one H A).le]
  exact hreal

lemma local_lemma_hypothesis {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) :
    eventProbability (fun _ : EdgeVariable n ↦ Bool) (distribution n)
        (badVariables H) (badSet H) A ≤
      ((charge H A * ∏ B ∈
        Lax41.MoserTardosDefinitions.dependencyNeighborhood
          (badVariables H) A, (1 - charge H B) : NNReal) : ℝ≥0∞) := by
  rw [bad_event_probability]
  rw [← ENNReal.coe_pow]
  apply ENNReal.coe_le_coe.mpr
  calc
    edgeChance n ^ 3 = charge H A * (1 / 2 : NNReal) := by
      simp only [charge]
      field_simp
    _ ≤ charge H A * ∏ B ∈
        Lax41.MoserTardosDefinitions.dependencyNeighborhood
          (badVariables H) A, (1 - charge H B : NNReal) := by
      exact mul_le_mul_left' (half_le_dependency_product H A) _

lemma dependencyNeighborhood_eq {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) :
    Lax41.MoserTardosDefinitions.dependencyNeighborhood (badVariables H) A =
      Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
        (badEvents H) (variablesOf H) A.1 := by
  classical
  ext C
  simp only [Lax41.MoserTardosDefinitions.dependencyNeighborhood,
    Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood,
    Finset.mem_filter, Finset.mem_univ, true_and, badVariables,
    badEventVariables]
  constructor
  · rintro ⟨hne, hoverlap⟩
    exact ⟨fun h ↦ hne (Subtype.ext h), fun hd ↦ hoverlap hd.symm⟩
  · rintro ⟨hne, hoverlap⟩
    exact ⟨fun h ↦ hne (congrArg Subtype.val h), fun hd ↦ hoverlap hd.symm⟩

/-- The imported, axiom-free Moser--Tardos theorem specialized to the
triangle resampling instance. -/
noncomputable def moserTardos_certificate {n : ℕ} (H : SimpleGraph (Fin n)) :=
  Lax41Proofs.moser_tardos (fun _ : EdgeVariable n ↦ Bool)
    (distribution n) (badVariables H) (badSet H)
    (fun _ ↦ Set.toFinite _ |>.measurableSet) (selectionRule H)
    (charge H) (charge_pos H) (charge_lt_one H)
    (local_lemma_hypothesis H)

/-- The imported, axiom-free HSS distributional theorem specialized to the
same run and to any observation in the common event universe. -/
noncomputable def hss_certificate {n : ℕ} (H : SimpleGraph (Fin n))
    (B : ReductionEvent n) :=
  Lax41Proofs.theorem_2_2 (fun _ : EdgeVariable n ↦ Bool)
    (distribution n) (badEvents H) (variablesOf H) (eventSet H)
    (bad_event_measurable H) (selectionRule H) (charge H)
    (charge_pos H) (charge_lt_one H)
    (fun A ↦ by
      rw [← dependencyNeighborhood_eq H A]
      exact local_lemma_hypothesis H A)
    B

/-- The probability that a fixed vertex set survives as an independent set in
the output is exponentially small in the number of queried blow-up edges. -/
lemma query_output_probability_le {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) :
    sampleMeasure n
        (eventOccursInOutput (fun _ : EdgeVariable n ↦ Bool)
          (badEvents H) (variablesOf H) (eventSet H) (selectionRule H)
          (Sum.inr S)) ≤
      ((1 - edgeChance n / 2 : NNReal) : ℝ≥0∞) ^
        (variablesOf H (Sum.inr S)).card := by
  have h := (hss_certificate H (Sum.inr S)).2
  rw [query_event_probability H S] at h
  calc
    sampleMeasure n
        (eventOccursInOutput (fun _ : EdgeVariable n ↦ Bool)
          (badEvents H) (variablesOf H) (eventSet H) (selectionRule H)
          (Sum.inr S)) ≤
        (((1 - edgeChance n : NNReal) ^
            (variablesOf H (Sum.inr S)).card : NNReal) : ℝ≥0∞) *
          ((∏ A ∈
            Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
              (badEvents H) (variablesOf H) (Sum.inr S),
            (1 - charge H A)⁻¹ : NNReal) : ℝ≥0∞) := by
      simpa only [probabilityEventInOutput, sampleMeasure, ENNReal.coe_pow] using h
    _ = (((1 - edgeChance n : NNReal) ^
          (variablesOf H (Sum.inr S)).card *
          (∏ A ∈
            Lax41.HaeuplerSahaSrinivasanDefinitions.dependencyNeighborhood
              (badEvents H) (variablesOf H) (Sum.inr S),
            (1 - charge H A)⁻¹ : NNReal) : NNReal) : ℝ≥0∞) := by
      rw [ENNReal.coe_mul]
    _ ≤ (((1 - edgeChance n / 2 : NNReal) ^
          (variablesOf H (Sum.inr S)).card : NNReal) : ℝ≥0∞) := by
      exact ENNReal.coe_le_coe.mpr (query_hss_upper_nnreal H S)
    _ = ((1 - edgeChance n / 2 : NNReal) : ℝ≥0∞) ^
          (variablesOf H (Sum.inr S)).card := by rw [ENNReal.coe_pow]

/-! ### Almost-sure termination and triangle-freeness -/

lemma local_lemma_bound_hypothesis {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) :
    eventProbability (fun _ : EdgeVariable n ↦ Bool) (distribution n)
        (badVariables H) (badSet H) A ≤
      (Lax41Proofs.localLemmaBound (badVariables H) (charge H) A : ℝ≥0∞) := by
  rw [Lax41Proofs.localLemmaBound_eq_dependencyNeighborhoodProduct]
  exact local_lemma_hypothesis H A

lemma passingTreeCount_lintegral_le {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) :
    (∫⁻ table, Lax41Proofs.passingTreeCount
        (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H) table A
      ∂sampleMeasure n) ≤ (Lax41Proofs.odds (charge H) A : ℝ≥0∞) := by
  apply Lax41Proofs.lintegral_passingTreeCount_le_of_charge
    (fun _ : EdgeVariable n ↦ Bool) (distribution n)
    (badVariables H) (badSet H)
    (fun _ ↦ Set.toFinite _ |>.measurableSet)
  exact Lax41Proofs.charge_of_localLemmaBound
    (badVariables H)
    (eventProbability (fun _ : EdgeVariable n ↦ Bool) (distribution n)
      (badVariables H) (badSet H))
    (charge H) (charge_lt_one H) (local_lemma_bound_hypothesis H)

lemma eventually_passingTreeCount_lt_top {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∀ᵐ table ∂sampleMeasure n,
      ∀ A : BadEventIndex (badEvents H),
        Lax41Proofs.passingTreeCount
          (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H) table A < ⊤ := by
  rw [Filter.eventually_all]
  intro A
  apply MeasureTheory.ae_lt_top
    (Lax41Proofs.measurable_passingTreeCount
      (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H)
      (fun _ ↦ Set.toFinite _ |>.measurableSet) A)
  exact ne_of_lt ((passingTreeCount_lintegral_le H A).trans_lt ENNReal.coe_lt_top)

lemma exists_termination_time {n : ℕ} {H : SimpleGraph (Fin n)}
    {table : SampleTable n}
    (hpass : ∀ A : BadEventIndex (badEvents H),
      Lax41Proofs.passingTreeCount
        (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H) table A < ⊤) :
    ∃ t, resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table t = none :=
  Lax41Proofs.exists_termination_time_of_passing_lt_top
    (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H)
    (selectionRule H) table hpass

lemma resamplingLog_outputTime_eq_none {n : ℕ} {H : SimpleGraph (Fin n)}
    {table : SampleTable n}
    (hterm : ∃ t, resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table t = none) :
    resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table
      (outputTime (fun _ : EdgeVariable n ↦ Bool)
        (badEvents H) (variablesOf H) (eventSet H) (selectionRule H) table) = none := by
  rw [outputTime]
  simp only [dif_pos hterm]
  exact Nat.find_spec hterm

lemma finalAssignment_avoids_badEvents {n : ℕ} {H : SimpleGraph (Fin n)}
    {table : SampleTable n}
    (hterm : ∃ t, resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table t = none) :
    ∀ A : BadEventIndex (badEvents H),
      ¬violates (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) (finalAssignment H table) A := by
  apply (selectionRule H).complete
  simpa only [resamplingLog, finalAssignment, outputAssignment] using
    resamplingLog_outputTime_eq_none hterm

lemma outputGraph_adj_iff {n : ℕ} {H : SimpleGraph (Fin n)}
    {table : SampleTable n} {u v : BlowupVertex n} :
    (outputGraph H table).Adj u v ↔
      (blowup H).Adj u v ∧ finalAssignment H table s(u, v) = true := by
  constructor
  · intro h
    rcases (SimpleGraph.fromEdgeSet_adj _).mp h with ⟨⟨hedge, hvalue⟩, _⟩
    exact ⟨(SimpleGraph.mem_edgeSet (blowup H)).mp hedge, hvalue⟩
  · rintro ⟨hadj, hvalue⟩
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    exact ⟨⟨(SimpleGraph.mem_edgeSet (blowup H)).mpr hadj, hvalue⟩,
      (blowup H).ne_of_adj hadj⟩

lemma violates_badEvent_of_output_triangle {n : ℕ} {H : SimpleGraph (Fin n)}
    {table : SampleTable n} {a b c : BlowupVertex n}
    (hab : (outputGraph H table).Adj a b)
    (hac : (outputGraph H table).Adj a c)
    (hbc : (outputGraph H table).Adj b c) :
    ∃ A : BadEventIndex (badEvents H),
      violates (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) (finalAssignment H table) A := by
  let t : VertexTriple n := (a, b, c)
  have ht : IsBlowupTriangle H t := by
    exact ⟨(outputGraph_adj_iff.mp hab).1,
      (outputGraph_adj_iff.mp hac).1, (outputGraph_adj_iff.mp hbc).1⟩
  have hmem : Sum.inl t ∈ badEvents H := by
    simp [badEvents, ht]
  let A : BadEventIndex (badEvents H) := ⟨Sum.inl t, hmem⟩
  refine ⟨A, ?_⟩
  change ∀ e : triangleVariables t, finalAssignment H table e.1 = true
  rintro ⟨e, he⟩
  simp only [triangleVariables, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact (outputGraph_adj_iff.mp hab).2
  · exact (outputGraph_adj_iff.mp hac).2
  · exact (outputGraph_adj_iff.mp hbc).2

lemma outputGraph_triangleFree_of_terminates {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n)
    (hterm : ∃ t, resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table t = none) :
    (outputGraph H table).CliqueFree 3 := by
  have hgood := finalAssignment_avoids_badEvents hterm
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hS
  obtain ⟨A, hA⟩ := violates_badEvent_of_output_triangle hab hac hbc
  exact hgood A hA

theorem outputGraph_triangleFree_ae {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∀ᵐ table ∂sampleMeasure n, (outputGraph H table).CliqueFree 3 := by
  filter_upwards [eventually_passingTreeCount_lt_top H] with table hpass
  exact outputGraph_triangleFree_of_terminates H table (exists_termination_time hpass)

/-! ### Completeness -/

theorem outputGraph_completeness {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) :
    H.indepNum * n ≤ (outputGraph H table).indepNum := by
  classical
  obtain ⟨S, hS⟩ := H.exists_isNIndepSet_indepNum
  let T : Finset (BlowupVertex n) := S ×ˢ (Finset.univ : Finset (Fin n))
  have hT : (outputGraph H table).IsIndepSet T := by
    intro u hu v hv huv hout
    have huS : u.1 ∈ S := (Finset.mem_product.mp hu).1
    have hvS : v.1 ∈ S := (Finset.mem_product.mp hv).1
    have hadj : H.Adj u.1 v.1 := (outputGraph_adj_iff.mp hout).1
    exact hS.1 huS hvS (H.ne_of_adj hadj) hadj
  calc
    H.indepNum * n = S.card * n := by rw [hS.2]
    _ = T.card := by simp [T]
    _ ≤ (outputGraph H table).indepNum := hT.card_le_indepNum

/-! ### Expected polynomial number of steps -/

lemma charge_le_half {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) : charge H A ≤ (1 / 2 : NNReal) := by
  have hp := edgeChance_le_hundredth n
  simp only [charge]
  calc
    2 * edgeChance n ^ 3 ≤ 2 * (1 / 100 : NNReal) ^ 3 := by gcongr
    _ ≤ 1 / 2 := by
      rw [← NNReal.coe_le_coe]
      norm_num

lemma odds_le_one {n : ℕ} (H : SimpleGraph (Fin n))
    (A : BadEventIndex (badEvents H)) : Lax41Proofs.odds (charge H) A ≤ 1 := by
  rw [Lax41Proofs.odds, div_le_one (tsub_pos_of_lt (charge_lt_one H A))]
  rw [← NNReal.coe_le_coe, NNReal.coe_sub (charge_lt_one H A).le]
  have hhalf : (charge H A : ℝ) ≤ 1 / 2 := by
    exact_mod_cast charge_le_half H A
  norm_num at hhalf ⊢
  nlinarith

lemma card_badEventIndex_le {n : ℕ} (H : SimpleGraph (Fin n)) :
    Fintype.card (BadEventIndex (badEvents H)) ≤ n ^ 6 := by
  calc
    Fintype.card (BadEventIndex (badEvents H)) ≤ Fintype.card (VertexTriple n) :=
      Fintype.card_le_of_injective (badTripleEmbedding H) badTriple_injective
    _ = n ^ 6 := by
      simp only [VertexTriple, BlowupVertex, Fintype.card_prod, Fintype.card_fin]
      ring

/-- The expected resampling bound is the Moser--Tardos theorem itself,
specialized to the triangle events. -/
theorem expectedResamplingCounts_polynomial {n : ℕ} (H : SimpleGraph (Fin n)) :
    (∑ A : BadEventIndex (badEvents H),
      expectedResamplings (fun _ : EdgeVariable n ↦ Bool)
        (distribution n) (badVariables H) (badSet H) (selectionRule H) A) ≤
      ((n + 1) ^ 6 : ℕ) := by
  calc
    (∑ A : BadEventIndex (badEvents H),
        expectedResamplings (fun _ : EdgeVariable n ↦ Bool)
          (distribution n) (badVariables H) (badSet H) (selectionRule H) A) ≤
        ∑ A : BadEventIndex (badEvents H),
          ((charge H A / (1 - charge H A) : NNReal) : ℝ≥0∞) :=
      (moserTardos_certificate H).2.2
    _ ≤ ∑ _A : BadEventIndex (badEvents H), (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro A _
      exact ENNReal.coe_le_coe.mpr (odds_le_one H A)
    _ = Fintype.card (BadEventIndex (badEvents H)) := by simp
    _ ≤ (n ^ 6 : ℕ) := by exact_mod_cast card_badEventIndex_le H
    _ ≤ ((n + 1) ^ 6 : ℕ) := by
      exact_mod_cast pow_le_pow_left' (Nat.le_succ n) 6

/-- A measurable witness-tree envelope for the number of resamplings. -/
noncomputable def workEnvelope {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) : ℝ≥0∞ :=
  ∑ A : BadEventIndex (badEvents H),
    Lax41Proofs.passingTreeCount (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) table A

/-- The Lax41 witness-tree injection bounds the actual number of resamplings. -/
lemma resamplingSteps_le_workEnvelope {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) :
    resamplingSteps H table ≤ workEnvelope H table := by
  unfold resamplingSteps workEnvelope
  apply Finset.sum_le_sum
  intro A _
  exact Lax41Proofs.resamplingCount_le_passingTreeCount
    (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H)
    (selectionRule H) table A

/-- Finitely many total resamplings force the run to terminate. -/
lemma exists_termination_time_of_resamplingSteps_lt_top {n : ℕ}
    {H : SimpleGraph (Fin n)} {table : SampleTable n}
    (hsteps : resamplingSteps H table < ⊤) :
    ∃ t, resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table t = none := by
  classical
  let times (A : BadEventIndex (badEvents H)) : Set ℕ :=
    {t | resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table t = some A}
  have hfinite (A : BadEventIndex (badEvents H)) : (times A).Finite := by
    apply Lax41Proofs.resamplingTimes_finite_of_count_lt_top
      (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H)
      (selectionRule H) table A
    have hle : resamplingCount (fun _ : EdgeVariable n ↦ Bool)
        (badVariables H) (badSet H) (selectionRule H) table A ≤
        resamplingSteps H table := by
      unfold resamplingSteps
      exact Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ A)
    exact hle.trans_lt hsteps
  have hall : (Set.iUnion times).Finite := Set.finite_iUnion hfinite
  obtain ⟨t, ht⟩ := hall.exists_notMem
  cases hlog : resamplingLog (fun _ : EdgeVariable n ↦ Bool)
      (badVariables H) (badSet H) (selectionRule H) table t with
  | none => exact ⟨t, hlog⟩
  | some A =>
      exfalso
      apply ht
      exact Set.mem_iUnion.mpr ⟨A, hlog⟩

lemma measurable_workEnvelope {n : ℕ} (H : SimpleGraph (Fin n)) :
    Measurable (workEnvelope H) := by
  unfold workEnvelope
  apply Finset.measurable_fun_sum
  intro A _
  exact Lax41Proofs.measurable_passingTreeCount
    (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H)
    (fun _ ↦ Set.toFinite _ |>.measurableSet) A

theorem workEnvelope_expected_polynomial {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∫⁻ table, workEnvelope H table ∂sampleMeasure n ≤ ((n + 1) ^ 6 : ℕ) := by
  calc
    (∫⁻ table, workEnvelope H table ∂sampleMeasure n) =
      ∑ A : BadEventIndex (badEvents H),
        ∫⁻ table, Lax41Proofs.passingTreeCount
          (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H) table A
          ∂sampleMeasure n := by
      unfold workEnvelope
      rw [MeasureTheory.lintegral_finsetSum]
      intro A _
      exact Lax41Proofs.measurable_passingTreeCount
        (fun _ : EdgeVariable n ↦ Bool) (badVariables H) (badSet H)
        (fun _ ↦ Set.toFinite _ |>.measurableSet) A
    _ ≤ ∑ A : BadEventIndex (badEvents H),
        (Lax41Proofs.odds (charge H) A : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro A _
      exact passingTreeCount_lintegral_le H A
    _ ≤ ∑ _A : BadEventIndex (badEvents H), (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro A _
      exact ENNReal.coe_le_coe.mpr (odds_le_one H A)
    _ = Fintype.card (BadEventIndex (badEvents H)) := by simp
    _ ≤ (n ^ 6 : ℕ) := by exact_mod_cast card_badEventIndex_le H
    _ ≤ ((n + 1) ^ 6 : ℕ) := by
      exact_mod_cast pow_le_pow_left' (Nat.le_succ n) 6

/-! ### Edge density inside a large vertex set -/

lemma blowup_independent_card_le {n : ℕ} (H : SimpleGraph (Fin n))
    {S : Finset (BlowupVertex n)} (hS : (blowup H).IsIndepSet S) :
    S.card ≤ H.indepNum * n := by
  classical
  let P : Finset (Fin n) := S.image Prod.fst
  have hP : H.IsIndepSet P := by
    intro u hu v hv huv hadj
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
    subst u
    subst v
    have hxy : x ≠ y := fun h ↦ huv (congrArg Prod.fst h)
    exact hS hx hy hxy hadj
  have hsubset : S ⊆ P ×ˢ (Finset.univ : Finset (Fin n)) := by
    intro x hx
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · exact Finset.mem_univ _
  calc
    S.card ≤ (P ×ˢ (Finset.univ : Finset (Fin n))).card :=
      Finset.card_le_card hsubset
    _ = P.card * n := by simp
    _ ≤ H.indepNum * n := Nat.mul_le_mul_right n hP.card_le_indepNum

lemma blowup_indepNum_le {n : ℕ} (H : SimpleGraph (Fin n)) :
    (blowup H).indepNum ≤ H.indepNum * n := by
  obtain ⟨S, hS⟩ := (blowup H).exists_isNIndepSet_indepNum
  rw [← hS.2]
  exact blowup_independent_card_le H hS.1

/-- The convenient multiplicative form of the loose Turán bound. -/
lemma cliqueFree_mul_card_edgeFinset_le
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hG : G.CliqueFree (r + 1)) :
    2 * r * G.edgeFinset.card ≤ (r - 1) * (Fintype.card V) ^ 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · simp
  · obtain ⟨M, _, hM⟩ := SimpleGraph.exists_isTuranMaximal (V := V) hr
    obtain ⟨iso⟩ := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp hM
    calc
      2 * r * G.edgeFinset.card ≤ 2 * r * M.edgeFinset.card := by
        exact Nat.mul_le_mul_left (2 * r) (hM.2 hG)
      _ = 2 * r * (SimpleGraph.turanGraph (Fintype.card V) r).edgeFinset.card := by
        rw [iso.card_edgeFinset_eq]
      _ ≤ (r - 1) * (Fintype.card V) ^ 2 :=
        SimpleGraph.mul_card_edgeFinset_turanGraph_le

lemma card_edgeFinset_add_compl (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  have hdis : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e he hec
    induction e using Sym2.ind with
    | _ u v =>
        have hadj := (SimpleGraph.mem_edgeSet G).mp
          ((SimpleGraph.mem_edgeFinset).mp he)
        have hcadj := (SimpleGraph.mem_edgeSet Gᶜ).mp
          ((SimpleGraph.mem_edgeFinset).mp hec)
        exact hcadj.2 hadj
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset =
      (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
        simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
        constructor
        · rintro (hadj | ⟨hne, _⟩)
          · exact G.ne_of_adj hadj
          · exact hne
        · intro hne
          by_cases hadj : G.Adj u v
          · exact Or.inl hadj
          · exact Or.inr ⟨hne, hadj⟩
  calc
    G.edgeFinset.card + Gᶜ.edgeFinset.card =
        (G.edgeFinset ∪ Gᶜ.edgeFinset).card :=
      (Finset.card_union_of_disjoint hdis).symm
    _ = (⊤ : SimpleGraph V).edgeFinset.card := by rw [hunion]
    _ = (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two

lemma compl_cliqueFree_of_indepNum_le
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hr : G.indepNum ≤ r) : Gᶜ.CliqueFree (r + 1) := by
  intro S hS
  have hind : G.IsIndepSet S := by simpa using hS.1
  have hcard := hind.card_le_indepNum
  rw [hS.2] at hcard
  omega

/-- Any graph with independence number at most $r$ has at least
$s^2/(4r)$ edges once its $s$ vertices satisfy $s\geq 2r$. -/
lemma four_mul_card_edgeFinset_ge_sq
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hr : G.indepNum ≤ r) (hrpos : 0 < r)
    (hsize : 2 * r ≤ Fintype.card V) :
    ((Fintype.card V : ℕ) : ℝ) ^ 2 ≤
      4 * r * G.edgeFinset.card := by
  have hturan := cliqueFree_mul_card_edgeFinset_le Gᶜ
    (compl_cliqueFree_of_indepNum_le G hr)
  have htotal := card_edgeFinset_add_compl V G
  have hturan' :
      (2 : ℝ) * r * Gᶜ.edgeFinset.card ≤
        (r - 1 : ℕ) * (Fintype.card V : ℕ) ^ 2 := by
    exact_mod_cast hturan
  have htotal' :
      (G.edgeFinset.card : ℝ) + Gᶜ.edgeFinset.card =
        (Fintype.card V : ℝ) * (Fintype.card V - 1) / 2 := by
    calc
      (G.edgeFinset.card : ℝ) + Gᶜ.edgeFinset.card =
          ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast htotal
      _ = (Fintype.card V : ℝ) * (Fintype.card V - 1) / 2 :=
        Nat.cast_choose_two ℝ _
  have hrsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hrpos]
    norm_num
  have hsize' : (2 : ℝ) * r ≤ Fintype.card V := by exact_mod_cast hsize
  rw [hrsub] at hturan'
  push_cast at hturan'
  nlinarith [sq_nonneg ((Fintype.card V : ℝ) - 2 * r)]

/-- The sampled-edge query graph induced on a prospective vertex set. -/
def inducedBlowup {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) : SimpleGraph S :=
  (blowup H).induce (S : Set (BlowupVertex n))

/-- Cross-cluster nonedges of $H$, restricted to $S$. -/
def inducedComplement {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) : SimpleGraph S :=
  (blowup Hᶜ).induce (S : Set (BlowupVertex n))

/-- Pairs in $S$ belonging to the same input-vertex cluster. -/
def withinCluster {n : ℕ} (S : Finset (BlowupVertex n)) : SimpleGraph S :=
  SimpleGraph.fromRel fun u v ↦ u.1.1 = v.1.1

/-- The cardinality of $\mathtt{edgeFinset}$ does not depend on which finite-instance
Lean selected for the edge set. Passing through $\mathtt{Set.ncard}$ makes that fact
available to rewriting below. -/
lemma card_edgeFinset_eq_ncard {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeFinset.card = G.edgeSet.ncard := by
  calc
    G.edgeFinset.card = (G.edgeFinset : Set (Sym2 V)).ncard :=
      (Set.ncard_coe_finset G.edgeFinset).symm
    _ = G.edgeSet.ncard := by rw [SimpleGraph.coe_edgeFinset]

/-- Likewise, graph degree is the intrinsic cardinality of the neighbor set. -/
lemma degree_eq_neighborSet_ncard {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] : G.degree v = (G.neighborSet v).ncard := by
  calc
    G.degree v = (G.neighborFinset v).card := rfl
    _ = ((G.neighborFinset v : Finset V) : Set V).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = (G.neighborSet v).ncard := by rw [SimpleGraph.coe_neighborFinset]

lemma withinCluster_adj_iff {n : ℕ} {S : Finset (BlowupVertex n)}
    {u v : S} :
    (withinCluster S).Adj u v ↔ u ≠ v ∧ u.1.1 = v.1.1 := by
  simp only [withinCluster, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, h.symm⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

lemma withinCluster_degree_le {n : ℕ} (S : Finset (BlowupVertex n))
    (u : S) : (withinCluster S).degree u ≤ n := by
  classical
  let f : (withinCluster S).neighborSet u → Fin n := fun v ↦ v.1.1.2
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hv : v.1.1.1 = u.1.1 := by
        exact (withinCluster_adj_iff.mp
          v.2.symm).2
      have hw : w.1.1.1 = u.1.1 := by
        exact (withinCluster_adj_iff.mp
          w.2.symm).2
      exact hv.trans hw.symm
    · exact hvw
  rw [degree_eq_neighborSet_ncard, ← Nat.card_coe_set_eq]
  simpa using Nat.card_le_card_of_injective f hf

lemma twice_withinCluster_edges_le {n : ℕ} (S : Finset (BlowupVertex n)) :
    2 * (withinCluster S).edgeFinset.card ≤ S.card * n := by
  classical
  have hhand := (withinCluster S).sum_degrees_eq_twice_card_edges
  rw [card_edgeFinset_eq_ncard] at hhand ⊢
  simp_rw [degree_eq_neighborSet_ncard] at hhand
  calc
    2 * (withinCluster S).edgeSet.ncard =
        ∑ u : S, ((withinCluster S).neighborSet u).ncard :=
      hhand.symm
    _ ≤ ∑ _u : S, n := by
      apply Finset.sum_le_sum
      intro u _
      have hu := withinCluster_degree_le S u
      rw [degree_eq_neighborSet_ncard] at hu
      exact hu
    _ = S.card * n := by simp

lemma inducedComplement_cliqueFree {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) :
    (inducedComplement H S).CliqueFree (H.indepNum + 1) := by
  classical
  intro T hT
  let P : Finset (Fin n) := T.image fun x ↦ x.1.1
  have hinj : Set.InjOn (fun x : S ↦ x.1.1) (T : Set S) := by
    intro u hu v hv huv
    by_contra hne
    have hadj := hT.1 hu hv hne
    change Hᶜ.Adj u.1.1 v.1.1 at hadj
    exact hadj.ne huv
  have hPcard : P.card = T.card :=
    (Finset.card_image_iff.mpr hinj)
  have hP : H.IsIndepSet P := by
    intro u hu v hv huv hadj
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
    subst u
    subst v
    have hxy : x ≠ y := fun h ↦ huv (congrArg (fun z : S ↦ z.1.1) h)
    have hcomp := hT.1 hx hy hxy
    change Hᶜ.Adj x.1.1 y.1.1 at hcomp
    exact hcomp.2 hadj
  have := hP.card_le_indepNum
  rw [hPcard, hT.2] at this
  omega

lemma induced_edge_partition {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) :
    (inducedBlowup H S).edgeFinset.card +
      (inducedComplement H S).edgeFinset.card =
        (withinCluster S)ᶜ.edgeFinset.card := by
  classical
  have hdis : Disjoint (inducedBlowup H S).edgeFinset
      (inducedComplement H S).edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heJ heK
    induction e using Sym2.ind with
    | _ u v =>
        have hJ := (SimpleGraph.mem_edgeSet (inducedBlowup H S)).mp
          ((SimpleGraph.mem_edgeFinset).mp heJ)
        have hK := (SimpleGraph.mem_edgeSet (inducedComplement H S)).mp
          ((SimpleGraph.mem_edgeFinset).mp heK)
        exact hK.2 hJ
  have hunion : (inducedBlowup H S).edgeFinset ∪
      (inducedComplement H S).edgeFinset =
        (withinCluster S)ᶜ.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
        simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, inducedBlowup, inducedComplement,
          SimpleGraph.induce_adj, blowup, SimpleGraph.comap_adj,
          SimpleGraph.compl_adj, withinCluster_adj_iff]
        constructor
        · rintro (hadj | ⟨hne, _⟩)
          · refine ⟨?_, ?_⟩
            · intro huv
              exact hadj.ne (congrArg (fun z : S ↦ z.1.1) huv)
            · rintro ⟨_, hfirst⟩
              exact hadj.ne hfirst
          · refine ⟨?_, ?_⟩
            · intro huv
              exact hne (congrArg (fun z : S ↦ z.1.1) huv)
            · rintro ⟨_, hfirst⟩
              exact hne hfirst
        · rintro ⟨huv, hnwithin⟩
          have hfirst : u.1.1 ≠ v.1.1 := by
            intro hfirst
            exact hnwithin ⟨huv, hfirst⟩
          by_cases hadj : H.Adj u.1.1 v.1.1
          · exact Or.inl hadj
          · exact Or.inr ⟨hfirst, hadj⟩
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdis] at hcard
  rw [card_edgeFinset_eq_ncard, card_edgeFinset_eq_ncard,
    card_edgeFinset_eq_ncard] at hcard ⊢
  exact hcard

lemma inducedBlowup_edge_card_eq_queryScope {n : ℕ}
    (H : SimpleGraph (Fin n)) (S : Finset (BlowupVertex n)) :
    (inducedBlowup H S).edgeFinset.card =
      (variablesOf H (Sum.inr S)).card := by
  classical
  have hmap := SimpleGraph.map_edgeFinset_induce
    (s := (S : Set (BlowupVertex n))) (G := blowup H)
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map, card_edgeFinset_eq_ncard,
    ← Set.ncard_coe_finset] at hcard
  simp only [Finset.coe_inter, SimpleGraph.coe_edgeFinset,
    Finset.coe_sym2, Set.coe_toFinset] at hcard
  rw [card_edgeFinset_eq_ncard]
  calc
    (inducedBlowup H S).edgeSet.ncard =
        ((blowup H).edgeSet ∩ (S : Set (BlowupVertex n)).sym2).ncard := by
      simpa only [inducedBlowup] using hcard
    _ = ((variablesOf H (Sum.inr S) : Finset (EdgeVariable n)) :
        Set (EdgeVariable n)).ncard := by
      apply congrArg Set.ncard
      ext e
      simp only [Set.mem_inter_iff, Finset.mem_coe,
        variablesOf, Finset.mem_inter, SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨he, hS⟩
        refine ⟨he, ?_⟩
        change e ∈ (S.sym2 : Set (EdgeVariable n))
        rwa [Finset.coe_sym2]
      · rintro ⟨he, hS⟩
        refine ⟨he, ?_⟩
        rw [← Finset.coe_sym2]
        exact hS
    _ = (variablesOf H (Sum.inr S)).card := Set.ncard_coe_finset _

lemma inducedBlowup_edge_ncard_eq_queryScope {n : ℕ}
    (H : SimpleGraph (Fin n)) (S : Finset (BlowupVertex n)) :
    (inducedBlowup H S).edgeSet.ncard =
      (variablesOf H (Sum.inr S)).card := by
  have h := inducedBlowup_edge_card_eq_queryScope H S
  rw [card_edgeFinset_eq_ncard] at h
  exact h

lemma indepNum_pos_of_nonempty {n : ℕ} (H : SimpleGraph (Fin n))
    (hn : 0 < n) : 0 < H.indepNum := by
  let v : Fin n := ⟨0, hn⟩
  have hsingle : H.IsIndepSet ({v} : Finset (Fin n)) := by simp
  have hcard := hsingle.card_le_indepNum
  simpa using hcard

/-- Every sufficiently large prospective independent set asks for quadratically
many sampled edges.  This is the weighted Turán estimate used in the paper's
union bound; unlike the coarse independence-number bound on the whole blow-up,
it retains the essential factor of $n$. -/
lemma queryScope_density {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) (hn : 0 < n)
    (hsize : 2 * H.indepNum * (n + 1) ≤ S.card) :
    (S.card : ℝ) ^ 2 ≤
      4 * H.indepNum * (variablesOf H (Sum.inr S)).card := by
  classical
  have hα : 0 < H.indepNum := indepNum_pos_of_nonempty H hn
  have hKnat := cliqueFree_mul_card_edgeFinset_le
    (inducedComplement H S) (inducedComplement_cliqueFree H S)
  rw [card_edgeFinset_eq_ncard] at hKnat
  have hK :
      (2 : ℝ) * H.indepNum * (inducedComplement H S).edgeSet.ncard ≤
        ((H.indepNum - 1 : ℕ) : ℝ) * (S.card : ℝ) ^ 2 := by
    simpa using (show
      ((2 * H.indepNum * (inducedComplement H S).edgeSet.ncard : ℕ) : ℝ) ≤
        (((H.indepNum - 1) * (Fintype.card S) ^ 2 : ℕ) : ℝ) by
          exact_mod_cast hKnat)
  have hαsub : ((H.indepNum - 1 : ℕ) : ℝ) = H.indepNum - 1 := by
    rw [Nat.cast_sub hα]
    norm_num
  rw [hαsub] at hK
  have hWnat := twice_withinCluster_edges_le S
  rw [card_edgeFinset_eq_ncard] at hWnat
  have hW :
      (2 : ℝ) * (withinCluster S).edgeSet.ncard ≤
        (S.card : ℝ) * n := by
    exact_mod_cast hWnat
  have hpart := induced_edge_partition H S
  have hall := card_edgeFinset_add_compl S (withinCluster S)
  simp_rw [card_edgeFinset_eq_ncard] at hpart hall
  simp only [Fintype.card_coe] at hall
  have htotalNat :
      (withinCluster S).edgeSet.ncard +
          (inducedBlowup H S).edgeSet.ncard +
          (inducedComplement H S).edgeSet.ncard = S.card.choose 2 := by
    omega
  have htotalCast :
      ((withinCluster S).edgeSet.ncard : ℝ) +
          (inducedBlowup H S).edgeSet.ncard +
          (inducedComplement H S).edgeSet.ncard =
        (S.card.choose 2 : ℝ) := by
    exact_mod_cast htotalNat
  have htotal :
      (2 : ℝ) *
          ((withinCluster S).edgeSet.ncard +
            (inducedBlowup H S).edgeSet.ncard +
            (inducedComplement H S).edgeSet.ncard) =
        (S.card : ℝ) * (S.card - 1) := by
    rw [htotalCast, Nat.cast_choose_two]
    ring
  have hsize' :
      (2 : ℝ) * H.indepNum * (n + 1) ≤ S.card := by
    exact_mod_cast hsize
  have hdensity :
      (S.card : ℝ) ^ 2 ≤
        4 * H.indepNum * (inducedBlowup H S).edgeSet.ncard := by
    nlinarith [sq_nonneg ((S.card : ℝ) -
      2 * H.indepNum * (n + 1))]
  rwa [inducedBlowup_edge_ncard_eq_queryScope H S] at hdensity

/-! ### The independent-set union bound -/

/-- The cardinality at which the union bound is applied. -/
def soundnessLevel {n : ℕ} (H : SimpleGraph (Fin n)) : ℕ :=
  3200 * H.indepNum * (n + 1) * (Nat.log2 n + 1)

/-- The number of $200(n+1)$-step survival blocks forced by edge density at
the soundness level. -/
def soundnessBlocks {n : ℕ} (H : SimpleGraph (Fin n)) : ℕ :=
  12800 * H.indepNum * (n + 1) * (Nat.log2 n + 1) ^ 2

def soundnessFamily {n : ℕ} (H : SimpleGraph (Fin n)) :
    Finset (Finset (BlowupVertex n)) :=
  Finset.univ.powersetCard (soundnessLevel H)

noncomputable def soundnessQueryEvent {n : ℕ}
    (H : SimpleGraph (Fin n)) (S : Finset (BlowupVertex n)) :
    Set (SampleTable n) :=
  eventOccursInOutput (fun _ : EdgeVariable n ↦ Bool)
    (badEvents H) (variablesOf H) (eventSet H) (selectionRule H)
    (Sum.inr S)

noncomputable def soundnessUnion {n : ℕ} (H : SimpleGraph (Fin n)) :
    Set (SampleTable n) :=
  ⋃ S ∈ soundnessFamily H, soundnessQueryEvent H S

/-- One block of $200(n+1)$ trials has survival probability at most one half. -/
lemma survival_block_le_half (n : ℕ) :
    (1 - edgeChance n / 2 : NNReal) ^ (200 * (n + 1)) ≤ 1 / 2 := by
  let d : ℕ := 200 * (n + 1)
  have hdpos : 0 < d := by simp [d]
  have hbase :
      ((1 - edgeChance n / 2 : NNReal) : ℝ) =
        1 - 1 / (d : ℝ) := by
    have hp2 : edgeChance n / 2 ≤ (1 : NNReal) := by
      apply (div_le_one (by norm_num)).2
      exact (edgeChance_le_one n).trans (by norm_num)
    rw [NNReal.coe_sub hp2]
    congr 1
    rw [edgeChance, NNReal.coe_div, NNReal.coe_inv]
    push_cast
    dsimp only [d]
    field_simp
    push_cast
    ring
  have hpow :
      (1 - 1 / (d : ℝ)) ^ d ≤ Real.exp (-1) := by
    exact Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hdpos)
  have hexp : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp 1 using 1 <;> norm_num
    simpa only [one_div] using
      (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).2 htwo
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  rw [show 200 * (n + 1) = d by rfl, hbase]
  exact hpow.trans hexp

/-- At the chosen level, edge density supplies all the survival blocks used in
the discrete union bound. -/
lemma soundness_blocks_fit {n : ℕ} (H : SimpleGraph (Fin n))
    (S : Finset (BlowupVertex n)) (hn : 0 < n)
    (hcard : S.card = soundnessLevel H) :
    200 * (n + 1) * soundnessBlocks H ≤
      (variablesOf H (Sum.inr S)).card := by
  have hα := indepNum_pos_of_nonempty H hn
  have hl : 0 < Nat.log2 n + 1 := Nat.succ_pos _
  have hlarge : 2 * H.indepNum * (n + 1) ≤ S.card := by
    rw [hcard, soundnessLevel]
    calc
      2 * H.indepNum * (n + 1) =
          (H.indepNum * (n + 1)) * 2 := by ring
      _ ≤ (H.indepNum * (n + 1)) *
          (3200 * (Nat.log2 n + 1)) := by
        apply Nat.mul_le_mul_left
        omega
      _ = 3200 * H.indepNum * (n + 1) *
          (Nat.log2 n + 1) := by ring
  have hdensity := queryScope_density H S hn hlarge
  have hid :
      4 * H.indepNum * (200 * (n + 1) * soundnessBlocks H) =
        (soundnessLevel H) ^ 2 := by
    simp only [soundnessBlocks, soundnessLevel]
    ring
  rw [hcard] at hdensity
  have hdensityNat :
      (soundnessLevel H) ^ 2 ≤
        4 * H.indepNum * (variablesOf H (Sum.inr S)).card := by
    exact_mod_cast hdensity
  rw [← hid] at hdensityNat
  have hc :
      (4 * H.indepNum) * (200 * (n + 1) * soundnessBlocks H) ≤
        (4 * H.indepNum) * (variablesOf H (Sum.inr S)).card := by
    simpa only [mul_assoc] using hdensityNat
  exact le_of_mul_le_mul_left hc (mul_pos (by norm_num) hα)

lemma query_probability_at_soundnessLevel {n : ℕ}
    (H : SimpleGraph (Fin n)) (S : Finset (BlowupVertex n))
    (hn : 0 < n) (hcard : S.card = soundnessLevel H) :
    sampleMeasure n
        (eventOccursInOutput (fun _ : EdgeVariable n ↦ Bool)
          (badEvents H) (variablesOf H) (eventSet H) (selectionRule H)
          (Sum.inr S)) ≤
      ((1 / 2 : NNReal) : ℝ≥0∞) ^ soundnessBlocks H := by
  have hfit := soundness_blocks_fit H S hn hcard
  have hbase : (1 - edgeChance n / 2 : NNReal) ≤ 1 := tsub_le_self
  calc
    sampleMeasure n
        (eventOccursInOutput (fun _ : EdgeVariable n ↦ Bool)
          (badEvents H) (variablesOf H) (eventSet H) (selectionRule H)
          (Sum.inr S)) ≤
        ((1 - edgeChance n / 2 : NNReal) : ℝ≥0∞) ^
          (variablesOf H (Sum.inr S)).card :=
      query_output_probability_le H S
    _ ≤ ((1 - edgeChance n / 2 : NNReal) : ℝ≥0∞) ^
        (200 * (n + 1) * soundnessBlocks H) := by
      exact pow_le_pow_right_of_le_one' (by exact_mod_cast hbase) hfit
    _ = ((((1 - edgeChance n / 2 : NNReal) ^ (200 * (n + 1))) ^
          soundnessBlocks H : NNReal) : ℝ≥0∞) := by
      rw [pow_mul, ENNReal.coe_pow, ENNReal.coe_pow]
    _ ≤ ((((1 / 2 : NNReal) ^ soundnessBlocks H : NNReal)) : ℝ≥0∞) := by
      exact ENNReal.coe_le_coe.mpr
        (pow_le_pow_left' (survival_block_le_half n) _)
    _ = ((1 / 2 : NNReal) : ℝ≥0∞) ^ soundnessBlocks H := by
      rw [ENNReal.coe_pow]

/-- An independent set in the output makes its all-edges-absent HSS query
true. -/
lemma query_occurs_of_output_independent {n : ℕ}
    (H : SimpleGraph (Fin n)) (table : SampleTable n)
    (S : Finset (BlowupVertex n))
    (hS : (outputGraph H table).IsIndepSet S) :
    table ∈ eventOccursInOutput (fun _ : EdgeVariable n ↦ Bool)
      (badEvents H) (variablesOf H) (eventSet H) (selectionRule H)
      (Sum.inr S) := by
  change violates (fun _ : EdgeVariable n ↦ Bool)
    (variablesOf H) (eventSet H) (finalAssignment H table) (Sum.inr S)
  change ∀ e : variablesOf H (Sum.inr S),
    finalAssignment H table e.1 = false
  intro e
  cases hvalue : finalAssignment H table e.1 with
  | false => rfl
  | true =>
    have he := e.2
    simp only [variablesOf, Finset.mem_inter,
      SimpleGraph.mem_edgeFinset] at he
    have heEdge : e.1 ∈ (blowup H).edgeSet := he.1
    have heScope : e.1 ∈ S.sym2 := he.2
    have noTrue : ∀ z : EdgeVariable n,
        z ∈ (blowup H).edgeSet → z ∈ S.sym2 →
          finalAssignment H table z = true → False := by
      intro z
      induction z using Sym2.inductionOn with
      | _ u v =>
        intro hzEdge hzScope hzTrue
        have huv := Finset.mk_mem_sym2_iff.mp hzScope
        have hblow : (blowup H).Adj u v :=
          (SimpleGraph.mem_edgeSet (blowup H)).mp hzEdge
        exact hS huv.1 huv.2 hblow.ne
          (outputGraph_adj_iff.mpr ⟨hblow, hzTrue⟩)
    exact False.elim (noTrue e.1 heEdge heScope hvalue)

lemma soundness_family_weight_le_quarter {n : ℕ}
    (H : SimpleGraph (Fin n)) (hn : 0 < n) :
    ((soundnessFamily H).card : NNReal) *
        (1 / 2 : NNReal) ^ soundnessBlocks H ≤ 1 / 4 := by
  let l : ℕ := Nat.log2 n + 1
  let e : ℕ := 6400 * H.indepNum * (n + 1) * l ^ 2
  have hα := indepNum_pos_of_nonempty H hn
  have hl : 0 < l := by simp [l]
  have hnle : n ≤ 2 ^ l := by
    exact Nat.le_of_lt (by simpa only [l] using (Nat.lt_log2_self (n := n)))
  have hvertices : n ^ 2 ≤ 2 ^ (2 * l) := by
    calc
      n ^ 2 ≤ (2 ^ l) ^ 2 := pow_le_pow_left' hnle 2
      _ = 2 ^ (2 * l) := by rw [← pow_mul]; congr 1 <;> omega
  have hfamily : (soundnessFamily H).card ≤
      (n ^ 2) ^ soundnessLevel H := by
    calc
      (soundnessFamily H).card = (n ^ 2).choose (soundnessLevel H) := by
        simp [soundnessFamily, Fintype.card_prod, pow_two]
      _ ≤ (n ^ 2) ^ soundnessLevel H := Nat.choose_le_pow _ _
  have hpow : (n ^ 2) ^ soundnessLevel H ≤ 2 ^ e := by
    calc
      (n ^ 2) ^ soundnessLevel H ≤
          (2 ^ (2 * l)) ^ soundnessLevel H :=
        pow_le_pow_left' hvertices _
      _ = 2 ^ (2 * l * soundnessLevel H) :=
        (pow_mul 2 (2 * l) (soundnessLevel H)).symm
      _ = 2 ^ e := by
        congr 1
        simp only [soundnessLevel, l, e]
        ring
  have hfamily' : (soundnessFamily H).card ≤ 2 ^ e := hfamily.trans hpow
  have hblocks : soundnessBlocks H = 2 * e := by
    simp only [soundnessBlocks, e, l]
    ring
  have hrest : 0 < H.indepNum * (n + 1) * l ^ 2 := by positivity
  have he : 2 ≤ e := by
    calc
      2 ≤ 6400 := by norm_num
      _ ≤ 6400 * (H.indepNum * (n + 1) * l ^ 2) :=
        Nat.le_mul_of_pos_right _ hrest
      _ = e := by simp only [e]; ring
  have hfamilyNN : ((soundnessFamily H).card : NNReal) ≤
      (2 : NNReal) ^ e := by exact_mod_cast hfamily'
  have hcancel :
      (2 : NNReal) ^ e * (1 / 2 : NNReal) ^ (2 * e) =
        (1 / 2 : NNReal) ^ e := by
    calc
      (2 : NNReal) ^ e * (1 / 2 : NNReal) ^ (2 * e) =
          (2 : NNReal) ^ e * ((1 / 2 : NNReal) ^ 2) ^ e := by
        exact congrArg (fun z : NNReal ↦ (2 : NNReal) ^ e * z)
          (pow_mul (1 / 2 : NNReal) 2 e)
      _ = ((2 : NNReal) * (1 / 2 : NNReal) ^ 2) ^ e :=
        (mul_pow (2 : NNReal) ((1 / 2 : NNReal) ^ 2) e).symm
      _ = (1 / 2 : NNReal) ^ e := by norm_num
  calc
    ((soundnessFamily H).card : NNReal) *
        (1 / 2 : NNReal) ^ soundnessBlocks H ≤
      (2 : NNReal) ^ e * (1 / 2 : NNReal) ^ soundnessBlocks H :=
        mul_le_mul_right' hfamilyNN _
    _ = (1 / 2 : NNReal) ^ e := by
      rw [hblocks]
      exact hcancel
    _ ≤ (1 / 2 : NNReal) ^ 2 :=
      pow_le_pow_right_of_le_one' (by norm_num) he
    _ = 1 / 4 := by norm_num

lemma measure_soundnessUnion_le_quarter {n : ℕ}
    (H : SimpleGraph (Fin n)) (hn : 0 < n) :
    sampleMeasure n (soundnessUnion H) ≤ ((1 / 4 : NNReal) : ℝ≥0∞) := by
  calc
    sampleMeasure n (soundnessUnion H) ≤
        ∑ S ∈ soundnessFamily H,
          sampleMeasure n (soundnessQueryEvent H S) := by
      unfold soundnessUnion
      exact MeasureTheory.measure_biUnion_finset_le (soundnessFamily H)
        (soundnessQueryEvent H)
    _ ≤ ∑ _S ∈ soundnessFamily H,
        ((1 / 2 : NNReal) : ℝ≥0∞) ^ soundnessBlocks H := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard := (Finset.mem_powersetCard.mp hS).2
      exact query_probability_at_soundnessLevel H S hn hcard
    _ = ((soundnessFamily H).card : ℝ≥0∞) *
        ((1 / 2 : NNReal) : ℝ≥0∞) ^ soundnessBlocks H := by simp
    _ ≤ ((1 / 4 : NNReal) : ℝ≥0∞) := by
      have h := ENNReal.coe_le_coe.mpr
        (soundness_family_weight_le_quarter H hn)
      simpa only [ENNReal.coe_mul, ENNReal.coe_natCast,
        ENNReal.coe_pow] using h

lemma large_output_subset_soundnessUnion {n : ℕ}
    (H : SimpleGraph (Fin n)) :
    {table : SampleTable n |
        soundnessLevel H ≤ (outputGraph H table).indepNum} ⊆
      soundnessUnion H := by
  intro table hlarge
  obtain ⟨T, hT⟩ := (outputGraph H table).exists_isNIndepSet_indepNum
  have hkT : soundnessLevel H ≤ T.card := by
    rw [hT.2]
    exact hlarge
  obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hkT
  have hS : (outputGraph H table).IsIndepSet S := hT.1.mono hST
  have hfamily : S ∈ soundnessFamily H := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ S, hScard⟩
  have hquery := query_occurs_of_output_independent H table S hS
  simp only [soundnessUnion, Set.mem_iUnion]
  exact ⟨S, ⟨hfamily, hquery⟩⟩

lemma measure_large_output_le_quarter {n : ℕ}
    (H : SimpleGraph (Fin n)) (hn : 0 < n) :
    sampleMeasure n
        {table | soundnessLevel H ≤ (outputGraph H table).indepNum} ≤
      ((1 / 4 : NNReal) : ℝ≥0∞) := by
  exact (MeasureTheory.measure_mono (large_output_subset_soundnessUnion H)).trans
    (measure_soundnessUnion_le_quarter H hn)

/-- The binary-log cutoff used by the counting proof is below the advertised
$C\alpha n\log n$ cutoff, with a uniform numerical constant. -/
lemma soundnessLevel_le_real_log {n : ℕ} (H : SimpleGraph (Fin n))
    (hn : 3 ≤ n) :
    (soundnessLevel H : ℝ) ≤
      20000 * H.indepNum * n * Real.log n := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogmono : Real.log 3 ≤ Real.log n :=
    Real.log_le_log (by norm_num) hnreal
  have hlogn : (1 : ℝ) ≤ Real.log n := by
    nlinarith [Real.log_three_gt_d9]
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogtwoPos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hq := Real.log2_le_logb n
  rw [Real.logb] at hq
  have hqmul : (Nat.log2 n : ℝ) * Real.log 2 ≤ Real.log n :=
    (le_div_iff₀ hlogtwoPos).mp hq
  have hqnonneg : (0 : ℝ) ≤ Nat.log2 n := by positivity
  have hhalfq : (Nat.log2 n : ℝ) * (1 / 2) ≤
      (Nat.log2 n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlogtwo hqnonneg
  have hql : (Nat.log2 n : ℝ) ≤ 2 * Real.log n := by
    nlinarith
  have hl : ((Nat.log2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log n := by
    push_cast
    nlinarith
  have hnplus : ((n + 1 : ℕ) : ℝ) ≤ 2 * n := by
    push_cast
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    nlinarith
  have hnplus' : (n : ℝ) + 1 ≤ 2 * n := by simpa using hnplus
  have hl' : (Nat.log2 n : ℝ) + 1 ≤ 3 * Real.log n := by
    simpa using hl
  calc
    (soundnessLevel H : ℝ) =
        3200 * H.indepNum * (n + 1) * (Nat.log2 n + 1) := by
      simp only [soundnessLevel]
      push_cast
      ring
    _ ≤ 3200 * H.indepNum * (2 * n) *
        ((Nat.log2 n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnplus' (by positivity)) (by positivity)
    _ ≤ 3200 * H.indepNum * (2 * n) * (3 * Real.log n) := by
      exact mul_le_mul_of_nonneg_left hl' (by positivity)
    _ = 19200 * H.indepNum * n * Real.log n := by ring
    _ ≤ 20000 * H.indepNum * n * Real.log n := by
      have hnonneg : (0 : ℝ) ≤ H.indepNum * n * Real.log n := by positivity
      nlinarith

theorem outputGraph_soundness_failure_le_quarter (n : ℕ) (hn : 3 ≤ n)
    (H : SimpleGraph (Fin n)) :
    sampleMeasure n
      {table | 20000 * H.indepNum * n * Real.log n <
        ((outputGraph H table).indepNum : ℝ)} ≤
      ((1 / 4 : NNReal) : ℝ≥0∞) := by
  let bad : Set (SampleTable n) :=
    {table | 20000 * H.indepNum * n * Real.log n <
      ((outputGraph H table).indepNum : ℝ)}
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbadSubset : bad ⊆
      {table | soundnessLevel H ≤ (outputGraph H table).indepNum} := by
    intro table htable
    have hlevel := soundnessLevel_le_real_log H hn
    have hreal : (soundnessLevel H : ℝ) ≤
        (outputGraph H table).indepNum :=
      (hlevel.trans htable.le)
    exact_mod_cast hreal
  have hbad : sampleMeasure n bad ≤ ((1 / 4 : NNReal) : ℝ≥0∞) :=
    (MeasureTheory.measure_mono hbadSubset).trans
      (measure_large_output_le_quarter H hnpos)
  exact hbad

/-- Twelve times the Moser--Tardos expectation bound used for the cutoff. -/
def cutoffBudget (n : ℕ) : ℕ :=
  12 * (n + 1) ^ 6

/-- A uniform polynomial accounting for construction and resampling work. -/
def constructionSteps (n : ℕ) : ℕ :=
  12 * (n + 1) ^ 10

/-- The actual number of resamplings stays within the cutoff budget. -/
def withinBudget {n : ℕ} (H : SimpleGraph (Fin n)) (table : SampleTable n) : Prop :=
  resamplingSteps H table < cutoffBudget n

/-- Run the triangle-removal construction within its polynomial budget and
return the edgeless graph on a cutoff failure. -/
noncomputable def truncatedGraph {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) : SimpleGraph (BlowupVertex n) := by
  classical
  exact if withinBudget H table then outputGraph H table else ⊥

lemma resamplingSteps_lt_top_of_withinBudget {n : ℕ}
    (H : SimpleGraph (Fin n)) (table : SampleTable n)
    (hbudget : withinBudget H table) :
    resamplingSteps H table < ⊤ :=
  hbudget.trans (ENNReal.natCast_lt_top (cutoffBudget n))

theorem truncatedGraph_triangleFree {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) : (truncatedGraph H table).CliqueFree 3 := by
  classical
  rw [truncatedGraph]
  split_ifs with hbudget
  · exact outputGraph_triangleFree_of_terminates H table
      (exists_termination_time_of_resamplingSteps_lt_top
        (resamplingSteps_lt_top_of_withinBudget H table hbudget))
  · simp

lemma indepNum_mul_le_blowup_card {n : ℕ} (H : SimpleGraph (Fin n)) :
    H.indepNum * n ≤ n * n := by
  obtain ⟨S, hS⟩ := H.exists_isNIndepSet_indepNum
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  rw [← hS.2]
  exact Nat.mul_le_mul_right n hcard

theorem truncatedGraph_completeness {n : ℕ} (H : SimpleGraph (Fin n))
    (table : SampleTable n) :
    H.indepNum * n ≤ (truncatedGraph H table).indepNum := by
  classical
  rw [truncatedGraph]
  split_ifs with hbudget
  · exact outputGraph_completeness H table
  · let S : Finset (BlowupVertex n) := Finset.univ
    have hS : (⊥ : SimpleGraph (BlowupVertex n)).IsIndepSet S := by
      intro u hu v hv huv hadj
      exact hadj
    calc
      H.indepNum * n ≤ n * n := indepNum_mul_le_blowup_card H
      _ = S.card := by simp [S, BlowupVertex]
      _ ≤ (⊥ : SimpleGraph (BlowupVertex n)).indepNum := hS.card_le_indepNum

lemma measure_outsideBudget_le {n : ℕ} (H : SimpleGraph (Fin n)) :
    sampleMeasure n {table | ¬withinBudget H table} ≤
      ((1 / 12 : NNReal) : ℝ≥0∞) := by
  have hcutoff0 : (cutoffBudget n : ℝ≥0∞) ≠ 0 := by
    simp [cutoffBudget]
  have hcutoffTop : (cutoffBudget n : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hbase0 : (((n + 1) ^ 6 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hbaseTop : (((n + 1) ^ 6 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hsubset : {table : SampleTable n | ¬withinBudget H table} ⊆
      {table | (cutoffBudget n : ℝ≥0∞) ≤ workEnvelope H table} := by
    intro table houtside
    have hcutoff : (cutoffBudget n : ℝ≥0∞) ≤ resamplingSteps H table := by
      simpa only [withinBudget, Set.mem_setOf_eq, not_lt] using houtside
    exact hcutoff.trans (resamplingSteps_le_workEnvelope H table)
  calc
    sampleMeasure n {table | ¬withinBudget H table} ≤
        sampleMeasure n {table | (cutoffBudget n : ℝ≥0∞) ≤ workEnvelope H table} :=
      MeasureTheory.measure_mono hsubset
    _ ≤ (∫⁻ table, workEnvelope H table ∂sampleMeasure n) /
        (cutoffBudget n : ℝ≥0∞) :=
      MeasureTheory.meas_ge_le_lintegral_div
        (measurable_workEnvelope H).aemeasurable hcutoff0 hcutoffTop
    _ ≤ (((n + 1) ^ 6 : ℕ) : ℝ≥0∞) / (cutoffBudget n : ℝ≥0∞) :=
      ENNReal.div_le_div_right (workEnvelope_expected_polynomial H) _
    _ = ((1 / 12 : NNReal) : ℝ≥0∞) := by
      rw [show (cutoffBudget n : ℝ≥0∞) =
          (12 : ℝ≥0∞) * (((n + 1) ^ 6 : ℕ) : ℝ≥0∞) by
        simp [cutoffBudget]]
      conv_lhs =>
        lhs
        rw [show (((n + 1) ^ 6 : ℕ) : ℝ≥0∞) =
          (1 : ℝ≥0∞) * (((n + 1) ^ 6 : ℕ) : ℝ≥0∞) by simp]
      rw [ENNReal.mul_div_mul_right 1 12 hbase0 hbaseTop]
      norm_num

theorem truncatedGraph_soundness_failure_le_third (n : ℕ) (hn : 3 ≤ n)
    (H : SimpleGraph (Fin n)) :
    sampleMeasure n
      {table | 20000 * H.indepNum * n * Real.log n <
        ((truncatedGraph H table).indepNum : ℝ)} ≤ (1 : ℝ≥0∞) / 3 := by
  let originalBad : Set (SampleTable n) :=
    {table | 20000 * H.indepNum * n * Real.log n <
      ((outputGraph H table).indepNum : ℝ)}
  let outside : Set (SampleTable n) := {table | ¬withinBudget H table}
  let truncatedBad : Set (SampleTable n) :=
    {table | 20000 * H.indepNum * n * Real.log n <
      ((truncatedGraph H table).indepNum : ℝ)}
  have horiginal : sampleMeasure n originalBad ≤
      ((1 / 4 : NNReal) : ℝ≥0∞) := by
    simpa only [originalBad] using outputGraph_soundness_failure_le_quarter n hn H
  have houtside : sampleMeasure n outside ≤ ((1 / 12 : NNReal) : ℝ≥0∞) := by
    simpa only [outside] using measure_outsideBudget_le H
  have hsubset : truncatedBad ⊆ originalBad ∪ outside := by
    intro table hbad
    by_cases hbudget : withinBudget H table
    · apply Or.inl
      change 20000 * H.indepNum * n * Real.log n <
        ((outputGraph H table).indepNum : ℝ)
      change 20000 * H.indepNum * n * Real.log n <
        ((truncatedGraph H table).indepNum : ℝ) at hbad
      classical
      simpa only [truncatedGraph, hbudget, if_true] using hbad
    · exact Or.inr hbudget
  calc
    sampleMeasure n truncatedBad ≤ sampleMeasure n (originalBad ∪ outside) :=
      MeasureTheory.measure_mono hsubset
    _ ≤ sampleMeasure n originalBad + sampleMeasure n outside :=
      MeasureTheory.measure_union_le _ _
    _ ≤ ((1 / 4 : NNReal) : ℝ≥0∞) + ((1 / 12 : NNReal) : ℝ≥0∞) :=
      add_le_add horiginal houtside
    _ = (1 : ℝ≥0∞) / 3 := by
      rw [← ENNReal.coe_add]
      norm_num

/-- The complete polynomial-cutoff randomized reduction certificate. -/
noncomputable def reduction : TriangleFreeReduction where
  measure := sampleMeasure
  output := fun _ H ↦ truncatedGraph H
  steps := fun n _ _ ↦ constructionSteps n
  probability := by
    intro n
    unfold sampleMeasure tableMeasure
    infer_instance
  triangleFree := by
    intro _ H table
    exact truncatedGraph_triangleFree H table
  completeness := by
    intro _ H table
    exact truncatedGraph_completeness H table
  soundnessConstant := 20000
  soundnessCutoff := 3
  soundnessConstant_pos := by norm_num
  soundness := by
    intro n hn H
    exact truncatedGraph_soundness_failure_le_third n hn H
  stepConstant := 12
  stepExponent := 10
  stepConstant_pos := by norm_num
  stepBound := by
    intro n H table
    simp [constructionSteps]

end

end Lax47Proofs.Construction
