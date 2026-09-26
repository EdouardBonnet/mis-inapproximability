import Lax759944Proofs.Legacy.Lib.Fill

/-! Input marshalling for the legacy IMP compiler. Adapted from the Apache-2.0
Lax13Proofs.Refine.Codegen.Harness used by the original submission. -/

namespace Lax47Proofs.InputHarness

open Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Reasoning Lax759944Proofs.Legacy.Reasoning.Lib

/-! ### A list as a cell function

`Fill` states what an array holds as `arrOf n g` for a cell function
`g`; the harness states it as the list of values that were read. These
two are the bridge, and it is needed in both directions: a list of
length `n` *is* an `arrOf`, and an entry of a list is a `getD`. -/

/-- An entry of a list, as the `getD` that `arrOf` produces. -/
theorem getD_eq_getElem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] :=
  (List.getElem_eq_getD 0).symm

/-- A list is the array of its own entries. -/
theorem arrOf_getD (l : List ℕ) : arrOf l.length (fun j => l.getD j 0) = l := by
  refine List.ext_getElem (by simp) (fun i h₁ h₂ => ?_)
  simp [arrOf, List.getElem?_eq_getElem h₂]

/-! ### The scalar prelude -/

/-- Read one input entry into each of the named cells, in order. -/
def readScalars : List String → Com
  | [] => .skip
  | x :: xs => .seq (.read x) (readScalars xs)

/-- It stores into no array. -/
@[simp] theorem warrs_readScalars (xs : List String) : (readScalars xs).warrs = [] := by
  induction xs with
  | nil => simp [readScalars]
  | cons x xs ih => simp [readScalars, Com.warrs, ih]

/-- And it writes nothing. -/
@[simp] theorem noWrite_readScalars (xs : List String) : (readScalars xs).NoWrite := by
  induction xs with
  | nil => exact Com.noWrite_skip
  | cons x xs ih => exact ⟨trivial, ih⟩

/-- **The scalar prelude.** Started on a tape beginning with `vs`, one
entry per name, the prelude leaves each named cell holding its entry and
the tape advanced past them. The names have to be distinct: they are
read in order, and a name read twice would keep only its second entry.

The frame condition on the cells rides in the postcondition rather than
being left to `Spec.frame`, because the induction needs it one step at a
time — the head cell survives the tail only because the tail cannot
assign to it.

The cost is `|xs| + 1`: one for each `read`, and one for the `skip` the
recursion ends in (P5/D-q: the recursion is `foldr`-shaped rather than
special-casing the singleton, so the constant is `+1` and every caller
carries it; a marshalling constant is not worth a second equation). -/
theorem readScalars_spec (B : ℕ) (xs : List String) (vs rest : List ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) :
    Spec B (fun σ => σ.inp = vs ++ rest) (readScalars xs)
      (fun σ σ' => (∀ p ∈ xs.zip vs, σ'.vars p.1 = p.2) ∧ σ'.inp = rest ∧
        (∀ y, y ∉ xs → σ'.vars y = σ.vars y))
      (xs.length + 1) := by
  induction xs generalizing vs rest with
  | nil =>
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      refine Spec.skip.post ?_
      rintro σ σ' hσ rfl
      exact ⟨by simp, by simpa using hσ, fun _ _ => rfl⟩
  | cons x xs ih =>
      obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp at hlen
        | cons v vs' => exact ⟨v, vs', rfl⟩
      have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
      refine (Spec.seq (Spec.read (x := x) (v := fun _ => v) (rest := fun _ => vs' ++ rest)
          (fun σ hσ => by simpa using hσ))
        (ih vs' rest (List.nodup_cons.1 hnd).2 (by simpa using hlen))
        (fun σ σ' _ hq => by rw [hq]) ?_).mono (by simp only [List.length_cons]; omega)
      rintro σ σ' σ'' hσ rfl ⟨hzip, hinp, hfr⟩
      refine ⟨?_, hinp, fun y hy => ?_⟩
      · rintro ⟨y, w⟩ hp
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with hp | hp
        · rw [Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          simpa using hfr y hx
        · exact hzip _ hp
      · have hyx : y ≠ x := by rintro rfl; exact hy (List.mem_cons_self ..)
        rw [hfr y (fun h => hy (List.mem_cons_of_mem _ h))]
        simp [hyx]

/-! ### The array prelude -/

/-- Read as many further entries into the array `a` as the cell `m`
holds, in order: `x` is the counter, and each entry passes through `tmp`
on its way into the array. The array is *not* created — it already has
the length `ext` declared. -/
def readArr (a x m tmp : String) : Com :=
  .seq (.assign x (.lit 0))
    (.while (.lt (.var x) (.var m)) (.seq (.read tmp) (Fill.put a x (.var tmp))))

@[simp] theorem wvars_readArr (a x m tmp : String) :
    (readArr a x m tmp).wvars = [x, tmp, x] := by
  simp [readArr, Com.wvars]

@[simp] theorem warrs_readArr (a x m tmp : String) : (readArr a x m tmp).warrs = [a] := by
  simp [readArr, Com.warrs]

@[simp] theorem noWrite_readArr (a x m tmp : String) : (readArr a x m tmp).NoWrite := by
  simp [readArr, Com.NoWrite]

/-- **The array prelude.** The array has the right length already and
the cell `m` holds it; what comes back is the array holding exactly the
entries that were on the tape, the tape advanced past them, and the
counter at the end.

A turn costs `8` — the `read`'s `1` and `Fill.put`'s `7` — so the phase
costs `12·n + 6`. The four names have to be distinct in the three ways
the proof uses them: neither the counter nor the temporary may be the
length cell, and the `read` must not land on the counter. -/
theorem readArr_spec (B : ℕ) (a x m tmp : String) (ys rest : List ℕ)
    (hxm : x ≠ m) (htm : tmp ≠ m) (htx : tmp ≠ x)
    (hnB : ys.length < B) (hyB : ∀ v ∈ ys, v < B) :
    Spec B (fun σ => (σ.arrs a).length = ys.length ∧ σ.vars m = ys.length ∧
        σ.inp = ys ++ rest)
      (readArr a x m tmp)
      (fun _ σ' => σ'.arrs a = ys ∧ σ'.inp = rest ∧ σ'.vars x = ys.length)
      (12 * ys.length + 6) := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ, ∀ j, F j = ys.getD j 0 := ⟨_, fun _ => rfl⟩
  have hFe : ∀ j, (h : j < ys.length) → F j = ys[j] := fun j h => by
    rw [hF]; exact getD_eq_getElem h
  have hFB : ∀ j, j < ys.length → F j < B := fun j h => by
    rw [hFe j h]; exact hyB _ (List.getElem_mem h)
  have hFarr : arrOf ys.length F = ys := by
    rw [show F = fun j => ys.getD j 0 from funext hF]; exact arrOf_getD ys
  have hbody : Spec B
      (fun τ => (Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧
        τ.inp = ys.drop (τ.vars x) ++ rest) ∧ τ.vars x < ys.length)
      (.seq (.read tmp) (Fill.put a x (.var tmp)))
      (fun τ τ' => (Fill.Below a x ys.length F τ' ∧ τ'.vars m = ys.length ∧
        τ'.inp = ys.drop (τ'.vars x) ++ rest) ∧ τ'.vars x = τ.vars x + 1) 8 := by
    refine (Spec.seq
      (Spec.read (x := tmp) (v := fun τ => F (τ.vars x))
        (rest := fun τ => ys.drop (τ.vars x + 1) ++ rest) ?_)
      ((Fill.put_spec B ys.length a x (.var tmp) F
        (fun τ => Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧ τ.vars x < ys.length ∧
          τ.vars tmp = F (τ.vars x) ∧ τ.inp = ys.drop (τ.vars x + 1) ++ rest)
        (fun τ hτ => ⟨hτ.1, hτ.2.2.1⟩) hnB
        (fun τ hτ => by
          rw [← hτ.2.2.2.1]
          exact evalB_var (by rw [hτ.2.2.2.1]; exact hFB _ hτ.2.2.1))).frame)
      ?_ ?_).mono (by simp)
    · rintro τ ⟨⟨-, -, hinp⟩, hlt⟩
      show τ.inp = F (τ.vars x) :: (ys.drop (τ.vars x + 1) ++ rest)
      rw [hinp, List.drop_eq_getElem_cons hlt, hFe _ hlt, List.cons_append]
    · rintro τ τ' ⟨⟨hb, hm, -⟩, hlt⟩ rfl
      exact ⟨hb.of_eq (by simp) (by simp [Ne.symm htx]), by simpa [Ne.symm htm] using hm,
        by simpa [Ne.symm htx] using hlt, by simp [Ne.symm htx], by simp [Ne.symm htx]⟩
    · rintro τ τ' τ'' ⟨⟨-, hm, -⟩, hlt⟩ rfl ⟨⟨hb'', hxx⟩, hfv, -, hfi, -⟩
      simp only [vars_setVar, if_neg (Ne.symm htx)] at hxx
      refine ⟨⟨hb'', ?_, ?_⟩, hxx⟩
      · rw [hfv m (by simp [Ne.symm hxm])]
        simpa [Ne.symm htm] using hm
      · rw [hfi (by simp), hxx]
  refine (((Spec.forRangeZero x m
    (fun τ => Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧
      τ.inp = ys.drop (τ.vars x) ++ rest)
    ys.length 8 hnB (fun τ hτ => hτ.1.le) (fun τ hτ => hτ.2.1) hbody).pre ?_).post ?_).mono
      (by omega)
  · rintro σ ⟨hlen, hm, hinp⟩
    refine ⟨Fill.below_zero (g := fun j => (σ.arrs a).getD j 0) ?_ (by simp), ?_, ?_⟩
    · rw [arrs_setVar, ← hlen, arrOf_getD]
    · simpa [Ne.symm hxm] using hm
    · simp [hinp]
  · rintro σ σ' - ⟨⟨hb, -, hinp⟩, hxe⟩
    obtain ⟨g, harr, hg⟩ := hb.done hxe
    exact ⟨by rw [harr, arrOf_congr hg, hFarr], by rw [hinp, hxe]; simp, hxe⟩

/-- The prelude of the length-prefixed shape: the scalars, then the
array whose length is one of them. -/
def readScalarsThenArr (xs : List String) (a x m tmp : String) : Com :=
  .seq (readScalars xs) (readArr a x m tmp)

/-- The named cells hold the scalar input, and `a` holds the remaining
entries. The counter `x` holds their number, and the temporary `tmp` is spent. -/
def ScalarsArrIn (ext : String → ℕ) (xs : List String) (a x tmp : String)
    (vs ys : List ℕ) (σ : Env) : Prop :=
  (∀ p ∈ xs.zip vs, σ.vars p.1 = p.2) ∧ σ.arrs a = ys ∧ σ.vars x = ys.length ∧
    (∀ y, y ∉ xs → y ≠ x → y ≠ tmp → σ.vars y = 0) ∧
    (∀ b, b ≠ a → σ.arrs b = List.replicate (ext b) 0) ∧ σ.inp = [] ∧ σ.out = []

namespace ScalarsArrIn

variable {ext : String → ℕ} {xs : List String} {a x tmp : String} {vs ys : List ℕ} {σ : Env}

/-- The cells the scalars were read into. -/
theorem cells (h : ScalarsArrIn ext xs a x tmp vs ys σ) :
    ∀ p ∈ xs.zip vs, σ.vars p.1 = p.2 := h.1

/-- The array holds what followed the scalars on the tape. -/
theorem arr (h : ScalarsArrIn ext xs a x tmp vs ys σ) : σ.arrs a = ys := h.2.1

/-- Every other array is what `ext` declared. -/
theorem arrs (h : ScalarsArrIn ext xs a x tmp vs ys σ) :
    ∀ b, b ≠ a → σ.arrs b = List.replicate (ext b) 0 := h.2.2.2.2.1

end ScalarsArrIn

/-! ### The preludes at `initEnv` -/

/-- **The scalar prelude on an initial environment**, with whatever it
did not read left on the tape. This is the form the length-prefixed
shape composes with; the shape that reads nothing else is the case
`rest = []` below. -/
theorem readScalars_initEnv_rest_spec (B : ℕ) (ext : String → ℕ) (xs : List String)
    (vs rest : List ℕ) (hnd : xs.Nodup) (hlen : vs.length = xs.length) :
    Spec B (fun σ => σ = initEnv ext (vs ++ rest)) (readScalars xs)
      (fun _ σ' => (∀ p ∈ xs.zip vs, σ'.vars p.1 = p.2) ∧ (∀ y, y ∉ xs → σ'.vars y = 0) ∧
        (∀ b, σ'.arrs b = List.replicate (ext b) 0) ∧ σ'.inp = rest ∧ σ'.out = [])
      (xs.length + 1) := by
  refine ((readScalars_spec B xs vs rest hnd hlen).frame.pre
    (fun σ hσ => by rw [hσ]; rfl)).post ?_
  rintro σ σ' rfl ⟨⟨hzip, hinp, hfr⟩, -, hfa, -, hout⟩
  exact ⟨hzip, fun y hy => by rw [hfr y hy]; rfl, fun b => by rw [hfa b (by simp)]; rfl,
    hinp, by rw [hout (noWrite_readScalars xs)]; rfl⟩

/-- **The length-prefixed prelude at `initEnv`.** The scalars come
first, one of them is the array's length, and the array's declared
length has to agree with it — the pre-sizing convention, as a
hypothesis. The counter and the temporary must be names of their own,
or the prelude would overwrite what it had just read.

The cost is the two phases': `|xs| + 12·n + 7`. -/
theorem readScalarsThenArr_spec (B : ℕ) (ext : String → ℕ) (xs : List String)
    (a x m tmp : String) (vs ys : List ℕ)
    (hnd : xs.Nodup) (hlen : vs.length = xs.length) (hm : (m, ys.length) ∈ xs.zip vs)
    (hx : x ∉ xs) (htmp : tmp ∉ xs) (hxm : x ≠ m) (htm : tmp ≠ m) (htx : tmp ≠ x)
    (hext : ext a = ys.length) (hnB : ys.length < B) (hyB : ∀ v ∈ ys, v < B) :
    Spec B (fun σ => σ = initEnv ext (vs ++ ys)) (readScalarsThenArr xs a x m tmp)
      (fun _ σ' => ScalarsArrIn ext xs a x tmp vs ys σ')
      (xs.length + 12 * ys.length + 7) := by
  refine (Spec.seq (readScalars_initEnv_rest_spec B ext xs vs ys hnd hlen)
    ((readArr_spec B a x m tmp ys [] hxm htm htx hnB hyB).frame) ?_ ?_).mono (by omega)
  · rintro σ σ' - ⟨hzip, -, harr, hinp, -⟩
    exact ⟨by rw [harr a]; simp [hext], hzip _ hm, by simp [hinp]⟩
  · rintro σ σ' σ'' - ⟨hzip, hzero, harr, -, hout⟩ ⟨⟨harr', hinp', hcnt'⟩, hfv, hfa, -, hfo⟩
    have hne : ∀ p ∈ xs.zip vs, p.1 ≠ x ∧ p.1 ≠ tmp := fun p hp => by
      have hp1 : p.1 ∈ xs := (List.of_mem_zip hp).1
      exact ⟨fun h => hx (h ▸ hp1), fun h => htmp (h ▸ hp1)⟩
    refine ⟨fun p hp => ?_, harr', hcnt', fun y hy hyx hyt => ?_, fun b hb => ?_, hinp', ?_⟩
    · rw [hfv p.1 (by simp [(hne p hp).1, (hne p hp).2])]
      exact hzip p hp
    · rw [hfv y (by simp [hyx, hyt])]; exact hzero y hy
    · rw [hfa b (by simp [hb])]; exact harr b
    · rw [hfo (noWrite_readArr a x m tmp)]; exact hout


end Lax47Proofs.InputHarness
