import lemmas.Ska.PokeHalt
import lemmas.Ska.BakeMeasure

/-!
# The worklist of `+bake-graph` ends: the leaf `BakeEnds` (track Q, README Gaps 31)

`BakeEnds` (`PokeHalt.lean`, leaf H2 of `HaltLeaves13`) asks that the
worklist of `+bake-graph` return within the fuel `bf E` on every `%full`
poke from an `InvB` state.  This file does three things.

* **The fuel.**  `bakeFuel E` is a fuel at which the worklist returns, when
  there is one (as `anaFuel` of `AnaEnds.lean` for the analysis), so
  `BakeEnds` at `bakeFuel` is exactly `BakeHalts`: the worklist returns at
  SOME fuel (`bakeEnds_of_halts`, `bakeHalts_of_ends`).  `bakeEnds_mono`:
  `BakeEnds` at a fuel gives it at every larger fuel (from `bakeLoop_mono`).
* **The measure.**  `kapX` is a measure of what a sock knows that depends
  only on its nouns (unlike `kap` of `BakeMeasure.lean`, which needs the
  normal form of `+norm-sock`): `&` on a noun of size `n` counts `2 n + 1`, a
  cape that knows nothing `0`, a cell cape that knows something the sum of
  its halves plus `1` (the cell).  So `[& &]` and `&` on one cell count the
  same, and data under `|` does not count.  `kapXS_lt`: of two socks with a
  noun, if the nouns of the first are nouns of the second and not the other
  way, the second counts less.  So every change of a bake LOWERS `kapXS`
  unless the old and the new bake have the same nouns (a TIE: `bakeChange_kapX`).
* **The loop.**  `bakeLoop_halts`: the worklist returns at some fuel when
  (1) the bells that ever get a bake are in a finite list `U`, (2) no step
  crashes, (3) no change of a bake is a tie and no bake is empty.  The
  measure is lexicographic: the bells of `U` with no bake, then the sum of
  `kapXS` over the bakes, then the length of the queue.  On the real
  compiler (85 pokes, `tools/hoon/bakehalt-*.hoon`) there was no tie.
-/

namespace Formalization
namespace SkaModel

open Nock Ana Bake

namespace Bake

/-! ## The measure of what a sock knows -/

/-- What a cape knows of its data, as a function of its nouns. -/
def kapX : Cape → Noun → Nat
  | Cape.no, _ => 0
  | Cape.yes, d => 2 * nsz d + 1
  | Cape.cell h t, d =>
    if (h.isNo && t.isNo) = true then 0 else
    match d with
    | Noun.cell dh dt => kapX h dh + kapX t dt + 1
    | Noun.atom _ => 0

/-- The measure on socks. -/
def kapXS : Sock → Nat
  | Sock.void => 0
  | Sock.mk c d => kapX c d

theorem fitsCape_isNo : ∀ {c : Cape} (d x : Noun), c.isNo = true → FitsCape c d x
  | Cape.no, _, _, _ => trivial
  | Cape.yes, _, _, h => by simp [Cape.isNo] at h
  | Cape.cell _ _, _, _, h => Or.inl h

theorem kapX_isNo : ∀ {c : Cape} (d : Noun), c.isNo = true → kapX c d = 0
  | Cape.no, _, _ => rfl
  | Cape.yes, _, h => by simp [Cape.isNo] at h
  | Cape.cell h t, d, e => by
    have e' : (h.isNo && t.isNo) = true := e
    simp only [kapX, e', if_true]

theorem kapX_cell {h t : Cape} (hn : (h.isNo && t.isNo) = false) (dh dt : Noun) :
    kapX (Cape.cell h t) (C dh dt) = kapX h dh + kapX t dt + 1 := by
  simp only [kapX, hn]; rfl

theorem fitsCape_cell {h t : Cape} {d x : Noun} (hn : (h.isNo && t.isNo) = false)
    (hx : FitsCape (Cape.cell h t) d x) :
    ∃ dh dt xh xt, d = C dh dt ∧ x = C xh xt ∧ FitsCape h dh xh ∧ FitsCape t dt xt := by
  rcases hx with e | hx
  · rw [hn] at e; cases e
  · exact hx

theorem fitsCape_cell_intro {h t : Cape} {dh dt xh xt : Noun} (a : FitsCape h dh xh) (b : FitsCape t dt xt) :
    FitsCape (Cape.cell h t) (C dh dt) (C xh xt) :=
  Or.inr ⟨dh, dt, xh, xt, rfl, rfl, a, b⟩

/-- A cape with exactly one noun counts as `&` on it. -/
theorem kapX_single : ∀ {c : Cape} {d e : Noun}, FitsCape c d e → (∀ x, FitsCape c d x → x = e) →
    kapX c d = 2 * nsz e + 1
  | Cape.no, _, _, _, h => by
    have h0 := h (A 0) trivial
    have h1 := h (A 1) trivial
    rw [← h1] at h0; cases h0
  | Cape.yes, d, e, he, _ => by
    simp only [FitsCape] at he; subst he; rfl
  | Cape.cell h t, d, e, he, hs => by
    cases hn : (h.isNo && t.isNo) with
    | true =>
      have h0 := hs (A 0) (Or.inl hn)
      have h1 := hs (A 1) (Or.inl hn)
      rw [← h1] at h0; cases h0
    | false =>
      obtain ⟨dh, dt, eh, et, rfl, rfl, fh, ft⟩ := fitsCape_cell hn he
      have sh : ∀ x, FitsCape h dh x → x = eh := fun x hx => by
        have := hs (C x et) (fitsCape_cell_intro hx ft); cases this; rfl
      have st : ∀ x, FitsCape t dt x → x = et := fun x hx => by
        have := hs (C eh x) (fitsCape_cell_intro fh hx); cases this; rfl
      rw [kapX_cell hn, kapX_single fh sh, kapX_single ft st]
      simp only [nsz]; omega

/-- A cape that knows something (some noun does not fit it) counts more
than `0`, when it has a noun. -/
theorem kapX_pos : ∀ {c : Cape} {d e : Noun}, FitsCape c d e → (∃ y, ¬ FitsCape c d y) → 0 < kapX c d
  | Cape.no, _, _, _, ⟨_, hy⟩ => absurd trivial hy
  | Cape.yes, _, _, _, _ => by simp only [kapX]; omega
  | Cape.cell h t, d, e, he, ⟨y, hy⟩ => by
    cases hn : (h.isNo && t.isNo) with
    | true => exact absurd (Or.inl hn) hy
    | false =>
      obtain ⟨dh, dt, _, _, rfl, rfl, _, _⟩ := fitsCape_cell hn he
      rw [kapX_cell hn]; omega

/-- **The measure follows the nouns**: if every noun of `a` (which has one)
fits `b`, then `b` counts no more than `a`, and less when some noun of `b`
does not fit `a`. -/
theorem kapX_sub : ∀ (cb : Cape) {db : Noun} {ca : Cape} {da e : Noun}, FitsCape ca da e →
    (∀ x, FitsCape ca da x → FitsCape cb db x) →
    kapX cb db ≤ kapX ca da ∧ ((∃ y, FitsCape cb db y ∧ ¬ FitsCape ca da y) → kapX cb db < kapX ca da)
  | Cape.no, _, ca, da, e, he, _ => by
    refine ⟨Nat.zero_le _, fun ⟨y, _, hy⟩ => ?_⟩
    exact kapX_pos he ⟨y, hy⟩
  | Cape.yes, db, ca, da, e, he, hs => by
    have hd : e = db := hs e he
    subst hd
    have k := kapX_single he (fun x hx => hs x hx)
    refine ⟨by simp only [kapX]; omega, fun ⟨y, hy, hy'⟩ => ?_⟩
    simp only [FitsCape] at hy; subst hy; exact absurd he hy'
  | Cape.cell h t, db, ca, da, e, he, hs => by
    cases hn : (h.isNo && t.isNo) with
    | true =>
      rw [kapX_isNo (c := Cape.cell h t) db hn]
      refine ⟨Nat.zero_le _, fun ⟨y, _, hy⟩ => kapX_pos he ⟨y, hy⟩⟩
    | false =>
      obtain ⟨dbh, dbt, ebh, ebt, rfl, rfl, fbh, fbt⟩ := fitsCape_cell hn (hs e he)
      rw [kapX_cell hn]
      -- `a` as two halves: its nouns are the cells of the nouns of the halves
      cases ca with
      | no =>
        have := hs (A 0) trivial
        obtain ⟨_, _, _, _, _, e', _, _⟩ := fitsCape_cell hn this; cases e'
      | yes =>
        simp only [FitsCape] at he
        subst he
        have sh : ∀ x, FitsCape Cape.yes ebh x → FitsCape h dbh x := fun x hx => by
          simp only [FitsCape] at hx; subst hx; exact fbh
        have st : ∀ x, FitsCape Cape.yes ebt x → FitsCape t dbt x := fun x hx => by
          simp only [FitsCape] at hx; subst hx; exact fbt
        have i1 := kapX_sub h (ca := Cape.yes) (da := ebh) (e := ebh) rfl sh
        have i2 := kapX_sub t (ca := Cape.yes) (da := ebt) (e := ebt) rfl st
        have hk : kapX Cape.yes (C ebh ebt) = kapX Cape.yes ebh + kapX Cape.yes ebt + 1 := by
          simp only [kapX, nsz]; omega
        rw [hk]
        refine ⟨by omega, fun ⟨y, hy, hy'⟩ => ?_⟩
        obtain ⟨_, _, yh, yt, e1, rfl, gh, gt⟩ := fitsCape_cell hn hy
        cases e1
        by_cases c1 : FitsCape Cape.yes ebh yh
        · by_cases c2 : FitsCape Cape.yes ebt yt
          · refine absurd ?_ hy'
            simp only [FitsCape] at c1 c2 ⊢
            rw [c1, c2]
          · have := i2.2 ⟨yt, gt, c2⟩; omega
        · have := i1.2 ⟨yh, gh, c1⟩; omega
      | cell h' t' =>
        cases hn' : (h'.isNo && t'.isNo) with
        | true =>
          have := hs (A 0) (Or.inl hn')
          obtain ⟨_, _, _, _, _, e', _, _⟩ := fitsCape_cell hn this; cases e'
        | false =>
          obtain ⟨dah, dat, eah, eat, rfl, e2, fah, fat⟩ := fitsCape_cell hn' he
          cases e2
          have sh : ∀ x, FitsCape h' dah x → FitsCape h dbh x := fun x hx => by
            obtain ⟨_, _, _, _, e1, e2, g, _⟩ := fitsCape_cell hn (hs _ (fitsCape_cell_intro hx fat))
            cases e1; cases e2; exact g
          have st : ∀ x, FitsCape t' dat x → FitsCape t dbt x := fun x hx => by
            obtain ⟨_, _, _, _, e1, e2, _, g⟩ := fitsCape_cell hn (hs _ (fitsCape_cell_intro fah hx))
            cases e1; cases e2; exact g
          have i1 := kapX_sub h fah sh
          have i2 := kapX_sub t fat st
          rw [kapX_cell hn']
          refine ⟨by omega, fun ⟨y, hy, hy'⟩ => ?_⟩
          obtain ⟨_, _, yh, yt, e1, rfl, gh, gt⟩ := fitsCape_cell hn hy
          cases e1
          by_cases c1 : FitsCape h' dah yh
          · by_cases c2 : FitsCape t' dat yt
            · exact absurd (fitsCape_cell_intro c1 c2) hy'
            · have := i2.2 ⟨yt, gt, c2⟩; omega
          · have := i1.2 ⟨yh, gh, c1⟩; omega

/-- **A strict loss of nouns lowers the measure**, for socks with a noun. -/
theorem kapXS_lt {a b : Sock} (ha : ∃ x, Fits a x) (hs : Sub a b) (hl : ¬ Sub b a) : kapXS b < kapXS a := by
  cases a with
  | void => obtain ⟨_, h⟩ := ha; exact absurd h id
  | mk ca da =>
  obtain ⟨e, he⟩ := ha
  cases b with
  | void => exact absurd (hs e he) id
  | mk cb db =>
  refine (kapX_sub cb he hs).2 ?_
  refine Classical.byContradiction fun hn => hl fun y hy => ?_
  exact Classical.byContradiction fun hy' => hn ⟨y, hy, hy'⟩

theorem kapXS_le {a b : Sock} (ha : ∃ x, Fits a x) (hs : Sub a b) : kapXS b ≤ kapXS a := by
  cases a with
  | void => obtain ⟨_, h⟩ := ha; exact absurd h id
  | mk ca da =>
  obtain ⟨e, he⟩ := ha
  cases b with
  | void => exact absurd (hs e he) id
  | mk cb db => exact (kapX_sub cb he hs).1

/-- `[& &]` and `&` on one cell count the same (where `kap` does not). -/
example : kapX (Cape.cell Cape.yes Cape.yes) (C (A 7) (A 8)) = kapX Cape.yes (C (A 7) (A 8)) := by decide

/-- **A rebake lowers the measure unless it is a tie**: a bake that changes
from a bake with a noun loses measure, unless the two have the same nouns. -/
theorem rebakeG_kapX {bake s o : Sock} {g g' : Nat} (h : rebakeG bake (some o) g = some (s, g'))
    (ho : ∃ x, Fits o x) : kapXS s ≤ kapXS o ∧ (¬ Sub s o → kapXS s < kapXS o) :=
  ⟨kapXS_le ho (rebakeG_grows h), kapXS_lt ho (rebakeG_grows h)⟩

/-! ## The loop: a measure that drops at every step ends it -/

section Loop

variable {M : Type → Type → Type} [Treap M]

/-- The lexicographic order of the measure of the worklist. -/
def LexLt (a b : Nat × Nat × Nat) : Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) a b

theorem lexLt_wf : WellFounded LexLt :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

/-- **A worklist whose every step returns and lowers a measure ends**: if
`R` holds of a state, every state of `R` with a queued bell takes a step
that returns into `R` with a smaller measure (lexicographic), then the
worklist returns at some fuel. -/
theorem bakeLoop_halts_of_drop (E : BEnv M) (μ : List Bell → BSt M → Nat × Nat × Nat)
    (R : List Bell → M Bell Unit → BSt M → Prop)
    (hstep : ∀ cur rest qs st, R (cur :: rest) qs st → ∃ q' qs' st',
      bakeStep E cur rest qs st = some (q', qs', st') ∧ R q' qs' st' ∧ LexLt (μ q' st') (μ (cur :: rest) st)) :
    ∀ q qs st, R q qs st → ∃ n st', bakeLoop E n q qs st = some st' := by
  intro q qs st
  suffices ∀ m, ∀ q qs st, μ q st = m → R q qs st → ∃ n st', bakeLoop E n q qs st = some st' from
    this _ q qs st rfl
  intro m
  induction m using lexLt_wf.induction with
  | _ m ih =>
    intro q qs st hm hR
    cases q with
    | nil => exact ⟨1, st, rfl⟩
    | cons cur rest =>
      obtain ⟨q', qs', st', h1, hR', hlt⟩ := hstep cur rest qs st hR
      obtain ⟨n, st'', h2⟩ := ih _ (hm ▸ hlt) q' qs' st' rfl hR'
      exact ⟨n + 1, st'', by simp only [bakeLoop, h1, Option.bind_some, h2]⟩

/-- The bells of `U` with no bake. -/
def unbaked (U : List Bell) (st : BSt M) : Nat := (U.filter fun c => (Treap.get st.bak c).isNone).length

/-- The sum of the measures of the bakes of the bells of `U`. -/
def kapSum (U : List Bell) (st : BSt M) : Nat :=
  (U.map fun c => match Treap.get st.bak c with
    | some s => kapXS s
    | none => 0).sum

/-- **The measure of the worklist**: the bells of `U` with no bake, the
sum of `kapXS` of the bakes, and the length of the queue. -/
def bakeMeasure (U : List Bell) (q : List Bell) (st : BSt M) : Nat × Nat × Nat :=
  (unbaked U st, kapSum U st, q.length)

/-- **The step of the worklist ends it**: `BakeHalts` of one environment
from a set `R` of states that contains the first one and that the steps
keep, when every step from a state of `R` returns and lowers
`bakeMeasure U`. -/
theorem bakeLoop_halts (E : BEnv M) (U : List Bell) (R : List Bell → M Bell Unit → BSt M → Prop)
    (h0 : R [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E))
    (hstep : ∀ cur rest qs st, R (cur :: rest) qs st → ∃ q' qs' st',
      bakeStep E cur rest qs st = some (q', qs', st') ∧ R q' qs' st' ∧
        LexLt (bakeMeasure U q' st') (bakeMeasure U (cur :: rest) st)) :
    ∃ n st, bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st :=
  bakeLoop_halts_of_drop E (fun q st => bakeMeasure U q st) R hstep _ _ _ h0

/-! ### One touched callee -/

theorem filter_len_le_of {U : List Bell} {p p' : Bell → Bool} (h : ∀ c ∈ U, p' c = true → p c = true) :
    (U.filter p').length ≤ (U.filter p).length := by
  induction U with
  | nil => simp
  | cons c U ih =>
    have ih' := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    have hc := h c List.mem_cons_self
    simp only [List.filter_cons]
    cases hp' : p' c <;> cases hp : p c <;> simp_all <;> omega

theorem filter_len_lt_of {U : List Bell} {p p' : Bell → Bool} (h : ∀ c ∈ U, p' c = true → p c = true)
    {c0 : Bell} (hc0 : c0 ∈ U) (hp : p c0 = true) (hp' : p' c0 = false) :
    (U.filter p').length < (U.filter p).length := by
  induction U with
  | nil => simp at hc0
  | cons c U ih =>
    have hle := filter_len_le_of (U := U) (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    have hc := h c List.mem_cons_self
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hc0 with rfl | hm
    · simp only [hp, hp', if_true]; simp; omega
    · have := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) hm
      cases hp1 : p' c <;> cases hp2 : p c <;> simp_all <;> omega

theorem sum_le_of {U : List Bell} {f f' : Bell → Nat} (h : ∀ c ∈ U, f' c ≤ f c) :
    (U.map f').sum ≤ (U.map f).sum := by
  induction U with
  | nil => simp
  | cons c U ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h c List.mem_cons_self
    have := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    omega

theorem sum_lt_of {U : List Bell} {f f' : Bell → Nat} (h : ∀ c ∈ U, f' c ≤ f c) {c0 : Bell} (hc0 : c0 ∈ U)
    (hl : f' c0 < f c0) : (U.map f').sum < (U.map f).sum := by
  induction U with
  | nil => simp at hc0
  | cons c U ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h c List.mem_cons_self
    have hle := sum_le_of (U := U) (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    rcases List.mem_cons.mp hc0 with rfl | hm
    · omega
    · have := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) hm; omega

/-- **A new bake for one callee lowers the first two parts of the
measure**: a callee of `U` that had no bake gets one (fewer bells without a
bake), or its bake changes from one with a noun to one that loses nouns (a
smaller sum of `kapXS`). -/
theorem put_drop {U : List Bell} {st st' : BSt M} {c : Bell} {s : Sock} (hc : c ∈ U)
    (hbak : st'.bak = Treap.put st.bak c s)
    (hcase : Treap.get st.bak c = none ∨ ∃ o, Treap.get st.bak c = some o ∧ (∃ x, Fits o x) ∧ Sub o s ∧ ¬ Sub s o) :
    Prod.Lex (· < ·) (· < ·) (unbaked U st', kapSum U st') (unbaked U st, kapSum U st) := by
  have hget : ∀ c', Treap.get st'.bak c' = if c' = c then some s else Treap.get st.bak c' := by
    intro c'; rw [hbak, Treap.get_put]
  rcases hcase with hn | ⟨o, ho, hne, hs, hl⟩
  · refine Prod.Lex.left _ _ ?_
    unfold unbaked
    refine filter_len_lt_of (fun c' _ h => ?_) hc (by simp [hn]) (by simp [hget])
    rw [hget] at h
    split at h
    · simp at h
    · exact h
  · have hu : unbaked U st' = unbaked U st := by
      unfold unbaked
      congr 1
      refine List.filter_congr fun c' _ => ?_
      rw [hget]
      split
      · rename_i e; subst e; simp [ho]
      · rfl
    rw [hu]
    refine Prod.Lex.right _ ?_
    unfold kapSum
    refine sum_lt_of (fun c' _ => ?_) hc ?_
    · by_cases e : c' = c
      · subst e; simp only [hget, if_true, ho]; exact kapXS_le hne hs
      · simp only [hget, if_neg e]; exact Nat.le_refl _
    · simp only [hget, if_true, ho]
      exact kapXS_lt hne hs hl

end Loop

end Bake

end SkaModel
end Formalization
