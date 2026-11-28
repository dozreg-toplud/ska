import lemmas.Ska.BakeHaltTie
import lemmas.Ska.BakeImp

/-!
# The normal floor: the worklist of `+bake-graph` ends with no tie hypothesis
(track Q, README Gaps 31.7)

The candidate fix of the coordinator (NOT in `desk/`): in `+bake-graph`, a bell
that is not fixed and not frozen gets the NORMAL floor `(norm-sock less.c)`
where the Hoon takes the raw `less.c`, at its two places (no informer, and the
sites contradict `less.c`):
```
      ?~  ks  (norm-sock less.c)
      ?.  (huge:so less.c both)  (norm-sock less.c)
```
The model of the fixed worklist is `bakeLoopN`.  It is the model's worklist
over its bake function made a parameter (`touchStepG`, `bakeStepG`,
`bakeLoopG`: `touchStepG bakeOf = touchStep` and `bakeStepG bakeOf = bakeStep`
by `rfl`, `bakeLoopG_bakeOf`), at `bakeOfN`, `bakeOf` with the normal floor.

* **No tie** (`touchStepN_noTie`): under `NInv` (a fixed bell's bake is
  `less.c`, every other bake but the root's is `Canon`), a change of a bake
  that had one is a strict loss.  A fixed bell's bake never changes once set
  (`rebakeG` of `less.c` against `less.c` keeps it), and two `Canon` bakes with
  the same nouns are equal (`canon_ext`), so a change is a change of nouns,
  and a change of nouns is a loss (`rebakeG_grows`).
* `NInv` holds at the start and every step keeps it (`bakeStepN_inv`).
* **The end** (`bakeLoopN_halts_of_drops`, `bakeHaltsN_of_drops`,
  `bakeEndsN_of_drops`): `BakeDropsN` is `BakeDrops` without hypothesis (a):
  a finite `U` that holds every bell whose bake changes, an old bake with a
  noun (c), and every step returning into `Rs` (b).
-/

namespace Formalization
namespace SkaModel

open Nock Ana Bake

namespace Bake

variable {M : Type → Type → Type} [Treap M]

/-! ## The worklist over its bake function -/

/-- `touchStep` with the bake function `bo` (`bakeOf` in the Hoon). -/
def touchStepG (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) (cur : Bell)
    (new : M Bell (List Sock)) (acc : Option (List Bell × BSt M)) (c : Bell) : Option (List Bell × BSt M) :=
  acc.bind fun ⟨changed, st⟩ =>
  let m := innUpd new cur c (Treap.gut st.inn c Treap.empty)
  let st := { st with inn := Treap.put st.inn c m }
  if c = E.root then some (changed, st) else
  let st := { st with fix := if E.jetted c then Treap.put st.fix c () else st.fix }
  let ks := ((Treap.tap m).map Prod.snd).flatten
  (bo (E.frozen || Treap.has st.fix c) c.less ks).bind fun bake =>
  let old := Treap.get st.bak c
  (rebakeG bake old st.grew).bind fun ⟨bake, grew⟩ =>
  let st := { st with grew := grew }
  if some bake = old then some (changed, st) else
  some (c :: changed, { st with bak := Treap.put st.bak c bake })

theorem touchStepG_bakeOf : touchStepG (M := M) bakeOf = touchStep := rfl

/-- `bakeStep` with the bake function `bo`. -/
def bakeStepG (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) (cur : Bell) (rest : List Bell)
    (qs : M Bell Unit) (st : BSt M) : Option (List Bell × M Bell Unit × BSt M) :=
  let qs := Treap.del qs cur
  (sitesOf E st cur).bind fun sites =>
  let st := { st with evals := st.evals + 1 }
  (sites.foldl (newStep E.vars) (some Treap.empty)).bind fun new =>
  let newBells := keySet new
  let prev := Treap.gut st.out cur Treap.empty
  let st := { st with out := Treap.put st.out cur newBells }
  let touched := uniIn prev newBells
  ((Treap.tap touched).map Prod.fst |>.foldl (touchStepG bo E cur new) (some ([], st))).map fun ⟨changed, st⟩ =>
  let fresh := changed.filter fun c => !Treap.has qs c
  (rest ++ fresh, gasIn qs fresh, st)

theorem bakeStepG_bakeOf : bakeStepG (M := M) bakeOf = bakeStep := rfl

/-- `bakeLoop` with the bake function `bo`. -/
def bakeLoopG (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) :
    Nat → List Bell → M Bell Unit → BSt M → Option (BSt M)
  | 0, _, _, _ => none
  | _ + 1, [], _, st => some st
  | n + 1, cur :: rest, qs, st => (bakeStepG bo E cur rest qs st).bind fun ⟨q, qs, st⟩ => bakeLoopG bo E n q qs st

theorem bakeLoopG_bakeOf (E : BEnv M) : ∀ n q qs st, bakeLoopG bakeOf E n q qs st = bakeLoop E n q qs st
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | n + 1, cur :: rest, qs, st => by
    simp only [bakeLoopG, bakeLoop, bakeStepG_bakeOf]
    congr 1; funext p; exact bakeLoopG_bakeOf E n _ _ _

/-- **The normal floor**: `bakeOf` where a bell that is not fixed gets
`norm-sock less.c` in place of `less.c`. -/
def bakeOfN (fixed : Bool) (lessc : Sock) (ks : List Sock) : Option Sock :=
  if fixed then some lessc else
  match ks with
  | [] => normSockH lessc
  | k :: ks => (normSockH (uniSock lessc (meet k ks))).bind fun both =>
      (So.huge lessc both).bind fun h => if h then some both else normSockH lessc

/-- The worklist of the fixed `+bake-graph`. -/
abbrev touchStepN (E : BEnv M) := touchStepG bakeOfN E
abbrev bakeStepN (E : BEnv M) := bakeStepG bakeOfN E
abbrev bakeLoopN (E : BEnv M) := bakeLoopG bakeOfN E

theorem bakeOfN_canon {lessc s : Sock} {ks : List Sock} (h : bakeOfN false lessc ks = some s) : Canon s := by
  unfold bakeOfN at h
  simp only [Bool.false_eq_true, if_false] at h
  split at h
  · exact normSockH_canon h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨both, hb, hh, _, h⟩ := h
    split at h
    · cases h; exact normSockH_canon hb
    · exact normSockH_canon h

theorem rebakeG_canonN {bake s : Sock} {old : Option Sock} {g g' : Nat} (hb : Canon bake)
    (h : rebakeG bake old g = some (s, g')) : Canon s := by
  unfold rebakeG at h
  split at h
  · cases h; exact hb
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨hv, _, h⟩ := h
    split at h
    · cases h; exact hb
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨s', hs', rfl, -⟩ := h
      exact normSockH_canon hs'

theorem huge_self_some (s : Sock) : So.huge s s = some true := by
  cases s with
  | void => rfl
  | mk c d => exact hugeMk_self c d

theorem rebakeG_self {s : Sock} {g : Nat} : rebakeG s (some s) g = some (s, g) := by
  simp [rebakeG, huge_self_some]

/-! ## One touched callee, unfolded -/

theorem touchFoldG_none (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) (cur : Bell)
    (new : M Bell (List Sock)) : ∀ (l : List Bell), l.foldl (touchStepG bo E cur new) none = none
  | [] => rfl
  | _ :: l => touchFoldG_none bo E cur new l

theorem touchStepG_cases {bo : Bool → Sock → List Sock → Option Sock} {E : BEnv M} {cur : Bell}
    {new : M Bell (List Sock)} {c : Bell} {changed0 changed1 : List Bell} {st0 st1 : BSt M}
    (h : touchStepG bo E cur new (some (changed0, st0)) c = some (changed1, st1)) :
    st1.fix = (if c = E.root then st0.fix else if E.jetted c then Treap.put st0.fix c () else st0.fix) ∧
    ((c = E.root ∧ st1.bak = st0.bak ∧ changed1 = changed0) ∨
     (c ≠ E.root ∧ ∃ bake bake' g g',
        bo (E.frozen || Treap.has (if E.jetted c then Treap.put st0.fix c () else st0.fix) c) c.less
          (((Treap.tap (innUpd new cur c (Treap.gut st0.inn c Treap.empty))).map Prod.snd).flatten) = some bake ∧
        rebakeG bake (Treap.get st0.bak c) g = some (bake', g') ∧
        ((some bake' = Treap.get st0.bak c ∧ st1.bak = st0.bak ∧ changed1 = changed0) ∨
         (some bake' ≠ Treap.get st0.bak c ∧ st1.bak = Treap.put st0.bak c bake' ∧
           changed1 = c :: changed0)))) := by
  simp only [touchStepG, Option.bind_some] at h
  by_cases hc : c = E.root
  · rw [if_pos hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [if_pos hc], Or.inl ⟨hc, rfl, rfl⟩⟩
  · rw [if_neg hc] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨bake, hbake, ⟨bake', grew'⟩, hre, h⟩ := h
    by_cases hold : some bake' = Treap.get st0.bak c
    · rw [if_pos hold] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [if_neg hc], Or.inr ⟨hc, bake, bake', _, grew', hbake, hre, Or.inl ⟨hold, rfl, rfl⟩⟩⟩
    · rw [if_neg hold] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [if_neg hc], Or.inr ⟨hc, bake, bake', _, grew', hbake, hre, Or.inr ⟨hold, rfl, rfl⟩⟩⟩

/-! ## The measure for any bake function (copies of `BakeHalt.lean`) -/

/-- `TouchOK` for the bake function `bo`. -/
def TouchOKG (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) (U : List Bell) (cur : Bell)
    (new : M Bell (List Sock)) (st : BSt M) (c : Bell) : Prop :=
  ∀ ch ch' st', touchStepG bo E cur new (some (ch, st)) c = some (ch', st') → ch' ≠ ch →
    c ∈ U ∧ (Treap.get st.bak c = none ∨
      ∃ o, Treap.get st.bak c = some o ∧ (∃ x, Fits o x) ∧ ∀ s, Treap.get st'.bak c = some s → ¬ Sub s o)

/-- `FoldOK` for the bake function `bo`. -/
def FoldOKG (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) (U : List Bell) (cur : Bell)
    (new : M Bell (List Sock)) : List Bell → List Bell × BSt M → Prop
  | [], _ => True
  | c :: l, (ch, st) => TouchOKG bo E U cur new st c ∧
      ∀ r, touchStepG bo E cur new (some (ch, st)) c = some r → FoldOKG bo E U cur new l r

theorem touchStepG_drop {bo : Bool → Sock → List Sock → Option Sock} {E : BEnv M} {U : List Bell} {cur : Bell}
    {new : M Bell (List Sock)} {c : Bell} {ch ch' : List Bell} {st st' : BSt M}
    (h : touchStepG bo E cur new (some (ch, st)) c = some (ch', st')) (hok : TouchOKG bo E U cur new st c) :
    (ch' = ch ∧ meas2 U st' = meas2 U st) ∨ Prod.Lex (· < ·) (· < ·) (meas2 U st') (meas2 U st) := by
  obtain ⟨_, hcase⟩ := touchStepG_cases h
  rcases hcase with ⟨_, hbak, hch⟩ | ⟨_, bake, bake', g, g', _, hre, hcase⟩
  · left; exact ⟨hch, by unfold meas2 unbaked kapSum; rw [hbak]⟩
  · rcases hcase with ⟨_, hbak, hch⟩ | ⟨_, hbak, hch⟩
    · left; exact ⟨hch, by unfold meas2 unbaked kapSum; rw [hbak]⟩
    · right
      have hne : ch' ≠ ch := by rw [hch]; exact fun e => by simpa using congrArg List.length e
      obtain ⟨hU, hold⟩ := hok ch ch' st' h hne
      refine put_drop hU hbak ?_
      rcases hold with hn | ⟨o, ho, hx, hl⟩
      · exact Or.inl hn
      · refine Or.inr ⟨o, ho, hx, ?_, hl bake' (by rw [hbak, Treap.get_put, if_pos rfl])⟩
        rw [ho] at hre
        exact rebakeG_grows hre

theorem touchFoldG_drop (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) (U : List Bell) (cur : Bell)
    (new : M Bell (List Sock)) :
    ∀ (l : List Bell) (ch0 ch1 : List Bell) (st0 st1 : BSt M),
      l.foldl (touchStepG bo E cur new) (some (ch0, st0)) = some (ch1, st1) → FoldOKG bo E U cur new l (ch0, st0) →
      (ch1 = ch0 ∧ meas2 U st1 = meas2 U st0) ∨ Prod.Lex (· < ·) (· < ·) (meas2 U st1) (meas2 U st0)
  | [], _, _, _, _, h, _ => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  | c :: l, ch0, ch1, st0, st1, h, hok => by
    simp only [List.foldl_cons] at h
    cases h1 : touchStepG bo E cur new (some (ch0, st0)) c with
    | none => rw [h1, touchFoldG_none] at h; cases h
    | some p =>
      obtain ⟨chm, stm⟩ := p
      rw [h1] at h
      have a := touchStepG_drop h1 hok.1
      have b := touchFoldG_drop bo E U cur new l chm ch1 stm st1 h (hok.2 _ h1)
      rcases a with ⟨e1, e2⟩ | a
      · subst e1
        rcases b with ⟨e3, e4⟩ | b
        · exact Or.inl ⟨e3, e4.trans e2⟩
        · exact Or.inr (by rw [← e2]; exact b)
      · right
        rcases b with ⟨_, e4⟩ | b
        · rw [e4]; exact a
        · exact lexLt2_of_lt_le b (Or.inl a)

/-- The fold of touched callees of a step, as `bakeStepG` runs it. -/
def StepFoldG (bo : Bool → Sock → List Sock → Option Sock)
    (P : M Bell (List Sock) → List Bell → List Bell × BSt M → Prop) (E : BEnv M) (cur : Bell) (st : BSt M) : Prop :=
  ∀ sites new, sitesOf E st cur = some sites →
    sites.foldl (newStep E.vars) (some Treap.empty) = some new →
    P new ((Treap.tap (uniIn (Treap.gut st.out cur Treap.empty) (keySet new))).map Prod.fst)
      ([], { st with evals := st.evals + 1, out := Treap.put st.out cur (keySet new) })

theorem bakeStepG_drop {bo : Bool → Sock → List Sock → Option Sock} {E : BEnv M} {U : List Bell} {cur : Bell}
    {rest q' : List Bell} {qs qs' : M Bell Unit} {st st' : BSt M}
    (h : bakeStepG bo E cur rest qs st = some (q', qs', st'))
    (hok : StepFoldG bo (FoldOKG bo E U cur) E cur st) :
    LexLt (bakeMeasure U q' st') (bakeMeasure U (cur :: rest) st) := by
  simp only [bakeStepG, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨sites, hs, new, hn, ⟨changed, st3⟩, hfold, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, rfl⟩ := he
  have hd := touchFoldG_drop bo E U cur new _ [] changed _ st3 hfold (hok sites new hs hn)
  have hm : meas2 U ({ st with evals := st.evals + 1, out := Treap.put st.out cur (keySet new) } : BSt M) =
      meas2 U st := rfl
  rw [hm] at hd
  unfold LexLt bakeMeasure
  rcases hd with ⟨rfl, e⟩ | hd
  · have e1 : unbaked U st3 = unbaked U st := congrArg Prod.fst e
    have e2 : kapSum U st3 = kapSum U st := congrArg Prod.snd e
    rw [e1, e2]
    refine Prod.Lex.right _ (Prod.Lex.right _ ?_)
    simp
  · have : ∀ a b : Nat × Nat, ∀ x y : Nat, Prod.Lex (· < ·) (· < ·) a b →
        Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a.1, a.2, x) (b.1, b.2, y) := by
      intro a b x y hab
      obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
      rw [Prod.lex_def] at hab
      rcases hab with h1 | ⟨rfl, h2⟩
      · exact Prod.Lex.left _ _ h1
      · exact Prod.Lex.right _ (Prod.Lex.left _ _ h2)
    exact this (meas2 U st3) (meas2 U st) _ _ hd

/-- **A worklist whose every step returns and lowers `bakeMeasure U` ends**,
for any bake function. -/
theorem bakeLoopG_halts (bo : Bool → Sock → List Sock → Option Sock) (E : BEnv M) (U : List Bell)
    (R : List Bell → M Bell Unit → BSt M → Prop)
    (hstep : ∀ cur rest qs st, R (cur :: rest) qs st → ∃ q' qs' st',
      bakeStepG bo E cur rest qs st = some (q', qs', st') ∧ R q' qs' st' ∧
        LexLt (bakeMeasure U q' st') (bakeMeasure U (cur :: rest) st)) :
    ∀ q qs st, R q qs st → ∃ n st', bakeLoopG bo E n q qs st = some st' := by
  intro q qs st
  suffices ∀ m, ∀ q qs st, bakeMeasure U q st = m → R q qs st → ∃ n st', bakeLoopG bo E n q qs st = some st' from
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
      exact ⟨n + 1, st'', by simp only [bakeLoopG, h1, Option.bind_some, h2]⟩

/-! ## The normal floor: no tie -/

/-- A bell is fixed at its touches exactly when the bakes are frozen or it
is jetted (the root is never rebaked). -/
def fixedN (E : BEnv M) (c : Bell) : Bool := E.frozen || E.jetted c

/-- **The invariant of the fixed worklist**: only the root and jetted bells
are fixed, a fixed bell's bake is its code requirement, and every other bake
but the root's is `Canon` (the normal form). -/
structure NInv (E : BEnv M) (st : BSt M) : Prop where
  fix : ∀ c, Treap.has st.fix c = true → c = E.root ∨ E.jetted c = true
  bak : ∀ c s, Treap.get st.bak c = some s → c ≠ E.root →
    (fixedN E c = true → s = c.less) ∧ (fixedN E c = false → Canon s)

theorem nInv_init (E : BEnv M) : NInv E (bakeInit E) where
  fix c h := by
    left
    simp only [bakeInit, Treap.has, Treap.get_put] at h
    split at h
    · assumption
    · simp [Treap.get_empty] at h
  bak c s h hc := by
    simp only [bakeInit, Treap.get_put, if_neg hc, Treap.get_empty] at h
    cases h

theorem fixed_flag {E : BEnv M} {st : BSt M} (hI : NInv E st) {c : Bell} (hc : c ≠ E.root) :
    (E.frozen || Treap.has (if E.jetted c then Treap.put st.fix c () else st.fix) c) = fixedN E c := by
  unfold fixedN
  cases hj : E.jetted c
  · simp only [Bool.false_eq_true, if_false, Bool.or_false]
    cases hh : Treap.has st.fix c
    · simp
    · rcases hI.fix c hh with h | h
      · exact absurd h hc
      · rw [hj] at h; cases h
  · simp only [if_true, Bool.or_true]
    simp [Treap.has, Treap.get_put]

/-- **A touch keeps the invariant.** -/
theorem touchStepN_inv {E : BEnv M} {cur : Bell} {new : M Bell (List Sock)} {c : Bell}
    {ch ch' : List Bell} {st st' : BSt M} (hI : NInv E st)
    (h : touchStepN E cur new (some (ch, st)) c = some (ch', st')) : NInv E st' := by
  obtain ⟨hfix, hcase⟩ := touchStepG_cases h
  refine ⟨fun c' h' => ?_, fun c' s h' hc' => ?_⟩
  · rw [hfix] at h'
    split at h'
    · exact hI.fix c' h'
    · split at h'
      · rename_i _ hj
        simp only [Treap.has, Treap.get_put] at h'
        split at h'
        · rename_i e; subst e; exact Or.inr hj
        · exact hI.fix c' h'
      · exact hI.fix c' h'
  · rcases hcase with ⟨_, hbak, _⟩ | ⟨hc, bake, bake', g, g', hbo, hre, hcase⟩
    · rw [hbak] at h'; exact hI.bak c' s h' hc'
    · rcases hcase with ⟨_, hbak, _⟩ | ⟨_, hbak, _⟩
      · rw [hbak] at h'; exact hI.bak c' s h' hc'
      · rw [hbak, Treap.get_put] at h'
        split at h'
        · rename_i e; subst e
          cases h'
          rw [fixed_flag hI hc] at hbo
          constructor
          · intro hf
            rw [hf] at hbo
            simp only [bakeOfN, if_true, Option.some.injEq] at hbo
            subst hbo
            cases ho : Treap.get st.bak c' with
            | none => rw [ho] at hre; simp only [rebakeG, Option.some.injEq, Prod.mk.injEq] at hre; exact hre.1.symm
            | some o =>
              rw [ho] at hre
              have := (hI.bak c' o ho hc).1 hf
              subst this
              rw [rebakeG_self] at hre
              simp only [Option.some.injEq, Prod.mk.injEq] at hre
              exact hre.1.symm
          · intro hf
            rw [hf] at hbo
            exact rebakeG_canonN (bakeOfN_canon hbo) hre
        · exact hI.bak c' s h' hc'

/-- **No tie under the normal floor**: when a touch changes the bake of a
bell that had one, the new bake does not keep all the nouns of the old one. -/
theorem touchStepN_noTie {E : BEnv M} {cur : Bell} {new : M Bell (List Sock)} {c : Bell}
    {ch ch' : List Bell} {st st' : BSt M} (hI : NInv E st)
    (h : touchStepN E cur new (some (ch, st)) c = some (ch', st')) (hne : ch' ≠ ch)
    {o : Sock} (ho : Treap.get st.bak c = some o) : ∀ s, Treap.get st'.bak c = some s → ¬ Sub s o := by
  obtain ⟨_, hcase⟩ := touchStepG_cases h
  rcases hcase with ⟨_, _, hch⟩ | ⟨hc, bake, bake', g, g', hbo, hre, hcase⟩
  · exact absurd hch hne
  rcases hcase with ⟨_, _, hch⟩ | ⟨hchg, hbak, _⟩
  · exact absurd hch hne
  intro s hs hsub
  rw [hbak, Treap.get_put, if_pos rfl] at hs
  cases hs
  rw [ho] at hre hchg
  have hne' : bake' ≠ o := fun e => hchg (by rw [e])
  rw [fixed_flag hI hc] at hbo
  cases hf : fixedN E c
  · rw [hf] at hbo
    exact hne' (canon_ext (rebakeG_canonN (bakeOfN_canon hbo) hre) ((hI.bak c o ho hc).2 hf) hsub
      (rebakeG_grows hre))
  · rw [hf] at hbo
    simp only [bakeOfN, if_true, Option.some.injEq] at hbo
    subst hbo
    have := (hI.bak c o ho hc).1 hf
    subst this
    rw [rebakeG_self] at hre
    simp only [Option.some.injEq, Prod.mk.injEq] at hre
    exact hne' hre.1.symm

/-! ## The step of the fixed worklist -/

/-- What one touched callee must satisfy when its bake changes, with no tie
clause: it is a bell of `U`, and it had no bake or a bake with a noun
(`TouchW` of `BakeHaltTie.lean` for `touchStepN`). -/
def TouchWN (E : BEnv M) (U : List Bell) (cur : Bell) (new : M Bell (List Sock)) (st : BSt M) (c : Bell) : Prop :=
  ∀ ch ch' st', touchStepN E cur new (some (ch, st)) c = some (ch', st') → ch' ≠ ch →
    c ∈ U ∧ (Treap.get st.bak c = none ∨ ∃ o, Treap.get st.bak c = some o ∧ ∃ x, Fits o x)

/-- `TouchWN` at every callee of a fold of `touchStepN`. -/
def FoldWN (E : BEnv M) (U : List Bell) (cur : Bell) (new : M Bell (List Sock)) :
    List Bell → List Bell × BSt M → Prop
  | [], _ => True
  | c :: l, (ch, st) => TouchWN E U cur new st c ∧
      ∀ r, touchStepN E cur new (some (ch, st)) c = some r → FoldWN E U cur new l r

/-- **`TouchOK` with no tie hypothesis**: under `NInv`, the no-tie clause holds. -/
theorem touchOK_of_W {E : BEnv M} {U : List Bell} {cur : Bell} {new : M Bell (List Sock)} {st : BSt M} {c : Bell}
    (hI : NInv E st) (hw : TouchWN E U cur new st c) : TouchOKG bakeOfN E U cur new st c := by
  intro ch ch' st' h hne
  obtain ⟨hU, ho⟩ := hw ch ch' st' h hne
  refine ⟨hU, ho.imp id fun ⟨o, ho, hx⟩ => ⟨o, ho, hx, touchStepN_noTie hI h hne ho⟩⟩

theorem foldOK_of_W {E : BEnv M} {U : List Bell} {cur : Bell} {new : M Bell (List Sock)} :
    ∀ (l : List Bell) (ch : List Bell) (st : BSt M), NInv E st → FoldWN E U cur new l (ch, st) →
      FoldOKG bakeOfN E U cur new l (ch, st)
  | [], _, _, _, _ => trivial
  | c :: l, ch, st, hI, ⟨h1, h2⟩ =>
    ⟨touchOK_of_W hI h1, fun ⟨ch', st'⟩ h => foldOK_of_W l ch' st' (touchStepN_inv hI h) (h2 _ h)⟩

theorem touchFoldN_inv {E : BEnv M} {cur : Bell} {new : M Bell (List Sock)} :
    ∀ (l : List Bell) (ch ch' : List Bell) (st st' : BSt M), NInv E st →
      l.foldl (touchStepN E cur new) (some (ch, st)) = some (ch', st') → NInv E st'
  | [], _, _, _, _, hI, h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact hI
  | c :: l, ch, ch', st, st', hI, h => by
    simp only [List.foldl_cons] at h
    cases h1 : touchStepN E cur new (some (ch, st)) c with
    | none => rw [h1, touchFoldG_none] at h; cases h
    | some p =>
      obtain ⟨chm, stm⟩ := p
      rw [h1] at h
      exact touchFoldN_inv l chm ch' stm st' (touchStepN_inv hI h1) h

/-- **A step of the fixed worklist keeps `NInv`.** -/
theorem bakeStepN_inv {E : BEnv M} {cur : Bell} {rest q' : List Bell} {qs qs' : M Bell Unit} {st st' : BSt M}
    (hI : NInv E st) (h : bakeStepN E cur rest qs st = some (q', qs', st')) : NInv E st' := by
  simp only [bakeStepN, bakeStepG, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨sites, _, new, _, ⟨changed, st3⟩, hfold, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, -, rfl⟩ := he
  have hI' : NInv E ({ st with evals := st.evals + 1, out := Treap.put st.out cur (keySet new) } : BSt M) :=
    ⟨hI.fix, hI.bak⟩
  exact touchFoldN_inv _ [] changed _ st3 hI' hfold

/-- **A step of the fixed worklist lowers the measure** when its fold is
`FoldWN` (no tie clause), from a state of `NInv`. -/
theorem bakeStepN_drop {E : BEnv M} {U : List Bell} {cur : Bell} {rest q' : List Bell} {qs qs' : M Bell Unit}
    {st st' : BSt M} (hI : NInv E st) (h : bakeStepN E cur rest qs st = some (q', qs', st'))
    (hw : StepFoldG bakeOfN (FoldWN E U cur) E cur st) :
    LexLt (bakeMeasure U q' st') (bakeMeasure U (cur :: rest) st) :=
  bakeStepG_drop h fun sites new hs hn =>
    have hI' : NInv E ({ st with evals := st.evals + 1, out := Treap.put st.out cur (keySet new) } : BSt M) :=
      ⟨hI.fix, hI.bak⟩
    foldOK_of_W _ [] _ hI' (hw sites new hs hn)

/-- **What is left of `BakeEnds` with the normal floor**: `BakeDrops` without
hypothesis (a).  A finite list `U` and a set `Rs` of states that holds of the
first one, such that every step from a state of `Rs` (and of `NInv`, which
is proved) returns into `Rs` (b), and every callee whose bake changes is in
`U` and had no bake or a bake with a noun (c). -/
def BakeDropsN (E : BEnv M) : Prop :=
  ∃ (U : List Bell) (Rs : List Bell → M Bell Unit → BSt M → Prop),
    Rs [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) ∧
    ∀ cur rest qs st, Rs (cur :: rest) qs st → NInv E st → ∃ q' qs' st',
      bakeStepN E cur rest qs st = some (q', qs', st') ∧ Rs q' qs' st' ∧
      StepFoldG bakeOfN (FoldWN E U cur) E cur st

/-- **The fixed worklist ends, with no tie hypothesis.** -/
theorem bakeLoopN_halts_of_drops {E : BEnv M} (h : BakeDropsN E) :
    ∃ n st, bakeLoopN E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st := by
  obtain ⟨U, Rs, h0, hs⟩ := h
  refine bakeLoopG_halts bakeOfN E U (fun q qs st => Rs q qs st ∧ NInv E st) ?_ _ _ _ ⟨h0, nInv_init E⟩
  intro cur rest qs st ⟨hR, hI⟩
  obtain ⟨q', qs', st', h1, hR', hw⟩ := hs cur rest qs st hR hI
  exact ⟨q', qs', st', h1, ⟨hR', bakeStepN_inv hI h1⟩, bakeStepN_drop hI h1 hw⟩

end Bake

namespace PokeM

variable {M : Type → Type → Type} [Treap M] {J H R : Type}

/-- `BakeHalts` of the fixed worklist: on every poke from a state of `InvB`,
`bakeLoopN` returns at some fuel. -/
def BakeHaltsN (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    ∃ n st, bakeLoopN (anaEnv jet fold frozen s f L j hot dats memo' rd reg') n
      [(anaEnv jet fold frozen s f L j hot dats memo' rd reg').root]
      (Treap.put Treap.empty (anaEnv jet fold frozen s f L j hot dats memo' rd reg').root ())
      (bakeInit (anaEnv jet fold frozen s f L j hot dats memo' rd reg')) = some st

/-- `BakeDropsN` on every poke from a state of `InvB`. -/
def BakeDropsNP (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    BakeDropsN (anaEnv jet fold frozen s f L j hot dats memo' rd reg')

theorem bakeHaltsN_of_drops {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : BakeDropsNP lib env jet fold frozen fuel regOf) : BakeHaltsN lib env jet fold frozen fuel regOf :=
  fun s f L j hot pr dats memo' rd reg' hI hp => bakeLoopN_halts_of_drops (h s f L j hot pr dats memo' rd reg' hI hp)

/-- The fuel of the fixed worklist (as `bakeFuel`). -/
noncomputable def bakeFuelN (E : BEnv M) : Nat := by
  classical
  exact if h : ∃ n st, bakeLoopN E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st then
    Classical.choose h else 0

theorem bakeFuelN_spec {E : BEnv M}
    (h : ∃ n st, bakeLoopN E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st) :
    ∃ st, bakeLoopN E (bakeFuelN E) [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st := by
  unfold bakeFuelN
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- `BakeEnds` of the fixed worklist at the fuel `bf`. -/
def BakeEndsN (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (bf : BEnv M → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    ∃ st, bakeLoopN (anaEnv jet fold frozen s f L j hot dats memo' rd reg')
      (bf (anaEnv jet fold frozen s f L j hot dats memo' rd reg'))
      [(anaEnv jet fold frozen s f L j hot dats memo' rd reg').root]
      (Treap.put Treap.empty (anaEnv jet fold frozen s f L j hot dats memo' rd reg').root ())
      (bakeInit (anaEnv jet fold frozen s f L j hot dats memo' rd reg')) = some st

/-- **The leaf H2 for the fixed worklist, with no tie hypothesis.** -/
theorem bakeEndsN_of_drops {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : BakeDropsNP lib env jet fold frozen fuel regOf) : BakeEndsN lib env jet fold frozen fuel bakeFuelN regOf :=
  fun s f L j hot pr dats memo' rd reg' hI hp =>
    bakeFuelN_spec (bakeHaltsN_of_drops h s f L j hot pr dats memo' rd reg' hI hp)

end PokeM

end SkaModel
end Formalization
