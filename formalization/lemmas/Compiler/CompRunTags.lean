import lemmas.Compiler.CompRunAllL

/-!
# The tags of the fork and bond blocks

`+proxy r o` reads the region of the lazy block `o` with `(~(got by tags.gen)
o)`: a crash on a block with no tag, where the model's `proxy` is `none`.
So the run link holds without any condition on `tags` (`CompRunGoalL.lean`),
but the model succeeds at a proxy only when the block has a tag.  `LTag g
laz`: every label of `laz` (forks and bonds to any depth) has a tag in `g`.

Who writes `tags`: only `+set-tag` (and `+copy-tag` of `%6`), and both put,
so no step loses a tag (`TagsUp`, carried by `KM`).  Who makes labels: only
`+past` (in the plain class), which tags the block it emits right away
(`past_tags`); `+split`, `+into`, `+from`, `+lazy-prune` and `+copy-lazy`
take their labels from their inputs (`splitL_labs`, `intoL_labs`,
`from_regs`, `copyL_labs`).  `+kern` writes no tag and makes no label.

`tag_all`: every run of the plain class from a goal with `GInv` whose lazy
need is tagged (`GTag`) returns a tagged need.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Every label of `laz` has a tag in `g`. -/
def LTag (g : Gen (TreapMap mugF)) (laz : Lazy CSet) : Prop :=
  ∀ o ∈ llabs laz, (HoonMap.get g.tags o).isSome = true

/-- The tags of a goal. -/
def GTag (g : Gen (TreapMap mugF)) : CGoalL CSet → Prop
  | CGoalL.next laz _ => LTag g laz
  | _ => True

theorem ltag_up {g g' : Gen (TreapMap mugF)} {laz : Lazy CSet} (h : LTag g laz) (t : TagsUp g g') : LTag g' laz :=
  fun o ho => t o (h o ho)

theorem ltag_sub {g : Gen (TreapMap mugF)} {laz laz' : Lazy CSet} (h : LTag g laz)
    (s : ∀ o ∈ llabs laz', o ∈ llabs laz) : LTag g laz' := fun o ho => h o (s o ho)

theorem ltag_ofSure (g : Gen (TreapMap mugF)) (s : Sure CSet) : LTag g (Lazy.ofSure s) := by
  intro o ho; simp [llabs_ofSure] at ho

theorem km_tags {α : Type} {m : CM (TreapMap mugF) α} (hm : KM m) {g g' : Gen (TreapMap mugF)} {x : α}
    (h : m g = some (x, g')) : TagsUp g g' := hm.tags g x g' h

/-! ## The helpers -/

theorem splitL_labs {g g' : Gen (TreapMap mugF)} {laz h t : Lazy CSet} {th : Jmp} {o : Nat}
    (hi : GInv g (CGoalL.next laz th)) (e : splitL ⟨laz, th⟩ g = some ((h, t, o), g')) :
    (∀ x ∈ llabs h, x ∈ llabs laz) ∧ ∀ x ∈ llabs t, x ∈ llabs laz := by
  have hb := lnb_regs hi.1.1
  obtain ⟨⟨-, hn, hk, hl⟩, -, -⟩ := hi
  simp only [splitL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  rw [emit_apply] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨⟨h', t'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  have H := split_halves laz g.bo (g.emitted ⟨[], [], Termin.hop th⟩) g2 h' t' hn (fun x hx => hb x hx) e2
  exact ⟨fun x hx => H.labs x (Or.inl hx), fun x hx => H.labs x (Or.inr hx)⟩

theorem intoL_labs {g g' : Gen (TreapMap mugF)} {laz d r : Lazy CSet} {th : Jmp} {o axe : Nat}
    (hi : GInv g (CGoalL.next laz th)) (e : intoL ⟨laz, th⟩ axe g = some ((d, r, o), g')) :
    (∀ x ∈ llabs d, x ∈ llabs laz) ∧ ∀ x ∈ llabs r, x ∈ llabs laz := by
  have hb := lnb_regs hi.1.1
  obtain ⟨⟨-, hn, hk, hl⟩, -, -⟩ := hi
  simp only [intoL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  rw [emit_apply] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨⟨d', r'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  have H := into_halves axe laz g.bo (g.emitted ⟨[], [], Termin.hop th⟩) g2 d' r' hn (fun x hx => hb x hx) e2
  exact ⟨fun x hx => H.labs x (Or.inl hx), fun x hx => H.labs x (Or.inr hx)⟩

/-- **`+past` tags the block it parks a need behind.** -/
theorem past_tags {cod : Bell → Option Bool} {nex nex' : NextL CSet} {nom : Nomm} {region : List Nat}
    {g g' : Gen (TreapMap mugF)} (hd : g.drop = false) (ht : LTag g nex.laz)
    (h : pastL cod nex nom region g = some (nex', g')) : LTag g' nex'.laz := by
  obtain ⟨⟨s, fk, bd⟩, th⟩ := nex
  simp only [pastL] at h
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ht
  · rcases hh : hinted cod nom with _ | _ | _
    · simp [hh] at h
    · simp only [hh, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ht
    · simp only [hh] at h
      obtain ⟨o1, g1, e1, h⟩ := bind_some h
      obtain ⟨u, g2, e2, h⟩ := bind_some h
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [emit_apply] at e1
      simp only [Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      simp only [setTag, Option.some.injEq, Prod.mk.injEq] at e2
      obtain ⟨-, rfl⟩ := e2
      have hd' : (g.emitted ⟨[], [], Termin.hop th⟩).drop = false := hd
      simp only [hd', Bool.false_eq_true, if_false]
      intro o ho
      simp only [llabs, flabs, blabs, List.nil_append, List.mem_cons, List.mem_append, List.append_nil] at ho
      simp only [HoonMap.get_put]
      split
      · rfl
      · rename_i hne
        have ht' : ∀ o ∈ flabs fk ++ blabs bd, (HoonMap.get g.tags o).isSome = true := ht
        rcases ho with ho | ho | ho
        · exact absurd ho hne
        · exact ht' o (List.mem_append_left _ ho)
        · exact ht' o (List.mem_append_right _ ho)

/-- **`+copy` takes its labels from its two needs**, under the hypotheses of
the tail (`copyL_inv`). -/
theorem copyL_labs {first : NextL CSet} {second : Lazy CSet} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (hf : LInv g.re g.bo first.laz) (hs : LInv g.re g.bo second) (ap : (lregs first.laz ++ lregs second).Nodup)
    (h : copyL first second g = some (nex, g')) : ∀ o ∈ llabs nex.laz, o ∈ llabs first.laz ∨ o ∈ llabs second := by
  simp only [copyL] at h
  obtain ⟨o, g1, e1, h⟩ := bind_some h
  rw [emit_apply] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨laz, g2, e2, h⟩ := bind_some h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hb : ∀ x ∈ lregs first.laz ++ lregs second, x < g.re := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact lnb_regs hf.1 x hx
    · exact lnb_regs hs.1 x hx
  exact (copy_regs first.laz g.bo second _ g2 laz hf.2.2.1 hs.2.2.1 ap (by simpa only [emitted_re] using hb) e2).labs

/-! ## A run keeps every tag -/

/-- One step of `km` with the helpers on lazy needs. -/
macro "kmx_step" : tactic => `(tactic| first
  | exact KM.pure' _ | exact KM.re' | exact KM.oo' | exact KM.get'
  | exact KM.emit' _ | exact KM.addOps' _ _ | exact KM.setTag' _ _
  | exact KM.fail | exact KM.liftO' _ | exact KM.proxy' _ _
  | exact km_splitL _ | exact km_intoL _ _ | exact km_pastL _ _ _ _ | exact km_copyL _ _
  | exact km_simpleNextL _ | exact km_kerf _ | exact km_medeL _ _ _ | exact km_collapseLazyAtomL _
  | exact km_forl _ _ | exact km_doneBlocks | exact km_bombL _
  | apply KM.bind' | apply KM.ite' | split | intro _)

macro "kmx" : tactic => `(tactic| repeat kmx_step)

/-- **Every run of the plain class keeps the counters growing, the mode and
the tags.** -/
theorem km_runLC (env : CallEnv) : ∀ (n : Nomm), PlainOk n = true → ∀ (msup : Option Nomm) (goal : CGoalL CSet)
    (region : List Nat), KM (runLC env msup n goal region : CM (TreapMap mugF) (NextL CSet))
  | Nomm.cons p q, h, msup, goal, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    have ihp := km_runLC env p h.1
    have ihq := km_runLC env q h.2
    simp only [runLC]
    refine KM.bind' (by cases goal <;> kmx) fun goal' => ?_
    cases goal' with
    | pick z o =>
      exact KM.bind' (KM.emit' _) fun _ => KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ =>
        KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
    | done => exact KM.fail
    | next laz th =>
      refine KM.bind' (km_splitL _) fun x => ?_
      obtain ⟨hed, tel, o⟩ := x
      exact KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ =>
        KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
  | Nomm.n0 ax, _, msup, goal, region => by
    simp only [runLC]
    refine KM.ite' _ (km_bombL _) (KM.bind' (km_simpleNextL _) fun nex => KM.ite' _ (KM.pure' _) ?_)
    split <;> kmx
  | Nomm.n1 k, _, msup, goal, region => by
    simp only [runLC]
    cases goal <;> kmx
  | Nomm.n2 p q Option.none, h, msup, goal, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    have ihp := km_runLC env p h.1
    have ihq := km_runLC env q h.2
    simp only [runLC, callL]
    refine KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf _) fun x => ?_
    obtain ⟨out, pro⟩ := x
    exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ =>
      KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
  | Nomm.n3 p, h, msup, goal, region => by
    simp only [PlainOk] at h
    have ih := km_runLC env p h
    simp only [runLC]
    cases goal with
    | next laz th =>
      refine KM.ite' _ (ih _ _ _) (KM.bind' (km_collapseLazyAtomL _) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact KM.fail
      · exact KM.bind' (km_forl _ _) fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | pick z o => exact KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | done =>
      exact KM.bind' km_doneBlocks fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
  | Nomm.n4 p, h, msup, goal, region => by
    simp only [PlainOk] at h
    have ih := km_runLC env p h
    simp only [runLC]
    cases goal with
    | next laz th =>
      refine KM.bind' (km_collapseLazyAtomL _) fun a => KM.bind' (by cases a <;> kmx) fun _ => ?_
      exact KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | pick z o => exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | done => exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
  | Nomm.n5 p q, h, msup, goal, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    have ihp := km_runLC env p h.1
    have ihq := km_runLC env q h.2
    simp only [runLC]
    refine KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' ?_ fun _ =>
      KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
    cases goal with
    | pick z o => exact KM.emit' _
    | done => exact KM.bind' km_doneBlocks fun _ => KM.emit' _
    | next laz th =>
      refine KM.bind' (km_collapseLazyAtomL _) fun a => ?_
      rcases a with _ | ⟨r, o⟩
      · exact KM.ite' _ (KM.emit' _) KM.fail
      · exact KM.bind' (km_forl _ _) fun _ => KM.emit' _
  | Nomm.n7 p q, h, msup, goal, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    simp only [runLC]
    exact KM.bind' (km_runLC env q h.2 _ _ _) fun _ => km_runLC env p h.1 _ _ _
  | Nomm.n10 a v q, h, msup, goal, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    have ihv := km_runLC env v h.1.2
    have ihq := km_runLC env q h.2
    simp only [runLC]
    refine KM.bind' (km_simpleNextL _) fun nx => KM.bind' (km_intoL _ _) fun x => ?_
    obtain ⟨don, rec, o⟩ := x
    exact KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihv _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ =>
      KM.bind' (ihq _ _ _) fun _ => km_copyL _ _
  | Nomm.n2 _ _ (some _), h, _, _, _ => by simp [PlainOk] at h
  | Nomm.n6 _ _ _, h, _, _, _ => by simp [PlainOk] at h
  | Nomm.n11s _ _ _, h, _, _, _ => by simp [PlainOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _ => by simp [PlainOk] at h
  | Nomm.n12 _ _, h, _, _, _ => by simp [PlainOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _ => by simp [PlainOk] at h

/-! ## The tail -/

/-- What a run of `n` returns, tagged. -/
def TagFor (env : CallEnv) (msup : Option Nomm) (n : Nomm) (region : List Nat) : Prop :=
  ∀ (goal : CGoalL CSet) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet), GInv g goal → GTag g goal →
    runLC env msup n goal region g = some (nex, g') → LTag g' nex.laz

/-- **The tail returns a tagged need.** -/
theorem tail_tags {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (hpl : PlainOk p = true) (hql : PlainOk q = true)
    (tq : TagFor env msup q region) (tp : TagFor env msup p region)
    {Gq Gp : Lazy CSet} {thq : Jmp} {g g2 g3 g4 g' : Gen (TreapMap mugF)} {n2 n2' n1 nex : NextL CSet}
    (hq : GInv g (CGoalL.next Gq thq)) (hp : LInv g.re g.bo Gp) (ap : (lregs Gp ++ lregs Gq).Nodup)
    (tgq : LTag g Gq) (tgp : LTag g Gp)
    (e1 : runLC env msup q (CGoalL.next Gq thq) region g = some (n2, g2))
    (e2 : pastL env.cod n2 p region g2 = some (n2', g3))
    (e3 : runLC env msup p (CGoalL.next Gp n2'.th) region g3 = some (n1, g4))
    (e4 : copyL n1 n2'.laz g4 = some (nex, g')) : LTag g' nex.laz := by
  have rq := res_all env q hql msup region
  have rp := res_all env p hpl msup region
  have R2 := rq _ _ _ _ hq e1
  have T2 := tq _ _ _ _ hq tgq e1
  have P := tail_pgoal hq hp R2 e2
  have u1 := km_tags (km_runLC env q hql _ _ _) e1
  have u2 := km_tags (km_pastL _ _ _ _) e2
  have T2' := past_tags R2.2.2.1.2.1 T2 e2
  have R1 := rp _ _ _ _ P.1 e3
  have T1 := tp _ _ _ _ P.1 (ltag_up tgp (u1.trans u2)) e3
  have u3 := km_tags (km_runLC env p hpl _ _ _) e3
  have u4 := km_tags (km_copyL _ _) e4
  obtain ⟨-, nd⟩ := tail_copyH hq hp ap R2 e2 R1
  obtain ⟨l4, b4, ⟨i4, d4, -⟩, -⟩ := R1
  have L := copyL_labs i4 (linv_mono P.2.2.2.2.1 l4 b4) nd e4
  intro o ho
  rcases L o ho with e | e
  · exact u4 o (T1 o e)
  · exact u4 o (u3 o (T2' o e))

/-! ## Every run of the plain class -/

/-- `+simple-next` keeps the goal's tags. -/
theorem simpleNextL_tags {g g1 : Gen (TreapMap mugF)} {goal : CGoalL CSet} {nex : NextL CSet} (ht : GTag g goal)
    (e : simpleNextL goal g = some (nex, g1)) : LTag g1 nex.laz := by
  cases goal with
  | next laz th =>
    simp only [simpleNextL, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; exact ht
  | done =>
    simp only [simpleNextL] at e
    obtain ⟨r, g5, h5, e⟩ := bind_some e
    obtain ⟨o, g6, h6, e⟩ := bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _
  | pick z o =>
    simp only [simpleNextL] at e
    obtain ⟨r, g5, h5, e⟩ := bind_some e
    obtain ⟨o', g6, h6, e⟩ := bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _

/-- **Every run of the plain class from a goal with `GInv` and `GTag`
returns a tagged need.** -/
theorem tag_all (env : CallEnv) : ∀ (n : Nomm), PlainOk n = true → ∀ (msup : Option Nomm) (region : List Nat),
    TagFor env msup n region
  | Nomm.cons p q, h, msup, region => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true] at h'
    have tp := tag_all env p h'.1 msup region
    have tq := tag_all env q h'.2 msup region
    intro goal g g' nex hi ht e
    have hd := ginv_drop hi
    simp only [runLC] at e
    obtain ⟨goal', g1, e1, e⟩ := bind_some e
    have G : GInv g1 goal' ∧ GTag g1 goal' := by
      cases goal with
      | done =>
        simp only at e1
        obtain ⟨r, g5, h5, e1⟩ := bind_some e1
        obtain ⟨rfl, rfl⟩ := re_step h5
        obtain ⟨o, g6, h6, e1⟩ := bind_some e1
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨l6, b6, d6⟩ := km_drop (KM.emit' _) h6 hd
        simp only at l6
        exact ⟨ginv_reg _ (by omega) d6, ltag_ofSure _ _⟩
      | pick z o =>
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1; exact ⟨hi, ht⟩
      | next laz th =>
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1; exact ⟨hi, ht⟩
    obtain ⟨gi, gt⟩ := G
    cases goal' with
    | pick z o =>
      obtain ⟨o', g2, e2, e⟩ := bind_some e
      obtain ⟨l2, b2, d2⟩ := km_drop (KM.emit' _) e2 gi.1
      obtain ⟨n2, g3, e3, e⟩ := bind_some e
      obtain ⟨n2', g4, e4, e⟩ := bind_some e
      obtain ⟨n1, g5, e5, e6⟩ := bind_some e
      exact tail_tags h'.1 h'.2 tq tp (ginv_bunt_j d2 (jmpIn_jmp0 _ _)) (linv_bunt _ _) (by simp [lregs_bunt])
        (ltag_ofSure _ _) (ltag_ofSure _ _) e3 e4 e5 e6
    | done => cases e
    | next laz th =>
      obtain ⟨⟨hed, tel, o⟩, g2, e2, e⟩ := bind_some e
      obtain ⟨nexh, g3, e3, e⟩ := bind_some e
      obtain ⟨n2, g4, e4, e⟩ := bind_some e
      obtain ⟨n2', g5, e5, e⟩ := bind_some e
      obtain ⟨n1, g6, e6, e7⟩ := bind_some e
      obtain ⟨l2, b2, d2, ih, it, nd, -⟩ := splitL_inv gi e2
      obtain ⟨sh, st⟩ := splitL_labs gi e2
      have u2 := km_tags (km_splitL _) e2
      obtain ⟨r3, b3, d3, i3, j3, rg3⟩ := pastL_inv ih (jmpIn_jmp0 _ _) e3
      have u3 := km_tags (km_pastL _ _ _ _) e3
      have hq : GInv g3 (CGoalL.next tel nexh.th) := ⟨linv_mono it (by omega) b3, d3.trans d2, j3⟩
      exact tail_tags h'.1 h'.2 tq tp hq i3 (by rw [rg3]; exact nd)
        (ltag_up (ltag_sub (ltag_up gt u2) st) u3)
        (past_tags (show g2.drop = false from d2) (ltag_sub (ltag_up gt u2) sh) e3) e4 e5 e6 e7
  | Nomm.n0 ax, _, msup, region => by
    intro goal g g' nex hi ht e
    simp only [runLC] at e
    split at e
    · simp only [bombL] at e
      obtain ⟨o, g1, e1, e⟩ := bind_some e
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _
    · obtain ⟨nex0, g1, e1, e⟩ := bind_some e
      have T := simpleNextL_tags ht e1
      split at e
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e; exact T
      · cases hf : Lazy.fromL ax nex0.laz with
        | none => simp [hf] at e
        | some laz' =>
          simp only [hf, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          obtain ⟨-, -, hl⟩ := from_regs ax _ _ hf
          exact fun o ho => T o (by rw [← hl]; exact ho)
  | Nomm.n1 k, _, msup, region => by
    intro goal g g' nex hi ht e
    cases goal with
    | done =>
      simp only [runLC] at e
      obtain ⟨r, g1, e1, e⟩ := bind_some e
      obtain ⟨o, g2, e2, e⟩ := bind_some e
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _
    | pick z o =>
      simp only [runLC] at e
      split at e
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _
      · split at e
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _
        · simp only [bombL] at e
          obtain ⟨o', g1, e1, e⟩ := bind_some e
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _
    | next laz th =>
      simp only [runLC] at e
      obtain ⟨o, g1, e1, e⟩ := bind_some e
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e; exact ltag_ofSure _ _
  | Nomm.n2 p q Option.none, h, msup, region => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true] at h'
    have tp := tag_all env p h'.1 msup region
    have tq := tag_all env q h'.2 msup region
    intro goal g g' nex hi ht e
    have hd := ginv_drop hi
    obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
      runLC_n2_none e
    obtain ⟨l1, b1, d1⟩ := km_drop (km_simpleNextL _) h1 hd
    obtain ⟨l2, b2, d2⟩ := km_drop (km_kerf _) h2 d1
    obtain ⟨l3, b3, d3⟩ := km_drop (KM.emit' _) h3 d2
    simp only at l3 b3
    exact tail_tags h'.1 h'.2 tq tp (ginv_reg_j (show g2.re + 1 < g3.re by omega) d3 (jmpIn_jmp0 _ _))
      (linv_reg (show g2.re < g3.re by omega)) (by simp [lregs_reg]) (ltag_ofSure _ _) (ltag_ofSure _ _) h4 h5 h6 h7
  | Nomm.n3 p, h, msup, region => by
    simp only [PlainOk] at h
    have ih := tag_all env p h msup region
    intro goal g g' nex hi ht e
    have hd := ginv_drop hi
    cases goal with
    | next laz th =>
      simp only [runLC] at e
      split at e
      · exact ih _ _ _ _ hi ht e
      · obtain ⟨a, g1, e1, e⟩ := bind_some e
        obtain ⟨l1, b1, d1⟩ := km_drop (km_collapseLazyAtomL _) e1 hd
        rcases a with _ | ⟨r, o⟩
        · cases e
        · obtain ⟨⟨z, o'⟩, g2, e2, e⟩ := bind_some e
          obtain ⟨l2, b2, d2⟩ := km_drop (km_forl _ _) e2 d1
          obtain ⟨r', g3, e3, e⟩ := bind_some e
          obtain ⟨rfl, rfl⟩ := re_step e3
          obtain ⟨oc, g4, e4, e⟩ := bind_some e
          obtain ⟨-, -, d4⟩ := km_drop (KM.emit' _) e4 d2
          exact ih _ _ _ _ (ginv_reg oc (by have := (KM.emit' _).keep _ _ _ e4; simp at this; omega) d4)
            (ltag_ofSure _ _) e
    | pick z o =>
      simp only [runLC] at e
      obtain ⟨r, g1, e1, e⟩ := bind_some e
      obtain ⟨rfl, rfl⟩ := re_step e1
      obtain ⟨oc, g2, e2, e⟩ := bind_some e
      obtain ⟨l2, -, d2⟩ := km_drop (KM.emit' _) e2 hd
      exact ih _ _ _ _ (ginv_reg oc (by simp at l2; omega) d2) (ltag_ofSure _ _) e
    | done =>
      simp only [runLC] at e
      obtain ⟨⟨o0, o1⟩, g1, e1, e⟩ := bind_some e
      obtain ⟨l1, b1, d1⟩ := km_drop km_doneBlocks e1 hd
      obtain ⟨r, g2, e2, e⟩ := bind_some e
      obtain ⟨rfl, rfl⟩ := re_step e2
      obtain ⟨oc, g3, e3, e⟩ := bind_some e
      obtain ⟨l3, -, d3⟩ := km_drop (KM.emit' _) e3 d1
      exact ih _ _ _ _ (ginv_reg oc (by simp at l3; omega) d3) (ltag_ofSure _ _) e
  | Nomm.n4 p, h, msup, region => by
    simp only [PlainOk] at h
    have ih := tag_all env p h msup region
    intro goal g g' nex hi ht e
    have hd := ginv_drop hi
    cases goal with
    | done =>
      simp only [runLC] at e
      obtain ⟨pro, g1, e1, e⟩ := bind_some e
      obtain ⟨rfl, rfl⟩ := re_step e1
      obtain ⟨arg, g2, e2, e⟩ := bind_some e
      obtain ⟨rfl, rfl⟩ := re_step e2
      obtain ⟨o, g3, e3, e⟩ := bind_some e
      obtain ⟨l3, -, d3⟩ := km_drop (KM.emit' _) e3 hd
      exact ih _ _ _ _ (ginv_reg o (by simp at l3 ⊢; omega) d3) (ltag_ofSure _ _) e
    | pick z o =>
      simp only [runLC] at e
      obtain ⟨pro, g1, e1, e⟩ := bind_some e
      obtain ⟨rfl, rfl⟩ := re_step e1
      obtain ⟨arg, g2, e2, e⟩ := bind_some e
      obtain ⟨rfl, rfl⟩ := re_step e2
      obtain ⟨o', g3, e3, e⟩ := bind_some e
      obtain ⟨l3, -, d3⟩ := km_drop (KM.emit' _) e3 hd
      exact ih _ _ _ _ (ginv_reg o' (by simp at l3 ⊢; omega) d3) (ltag_ofSure _ _) e
    | next laz th =>
      simp only [runLC] at e
      obtain ⟨a, g1, e1, e⟩ := bind_some e
      obtain ⟨l1, b1, d1⟩ := km_drop (km_collapseLazyAtomL _) e1 hd
      obtain ⟨⟨pro, th'⟩, g2, e2, e⟩ := bind_some e
      have k2 : g2.drop = false := by
        rcases a with _ | x
        · simp only at e2
          obtain ⟨r, g5, h5, e2⟩ := bind_some e2
          obtain ⟨rfl, rfl⟩ := re_step h5
          split at e2
          · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e2
            obtain ⟨-, rfl⟩ := e2; exact d1
          · cases e2
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e2
          obtain ⟨-, rfl⟩ := e2; exact d1
      obtain ⟨arg, g3, e3, e⟩ := bind_some e
      obtain ⟨rfl, rfl⟩ := re_step e3
      obtain ⟨o, g4, e4, e⟩ := bind_some e
      obtain ⟨l4, -, d4⟩ := km_drop (KM.emit' _) e4 k2
      exact ih _ _ _ _ (ginv_reg o (by simp at l4; omega) d4) (ltag_ofSure _ _) e
  | Nomm.n5 p q, h, msup, region => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true] at h'
    have tp := tag_all env p h'.1 msup region
    have tq := tag_all env q h'.2 msup region
    intro goal g g' nex hi ht e
    have hd := ginv_drop hi
    rw [cr5_modelL] at e
    obtain ⟨o, g1, e1, e⟩ := bind_some e
    obtain ⟨l1, b1, d1⟩ := km_drop (km_cr5BrML _ _ _) e1 hd
    simp only at l1
    obtain ⟨n2, g2, e2, e⟩ := bind_some e
    obtain ⟨n2', g3, e3, e⟩ := bind_some e
    obtain ⟨n1, g4, e4, e5⟩ := bind_some e
    exact tail_tags h'.1 h'.2 tq tp (ginv_reg o (show g.re + 1 < g1.re by omega) d1)
      (linv_reg (show g.re < g1.re by omega)) (by simp [lregs_reg]) (ltag_ofSure _ _) (ltag_ofSure _ _) e2 e3 e4 e5
  | Nomm.n7 p q, h, msup, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    have tp := tag_all env p h.1 msup region
    have tq := tag_all env q h.2 (some p) region
    intro goal g g' nex hi ht e
    simp only [runLC] at e
    obtain ⟨nex1, g1, e1, e⟩ := bind_some e
    have R1 := res_all env q h.2 (some p) region _ _ _ _ hi e1
    exact tp _ _ _ _ R1.2.2.1 (tq _ _ _ _ hi ht e1) e
  | Nomm.n10 a v q, h, msup, region => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
    have tv := tag_all env v h'.1.2 msup region
    have tq := tag_all env q h'.2 msup region
    intro goal g g' nex hi ht e
    simp only [runLC] at e
    obtain ⟨nx, g1, e1, e⟩ := bind_some e
    have S := simpleNextL_res hi e1
    have T := simpleNextL_tags ht e1
    obtain ⟨⟨don, rec, o⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨nexR, g3, e3, e⟩ := bind_some e
    obtain ⟨n2, g4, e4, e⟩ := bind_some e
    obtain ⟨n2', g5, e5, e⟩ := bind_some e
    obtain ⟨n1, g6, e6, e7⟩ := bind_some e
    obtain ⟨sl, sb, si, ss⟩ := S
    obtain ⟨l2, b2, d2, id, ir, nd, -⟩ := intoL_inv h'.1.1 si e2
    obtain ⟨sd, sr⟩ := intoL_labs si e2
    have u2 := km_tags (km_intoL _ _) e2
    obtain ⟨r3, b3, d3, i3, j3, rg3⟩ := pastL_inv ir (jmpIn_jmp0 _ _) e3
    have u3 := km_tags (km_pastL _ _ _ _) e3
    have hq : GInv g3 (CGoalL.next don nexR.th) := ⟨linv_mono id (by omega) b3, d3.trans d2, j3⟩
    have nd' : (lregs nexR.laz ++ lregs don).Nodup := by
      rw [rg3, List.nodup_append]
      obtain ⟨a1, a2, a3⟩ := List.nodup_append.1 nd
      exact ⟨a2, a1, fun x hx y hy e => a3 y hy x hx e.symm⟩
    exact tail_tags h'.2 h'.1.2 tv tq hq i3 nd' (ltag_up (ltag_sub (ltag_up T u2) sd) u3)
      (past_tags (show g2.drop = false from d2) (ltag_sub (ltag_up T u2) sr) e3) e4 e5 e6 e7
  | Nomm.n2 _ _ (some _), h, _, _ => by simp [PlainOk] at h
  | Nomm.n6 _ _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.n11s _ _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.n11d _ _ _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.n12 _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [PlainOk] at h

/-- **From `%done`**, every run of the plain class returns a tagged need. -/
theorem tag_done (env : CallEnv) {n : Nomm} (hn : PlainOk n = true) (msup : Option Nomm) (region : List Nat)
    {g g' : Gen (TreapMap mugF)} {nex : NextL CSet} (hd : g.drop = false)
    (e : runLC env msup n CGoalL.done region g = some (nex, g')) : LTag g' nex.laz :=
  tag_all env n hn msup region CGoalL.done g g' nex hd trivial e

/-- **What the tags are for**: `+proxy` at a tagged block succeeds. -/
theorem proxy_tagged {g : Gen (TreapMap mugF)} {r o : Nat} (ht : (HoonMap.get g.tags o).isSome = true) :
    ∃ p g', proxy r o g = some (p, g') := by
  unfold proxy
  simp only
  split
  · exact ⟨_, _, rfl⟩
  · obtain ⟨tag, htag⟩ := Option.isSome_iff_exists.1 ht
    simp only [htag, Option.map_some]
    exact ⟨_, _, rfl⟩

end Compiler
end Formalization
