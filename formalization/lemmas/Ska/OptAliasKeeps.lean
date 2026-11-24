import lemmas.Ska.OptAliasSim

/-!
# Toward `KeepsB` for `+alias`: the walk at a place, the rebase, presence

Three pieces of the simulation of `+alias` (README Gaps 12.8).

* **`alias_at_of`**: at a configuration of an execution from the entry that
  passed the parameters of its block `o` and runs its body from place `k`,
  given the walk up to `o` (`pre`, the state `g1`, the start state `st0` of
  `aStart`, and the state `sta` the walk reaches after the first `k` ops),
  `AOK` and `ABInv` hold at `sta` with `Done` the `bodyDone` of the first `k`
  ops from `DoneS` (before the first dead fill), `BodyOK` holds for the ops
  from `k` up to the first dead fill, and every register read at place `k` is
  done.  With it, `akb_op` applies at each op (`ab_fresh`, `ab_src`).
* **`akept_jump`**: the agreement `AKept` at the end of the body of a jumping
  block `q`, with the walk-time state there, gives `AKept` with the `old` of
  the walk at any later point and `DoneE` there, which is what `aedge_kept`
  takes (`awa_frame_seg`, `awa_done_seg`: the frame of the walk over a part of
  `topo`).
* **`APres`**, presence: every done register present in the file before has
  its `old` present in the file after.  `+move` (`evalPass`) crashes on a
  missing register and copies a poisoned one, which `AKept` on read values
  does not see.  `apres_op` keeps it through one op (kept or dropped),
  `apass_after` gives the pass of the arguments after from presence and the
  check of the parameters, and `apres_pass` keeps it through the passes.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-! ## (a) The walk at a place of a body -/

theorem take_of_drop_eq {α : Type} {l : List α} {k k' : Nat} (hk : k ≤ l.length) (h : l.drop k' = l.drop k) :
    l.take k' = l.take k := by
  have h1 := congrArg List.length h
  simp only [List.length_drop] at h1
  by_cases hk' : k' ≤ l.length
  · have e : k' = k := by omega
    rw [e]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **The walk at a place of a body, over executions** (`alias_walk_at`
with the walk state exposed): given the walk up to block `o` and the state
`sta` after the first `k` ops of its body from the start state of `aStart`,
at every configuration of an execution from the entry that passed the
parameters of `o` and runs its body from `k`: the path, `AWInv` at `pre`,
every register read at `k` is done, and before the first dead fill `AOK` and
`ABInv` at `sta` and `BodyOK` of the next ops up to any place `m` below the
first dead fill. -/
theorem alias_at_of {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {pre l : List Nat} {o : Nat} {g1 g2 : AGen Map} (hto : topo = pre ++ o :: l)
    (h1 : aliasWalk pick nargs c.blocks pre (aliasInit rev) = some g1)
    (h2 : aliasBlock pick nargs c.blocks g1 o = some g2)
    {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {y : Path.Cfg σ Map} {b : Blob}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y)
    (hp : y.params = []) (hq : y.b.par = []) (hyo : y.lab = o) (hb : HoonMap.get c.blocks o = some b)
    {st0 : ABody} (hA : aStart nargs g1 o b = some st0) {k : Nat} (hkl : k ≤ b.body.length)
    (hk : y.b.body = b.body.drop k) {outa : List Pole} {sta : ABody}
    (hta : aliasBody pick (b.body.take k) st0 = some (outa, sta)) :
    BPath c.blocks (o :: epath es) ∧ AWInv lib O c gul topo pre g1 ∧ o ∉ pre ∧
    (∀ x, ReadAt b k x → bodyDone (ClR c.blocks) (b.body.take k) (DoneS c.blocks pre (epath es) b) x) ∧
    ((∀ i r, i < k → ¬ DeadFill c.blocks r o i) →
      AOK sta (fun x => read x y.regs) (bodyDone (ClR c.blocks) (b.body.take k) (DoneS c.blocks pre (epath es) b)) ∧
      ABInv sta (bodyDef (b.body.take k) (fun x => DefW c.blocks pre x ∨ x ∈ b.par))
        (bodyDone (ClR c.blocks) (b.body.take k) (DoneS c.blocks pre (epath es) b)) (ClR c.blocks)) ∧
    (∀ m, k ≤ m → (∀ i r, i < m → ¬ DeadFill c.blocks r o i) →
      BodyOK (ClR c.blocks) ((b.body.take m).drop k) (bodyDef (b.body.take k) (fun x => DefW c.blocks pre x ∨ x ∈ b.par))
        (bodyDone (ClR c.blocks) (b.body.take k) (DoneS c.blocks pre (epath es) b))) := by
  have hS : AliasSSAB c.blocks := hD.2.1
  have hAc : Acyclic c.blocks := hD.1.1.2.1
  have hTo := hT.1.1
  subst hto
  have hI : AWInv lib O c gul (pre ++ o :: l) pre g1 := by
    have := awa_walk_part (lib := lib) (O := O) (gul := gul) hpick hD pre [] (o :: l) _ g1 (by simpa using hTo)
      (by simpa using awa_init (lib := lib) (O := O) (gul := gul) hT) h1
    simpa using this
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp hTo.1).2.2 _ h' _ List.mem_cons_self rfl
  obtain ⟨loc0, imms, rb, rf, k', Rp, hπ, -, -, -, hok, hab, hdrop, hrun, hA2⟩ :=
    awa_start hD hTo hI h2 hfe hp hq hyo hb
  rw [hA] at hA2
  cases hA2
  have htk : b.body.take k' = b.body.take k := take_of_drop_eq hkl (hdrop.symm.trans hk)
  rw [htk] at hrun
  refine ⟨hπ, hI, hopre, fun x hx => awa_read_done hS hπ hb hopre hx, fun hnd => ?_, fun m hm hnd => ?_⟩
  · have hBO := awi_bodyOK hS hAc hπ hb hnd hopre (awi_doneS_body hopre)
    exact as_body hpick _ _ Rp _ _ outa sta _ hta hok hab hBO hrun
  · have hBO := awi_bodyOK hS hAc hπ hb hnd hopre (awi_doneS_body hopre)
    have e := List.take_append_drop k (b.body.take m)
    rw [List.take_take, Nat.min_eq_left hm] at e
    rw [← e] at hBO
    exact ((bodyOK_append _ _ _ _).mp hBO).2

/-- **The decomposition at the start of a body**: a block `o` reached by an
execution from the entry is in `topo`, and the walk up to it reaches a state
`g1`, walks `o` to `g2` with the start state `st0` of `aStart`, and walks the
rest to the final state. -/
theorem alias_start_parts {pick : List Nat → Nat} {nargs : Nat} {topo : List Nat} {rev : Map (List Nat)}
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g) {o : Nat} (ho : o ∈ topo) :
    ∃ pre l g1 g2, topo = pre ++ o :: l ∧ aliasWalk pick nargs c.blocks pre (aliasInit rev) = some g1 ∧
      aliasBlock pick nargs c.blocks g1 o = some g2 ∧ aliasWalk pick nargs c.blocks l g2 = some g := by
  obtain ⟨pre, l, rfl⟩ := List.append_of_mem ho
  rw [awa_walk_append] at h
  obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [aliasWalk] at h
  obtain ⟨g2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨pre, l, g1, g2, rfl, h1, h2, h3⟩

/-- `aStart` of a block the walk does not drop. -/
theorem aStart_some {pick : List Nat → Nat} {nargs : Nat} {g g' : AGen Map} {o : Nat} {b : Blob}
    (h : aliasBlock pick nargs c.blocks g o = some g') (hne : ¬ (g.rev o = [] ∧ o ≠ 0))
    (hb : HoonMap.get c.blocks o = some b) :
    ∃ st0 rb rf, aStart nargs g o b = some st0 ∧ st0.old = g.old ∧ aliasBody pick b.body st0 = some rb ∧
      aliasFin rb.2.old rb.2.loc g.rev g.folded o b.fin = some rf ∧
      g' = AGen.mk (HoonMap.put g.new o { par := b.par, body := rb.1, fin := rf.1 }) rb.2.old
        (updA g.info o (some rb.2.loc)) (updA g.imms o (some rb.2.imml)) rf.2.1 rf.2.2 := by
  obtain ⟨info, imms, b1, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ := awa_block_parts h hne
  rw [hb] at e3
  cases e3
  exact ⟨_, rb, rf, aStart_of_parts e1 e2 e4 e5, rfl, e6, e7, e8⟩

end

/-! ## (b) The frame of the walk over a part of `topo`, and the rebase of `AKept` -/

/-- **A part of `topo` walked changes `old` only at destinations of ops of its
reachable blocks** (`awi_frame_walk` for a part followed by more of `topo`). -/
theorem awa_frame_seg {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} :
    ∀ (mid pre r : List Nat) (g g' : AGen Map), TopoOK bl (pre ++ mid ++ r) → ARev bl (pre ++ mid ++ r) pre g →
      aliasWalk pick nargs bl mid g = some g' →
      ∀ x, (∀ o ∈ mid, Reach bl o → ∀ b, HoonMap.get bl o = some b → x ∉ b.body.filterMap aliasDst) →
        g'.old x = g.old x
  | [], pre, r, g, g', _, _, h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    exact fun _ _ => rfl
  | o :: mid, pre, r, g, g', ht, hi, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have ht0 : TopoOK bl (pre ++ o :: (mid ++ r)) := by simpa using ht
    have hi0 : ARev bl (pre ++ o :: (mid ++ r)) pre g := by simpa using hi
    have hi1 := (arev_step ht0 hi0 h1).1
    have ht' : TopoOK bl ((pre ++ [o]) ++ mid ++ r) := by simpa using ht
    have hi1' : ARev bl ((pre ++ [o]) ++ mid ++ r) (pre ++ [o]) g1 := by simpa using hi1
    intro x hx
    rw [awa_frame_seg mid (pre ++ [o]) r g1 g' ht' hi1' h x (fun o' ho' => hx o' (List.mem_cons_of_mem _ ho')),
      awi_frame_step ht0 hi0 h1 (hx o List.mem_cons_self)]

/-- **`Done` at the end of a walked jumping block is safe from a part of the
walk after it** (`awi_done_stable` for a part followed by more of `topo`). -/
theorem awa_done_seg {bl : Map Blob} (hS : AliasSSAB bl) {pre mid r : List Nat} (ht : TopoOK bl (pre ++ (mid ++ r)))
    {q : Nat} {p : List Nat} {b : Blob} {j : Jmp} (hπ : BPath bl (q :: p)) (hb : HoonMap.get bl q = some b)
    (hj : j ∈ getJmps b.fin) (hq : q ∈ pre) {x : Nat} (hx : DoneE bl (pre ++ mid) p b x) :
    ∀ o ∈ mid, Reach bl o → ∀ b', HoonMap.get bl o = some b' → x ∉ b'.body.filterMap aliasDst := by
  intro o ho hR b' hb' hm
  have hdisj : ∀ a ∈ pre, a ≠ o := fun a ha e =>
    (List.nodup_append.mp ht.1).2.2 a ha o (List.mem_append_left _ ho) e
  have hRq : Reach bl q := ssk_bpath_reach hπ q List.mem_cons_self
  obtain ⟨k, op, hk, he⟩ := bdef_idx hm
  have hlive : LiveDef bl x (o, some k) := ⟨hR, ⟨b', op, hb', hk, he⟩, fun i hi hdf => by
    cases hi; exact hx.2.2 o k hdf (List.mem_append_right _ ho)⟩
  rcases hx.1 with (hd | hd | ⟨o', ho', b2, hb2, hd⟩) | hd
  · exact hd (bdef_allDefs hb' (List.mem_append_right _ hm))
  · have e := hS.1 x _ _ hlive (awi_par_live hRq hb hd); simp at e
  · have hR' := ssk_bpath_reach hπ o' (List.mem_cons_of_mem _ ho')
    have ho'pre := awi_path_pre ht hπ hq o' ho'
    obtain ⟨b3, j3, hb3, hj3⟩ := bdef_jumps hπ rfl o' ho'
    rw [hb2] at hb3; cases hb3
    rcases List.mem_append.mp hd with hd | hd
    · have e := hS.1 x _ _ hlive (awi_par_live hR' hb2 hd); simp at e
    · obtain ⟨i, op', hi, he'⟩ := bdef_idx hd
      have e := hS.1 x _ _ hlive (awi_jump_live hR' hb2 hj3 hi he')
      simp only [Prod.mk.injEq] at e
      exact hdisj o' ho'pre e.1.symm
  · obtain ⟨i, op', hi, he'⟩ := bdef_idx hd
    have e := hS.1 x _ _ hlive (awi_jump_live hRq hb hj hi he')
    simp only [Prod.mk.injEq] at e
    exact hdisj q hq e.1.symm

/-- `DoneE` after a block is walked is in the `bodyDone` of its body. -/
theorem awa_doneE_body {bl : Map Blob} {pre p : List Nat} {o : Nat} {bo : Blob} (x : Nat)
    (hx : DoneE bl (pre ++ [o]) p bo x) : bodyDone (ClR bl) bo.body (DoneS bl pre p bo) x := by
  obtain ⟨h1, h2, h3⟩ := hx
  rcases h1 with h1 | h1
  · exact awa_bodyDone_base _ _ _ ⟨h1, h2, fun o' i hd ho' => h3 o' i hd (List.mem_append_left _ ho')⟩
  · exact awa_bodyDone_dst _ _ _ h1 h2

/-- `AKept` for another `old` that agrees on fewer done registers. -/
theorem akept_rebase {old old' : Nat → Nat} {loc : AInfo} {imml : AImms} {R R' : Nat → Option Noun}
    {D D' : Nat → Prop} (hk : AKept ⟨old, loc, imml⟩ R R' D) (hD : ∀ d, D' d → D d ∧ old' d = old d) :
    AKept ⟨old', loc, imml⟩ R R' D' :=
  ⟨hk.imm, hk.names, fun d hd => by
    obtain ⟨h1, h2⟩ := hD d hd
    show R' (old' d) = R (old' d)
    rw [h2]; exact hk.old d h1⟩

/-- **`AKept` at the end of a walked jumping block, rebased**: from `AKept`
with the walk-time state `st'` at the end of the body of `q` (its `old` that
of the walk state `g2` right after `q`), `AKept` with the `old` of the walk
`g'` after a further part `mid` of `topo`, on `DoneE` at that point. -/
theorem akept_jump {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} (hS : AliasSSAB bl)
    {pre mid r : List Nat} {q : Nat} {g2 g' : AGen Map} (ht : TopoOK bl (pre ++ q :: (mid ++ r)))
    (hi : ARev bl (pre ++ q :: (mid ++ r)) (pre ++ [q]) g2) (hw : aliasWalk pick nargs bl mid g2 = some g')
    {p : List Nat} {bq : Blob} {j : Jmp} (hπ : BPath bl (q :: p)) (hb : HoonMap.get bl q = some bq)
    (hj : j ∈ getJmps bq.fin) {st' : ABody} (hold : st'.old = g2.old) {R R' : Nat → Option Noun}
    (hk : AKept st' R R' (bodyDone (ClR bl) bq.body (DoneS bl pre p bq))) :
    AKept ⟨g'.old, st'.loc, st'.imml⟩ R R' (DoneE bl (pre ++ q :: mid) p bq) ∧
      ∀ d, DoneE bl (pre ++ q :: mid) p bq d →
        bodyDone (ClR bl) bq.body (DoneS bl pre p bq) d ∧ g'.old d = st'.old d := by
  have ht1 : TopoOK bl ((pre ++ [q]) ++ mid ++ r) := by simpa using ht
  have hi1 : ARev bl ((pre ++ [q]) ++ mid ++ r) (pre ++ [q]) g2 := by simpa using hi
  have ht2 : TopoOK bl ((pre ++ [q]) ++ (mid ++ r)) := by simpa using ht
  have hq : q ∈ pre ++ [q] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hD : ∀ d, DoneE bl (pre ++ q :: mid) p bq d →
      bodyDone (ClR bl) bq.body (DoneS bl pre p bq) d ∧ g'.old d = st'.old d := by
    intro d hd
    have hd1 : DoneE bl ((pre ++ [q]) ++ mid) p bq d := by simpa using hd
    have hd2 : DoneE bl (pre ++ [q]) p bq d :=
      ⟨hd1.1, hd1.2.1, fun o' i hdf ho' => hd1.2.2 o' i hdf (List.mem_append_left _ ho')⟩
    refine ⟨awa_doneE_body d hd2, ?_⟩
    rw [hold]
    exact awa_frame_seg mid (pre ++ [q]) r g2 g' ht1 hi1 hw d (awa_done_seg hS ht2 hπ hb hj hq hd1)
  exact ⟨akept_rebase (old := st'.old) hk hD, hD⟩

/-! ## (c) Presence -/

/-- **Presence**: every done register present in the file before has its
`old` present in the file after. -/
def APres (old : Nat → Nat) (R R' : Map (Option Noun)) (Done : Nat → Prop) : Prop :=
  ∀ d, Done d → (HoonMap.get R d).isSome → (HoonMap.get R' (old d)).isSome

theorem apres_rebase {old old' : Nat → Nat} {R R' : Map (Option Noun)} {D D' : Nat → Prop}
    (h : APres old R R' D) (hD : ∀ d, D' d → D d ∧ old' d = old d) : APres old' R R' D' := by
  intro d hd hs
  obtain ⟨h1, h2⟩ := hD d hd
  rw [h2]; exact h d h1 hs

theorem get_isSome_of_read {x : Nat} {R : Map (Option Noun)} {v : Noun} (h : read x R = some v) :
    (HoonMap.get R x).isSome := by
  rw [read_eq_some.mp h]; rfl

theorem get_put_isSome {R : Map (Option Noun)} {x d : Nat} {u : Option Noun} (h : (HoonMap.get R x).isSome) :
    (HoonMap.get (HoonMap.put R d u) x).isSome := by
  rw [HoonMap.get_put]; split <;> simp_all

theorem poleWr_dst {op : Pole} {x : Nat} (h : aliasDst op ≠ some x) : x ∉ Comp.poleWr op := by
  cases op <;> simp_all [Comp.poleWr, aliasDst] <;> exact fun e => h e.symm

section
variable {σ : Type}

/-- **A dropped op that goes on writes a value at its destination**, unless
it is a `%mov` (which copies its source, poison included). -/
theorem dropped_dst_val {pick : List Nat → Nat} {st st2 : ABody} {op : Pole}
    (h : aliasOp pick st op = some (none, st2)) {lib : Lib} {O : Oracle σ} {gul : Noun} {s s2 : σ}
    {regs R2 : Map (Option Noun)} {t t2 : Trace} {n : Noun}
    (hx : execPole lib O gul s op regs t = some (Tone.zero n, R2, t2, s2)) :
    ∀ e, aliasDst op = some e → (∃ v, read e R2 = some v) ∨ ∃ a, op = Pole.mov a e := by
  intro e he
  have hsem := as_sem hx
  have fin : ∀ (F : Nat → Option Noun) (w : Noun), (fun x => read x R2) = updA F e (some w) →
      ∃ v, read e R2 = some v := fun F w E => ⟨w, by have := congrFun E e; simpa [as_upd_self] using this⟩
  cases op
  all_goals first
    | (simp [aliasDst] at he; done)
    | (simp [aliasOp] at h; done)
    | skip
  case imm n0 d =>
    simp only [aliasDst, Option.some.injEq] at he; subst he; exact Or.inl (fin _ _ hsem)
  case mov a d =>
    simp only [aliasDst, Option.some.injEq] at he; subst he; exact Or.inr ⟨a, rfl⟩
  case inc a d =>
    simp only [aliasDst, Option.some.injEq] at he; subst he
    obtain ⟨_, _, E⟩ := hsem; exact Or.inl (fin _ _ E)
  case con a b d =>
    simp only [aliasDst, Option.some.injEq] at he; subst he
    obtain ⟨_, _, _, _, E⟩ := hsem; exact Or.inl (fin _ _ E)
  case hed a d =>
    simp only [aliasDst, Option.some.injEq] at he; subst he
    obtain ⟨_, _, _, E⟩ := hsem; exact Or.inl (fin _ _ E)
  case tal a d =>
    simp only [aliasDst, Option.some.injEq] at he; subst he
    obtain ⟨_, _, _, E⟩ := hsem; exact Or.inl (fin _ _ E)

/-- **Presence through one op**: the op before goes on with the file `R2`,
the file after is `R2'`, which only adds to the file after (`hR2'`); `AKept`
and `AOK` hold after the op (`akb_op`, `as_body`).  A done register present
before keeps its `old` present (`old` is unchanged off the destination).  The
new destination `e`: if the op before wrote a value there, `AKept` and `AOK`
give that value at `old e` after; otherwise it is a dropped `%mov` from a
done register `a` (`hwr`), the file after is unchanged and `old e` is
`old a`. -/
theorem apres_op {pick : List Nat → Nat} {st st2 : ABody} {op : Pole} {res : Option Pole} {Done : Nat → Prop}
    (h : aliasOp pick st op = some (res, st2)) {lib : Lib} {O : Oracle σ} {gul : Noun} {s s2 : σ}
    {regs R2 regs' R2' : Map (Option Noun)} {t t2 : Trace} {n : Noun}
    (hx : execPole lib O gul s op regs t = some (Tone.zero n, R2, t2, s2))
    (hp : APres st.old regs regs' Done) (hsrc : ∀ x ∈ asSrc op, Done x)
    (hnd : ∀ e, aliasDst op = some e → ¬ Done e)
    (hR2' : ∀ x, (HoonMap.get regs' x).isSome → (HoonMap.get R2' x).isSome)
    {D2 : Nat → Prop} (hD2 : ∀ x, D2 x → Done x ∨ aliasDst op = some x)
    (hk2 : AKept st2 (fun x => read x R2) (fun x => read x R2') D2) (hok2 : AOK st2 (fun x => read x R2) D2)
    (hwr : ∀ e, aliasDst op = some e → (∃ v, read e R2 = some v) ∨ ∃ a, op = Pole.mov a e) :
    APres st2.old R2 R2' D2 := by
  intro d hd0 hs
  have hd := hD2 d hd0
  by_cases hdst : aliasDst op = some d
  · -- the new destination
    rcases hwr d hdst with ⟨v, hv⟩ | ⟨a, rfl⟩
    · have e1 : read (st2.old d) R2 = read d R2 := hok2.old d hd0
      have e2 : read (st2.old d) R2' = read (st2.old d) R2 := hk2.old d hd0
      exact get_isSome_of_read (e2.trans (e1.trans hv))
    · simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [execPole, localPole, move] at hx
      cases hga : HoonMap.get regs a with
      | none => rw [hga] at hx; simp at hx
      | some u =>
        show (HoonMap.get R2' (updA st.old d (st.old a) d)).isSome = true
        rw [as_upd_self]
        exact hR2' _ (hp a (hsrc a (by simp [asSrc])) (by rw [hga]; rfl))
  · rcases hd with hd | hd
    · rw [awk_op_old h d hdst]
      apply hR2'
      apply hp d hd
      rw [← Comp.execPole_frame lib O gul hx d (poleWr_dst hdst)]
      exact hs
    · exact absurd hd hdst

end

/-! ### The pass -/

/-- A pass that goes on puts every parameter. -/
theorem apass_par : ∀ (args : List (Option Nat)) (par : List Nat) (regs R : Map (Option Noun)),
    evalPassLoop args par regs = some R → ∀ x ∈ par, (HoonMap.get R x).isSome
  | [], par, regs, R, h, x, hx => by
    simp only [evalPassLoop] at h
    split at h
    · rename_i e; subst e; cases hx
    · cases h
  | _ :: _, [], _, _, _, _, hx => absurd hx List.not_mem_nil
  | a :: args, p :: par, regs, R, h, x, hx => by
    simp only [evalPassLoop] at h
    obtain ⟨R1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    by_cases hxp : x ∈ par
    · exact apass_par args par R1 R h2 x hxp
    · have hxe : x = p := by
        rcases List.mem_cons.mp hx with e | e
        · exact e
        · exact absurd e hxp
      subst hxe
      rw [Comp.evalPassLoop_frame args par R1 R h2 x hxp]
      cases a with
      | none =>
        simp only [Option.some.injEq] at h1; subst h1
        simp [poison, HoonMap.get_put]
      | some r =>
        simp only [move] at h1
        obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.mp h1
        simp [HoonMap.get_put]

/-- **The pass after goes on**: the arguments renamed by `f`, when every
argument present before is present after through `f`, and neither an
argument nor its renaming is a parameter (the check of `+eval-pass`). -/
theorem apass_loop (f : Nat → Nat) : ∀ (args : List (Option Nat)) (par : List Nat) (R R' R2 : Map (Option Noun)),
    (∀ u, some u ∈ args → u ∉ par) → (∀ u, some u ∈ args → f u ∉ par) →
    (∀ u, some u ∈ args → (HoonMap.get R u).isSome → (HoonMap.get R' (f u)).isSome) →
    evalPassLoop args par R = some R2 → ∃ R2', evalPassLoop (args.map (Option.map f)) par R' = some R2'
  | [], par, R, R', R2, _, _, _, h => by
    simp only [evalPassLoop] at h
    split at h
    · rename_i e; subst e; exact ⟨R', by simp [evalPassLoop]⟩
    · cases h
  | _ :: _, [], _, _, _, _, _, _, h => by simp [evalPassLoop] at h
  | a :: args, p :: par, R, R', R2, hu, hf, hpr, h => by
    simp only [evalPassLoop] at h
    obtain ⟨R1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hu' : ∀ u, some u ∈ args → u ∉ par := fun u hm hp => hu u (List.mem_cons_of_mem _ hm) (List.mem_cons_of_mem _ hp)
    have hf' : ∀ u, some u ∈ args → f u ∉ par := fun u hm hp => hf u (List.mem_cons_of_mem _ hm) (List.mem_cons_of_mem _ hp)
    have hup : ∀ u, some u ∈ args → u ≠ p := fun u hm e => hu u (List.mem_cons_of_mem _ hm) (by rw [e]; exact List.mem_cons_self)
    have hfp : ∀ u, some u ∈ args → f u ≠ p := fun u hm e => hf u (List.mem_cons_of_mem _ hm) (by rw [e]; exact List.mem_cons_self)
    have keep : ∀ (w w' : Option Noun), (∀ u, some u ∈ args → (HoonMap.get (HoonMap.put R p w) u).isSome →
        (HoonMap.get (HoonMap.put R' p w') (f u)).isSome) := by
      intro w w' u hm hs
      rw [HoonMap.get_put, if_neg (hup u hm)] at hs
      rw [HoonMap.get_put, if_neg (hfp u hm)]
      exact hpr u (List.mem_cons_of_mem _ hm) hs
    cases a with
    | none =>
      simp only [Option.some.injEq] at h1; subst h1
      obtain ⟨R2', e⟩ := apass_loop f args par _ (poison p R') R2 hu' hf' (keep none none) h2
      exact ⟨R2', by simp only [List.map_cons, Option.map_none, evalPassLoop, Option.bind_some]; exact e⟩
    | some r =>
      simp only [move] at h1
      obtain ⟨u, hgu, rfl⟩ := Option.map_eq_some_iff.mp h1
      have hr' := hpr r List.mem_cons_self (by rw [hgu]; rfl)
      obtain ⟨u', hgu'⟩ := Option.isSome_iff_exists.mp hr'
      obtain ⟨R2', e⟩ := apass_loop f args par _ (HoonMap.put R' p u') R2 hu' hf' (keep u u') h2
      exact ⟨R2', by simp only [List.map_cons, Option.map_some, evalPassLoop, move, hgu', Option.map_some,
        Option.bind_some]; exact e⟩

/-- The check of `+eval-pass` of renamed arguments. -/
theorem apass_check {f : Nat → Nat} {args : List (Option Nat)} {par : List Nat} (R : Map (Option Noun))
    (h : ∀ u, some u ∈ args → f u ∉ par) :
    evalPass (args.map (Option.map f)) par R = evalPassLoop (args.map (Option.map f)) par R := by
  unfold evalPass
  rw [if_pos]
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
  cases a0 with
  | none => rfl
  | some u => simpa using h u ha0

/-! ### Along the edge taken -/

/-- **The agreement along the edge taken**: at the end of a walked jumping
block `q` (the facts and immediates `lq`, `mq`, the block after `pb`, `AOK`
and `ABInv` with the `old` of the walk state `g` just before `o` is walked,
`DoneE` there), with `AKept` and presence on the files before and after, the
pass after of the arguments renamed by `old` goes on whenever the pass before
does, and `AKept` and presence hold at the start of `o` (the start state of
`aStart`, `DoneS` along `q :: p`). -/
theorem akp_edge {bl : Map Blob} (hS : AliasSSAB bl) (hpn : ParNodup bl) {pre l : List Nat}
    (ht : TopoOK bl (pre ++ l)) {g : AGen Map} (hw : OldW bl pre g) {o q : Nat} {p : List Nat} {bo bq : Blob}
    (hRo : Reach bl o) (hbo : HoonMap.get bl o = some bo) (hopre : o ∉ pre) (hbq : HoonMap.get bl q = some bq)
    {lq : AInfo} {mq : AImms} {pb : Blob}
    (hlq : g.info q = some lq) (hmq : g.imms q = some mq) (hpb : HoonMap.get g.new q = some pb)
    {regs regs' Rp : Map (Option Noun)}
    (hok : AOK ⟨g.old, lq, mq⟩ (fun x => read x regs) (DoneE bl pre p bq))
    (hab : ABInv ⟨g.old, lq, mq⟩ (DefW bl pre) (DoneE bl pre p bq) (ClR bl))
    (hk : AKept ⟨g.old, lq, mq⟩ (fun x => read x regs) (fun x => read x regs') (DoneE bl pre p bq))
    (hP : APres g.old regs regs' (DoneE bl pre p bq))
    (hq : q ∈ g.rev o) {j j' : Jmp} (hj' : j' ∈ getJmps pb.fin) (hjo : j'.there = o)
    (hargs : j'.args = j.args.map (Option.map g.old)) (hau : ∀ u, some u ∈ j.args → DoneE bl pre p bq u)
    (hpass : evalPass j.args bo.par regs = some Rp)
    {info : AInfo} {imms : AImms} {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : aliasStart g o (g.rev o) = some info) (him : aliasStartImms g (g.rev o) = some imms)
    (hed : aliasEdges g o (g.rev o) = some edges) (hpa : aliasPars g bo.par edges info = some loc0) :
    ∃ Rp', evalPass j'.args bo.par regs' = some Rp' ∧
      AKept ⟨g.old, loc0, imms⟩ (fun x => read x Rp) (fun x => read x Rp') (DoneS bl pre (q :: p) bo) ∧
      APres g.old Rp Rp' (DoneS bl pre (q :: p) bo) := by
  obtain ⟨hno, hloop⟩ := evalPass_check hpass
  obtain ⟨hnm, hnmi, hDo, -⟩ := awi_edge_side hS ht hw hRo hbo hopre hbq hab
  have hu : ∀ u, some u ∈ j.args → u ∉ bo.par := fun u hu => hno _ hu u rfl
  have hfu : ∀ u, some u ∈ j.args → g.old u ∉ bo.par := fun u hu hp =>
    awi_par_notDefW hS.1 hRo hbo hp hopre (hab.old u (hau u hu))
  obtain ⟨Rp', hloop'⟩ := apass_loop g.old j.args bo.par regs regs' Rp hu hfu
    (fun u hu' hs => hP u (hau u hu') hs) hloop
  have hpass' : evalPass j'.args bo.par regs' = some Rp' := by
    rw [hargs, apass_check regs' hfu]
    exact hloop'
  have hu' : ∀ u, some u ∈ j'.args → u ∉ bo.par := by
    intro u hm
    rw [hargs] at hm
    obtain ⟨a0, ha0, e⟩ := List.mem_map.mp hm
    cases a0 with
    | none => cases e
    | some u0 =>
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      exact hfu u0 ha0
  have hloop2 : evalPassLoop j'.args bo.par regs' = some Rp' := by rw [hargs]; exact hloop'
  have hpar : ∀ (k x : Nat), bo.par[k]? = some x → (fun x => read x Rp) x = argV (fun x => read x regs) j.args[k]? := by
    intro k x hk
    rw [← awa_argV]
    exact aedge_pass j.args bo.par regs Rp hu (hpn o bo hbo) hloop k x hk
  have hpar' : ∀ (k x : Nat), bo.par[k]? = some x →
      (fun x => read x Rp') x = argV (fun x => read x regs') j'.args[k]? := by
    intro k x hk
    rw [← awa_argV]
    exact aedge_pass j'.args bo.par regs' Rp' hu' (hpn o bo hbo) hloop2 k x hk
  have hoff : ∀ x, x ∉ bo.par → (fun x => read x Rp) x = (fun x => read x regs) x := by
    intro x hx; simp only [read]; rw [Comp.evalPass_frame hpass x hx]
  have hoff' : ∀ x, x ∉ bo.par → (fun x => read x Rp') x = (fun x => read x regs') x := by
    intro x hx; simp only [read]; rw [Comp.evalPass_frame hpass' x hx]
  refine ⟨Rp', hpass', aedge_kept hst him hed hpa hq hlq hmq hpb hok hk hj' hjo hargs hau hpar hpar' hoff hoff'
    hnm hnmi (fun x hx => (hDo x hx).imp (fun h => ⟨h.1, h.2.2.2⟩) id), ?_⟩
  intro d hd hs
  rcases hDo d hd with ⟨h1, -, h3, h4⟩ | ⟨h1, h2⟩
  · rw [Comp.evalPass_frame hpass d h3] at hs
    rw [Comp.evalPass_frame hpass' _ h4]
    exact hP d h1 hs
  · rw [h2]
    exact apass_par _ _ _ _ hloop2 d h1

/-! ## (d) One op of a live body, forward -/

theorem akept_mono {st : ABody} {R R' : Nat → Option Noun} {D D' : Nat → Prop} (hk : AKept st R R' D)
    (hD : ∀ d, D' d → D d) : AKept st R R' D' :=
  ⟨hk.imm, hk.names, fun d hd => hk.old d (hD d hd)⟩

theorem wrX_isSome {W : Option (Nat × Noun)} {R : Map (Option Noun)} {x : Nat} (h : (HoonMap.get R x).isSome) :
    (HoonMap.get (wrX W R) x).isSome := by
  rcases W with _ | ⟨d, v⟩
  · exact h
  · exact get_put_isSome h

section
variable {σ : Type}

/-- **One op of a live body, forward, with presence**: at a walk state `st`
where `AOK`, `ABInv`, `AKept` and presence hold, the next op meets `BodyOK`
and its reads are done, an op before that goes on is matched by the op kept
after (same tone, trace, state) or by nothing when dropped, and `AOK`,
`ABInv`, `AKept` and presence hold after the op with `Done` the `bodyDone` of
the op. -/
theorem akb_live {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    {st st2 : ABody} {op : Pole} {res : Option Pole} {Def Done Cl : Nat → Prop}
    (h : aliasOp pick st op = some (res, st2)) (lib : Lib) (O : Oracle σ) (gul : Noun) (s : σ)
    {regs regs' : Map (Option Noun)} (t : Trace)
    (hok : AOK st (fun x => read x regs) Done) (hab : ABInv st Def Done Cl) (hBO : BodyOK Cl [op] Def Done)
    (hrd : ∀ x ∈ aliasReads op, Done x)
    (hk : AKept st (fun x => read x regs) (fun x => read x regs') Done) (hP : APres st.old regs regs' Done)
    {n : Noun} {R2 : Map (Option Noun)} {t2 : Trace} {s2 : σ}
    (hx : execPole lib O gul s op regs t = some (Tone.zero n, R2, t2, s2)) :
    AOK st2 (fun x => read x R2) (bodyDone Cl [op] Done) ∧ ABInv st2 (bodyDef [op] Def) (bodyDone Cl [op] Done) Cl ∧
    (∀ op', res = some op' → ∃ R2', execPole lib O gul s op' regs' t = some (Tone.zero n, R2', t2, s2) ∧
      AKept st2 (fun x => read x R2) (fun x => read x R2') (bodyDone Cl [op] Done) ∧
      APres st2.old R2 R2' (bodyDone Cl [op] Done)) ∧
    (res = none → AKept st2 (fun x => read x R2) (fun x => read x regs') (bodyDone Cl [op] Done) ∧
      APres st2.old R2 regs' (bodyDone Cl [op] Done)) := by
  obtain ⟨hsrc, hdst, -⟩ := hBO
  have hf : ∀ e, aliasDst op = some e → AFresh st Done e := fun e he => ab_fresh hab (hdst e he)
  have haB : aliasBody pick [op] st = some (res.toList, st2) := by
    simp only [aliasBody, h, Option.bind_some, Option.map_some, List.append_nil]
  obtain ⟨hok2, hab2⟩ := as_body hpick [op] st _ Def Done _ st2 _ haB hok hab ⟨hsrc, hdst, trivial⟩
    (OpsRun.cons (as_sem hx) (OpsRun.nil _))
  have hsub : ∀ x, bodyDone Cl [op] Done x → Done x ∨ (aliasDst op = some x ∧ st.old x = x) := by
    rintro x (hx' | ⟨he, hc⟩)
    · exact Or.inl hx'
    · exact Or.inr ⟨he, hab.self x (hdst x he) hc⟩
  have hD2 : ∀ x, bodyDone Cl [op] Done x → Done x ∨ aliasDst op = some x := fun x hx' =>
    (hsub x hx').imp_right fun h => h.1
  have hnd : ∀ e, aliasDst op = some e → ¬ Done e := fun e he => (hf e he).done
  obtain ⟨hkept, hdrop⟩ := akb_op hpick h lib O gul s t hok hk hrd hsrc hf hx
  refine ⟨hok2, hab2, fun op' hr => ?_, fun hr => ?_⟩
  · obtain ⟨R2', e2, hk2⟩ := hkept op' hr
    subst hr
    have hrd' : ∀ x ∈ aliasReads op, read (st.old x) regs' = read x regs := fun x hx' =>
      (hk.old x (hrd x hx')).trans (hok.old x (hrd x hx'))
    rcases akx_exec h lib O gul s t hrd' with ⟨e, -⟩ | ⟨ton, t3, s3, W, e1, e3, hW1, hW2⟩
    · rw [e] at hx; cases hx
    · rw [hx] at e1
      simp only [Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e1
      rw [e2] at e3
      simp only [Option.some.injEq, Prod.mk.injEq] at e3
      obtain ⟨-, rfl, -, -⟩ := e3
      have hk2' := akept_mono hk2 hsub
      refine ⟨_, e2, hk2', apres_op h hx hP hsrc hnd (fun x hs => wrX_isSome hs) hD2 hk2' hok2 ?_⟩
      intro e he
      left
      rcases W with _ | ⟨d, v⟩
      · rw [hW2 rfl n rfl] at he; cases he
      · have hd := hW1 _ rfl
        rw [hd] at he; cases he
        exact ⟨v, read_store_self d v regs⟩
  · subst hr
    have hk2' := akept_mono (hdrop rfl) hsub
    exact ⟨hk2', apres_op h hx hP hsrc hnd (fun x hs => hs) hD2 hk2' hok2 (dropped_dst_val h hx)⟩

end

/-! ## (d) The jump at the end of a block -/

/-- Two splits of a list at a member absent from both prefixes are one. -/
theorem split_unique {q : Nat} : ∀ (A A' C C' : List Nat), q ∉ A → q ∉ A' → A ++ q :: C = A' ++ q :: C' →
    A = A' ∧ C = C'
  | [], [], C, C', _, _, h => by simp only [List.nil_append, List.cons.injEq, true_and] at h; exact ⟨rfl, h⟩
  | [], a :: A', C, C', _, h2, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h2
  | a :: A, [], C, C', h1, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h1
  | a :: A, a' :: A', C, C', h1, h2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨e1, e2⟩ := split_unique A A' C C' (fun h' => h1 (List.mem_cons_of_mem _ h'))
      (fun h' => h2 (List.mem_cons_of_mem _ h')) h.2
    exact ⟨by rw [h.1, e1], e2⟩

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **The jump at the end of a walked block, with its pass**: at a
configuration `x` of an execution from the entry that stands at the end of
the body of a jumping block `q` (walked from `g1q` to `g2q`, its end state
`st'`), with `AKept` and presence at `st'` on `bodyDone` of the whole body,
when the end before takes the jump `j` to `o` and the pass before goes on
(`Rp`): the end after (the block stored for `q` in the final state) takes a
jump `j'` to `o` with the arguments renamed, the block after at `o` has the
parameters of `o`, the pass after goes on (`Rp'`), and at the start of `o`
(the walk up to `o`, its start state `st0`) `AKept` and presence hold on
`DoneS` along `q :: epath es`. -/
theorem akj_jump {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    {preq lq' : List Nat} {q : Nat} {g1q g2q : AGen Map} (htq : topo = preq ++ q :: lq')
    (h1q : aliasWalk pick nargs c.blocks preq (aliasInit rev) = some g1q)
    (h2q : aliasBlock pick nargs c.blocks g1q q = some g2q) {st' : ABody}
    (hg2 : g2q.old = st'.old ∧ g2q.info q = some st'.loc ∧ g2q.imms q = some st'.imml)
    {st : σ} {vals : List Noun} {t : Trace} {es : List (Nat × Nat)} {x : Path.Cfg σ Map} {bq : Blob}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es x)
    (hp : x.params = []) (hq : x.b.par = []) (hbody : x.b.body = []) (hxq : x.lab = q)
    (hbq : HoonMap.get c.blocks q = some bq) (hfin : x.b.fin = bq.fin)
    {out : List Pole} {rf : Termin × (Nat → List Nat) × Bool}
    (hfinq : aliasFin st'.old st'.loc g1q.rev g1q.folded q bq.fin = some rf)
    (hpbq : HoonMap.get g2q.new q = some { par := bq.par, body := out, fin := rf.1 }) {regs' : Map (Option Noun)}
    (hk : AKept st' (fun x' => read x' x.regs) (fun x' => read x' regs')
      (bodyDone (ClR c.blocks) bq.body (DoneS c.blocks preq (epath es) bq)))
    (hP : APres st'.old x.regs regs' (bodyDone (ClR c.blocks) bq.body (DoneS c.blocks preq (epath es) bq)))
    {j : Jmp} {bo : Blob} (htk : Path.taken x.regs x.b.fin = some j) (hbo : HoonMap.get c.blocks j.there = some bo)
    {Rp : Map (Option Noun)} (hpass : evalPass j.args bo.par x.regs = some Rp) :
    ∃ j' preo lo g1o g2o st0 Rp' pbo, HoonMap.get g.new q = some { par := bq.par, body := out, fin := rf.1 } ∧
      Path.taken regs' rf.1 = some j' ∧
      j'.there = j.there ∧ j'.args = j.args.map (Option.map g1o.old) ∧
      HoonMap.get g.new j.there = some pbo ∧ pbo.par = bo.par ∧
      evalPass j'.args bo.par regs' = some Rp' ∧
      topo = preo ++ j.there :: lo ∧ aliasWalk pick nargs c.blocks preo (aliasInit rev) = some g1o ∧
      aliasBlock pick nargs c.blocks g1o j.there = some g2o ∧ aStart nargs g1o j.there bo = some st0 ∧
      AKept st0 (fun x' => read x' Rp) (fun x' => read x' Rp') (DoneS c.blocks preo (q :: epath es) bo) ∧
      APres st0.old Rp Rp' (DoneS c.blocks preo (q :: epath es) bo) := by
  have hS : AliasSSAB c.blocks := hD.2.1
  have hpn : ParNodup c.blocks := hD.1.1.1.1
  have hTo := hT.1.1
  have hat := awa_entry_at hfe
  obtain ⟨hπ, B, k1, hB, hfB, -, -⟩ := hat
  rw [hxq] at hπ hB
  rw [hbq] at hB; cases hB
  have hRq : Reach c.blocks q := ssk_bpath_reach hπ q List.mem_cons_self
  rw [hfin] at htk
  have hj : j ∈ getJmps bq.fin := taken_mem htk
  have hRo : Reach c.blocks j.there := Reach.jump hRq hbq hj
  have hoT : j.there ∈ topo := hTo.2.2.2.1 _ hRo
  obtain ⟨preo, lo, g1o, g2o, htopo, h1o, h2o, h3o⟩ := alias_start_parts h hoT
  -- the walk invariant at `preo`
  have hI : AWInv lib O c gul topo preo g1o := by
    subst htopo
    have := awa_walk_part (lib := lib) (O := O) (gul := gul) hpick hD preo [] (j.there :: lo) _ g1o
      (by simpa using hTo) (by simpa using awa_init (lib := lib) (O := O) (gul := gul) hT) h1o
    simpa using this
  have hopre : j.there ∉ preo := fun h' =>
    (List.nodup_append.mp (htopo ▸ hTo).1).2.2 _ h' _ List.mem_cons_self rfl
  have hqpre : q ∈ preo := awr_pre (htopo ▸ hTo) (htopo ▸ hTo.2.2.2.1 _ hRq) hbq hj rfl
  -- `preo` is `preq ++ q :: mid`
  obtain ⟨A, mid, hA⟩ := List.append_of_mem hqpre
  subst hA
  have hnd : topo.Nodup := hTo.1
  have hqA : q ∉ A := by
    intro hm
    rw [htopo] at hnd
    have := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 q hm q List.mem_cons_self
    exact this rfl
  have hqpreq : q ∉ preq := fun hm => (List.nodup_append.mp (htq ▸ hnd)).2.2 q hm q List.mem_cons_self rfl
  have e1 : A ++ q :: (mid ++ j.there :: lo) = preq ++ q :: lq' := by rw [← htq, htopo]; simp
  obtain ⟨rfl, hlq⟩ := split_unique A preq _ _ hqA hqpreq e1
  have htopo2 : topo = A ++ q :: (mid ++ j.there :: lo) := by rw [htopo]; simp
  have hT2 := hT
  rw [htopo2] at hT2
  -- the walk over `mid` from `g2q` reaches `g1o`
  have hwq : aliasWalk pick nargs c.blocks (A ++ [q]) (aliasInit rev) = some g2q := by
    rw [awa_walk_append, h1q]; simp only [Option.bind_some, aliasWalk, h2q]
  have hmid : aliasWalk pick nargs c.blocks mid g2q = some g1o := by
    have e := h1o
    rw [show A ++ q :: mid = (A ++ [q]) ++ mid by simp, awa_walk_append, hwq, Option.bind_some] at e
    exact e
  have htm : TopoOK c.blocks (A ++ q :: (mid ++ j.there :: lo)) := hT2.1.1
  have hIq : AWInv lib O c gul topo (A ++ [q]) g2q := by
    have := awa_walk_part (lib := lib) (O := O) (gul := gul) hpick hD (A ++ [q]) [] (mid ++ j.there :: lo) _ g2q
      (by simpa using htm) (by simpa using awa_init (lib := lib) (O := O) (gul := gul) hT2) hwq
    rw [htopo2]; simpa using this
  have hiq : ARev c.blocks (A ++ q :: (mid ++ j.there :: lo)) (A ++ [q]) g2q := by
    have := hIq.rev; rw [htopo2] at this; exact this
  obtain ⟨hk1, hDm⟩ := akept_jump hS htm hiq hmid hπ hbq hj hg2.1.symm hk
  have hP1 : APres g1o.old x.regs regs' (DoneE c.blocks (A ++ q :: mid) (epath es) bq) :=
    apres_rebase hP fun d hd => hDm d hd
  -- `EndOK` at `preo`
  have hE := hI.ends st vals t es x bq j hfe hp hq hbody (by rw [hxq]; exact hqpre) (by rw [hxq]; exact hbq) hj
  rw [hxq] at hE
  obtain ⟨lq, mq, pb, hlq', hmq', hpb, -, hok, hab, htake⟩ := hE
  have hqmid : q ∉ mid := fun hm => (List.nodup_cons.mp (List.nodup_append.mp htm.1).2.1).1 (List.mem_append_left _ hm)
  have hframe := (awk_walk mid g2q g1o hmid).2 q hqmid
  rw [hframe.1, hg2.2.1] at hlq'; cases hlq'
  rw [hframe.2.1, hg2.2.2] at hmq'; cases hmq'
  rw [hframe.2.2, hpbq] at hpb; cases hpb
  have htkR : takenR (fun x' => read x' x.regs) bq.fin = some j := by rw [← afn_taken]; exact htk
  obtain ⟨hqrev, j', hj'R, hj'o, hj'args, -⟩ := htake j htkR
  -- the parts of the walk of `o`
  have hne : g1o.rev j.there ≠ [] := List.ne_nil_of_mem hqrev
  obtain ⟨info, imms, b1, edges, loc0, rb, rfo, f1, f2, f3, f4, f5, -, -, f8⟩ := awa_block_parts h2o (fun e => hne e.1)
  rw [hbo] at f3; cases f3
  have hA0 := aStart_of_parts f1 f2 f4 f5
  rw [if_neg hne] at f1
  have hau : ∀ u, some u ∈ j.args → DoneE c.blocks (A ++ q :: mid) (epath es) bq u := fun u hu =>
    awi_fin_done hS hπ hbq hj (jmp_finRegs hj hu)
  have htT : TopoOK c.blocks ((A ++ q :: mid) ++ j.there :: lo) := htopo ▸ hTo
  obtain ⟨Rp', hpass', hk2, hP2⟩ := akp_edge hS hpn htT hI.oldw hRo hbo hopre hbq (hframe.1.trans hg2.2.1)
    (hframe.2.1.trans hg2.2.2) (hframe.2.2.trans hpbq) hok hab hk1 hP1
    hqrev (aedge_taken_mem hj'R) hj'o hj'args hau hpass f1 f2 f4 f5
  -- the end after on the file after
  have hrd : ∀ x' ∈ Path.finReads rf.1, read x' regs' = read x' x.regs := by
    intro x' hx'
    obtain ⟨y, hy, rfl⟩ := awa_fin_reads hfinq (hD.2.2 q bq hbq) x' hx'
    have hyd : DoneE c.blocks (A ++ [q]) (epath es) bq y := awi_fin_done hS hπ hbq hj (awk_finReads_sub hy)
    exact hk.old y (awa_doneE_body y hyd)
  have htk' : Path.taken regs' rf.1 = some j' := by
    rw [afn_taken, afn_taken_congr hrd]; exact hj'R
  -- the blocks after in the final state
  have hol : j.there ∉ lo := fun hm => (List.nodup_cons.mp (List.nodup_append.mp htT.1).2.1).1 hm
  have hqo : q ≠ j.there := fun e => hopre (e ▸ hqpre)
  have hql : q ∉ lo := by
    intro hm
    have := (List.nodup_append.mp htT.1).2.2 q hqpre q (List.mem_cons_of_mem _ hm)
    exact this rfl
  have hfl := (awk_walk lo g2o g h3o).2
  refine ⟨j', A ++ q :: mid, lo, g1o, g2o, _, Rp', { par := bo.par, body := rb.1, fin := rfo.1 }, ?_, htk', hj'o,
    hj'args, ?_, rfl, hpass', htopo, h1o, h2o,
    hA0, hk2, hP2⟩
  · rw [(hfl q hql).2.2, ((awk_block h2o).2 q hqo).2.2]
    exact hframe.2.2.trans hpbq
  · rw [(hfl _ hol).2.2, f8]
    simp only [HoonMap.get_put, if_true]

end

end Opt
end SkaModel
end Formalization
