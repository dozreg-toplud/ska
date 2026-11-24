import lemmas.Ska.OptAliasKeeps

/-!
# The simulation of `+alias`: the relation on configurations, forward

The configuration `x` of the code before (blocks `c.blocks`) and `x'` of the
code after (blocks `g.new`, the final state of the walk) are related by
**`AliasI`**: `x` is reached from the entry `(S0, V0, T0)` along the edges
`es`, both stand at the same label with the same trace and state, and one of
three modes holds.

* **Live** (`ALive`, at the split `s : ASplit` of the walk at place `k` of
  the body of `x.lab`): both have passed their parameters, `x` runs the body
  from `k`, `x'` runs the ops `aliasBody` keeps of the rest from the walk
  state `sta` after the first `k` ops (`outb`) and the end `aliasFin` makes
  (`rf.1`), no op below `k` is a dead fill, and `AKept` and presence hold at
  `sta` with `Done` the `bodyDone` of the first `k` ops (`ASplit.done`).
* **Dead** (`ADead`): both have passed, both bodies are `%imm` ops only and
  both ends are `%bom`; this is the rest of a block after a dead fill.
* **Pending** (`APend`): right after a jump, the parameters not yet passed;
  the arguments after are those before renamed by some `f`, an argument
  present before has its renaming present after, no argument is a parameter,
  and whenever the pass before goes on the pass after goes on and the live
  mode holds at place `0` after both passes.

`asplit_g2` reads the state the walk reaches after the block from a split,
`alive_at` gives `AOK`, `ABInv`, `BodyOK` and the reads done at a live
configuration (`alias_at_of`), `alive_dead` turns the live mode at a dead
fill into the dead mode, and `alive_jump` the end of a live jumping block
into the mode after the jump (`akj_jump`).  The forward steps are
`alias_fwd_step` and `alias_fwd_end`, put together in `alias_fwd`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-! ## The relation -/

/-- **The walk split at place `k` of the body of a block** `o`: the part of
`topo` before `o` (`pre`, with the state `g1` there) and after it (`l`), the
state `g2` after `o`, the block `b`, the start state `st0`, the ops kept from
the first `k` ops (`outa`, reaching `sta`) and from the rest (`outb`,
reaching `st'`), and the end made (`rf`). -/
structure ASplit (Map : Type → Type) where
  pre : List Nat
  l : List Nat
  g1 : AGen Map
  g2 : AGen Map
  b : Blob
  st0 : ABody
  k : Nat
  outa : List Pole
  sta : ABody
  outb : List Pole
  st' : ABody
  rf : Termin × (Nat → List Nat) × Bool

/-- What a split is. -/
structure ASplitOK (pick : List Nat → Nat) (nargs : Nat) (bl : Map Blob) (topo : List Nat)
    (rev : Map (List Nat)) (o : Nat) (s : ASplit Map) : Prop where
  to : topo = s.pre ++ o :: s.l
  w1 : aliasWalk pick nargs bl s.pre (aliasInit rev) = some s.g1
  w2 : aliasBlock pick nargs bl s.g1 o = some s.g2
  ne : ¬ (s.g1.rev o = [] ∧ o ≠ 0)
  hb : HoonMap.get bl o = some s.b
  st : aStart nargs s.g1 o s.b = some s.st0
  kle : s.k ≤ s.b.body.length
  ta : aliasBody pick (s.b.body.take s.k) s.st0 = some (s.outa, s.sta)
  tb : aliasBody pick (s.b.body.drop s.k) s.sta = some (s.outb, s.st')
  fin : aliasFin s.st'.old s.st'.loc s.g1.rev s.g1.folded o s.b.fin = some s.rf

/-- The done registers at a split, along the path of the edges `es`. -/
def ASplit.done (bl : Map Blob) (s : ASplit Map) (es : List (Nat × Nat)) : Nat → Prop :=
  bodyDone (ClR bl) (s.b.body.take s.k) (DoneS bl s.pre (epath es) s.b)

section
variable {σ : Type}

/-- **The live mode** at the split `s`. -/
structure ALive (pick : List Nat → Nat) (nargs : Nat) (c : Straight Map) (topo : List Nat)
    (rev : Map (List Nat)) (es : List (Nat × Nat)) (x x' : Path.Cfg σ Map) (s : ASplit Map) : Prop where
  ok : ASplitOK pick nargs c.blocks topo rev x.lab s
  px : x.params = []
  bx : x.b = { par := [], body := s.b.body.drop s.k, fin := s.b.fin }
  px' : x'.params = []
  bx' : x'.b = { par := [], body := s.outb, fin := s.rf.1 }
  nodf : ∀ i r, i < s.k → ¬ DeadFill c.blocks r x.lab i
  kept : AKept s.sta (fun y => read y x.regs) (fun y => read y x'.regs) (s.done c.blocks es)
  pres : APres s.sta.old x.regs x'.regs (s.done c.blocks es)

/-- **The dead mode**: `%imm` ops only up to a `%bom` on both sides. -/
structure ADead (x x' : Path.Cfg σ Map) : Prop where
  px : x.params = []
  qx : x.b.par = []
  px' : x'.params = []
  qx' : x'.b.par = []
  imm : ∀ op ∈ x.b.body, ∃ n d, op = Pole.imm n d
  imm' : ∀ op ∈ x'.b.body, ∃ n d, op = Pole.imm n d
  bom : ∃ u, x.b.fin = Termin.bom u
  bom' : ∃ u, x'.b.fin = Termin.bom u

/-- **The pending mode**, right after a jump. -/
def APend (pick : List Nat → Nat) (nargs : Nat) (c : Straight Map) (topo : List Nat) (rev : Map (List Nat))
    (es : List (Nat × Nat)) (x x' : Path.Cfg σ Map) : Prop :=
  (x.params ≠ [] ∨ x.b.par ≠ []) ∧ x'.b.par = x.b.par ∧ (∀ u, some u ∈ x.params → u ∉ x.b.par) ∧
  ∃ f : Nat → Nat, x'.params = x.params.map (Option.map f) ∧
    (∀ u, some u ∈ x.params → (HoonMap.get x.regs u).isSome → (HoonMap.get x'.regs (f u)).isSome) ∧
    ∀ Rp, evalPass x.params x.b.par x.regs = some Rp → ∃ Rp', evalPass x'.params x'.b.par x'.regs = some Rp' ∧
      ∃ s, ALive pick nargs c topo rev es { x with b := { x.b with par := [] }, params := [], regs := Rp }
        { x' with b := { x'.b with par := [] }, params := [], regs := Rp' } s

/-- **The relation of the simulation of `+alias`.** -/
def AliasI (pick : List Nat → Nat) (nargs : Nat) (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun)
    (topo : List Nat) (rev : Map (List Nat)) (S0 : σ) (V0 : List Noun) (T0 : Trace) (x x' : Path.Cfg σ Map) :
    Prop :=
  ∃ es, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x ∧
    x'.lab = x.lab ∧ x'.t = x.t ∧ x'.st = x.st ∧
    (APend pick nargs c topo rev es x x' ∨ (∃ s, ALive pick nargs c topo rev es x x' s) ∨ ADead x x')

end

/-! ## Small facts -/

theorem bodyDone_append {Cl : Nat → Prop} : ∀ (a b : List Pole) (D : Nat → Prop),
    bodyDone Cl (a ++ b) D = bodyDone Cl b (bodyDone Cl a D)
  | [], _, _ => rfl
  | _ :: a, b, _ => bodyDone_append a b _

theorem take_succ_of {α : Type} {l : List α} {k : Nat} {a : α} (h : l[k]? = some a) :
    l.take (k + 1) = l.take k ++ [a] := by
  rw [List.take_add_one, h]; rfl

theorem drop_cons_idx {α : Type} {l rest : List α} {k : Nat} {a : α} (h : l.drop k = a :: rest) :
    l[k]? = some a := by
  rw [← List.head?_drop, h]; rfl

/-- `aliasBody` keeps only `%imm` ops of a list of `%imm` ops. -/
theorem aliasBody_imm {pick : List Nat → Nat} : ∀ (l : List Pole) (st : ABody) (out : List Pole) (st' : ABody),
    (∀ op ∈ l, ∃ n d, op = Pole.imm n d) → aliasBody pick l st = some (out, st') →
    ∀ op ∈ out, ∃ n d, op = Pole.imm n d
  | [], _, out, _, _, h => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro op hop; cases hop
  | op :: l, st, out, st', hl, h => by
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ih := aliasBody_imm l st1 out2 st2 (fun o ho => hl o (List.mem_cons_of_mem _ ho)) h2
    obtain ⟨n, d, rfl⟩ := hl op List.mem_cons_self
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · simp only [aliasOp] at h1
      split at h1
      · simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, -⟩ := h1; cases ho
      · simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, -⟩ := h1
        simp only [Option.toList_some, List.mem_singleton] at ho; exact ⟨n, d, ho⟩
    · exact ih o ho

/-- `endR` reads only the registers of `finReads`. -/
theorem endR_congr {σ : Type} {O : Oracle σ} {gul : Noun} {R R' : Nat → Option Noun} {st : σ} {t : Trace}
    {fin : Termin} (h : ∀ x ∈ Path.finReads fin, R' x = R x) : endR O gul R' st t fin = endR O gul R st t fin := by
  have mm : ∀ v : List Nat, (∀ x ∈ v, R' x = R x) → v.mapM R' = v.mapM R := by
    intro v hv
    induction v with
    | nil => rfl
    | cons a v ih =>
      simp only [List.mapM_cons, hv a List.mem_cons_self, ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
  cases fin <;> simp only [endR, Path.finReads, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h ⊢
  all_goals first
    | rfl
    | (rw [h])
    | (rw [mm _ h])

/-- A `%mov` that goes on finds its source. -/
theorem mov_isSome {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {s : σ} {a d : Nat}
    {regs : Map (Option Noun)} {t : Trace} (h : (execPole lib O gul s (Pole.mov a d) regs t).isSome) :
    (move a d regs).isSome := by
  simp only [execPole, localPole] at h
  cases e : move a d regs with
  | none => rw [e] at h; simp at h
  | some _ => rfl

/-! ## A split -/

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **The walk state after the block of a split.** -/
theorem asplit_g2 {pick : List Nat → Nat} {nargs : Nat} {topo : List Nat} {rev : Map (List Nat)} {o : Nat}
    {s : ASplit Map} (h : ASplitOK pick nargs c.blocks topo rev o s) :
    s.st0.old = s.g1.old ∧ aliasBody pick s.b.body s.st0 = some (s.outa ++ s.outb, s.st') ∧
    s.g2.old = s.st'.old ∧ s.g2.info o = some s.st'.loc ∧ s.g2.imms o = some s.st'.imml ∧
    HoonMap.get s.g2.new o = some { par := s.b.par, body := s.outa ++ s.outb, fin := s.rf.1 } := by
  obtain ⟨st0', rb, rf', hA', hold, hrb, hrf', hg'⟩ := aStart_some (c := c) h.w2 h.ne h.hb
  rw [h.st] at hA'
  cases hA'
  have hbody : aliasBody pick s.b.body s.st0 = some (s.outa ++ s.outb, s.st') := by
    rw [← List.take_append_drop s.k s.b.body, aliasBody_append, h.ta, Option.bind_some, h.tb]; rfl
  rw [hbody] at hrb
  cases hrb
  rw [h.fin] at hrf'
  cases hrf'
  rw [hg']
  exact ⟨hold, hbody, rfl, as_upd_self _ _ _, as_upd_self _ _ _, by simp only [HoonMap.get_put, if_true]⟩

/-- **The live mode read through `alias_at_of`**: the path, `o ∉ pre`, the
registers read at `k` are done, `AOK` and `ABInv` at `sta`, and `BodyOK` of
the next ops below any place up to which no op is a dead fill. -/
theorem alive_at {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {S0 : σ} {V0 : List Noun} {T0 : Trace} {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} {s : ASplit Map}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x)
    (hl : ALive pick nargs c topo rev es x x' s) :
    BPath c.blocks (x.lab :: epath es) ∧ x.lab ∉ s.pre ∧ (∀ y, ReadAt s.b s.k y → s.done c.blocks es y) ∧
    AOK s.sta (fun y => read y x.regs) (s.done c.blocks es) ∧
    ABInv s.sta (bodyDef (s.b.body.take s.k) (fun y => DefW c.blocks s.pre y ∨ y ∈ s.b.par))
      (s.done c.blocks es) (ClR c.blocks) ∧
    (∀ m, s.k ≤ m → (∀ i r, i < m → ¬ DeadFill c.blocks r x.lab i) →
      BodyOK (ClR c.blocks) ((s.b.body.take m).drop s.k)
        (bodyDef (s.b.body.take s.k) (fun y => DefW c.blocks s.pre y ∨ y ∈ s.b.par)) (s.done c.blocks es)) := by
  have hq : x.b.par = [] := by rw [hl.bx]
  have hk : x.b.body = s.b.body.drop s.k := by rw [hl.bx]
  obtain ⟨hπ, -, hopre, hrd, hAB, hBO⟩ := alias_at_of hpick hD hT hl.ok.to hl.ok.w1 hl.ok.w2 hfe hl.px hq rfl
    hl.ok.hb hl.ok.st hl.ok.kle hk hl.ok.ta
  obtain ⟨hok, hab⟩ := hAB hl.nodf
  exact ⟨hπ, hopre, hrd, hok, hab, hBO⟩

/-- **A dropped op of the live mode goes on, with the trace and state
unchanged** (`akd_exec`, with `ReadsOK` and `LocalOK` of the entry). -/
theorem alive_drop_exec {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {S0 : σ} {V0 : List Noun} {T0 : Trace} (hE : EntryOK lib O c gul S0 V0 T0)
    {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} {s : ASplit Map}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x)
    (hl : ALive pick nargs c topo rev es x x' s) {op : Pole} {rest : List Pole} (hbd : x.b.body = op :: rest)
    {st2 : ABody} (hop : aliasOp pick s.sta op = some (none, st2)) :
    ∃ R2, execPole lib O gul x.st op x.regs x.t = some (Tone.zero (A 0), R2, x.t, x.st) := by
  obtain ⟨-, -, hrd, hok, -, -⟩ := alive_at hpick hD hT hfe hl
  have hq : x.b.par = [] := by rw [hl.bx]
  have hk : s.b.body.drop s.k = op :: rest := by rw [← hbd, hl.bx]
  refine akd_exec hop lib O gul x.st x.t hok.info (fun y hy => hok.old y (hrd y (Or.inl ?_)))
    (fun y hy => hE.1 es x y hfe ⟨hl.px, hq, Or.inl ⟨op, rest, hbd, hy⟩⟩) (fun a d e => ?_)
  · rw [hk]; exact hy
  · subst e
    exact mov_isSome (hE.2.2 es x _ rest hfe hl.px hq hbd rfl)

/-- **One op of the live mode, forward**, when it is no dead fill: the op is
kept, and the op after runs as the op before into the live mode at the next
place, or it is dropped, the trace and state unchanged, and the live mode
holds at the next place with the configuration after unchanged. -/
theorem alive_op {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {S0 : σ} {V0 : List Noun} {T0 : Trace} (hE : EntryOK lib O c gul S0 V0 T0)
    {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} {s : ASplit Map}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x)
    (hl : ALive pick nargs c topo rev es x x' s) {op : Pole} {rest : List Pole} (hbd : x.b.body = op :: rest)
    (hnd : ∀ r, ¬ DeadFill c.blocks r x.lab s.k)
    {n : Noun} {R2 : Map (Option Noun)} {t2 : Trace} {s2 : σ}
    (hx : execPole lib O gul x.st op x.regs x.t = some (Tone.zero n, R2, t2, s2)) :
    ∃ res st2 s', aliasOp pick s.sta op = some (res, st2) ∧
      (∀ op', res = some op' → ∃ R2', s.outb = op' :: s'.outb ∧
        execPole lib O gul x.st op' x'.regs x.t = some (Tone.zero n, R2', t2, s2) ∧
        ALive pick nargs c topo rev es { x with b := { x.b with body := rest }, regs := R2, t := t2, st := s2 }
          { x' with b := { x'.b with body := s'.outb }, regs := R2', t := t2, st := s2 } s') ∧
      (res = none → t2 = x.t ∧ s2 = x.st ∧ s'.outb = s.outb ∧
        ALive pick nargs c topo rev es { x with b := { x.b with body := rest }, regs := R2, t := t2, st := s2 } x' s') := by
  obtain ⟨-, -, hrd, hok, hab, hBO⟩ := alive_at hpick hD hT hfe hl
  have hk : s.b.body.drop s.k = op :: rest := by rw [← hbd, hl.bx]
  have hidx : s.b.body[s.k]? = some op := drop_cons_idx hk
  have hklt : s.k < s.b.body.length := by
    have := List.getElem?_eq_some_iff.mp hidx; exact this.1
  have hrest : s.b.body.drop (s.k + 1) = rest := awi_drop_succ hk
  have htb := hl.ok.tb
  rw [hk] at htb
  simp only [aliasBody] at htb
  obtain ⟨⟨res, st2⟩, h1, htb⟩ := Option.bind_eq_some_iff.mp htb
  obtain ⟨⟨outb2, st3⟩, h2, he⟩ := Option.map_eq_some_iff.mp htb
  simp only [Prod.mk.injEq] at he
  obtain ⟨hout, rfl⟩ := he
  have hnd1 : ∀ i r, i < s.k + 1 → ¬ DeadFill c.blocks r x.lab i := fun i r hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hl.nodf i r hi
    · exact hnd r
  have hBO1 := hBO (s.k + 1) (Nat.le_succ _) hnd1
  rw [take_succ_of hidx, List.drop_left' (by rw [List.length_take]; omega)] at hBO1
  have hrd1 : ∀ y ∈ aliasReads op, s.done c.blocks es y := fun y hy => hrd y (Or.inl (by rw [hk]; exact hy))
  obtain ⟨hok2, hab2, hkept, hdrop⟩ := akb_live hpick h1 lib O gul x.st x.t hok hab hBO1 hrd1 hl.kept hl.pres hx
  let s' : ASplit Map := { s with k := s.k + 1, outa := s.outa ++ res.toList, sta := st2, outb := outb2 }
  have hok' : ASplitOK pick nargs c.blocks topo rev x.lab s' := by
    refine ⟨hl.ok.to, hl.ok.w1, hl.ok.w2, hl.ok.ne, hl.ok.hb, hl.ok.st, hklt, ?_, ?_, hl.ok.fin⟩
    · show aliasBody pick (s.b.body.take (s.k + 1)) s.st0 = some (s.outa ++ res.toList, st2)
      rw [take_succ_of hidx, aliasBody_append, hl.ok.ta, Option.bind_some]
      simp only [aliasBody, h1, Option.bind_some, Option.map_some, List.append_nil]
    · show aliasBody pick (s.b.body.drop (s.k + 1)) st2 = some (outb2, s.st')
      rw [hrest]; exact h2
  have hdone : s'.done c.blocks es = bodyDone (ClR c.blocks) [op] (s.done c.blocks es) := by
    show bodyDone (ClR c.blocks) (s.b.body.take (s.k + 1)) _ = _
    rw [take_succ_of hidx, bodyDone_append]; rfl
  have hbx : ({ x.b with body := rest } : Blob) = { par := [], body := s'.b.body.drop s'.k, fin := s'.b.fin } := by
    show ({ x.b with body := rest } : Blob) = { par := [], body := s.b.body.drop (s.k + 1), fin := s.b.fin }
    rw [hrest, hl.bx]
  refine ⟨res, st2, s', h1, fun op' hr => ?_, fun hr => ?_⟩
  · obtain ⟨R2', e2, hk2, hP2⟩ := hkept op' hr
    subst hr
    refine ⟨R2', by rw [← hout]; rfl, e2, ⟨hok', hl.px, hbx, hl.px', ?_, hnd1, by rw [hdone]; exact hk2,
      by rw [hdone]; exact hP2⟩⟩
    show ({ x'.b with body := outb2 } : Blob) = { par := [], body := outb2, fin := s.rf.1 }
    rw [hl.bx']
  · obtain ⟨hk2, hP2⟩ := hdrop hr
    subst hr
    obtain ⟨R0, hR0⟩ := alive_drop_exec hpick hD hT hE hfe hl hbd h1
    rw [hx] at hR0
    simp only [Option.some.injEq, Prod.mk.injEq] at hR0
    obtain ⟨-, -, rfl, rfl⟩ := hR0
    refine ⟨rfl, rfl, by rw [← hout]; rfl, ⟨hok', hl.px, hbx, hl.px', ?_, hnd1, by rw [hdone]; exact hk2,
      by rw [hdone]; exact hP2⟩⟩
    show x'.b = { par := [], body := outb2, fin := s.rf.1 }
    rw [hl.bx', ← hout]; rfl

/-- **The live mode at a dead fill is the dead mode.** -/
theorem alive_dead {pick : List Nat → Nat} {nargs : Nat} {topo : List Nat} {rev : Map (List Nat)}
    {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} {s : ASplit Map}
    (hl : ALive pick nargs c topo rev es x x' s) {r : Nat} (hdf : DeadFill c.blocks r x.lab s.k) : ADead x x' := by
  obtain ⟨b, hb, ⟨u, hu⟩, -, hall, -⟩ := hdf
  rw [hl.ok.hb] at hb
  cases hb
  have hrf := hl.ok.fin
  rw [hu] at hrf
  simp only [aliasFin, Option.some.injEq] at hrf
  refine ⟨hl.px, by rw [hl.bx], hl.px', by rw [hl.bx'], fun op hop => ?_, fun op hop => ?_, ⟨u, by rw [hl.bx]; exact hu⟩,
    ⟨u, by rw [hl.bx', ← hrf]⟩⟩
  · rw [hl.bx] at hop; exact hall op hop
  · rw [hl.bx'] at hop; exact aliasBody_imm _ _ _ _ hall hl.ok.tb op hop

/-- **The next op of the live mode**: its walk, the ops kept from the rest,
and, when it is kept, the op after runs as the op before (`akx_exec`). -/
theorem alive_next {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {S0 : σ} {V0 : List Noun} {T0 : Trace} {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} {s : ASplit Map}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x)
    (hl : ALive pick nargs c topo rev es x x' s) {op : Pole} {rest : List Pole} (hbd : x.b.body = op :: rest) :
    ∃ res st2 outb2, aliasOp pick s.sta op = some (res, st2) ∧ s.outb = res.toList ++ outb2 ∧
      (∀ y ∈ aliasReads op, read (s.sta.old y) x'.regs = read y x.regs) ∧
      ∀ op', res = some op' → XRel (execPole lib O gul x.st op x.regs x.t)
        (execPole lib O gul x.st op' x'.regs x.t) x.regs x'.regs (aliasDst op) := by
  obtain ⟨-, -, hrd, hok, -, -⟩ := alive_at hpick hD hT hfe hl
  have hk : s.b.body.drop s.k = op :: rest := by rw [← hbd, hl.bx]
  have htb := hl.ok.tb
  rw [hk] at htb
  simp only [aliasBody] at htb
  obtain ⟨⟨res, st2⟩, h1, htb⟩ := Option.bind_eq_some_iff.mp htb
  obtain ⟨⟨outb2, st3⟩, -, he⟩ := Option.map_eq_some_iff.mp htb
  simp only [Prod.mk.injEq] at he
  obtain ⟨hout, -⟩ := he
  have hrd' : ∀ y ∈ aliasReads op, read (s.sta.old y) x'.regs = read y x.regs := fun y hy =>
    have hd := hrd y (Or.inl (by rw [hk]; exact hy))
    (hl.kept.old y hd).trans (hok.old y hd)
  refine ⟨res, st2, outb2, h1, hout.symm, hrd', fun op' hr => ?_⟩
  subst hr
  exact akx_exec h1 lib O gul x.st x.t hrd'

/-- **The end of the live mode**: the body is done, the end after is `rf.1`,
the facts at the end hold, every register the end before reads reads through
`old` what it holds and is done, and the end after reads the same values on
both files. -/
theorem alive_end {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {S0 : σ} {V0 : List Noun} {T0 : Trace} {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} {s : ASplit Map}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x)
    (hl : ALive pick nargs c topo rev es x x' s) (hbd : x.b.body = []) :
    s.k = s.b.body.length ∧ s.outb = [] ∧ s.st' = s.sta ∧
    FactsOK (fun y => read y x.regs) s.sta.loc ∧
    (∀ y ∈ Path.finReads s.b.fin, read (s.sta.old y) x.regs = read y x.regs ∧ s.done c.blocks es y) ∧
    (∀ y ∈ Path.finReads s.rf.1, read y x'.regs = read y x.regs) := by
  obtain ⟨-, -, hrd, hok, -, -⟩ := alive_at hpick hD hT hfe hl
  have hk0 : s.b.body.drop s.k = [] := by rw [← hbd, hl.bx]
  have hk : s.k = s.b.body.length := Nat.le_antisymm hl.ok.kle (List.drop_eq_nil_iff.mp hk0)
  have htb := hl.ok.tb
  rw [hk0] at htb
  simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at htb
  obtain ⟨hout, hst⟩ := htb
  have hfin := hl.ok.fin
  rw [← hst] at hfin
  have hfd : ∀ y ∈ Path.finReads s.b.fin, s.done c.blocks es y := fun y hy =>
    hrd y (Or.inr ⟨hk, awk_finReads_sub hy⟩)
  refine ⟨hk, hout.symm, hst.symm, hok.info, fun y hy => ⟨hok.old y (hfd y hy), hfd y hy⟩, fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := awa_fin_reads hfin (hD.2.2 _ s.b hl.ok.hb) y hy
  exact hl.kept.old z (hfd z hz)

theorem blob_par_nil {b : Blob} (h : b.par = []) : b = { par := [], body := b.body.drop 0, fin := b.fin } := by
  cases b; simp only at h; subst h; rfl

/-- **The jump at the end of the live mode**: when the end before takes the
jump `j` to a block `bo`, the end after takes a jump `j'` to the same block,
whose block after is `pbo`, and the configurations right after the two jumps
are in the pending mode, or in the live mode at place `0` when there is
nothing to pass (`akj_jump`). -/
theorem alive_jump {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    (hD : DInvS c.blocks) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR c.blocks topo rev)
    {g : AGen Map} (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    {S0 : σ} {V0 : List Noun} {T0 : Trace} {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} {s : ASplit Map}
    (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x)
    (hl : ALive pick nargs c topo rev es x x' s) (hbd : x.b.body = [])
    {j : Jmp} {bo : Blob} (htk : Path.taken x.regs x.b.fin = some j) (hbo : HoonMap.get c.blocks j.there = some bo) :
    ∃ j' pbo, Path.taken x'.regs x'.b.fin = some j' ∧ j'.there = j.there ∧ HoonMap.get g.new j.there = some pbo ∧
      x'.b.par = [] ∧ x'.b.body = [] ∧
      (APend pick nargs c topo rev (es ++ [(x.lab, j.there)]) (⟨j.there, bo, j.args, x.regs, x.t, x.st⟩ : Path.Cfg σ Map)
          ⟨j.there, pbo, j'.args, x'.regs, x'.t, x'.st⟩ ∨
        ∃ s', ALive pick nargs c topo rev (es ++ [(x.lab, j.there)])
          (⟨j.there, bo, j.args, x.regs, x.t, x.st⟩ : Path.Cfg σ Map) ⟨j.there, pbo, j'.args, x'.regs, x'.t, x'.st⟩ s') := by
  obtain ⟨hk, hout, hst, -, -, -⟩ := alive_end hpick hD hT hfe hl hbd
  obtain ⟨-, -, hg2o, hg2i, hg2m, hg2n⟩ := asplit_g2 hl.ok
  have hq : x.b.par = [] := by rw [hl.bx]
  have hfin : x.b.fin = s.b.fin := by rw [hl.bx]
  have htake : s.b.body.take s.k = s.b.body := by rw [hk]; exact List.take_length
  have hkept : AKept s.st' (fun y => read y x.regs) (fun y => read y x'.regs)
      (bodyDone (ClR c.blocks) s.b.body (DoneS c.blocks s.pre (epath es) s.b)) := by
    rw [hst, ← htake]; exact hl.kept
  have hpres : APres s.st'.old x.regs x'.regs
      (bodyDone (ClR c.blocks) s.b.body (DoneS c.blocks s.pre (epath es) s.b)) := by
    rw [hst, ← htake]; exact hl.pres
  obtain ⟨j', preo, lo, g1o, g2o, st0, outb, st'o, rfo, -, htk', hj'o, hj'args, hpr, hto, h1o, h2o, hneo, hAo,
    hbo2, hfo, hgo, hpassC⟩ :=
    akj_jump hpick hD hT h hl.ok.to hl.ok.w1 hl.ok.w2 ⟨hg2o, hg2i, hg2m⟩ hfe hl.px hq hbd rfl hl.ok.hb hfin
      hl.ok.fin hg2n hkept hpres htk hbo
  let s' : ASplit Map := ⟨preo, lo, g1o, g2o, bo, st0, 0, [], st0, outb, st'o, rfo⟩
  have hok' : ASplitOK pick nargs c.blocks topo rev j.there s' :=
    ⟨hto, h1o, h2o, hneo, hbo, hAo, Nat.zero_le _, by simp [s', aliasBody],
      by show aliasBody pick (bo.body.drop 0) st0 = some (outb, st'o); rw [List.drop_zero]; exact hbo2, hfo⟩
  have hdone : s'.done c.blocks (es ++ [(x.lab, j.there)]) = DoneS c.blocks preo (x.lab :: epath es) bo := by
    show bodyDone _ (bo.body.take 0) _ = _
    rw [List.take_zero, awa_epath_snoc]; rfl
  have hj : j ∈ getJmps s.b.fin := by rw [← hfin]; exact taken_mem htk
  have hchk : ∀ u, some u ∈ j.args → u ∉ bo.par := hD.1.1.1.2 x.lab s.b j bo hl.ok.hb hj hbo
  refine ⟨j', _, by rw [hl.bx']; exact htk', hj'o, hgo, by rw [hl.bx'], by rw [hl.bx', hout], ?_⟩
  by_cases hpp : j.args = [] ∧ bo.par = []
  · right
    obtain ⟨Rp', hRp', hk2, hP2⟩ := hpassC x.regs (by rw [hpp.1, hpp.2]; exact awa_pass_empty _)
    have hj'nil : j'.args = [] := by rw [hj'args, hpp.1]; rfl
    rw [hj'nil, hpp.2] at hRp'
    obtain ⟨-, rfl⟩ := awa_pass_nil hRp'
    refine ⟨s', ⟨hok', hpp.1, blob_par_nil hpp.2, hj'nil, ?_, fun i r hi => absurd hi (Nat.not_lt_zero _),
      by rw [hdone]; exact hk2, by rw [hdone]; exact hP2⟩⟩
    show ({ par := bo.par, body := outb, fin := rfo.1 } : Blob) = { par := [], body := outb, fin := rfo.1 }
    rw [hpp.2]
  · left
    have hne : j.args ≠ [] ∨ bo.par ≠ [] := by
      by_cases ha : j.args = []
      · exact Or.inr fun hb => hpp ⟨ha, hb⟩
      · exact Or.inl ha
    refine ⟨hne, rfl, hchk, g1o.old, hj'args, fun u hu hs => hpr u hu hs, fun Rp hRp => ?_⟩
    obtain ⟨Rp', hRp', hk2, hP2⟩ := hpassC Rp hRp
    exact ⟨Rp', hRp', s', ⟨hok', rfl, rfl, rfl, rfl, fun i r hi => absurd hi (Nat.not_lt_zero _),
      by rw [hdone]; exact hk2, by rw [hdone]; exact hP2⟩⟩

end

end Opt
end SkaModel
end Formalization
