import lemmas.Ska.CompTop

/-!
# `+to-straight` in full

`toStraight` of `CompTop.lean` models only the pure-renaming path of
`+to-straight`, and is `none` where the Hoon takes its other path.  Here is
the whole arm, `toStraightF`: the test `&(run !proxies)`, the renaming path
when it holds, and otherwise the map path, which numbers the registers
afresh through the map `m` in the order the fold meets them (or renames
them by `ren` when the inputs are a run), after replacing each proxy
register of `cond` by its definition (`unproxy`).  The map path is
`+rewrite-input`, then `~(rep by blocks)` with `+rewrite-par`,
`+rewrite-body` (`+rewrite-op` on each op) and `+rewrite-fin`
(`+rewrite-jump`, `+rewrite-hop`, `+rewrite-args`).

`toStraightF_eq`: when `cond` is empty and the inputs are a run,
`toStraightF` is `toStraight`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The state of the map path: `re-gen` and the map `m` from old registers
to new ones. -/
abbrev RM (Map : Type → Type) := StateT (Nat × Map Nat) Option

/-- An `Option` as a step of `RM`. -/
def liftR {α : Type} (x : Option α) : RM Map α := fun st => x.map fun a => (a, st)

/-- `unproxy`: a proxy register is read as its definition. -/
def unproxy (cond : Map (Nat × List Nat)) (r : Nat) : Nat :=
  match HoonMap.get cond r with
  | some e => e.1
  | Option.none => r

/-- `+rer`: the new name of a register, unproxied first when there are
proxies; by `ren` when the inputs are a run, else through `m`, allocating
the next number at the first meeting. -/
def rer (cond : Map (Nat × List Nat)) (proxies run : Bool) (ren : Nat → Nat) (r : Nat) : RM Map Nat :=
  fun st =>
    let r := if proxies then unproxy cond r else r
    if run then some (ren r, st) else
    match HoonMap.get st.2 r with
    | some r1 => some (r1, st)
    | Option.none => some (st.1, (st.1 + 1, HoonMap.put st.2 r st.1))

section Rewrite
variable (rr : Nat → RM Map Nat)

/-- The loop of `+rewrite-input`. -/
def rewriteInputGo : Need → RM Map NeedOrd
  | Need.none => pure NeedOrd.none
  | Need.this r => do
    let _ ← rr r
    pure NeedOrd.this
  | Need.pair p q => do
    let l ← rewriteInputGo p
    let r ← rewriteInputGo q
    pure (NeedOrd.pair l r)
  | Need.both r h t => do
    let _ ← rr r
    let h' ← rewriteInputGo h
    let t' ← rewriteInputGo t
    pure (NeedOrd.both h' t')

/-- `+rewrite-input`, with its assertion that nothing was numbered yet. -/
def rewriteInput (ned : Need) : RM Map NeedOrd := fun st =>
  if st.1 = 0 then rewriteInputGo rr ned st else Option.none

/-- `+rewrite-par`: `?:  =(~ par)  [~ gen]` and a `spin` from the left,
which is `mapM`. -/
def rewritePar (par : List Nat) : RM Map (List Nat) := par.mapM rr

/-- `+rewrite-op`, the fields in the Hoon's order. -/
def rewriteOp : Pole → RM Map Pole
  | Pole.imm n d => do let d1 ← rr d; pure (Pole.imm n d1)
  | Pole.mov s d => do let s1 ← rr s; let d1 ← rr d; pure (Pole.mov s1 d1)
  | Pole.inc s d => do let s1 ← rr s; let d1 ← rr d; pure (Pole.inc s1 d1)
  | Pole.con h t d => do let h1 ← rr h; let t1 ← rr t; let d1 ← rr d; pure (Pole.con h1 t1 d1)
  | Pole.hed s d => do let s1 ← rr s; let d1 ← rr d; pure (Pole.hed s1 d1)
  | Pole.tal s d => do let s1 ← rr s; let d1 ← rr d; pure (Pole.tal s1 d1)
  | Pole.cel p => do let p1 ← rr p; pure (Pole.cel p1)
  | Pole.lob p => do let p1 ← rr p; pure (Pole.lob p1)
  | Pole.equ l r => do let l1 ← rr l; let r1 ← rr r; pure (Pole.equ l1 r1)
  | Pole.hsp n f => pure (Pole.hsp n f)
  | Pole.hse n f => pure (Pole.hse n f)
  | Pole.hdp n p f => do let p1 ← rr p; pure (Pole.hdp n p1 f)
  | Pole.hde n p f => do let p1 ← rr p; pure (Pole.hde n p1 f)
  | Pole.hmp a v f => do let v1 ← rewritePar rr v; pure (Pole.hmp a v1 f)
  | Pole.hme a v f => do let v1 ← rewritePar rr v; pure (Pole.hme a v1 f)
  | Pole.hcp n f => pure (Pole.hcp n f)
  | Pole.hce n f => pure (Pole.hce n f)
  | Pole.spy e p d => do let e1 ← rr e; let p1 ← rr p; let d1 ← rr d; pure (Pole.spy e1 p1 d1)
  | Pole.nok u f d => do let u1 ← rr u; let f1 ← rr f; let d1 ← rr d; pure (Pole.nok u1 f1 d1)
  | Pole.cal a v d => do let v1 ← rewritePar rr v; let d1 ← rr d; pure (Pole.cal a v1 d1)
  | Pole.caf a v d n => do let v1 ← rewritePar rr v; let d1 ← rr d; pure (Pole.caf a v1 d1 n)
  | Pole.cam a v d k => do let v1 ← rewritePar rr v; let d1 ← rr d; pure (Pole.cam a v1 d1 k)
  | Pole.csl a s d => do let s1 ← rr s; let d1 ← rr d; pure (Pole.csl a s1 d1)
  | Pole.csf a s d n => do let s1 ← rr s; let d1 ← rr d; pure (Pole.csf a s1 d1 n)
  | Pole.csm a s d k => do let s1 ← rr s; let d1 ← rr d; pure (Pole.csm a s1 d1 k)

/-- `+rewrite-body`. -/
def rewriteBody (bod : List Pole) : RM Map (List Pole) := bod.mapM (rewriteOp rr)

/-- `+rewrite-args`. -/
def rewriteArgs (j : Jmp) : RM Map Jmp :=
  if j.args = [] then pure j else do
    let args1 ← j.args.mapM fun a => match a with
      | Option.none => pure Option.none
      | some r => do let r1 ← rr r; pure (some r1)
    pure ⟨args1, j.there⟩

variable (bs : Map Blob)

/-- `+rewrite-jump`: a branch edge, chased, then its arguments renamed. -/
def rewriteJump (j : Jmp) : RM Map Jmp := do
  let j ← liftR (chase bs true j)
  rewriteArgs rr j

/-- `+rewrite-hop`: a hop edge. -/
def rewriteHop (j : Jmp) : RM Map Jmp := do
  let j ← liftR (chase bs false j)
  rewriteArgs rr j

/-- `+rewrite-fin`.  A block of `+comp` has no `%lti`. -/
def rewriteFin : Termin → RM Map Termin
  | Termin.clq s z o => do
    let s1 ← rr s; let z1 ← rewriteJump rr bs z; let o1 ← rewriteJump rr bs o
    pure (Termin.clq s1 z1 o1)
  | Termin.eqq l r z o => do
    let l1 ← rr l; let r1 ← rr r; let z1 ← rewriteJump rr bs z; let o1 ← rewriteJump rr bs o
    pure (Termin.eqq l1 r1 z1 o1)
  | Termin.brn s z o => do
    let s1 ← rr s; let z1 ← rewriteJump rr bs z; let o1 ← rewriteJump rr bs o
    pure (Termin.brn s1 z1 o1)
  | Termin.brz s z o => do
    let s1 ← rr s; let z1 ← rewriteJump rr bs z; let o1 ← rewriteJump rr bs o
    pure (Termin.brz s1 z1 o1)
  | Termin.hop t => do let t1 ← rewriteHop rr bs t; pure (Termin.hop t1)
  | Termin.jmp a v => do let v1 ← rewritePar rr v; pure (Termin.jmp a v1)
  | Termin.jmf a v n => do let v1 ← rewritePar rr v; pure (Termin.jmf a v1 n)
  | Termin.jsp a s => do let s1 ← rr s; pure (Termin.jsp a s1)
  | Termin.jsf a s n => do let s1 ← rr s; pure (Termin.jsf a s1 n)
  | Termin.don s => do let s1 ← rr s; pure (Termin.don s1)
  | Termin.bom Option.none => pure (Termin.bom Option.none)
  | Termin.bom (some x) => do
    let j ← liftR (chase bs true ⟨[], x⟩)
    pure (Termin.bom (some j.there))
  | Termin.lti _ _ _ _ => fun _ => Option.none

/-- One block of the map path: parameters, body, terminator. -/
def rewriteBlob (b : Blob) : RM Map Blob := do
  let par1 ← rewritePar rr b.par
  let body1 ← rewriteBody rr b.body
  let fin1 ← rewriteFin rr bs b.fin
  pure ⟨par1, body1, fin1⟩

/-- The fold `~(rep by blocks)` of the map path, from the state `st0`
that `+rewrite-input` left. -/
def mapBlocks [HoonMapKeys Map] (st0 : Nat × Map Nat) : Option (Map Blob) :=
  ((HoonMapKeys.keys bs).foldl (fun acc k => acc.bind fun (new, st) =>
    (HoonMap.get bs k).bind fun b =>
      if k ≠ 0 ∧ bypassable true b then some (new, st) else
      (rewriteBlob rr bs b st).map fun (b1, st1) => (HoonMap.put new k b1, st1))
    (some (HoonMap.empty, st0))).map Prod.fst

end Rewrite

/-- `!=(~ cond.gen)`: some proxy register exists. -/
def hasProxies [HoonMapKeys Map] (cond : Map (Nat × List Nat)) : Bool :=
  !(HoonMapKeys.keys cond).isEmpty

/-- **`+to-straight`** of `[%next [[ned ~] ~ ~] ~ o]` with the proxy map
`cond`: the renaming path when the inputs are a run and there is no proxy,
the map path otherwise. -/
def toStraightF [HoonMapKeys Map] (cond : Map (Nat × List Nat)) (blocks : Map Blob) (ned : Need) (o : Nat) :
    Option (Straight Map) :=
  let ins := flattenNeed ned
  let r0 := ins.headD 0
  let n := ins.length
  let run := isRun ins r0 0
  let proxies := hasProxies cond
  (HoonMap.get blocks o).bind fun start =>
    let bs := HoonMap.put (HoonMap.del blocks o) 0 start
    let rr := rer cond proxies run (renReg r0 n)
    (rewriteInput rr ned (0, HoonMap.empty)).bind fun (input, st) =>
      if run && !proxies then
        (renameBlocks bs (renReg r0 n)).map fun new => ⟨input, countArgs input, new⟩
      else
        (mapBlocks rr bs st).map fun new => ⟨input, countArgs input, new⟩

/-! ## The renaming path is the old model -/

theorem hasProxies_false [HoonMapKeys Map] {cond : Map (Nat × List Nat)}
    (h : ∀ k, HoonMap.get cond k = Option.none) : hasProxies cond = false := by
  unfold hasProxies
  cases e : HoonMapKeys.keys cond with
  | nil => rfl
  | cons k ks =>
    have := (HoonMapKeys.mem_keys cond k).mp (by rw [e]; exact List.mem_cons_self)
    rw [h k] at this; cases this

theorem bindR_apply {α β : Type} (x : RM Map α) (f : α → RM Map β) (st : Nat × Map Nat) :
    (x >>= f) st = (x st).bind fun p => f p.1 p.2 := rfl

theorem rewriteInputGo_run (cond : Map (Nat × List Nat)) (proxies : Bool) (ren : Nat → Nat) :
    ∀ (ned : Need) (st : Nat × Map Nat),
      rewriteInputGo (rer cond proxies true ren) ned st = some (needToOrd ned, st)
  | Need.none, st => rfl
  | Need.this r, st => rfl
  | Need.pair p q, st => by
    have e1 := rewriteInputGo_run cond proxies ren p st
    have e2 := rewriteInputGo_run cond proxies ren q st
    simp only [rewriteInputGo, needToOrd, bindR_apply, e1, e2, Option.bind_some]; rfl
  | Need.both r h t, st => by
    have e1 := rewriteInputGo_run cond proxies ren h st
    have e2 := rewriteInputGo_run cond proxies ren t st
    simp only [rewriteInputGo, needToOrd, bindR_apply, rer, if_true, e1, e2, Option.bind_some]; rfl

/-- **Without proxies and on a run of inputs, `+to-straight` is its
renaming path**, the model `toStraight`. -/
theorem toStraightF_eq [HoonMapKeys Map] {cond : Map (Nat × List Nat)} (hc : ∀ k, HoonMap.get cond k = Option.none)
    {blocks : Map Blob} {ned : Need} {o : Nat}
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    toStraightF cond blocks ned o = toStraight blocks ned o := by
  unfold toStraightF toStraight
  simp only [hasProxies_false hc, hrun, Bool.not_false, Bool.and_true, if_true]
  cases HoonMap.get blocks o with
  | none => rfl
  | some start =>
    simp only [Option.bind_some, rewriteInput, if_true]
    rw [rewriteInputGo_run]
    simp only [Option.bind_some, Bool.true_eq_false, if_false]

/-! ## On a run of inputs the map path is a renaming

When the inputs are a run, as they are when nothing is baked, `+rer` reads
and writes no state: it renames by `ren` after unproxying.  So the map path
is the renaming path with the renaming `ren ∘ unproxy`, which is not
injective: a proxy register and its definition get one name.
-/

/-- The renaming of the map path on a run of inputs. -/
def proxRen (cond : Map (Nat × List Nat)) (proxies : Bool) (ren : Nat → Nat) (r : Nat) : Nat :=
  ren (if proxies then unproxy cond r else r)

theorem pureR_apply {α : Type} (a : α) (st : Nat × Map Nat) : (pure a : RM Map α) st = some (a, st) := rfl

section Stateless
variable {rr : Nat → RM Map Nat} {f : Nat → Nat} (hr : ∀ a st, rr a st = some (f a, st))
include hr

theorem mapM_stateless : ∀ (l : List Nat) (st : Nat × Map Nat), l.mapM rr st = some (l.map f, st)
  | [], st => rfl
  | a :: l, st => by
    simp only [List.mapM_cons, bindR_apply, hr, Option.bind_some, mapM_stateless l st, List.map_cons]; rfl

theorem rewriteOp_stateless (p : Pole) (st : Nat × Map Nat) : rewriteOp rr p st = some (renPole f p, st) := by
  cases p <;> simp only [rewriteOp, renPole, rewritePar, bindR_apply, hr, Option.bind_some, pureR_apply,
    mapM_stateless hr]

theorem rewriteBody_stateless : ∀ (l : List Pole) (st : Nat × Map Nat),
    rewriteBody rr l st = some (l.map (renPole f), st)
  | [], st => rfl
  | a :: l, st => by
    unfold rewriteBody
    simp only [List.mapM_cons, bindR_apply, rewriteOp_stateless hr, Option.bind_some, List.map_cons]
    have := rewriteBody_stateless l st
    unfold rewriteBody at this
    rw [this]; rfl

theorem rewriteArgs_stateless (j : Jmp) (st : Nat × Map Nat) : rewriteArgs rr j st = some (renJmp f j, st) := by
  rcases j with ⟨args, there⟩
  unfold rewriteArgs
  by_cases h : args = []
  · subst h; rfl
  · simp only [h, if_false, bindR_apply]
    have : ∀ (l : List (Option Nat)) st, (l.mapM (fun a => match a with
        | Option.none => pure Option.none
        | some r => do let r1 ← rr r; pure (some r1)) : RM Map (List (Option Nat))) st =
          some (l.map (Option.map f), st) := by
      intro l
      induction l with
      | nil => intro st; rfl
      | cons a l ih =>
        intro st
        cases a <;> simp only [List.mapM_cons, bindR_apply, pureR_apply, hr, Option.bind_some, ih,
          List.map_cons, Option.map_none, Option.map_some]
    rw [this]; rfl

theorem rewriteFin_stateless (bs : Map Blob) (fin : Termin) (st : Nat × Map Nat) :
    rewriteFin rr bs fin st = (chaseFin bs f fin).map fun t => (t, st) := by
  cases fin with
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    simp only [rewriteFin, chaseFin, rewriteJump, liftR, bindR_apply, hr, Option.bind_some]
    cases chase bs true z <;> cases chase bs true o <;>
      simp [rewriteArgs_stateless hr, pureR_apply]
  | hop t =>
    simp only [rewriteFin, chaseFin, rewriteHop, liftR, bindR_apply]
    cases chase bs false t <;> simp [rewriteArgs_stateless hr, pureR_apply]
  | bom x =>
    cases x with
    | none => rfl
    | some x =>
      simp only [rewriteFin, chaseFin, liftR, bindR_apply]
      cases chase bs true ⟨[], x⟩ <;> simp [pureR_apply]
  | lti _ _ _ _ => rfl
  | _ => simp only [rewriteFin, chaseFin, rewritePar, bindR_apply, hr, mapM_stateless hr, Option.bind_some,
      pureR_apply, Option.map_some]

theorem rewriteBlob_stateless (bs : Map Blob) (b : Blob) (st : Nat × Map Nat) :
    rewriteBlob rr bs b st =
      (chaseFin bs f b.fin).map fun t => (⟨b.par.map f, b.body.map (renPole f), t⟩, st) := by
  unfold rewriteBlob rewritePar
  simp only [bindR_apply, mapM_stateless hr, Option.bind_some, rewriteBody_stateless hr,
    rewriteFin_stateless hr]
  cases chaseFin bs f b.fin <;> rfl

theorem mapBlocks_stateless [HoonMapKeys Map] (bs : Map Blob) (st : Nat × Map Nat) :
    mapBlocks rr bs st = renameBlocks bs f := by
  unfold mapBlocks renameBlocks
  suffices H : ∀ (ks : List Nat) (acc : Option (Map Blob)),
      (ks.foldl (fun acc k => acc.bind fun (new, st) =>
        (HoonMap.get bs k).bind fun b =>
          if k ≠ 0 ∧ bypassable true b then some (new, st) else
          (rewriteBlob rr bs b st).map fun (b1, st1) => (HoonMap.put new k b1, st1))
        (acc.map fun m => (m, st))) =
      (ks.foldl (fun acc k => acc.bind fun new =>
        (HoonMap.get bs k).bind fun b => (keepBlock bs f k b).map fun kb =>
          match kb with
          | Option.none => new
          | some b1 => HoonMap.put new k b1) acc).map fun m => (m, st) by
    have := H (HoonMapKeys.keys bs) (some HoonMap.empty)
    simp only [Option.map_some] at this
    rw [this, Option.map_map]
    simp only [Function.comp_def, Option.map_id']
    rfl
  intro ks
  induction ks with
  | nil => intro acc; rfl
  | cons k ks ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    cases acc with
    | none => rfl
    | some m =>
      simp only [Option.map_some, Option.bind_some]
      cases HoonMap.get bs k with
      | none => rfl
      | some b =>
        simp only [Option.bind_some, keepBlock]
        by_cases e : k ≠ 0 ∧ bypassable true b = true
        · rw [if_pos e, if_pos e]; rfl
        · rw [if_neg e, if_neg e, rewriteBlob_stateless hr]
          cases chaseFin bs f b.fin <;> rfl

end Stateless

theorem rer_run (cond : Map (Nat × List Nat)) (proxies : Bool) (ren : Nat → Nat) (r : Nat) (st : Nat × Map Nat) :
    rer cond proxies true ren r st = some (proxRen cond proxies ren r, st) := rfl

/-- **On a run of inputs, `+to-straight` is the renaming path with each
proxy register renamed as its definition.** -/
theorem toStraightF_run [HoonMapKeys Map] (cond : Map (Nat × List Nat)) (blocks : Map Blob) {ned : Need} (o : Nat)
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    toStraightF cond blocks ned o = (HoonMap.get blocks o).bind fun start =>
      (renameBlocks (HoonMap.put (HoonMap.del blocks o) 0 start)
        (proxRen cond (hasProxies cond) (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length))).map
        fun new => ⟨needToOrd ned, countArgs (needToOrd ned), new⟩ := by
  unfold toStraightF
  simp only [hrun, Bool.true_and]
  cases HoonMap.get blocks o with
  | none => rfl
  | some start =>
    simp only [Option.bind_some, rewriteInput, if_true]
    rw [rewriteInputGo_run]
    simp only [Option.bind_some]
    cases hp : hasProxies cond
    · simp only [Bool.not_false, if_true]
      congr 1
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [mapBlocks_stateless (rer_run cond true _)]

end Comp
end SkaModel
end Formalization
