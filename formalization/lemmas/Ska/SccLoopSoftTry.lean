import lemmas.Ska.SccLoopSoft2
import lemmas.Ska.SccLoopSoftFin
import lemmas.Ska.CompDirectM
import lemmas.Ska.SofModel
import lemmas.Ska.Opt

/-! # `+soft-emit` with tries, `finishLFCS2` (README Gaps 21.20)

`softEmitT` (`SccLoopSoftFin.lean`) gives `none` where `+soft-emit` (line 5323) would make a
try.  `softEmit` here is the whole arm for `kin` `%tail` and `%call` without a ring (`%mean`
and `rin` are not modelled: `none`), line by line:
* `+soft-cut` (line 5610) with `+soft-axis` / `+soft-pair` (lines 5558, 5584) and `+sure-at`
  (line 7682): a cell or `%both` that is not under one place of the callee's subject, or that
  the callee reads first thing, is fetched with `%cel` / `%hed` / `%tal` (registers by `re`);
* the moves of `tops` (`softMoves`) and the tries (`softTriesP`: `%both` cut to its pair);
* `+soft-cons` (line 5674): the callee's subject in `rub`, from `tops` (`+malt`: the last entry
  wins), the registers of the need, and the sock's data where the need is `%none`;
* the subject-version call `pes` (`%jsp` for `%tail`; for `%call` the merge block, `%cal` into
  `plain`, `%csl`), `fail` (`+emit-cold`: label `(con (bex 30) o)`);
* `+soft-free` (line 5490; fuel `100000`, `none` when out): on `&` the tries by
  `+mono-try-call` in front of the bond's last hop, on `|` the flag path (`softFlag`, the arm
  `flag` of line 5361 with `+soft-try` line 5517). -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- The product of `+soft-axis`: `%any`, `%no` or `[%at q]`. -/
inductive SoftAx where
  | any | no | at (q : Nat)
  deriving DecidableEq, Repr

/-- **`+soft-pair`** (line 5584). -/
def softPair : SoftAx → SoftAx → SoftAx
  | SoftAx.no, _ => SoftAx.no
  | _, SoftAx.no => SoftAx.no
  | h, t =>
    let qh : Option Nat := match h with
      | SoftAx.at q => if q > 1 ∧ q % 2 = 0 then some (q / 2) else some 0
      | _ => none
    let qt : Option Nat := match t with
      | SoftAx.at q => if q > 1 ∧ q % 2 = 1 then some (q / 2) else some 0
      | _ => none
    match qh, qt with
    | none, none => SoftAx.any
    | none, some u => if u = 0 then SoftAx.no else SoftAx.at u
    | some u, none => if u = 0 then SoftAx.no else SoftAx.at u
    | some u, some v => if u = 0 then SoftAx.no else if u ≠ v then SoftAx.no else SoftAx.at u

/-- **`+soft-axis`** (line 5558), `axs` as `softAxes` gives it. -/
def softAxis (axs : List (Nat × Nat)) : Need → SoftAx
  | Need.none => SoftAx.any
  | Need.this r => match axs.lookup r with
    | none => SoftAx.no
    | some a => SoftAx.at a
  | Need.pair h t => softPair (softAxis axs h) (softAxis axs t)
  | Need.both r h t =>
    let b := softPair (softAxis axs h) (softAxis axs t)
    match axs.lookup r with
    | none => if b = SoftAx.any then SoftAx.no else b
    | some a => match b with
      | SoftAx.any => SoftAx.at a
      | SoftAx.no => SoftAx.no
      | SoftAx.at q => if q ≠ a then SoftAx.no else b

/-- **`+sure-at`** (line 7682); `none` is a crash (`+cell-sure` on `%void`, `+cap` of `0`). -/
def sureAt (axe : Nat) (sur : NeedOrd) (k : Sock) : Option Bool :=
  if h1 : axe = 1 then cellSure sur k else
  if h0 : axe = 0 then none else
  if cap axe = 2 then sureAt (mas axe) (ordHed sur) (So.hed k)
  else sureAt (mas axe) (ordTel sur) (So.tel k)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- The fetch of a head or tail in `+soft-cut`: nothing when that side has nothing. -/
def softSide (p : Pole) (ops : List Pole) (tops : List (Nat × Nat × Need)) : List Pole :=
  if ops = [] ∧ tops = [] then [] else p :: ops

/-- **`+soft-cut`** (line 5610): `[ops tops]` for the requirement `[src ned]`. -/
def softCutM (axs : List (Nat × Nat)) (sur : NeedOrd) (k : Sock) :
    Nat → Need → CM Map (List Pole × List (Nat × Nat × Need))
  | _, Need.none => pure ([], [])
  | src, Need.this r => match axs.lookup r with
    | some q => pure ([], [(q, src, Need.this r)])
    | none => if src = r then crashM else pure ([Pole.mov src r], [])
  | src, Need.pair h t =>
    let go : CM Map (List Pole × List (Nat × Nat × Need)) := do
      let rh ← re
      let rt ← re
      let (oh, th) ← softCutM axs sur k rh h
      let (ot, tt) ← softCutM axs sur k rt t
      pure (Pole.cel src :: (softSide (Pole.hed src rh) oh th ++ softSide (Pole.tal src rt) ot tt), th ++ tt)
    match softAxis axs (Need.pair h t) with
    | SoftAx.any => pure ([], [])
    | SoftAx.at q => match sureAt q sur k with
      | none => crashM
      | some false => pure ([], [(q, src, Need.pair h t)])
      | some true => go
    | SoftAx.no => go
  | src, Need.both r h t =>
    let go : CM Map (List Pole × List (Nat × Nat × Need)) :=
      if src = r then crashM else do
      let rh ← re
      let rt ← re
      let (oh, th) ← softCutM axs sur k rh h
      let (ot, tt) ← softCutM axs sur k rt t
      pure (Pole.mov src r :: Pole.cel src ::
        (softSide (Pole.hed src rh) oh th ++ softSide (Pole.tal src rt) ot tt), th ++ tt)
    match softAxis axs (Need.both r h t) with
    | SoftAx.any => pure ([], [])
    | SoftAx.at q => match sureAt q sur k with
      | none => crashM
      | some false => pure ([], [(q, src, Need.both r h t)])
      | some true => go
    | SoftAx.no => go

/-- The loop of `+soft-emit` over `req.s` (line 5328). -/
def softCutsM (axs : List (Nat × Nat)) (sur : NeedOrd) (k : Sock) :
    List (Nat × Need) → List Pole × List (Nat × Nat × Need) → CM Map (List Pole × List (Nat × Nat × Need))
  | [], acc => pure acc
  | (src, ned) :: rest, acc => do
    let (o, t) ← softCutM axs sur k src ned
    softCutsM axs sur k rest (o ++ acc.1, t ++ acc.2)

/-- `tries` (line 5350): the `tops` entries that are cells, a `%both` as its pair. -/
def softTriesP (tops : List (Nat × Nat × Need)) : List (Nat × Nat × Need) :=
  tops.filterMap fun (q, r, ned) => match ned with
    | Need.none => none
    | Need.this _ => none
    | Need.both _ h t => some (q, r, Need.pair h t)
    | n => some (q, r, n)

/-- **`+soft-try`** (line 5517). -/
def softTry (src : Nat) (ned : Need) (pre f nxt : Nat) : CM Map Nat := do
  let out := flattenNeed ned
  let merge ← emit ⟨out ++ [f], [], Termin.hop (jmp0 nxt)⟩
  let tem ← needOrdAllocRegs (needToOrd ned)
  let good ← emit ⟨[], [], Termin.hop ⟨(flattenNeed tem).map some ++ [some pre], merge⟩⟩
  let zero ← re
  let one ← re
  let bad ← emit ⟨[], [Pole.imm (A 0) zero, Pole.imm (A 1) one],
    Termin.hop ⟨out.map (fun _ => some zero) ++ [some one], merge⟩⟩
  monoTryCall tem good src bad

/-- `n` registers, front to back. -/
def reN : Nat → CM Map (List Nat)
  | 0 => pure []
  | n + 1 => do
    let r ← re
    let rest ← reN n
    pure (r :: rest)

/-- The loop of `flag` over the flopped tries and flags: `[first f]`. -/
def softFlagLoop (f0 : Nat) : List (Nat × Nat × Need) → List Nat → Nat → CM Map (Nat × Nat)
  | [], _, nxt => pure (nxt, f0)
  | (_, r, ned) :: tops, fl :: fla, nxt => do
    let pre := match fla with
      | [] => f0
      | p :: _ => p
    let n ← softTry r ned pre fl nxt
    let (fir, _) ← softFlagLoop f0 tops fla n
    pure (fir, fl)
  | _ :: _, [], _ => crashM

/-- **`flag`** (line 5361): the tries before the bond, the flag tested at its last block. -/
def softFlag (s : SoftCall) (ops : List Pole) (tries : List (Nat × Nat × Need)) (ht lt : Jmp)
    (fail : Nat) : CM Map Nat := do
  let f0 ← re
  let fla ← reN tries.length
  let (first, f) ← softFlagLoop f0 tries.reverse fla.reverse ht.there
  emir s.head ⟨[], ops ++ [Pole.imm (A 0) f0], Termin.hop (jmp0 first)⟩
  emir s.last ⟨[], [], Termin.brz f lt (jmp0 fail)⟩
  pure f

/-- **`+soft-cons`** (line 5674): the callee's subject from `tom`, the need and the sock. -/
def softConsM (tom : List (Nat × Nat)) : Need → Nat → Sock → CM Map (List Pole × Nat)
  | ned, axe, k => match tom.lookup axe with
    | some r => pure ([], r)
    | none => match ned with
      | Need.this r => pure ([], r)
      | Need.both r _ _ => pure ([], r)
      | Need.none => do
        let r ← re
        match k with
        | Sock.mk _ d => pure ([Pole.imm d r], r)
        | Sock.void => crashM
      | Need.pair h t => do
        let (oh, rh) ← softConsM tom h (Hoon.pegF axe 2) (So.hed k)
        let (ot, rt) ← softConsM tom t (Hoon.pegF axe 3) (So.tel k)
        let r ← re
        pure (oh ++ ot ++ [Pole.con rh rt r], r)

/-- **`+emit-cold`** (line 5481). -/
def emitCold (b : Blob) : CM Map Nat := do
  let o ← oo
  let c := o ||| 2 ^ 30
  emir c b
  pure c

/-- The successors `+soft-free` follows. -/
def finNext : Termin → List Nat
  | Termin.hop t => [t.there]
  | Termin.clq _ z o => [z.there, o.there]
  | Termin.eqq _ _ z o => [z.there, o.there]
  | Termin.brn _ z o => [z.there, o.there]
  | Termin.brz _ z o => [z.there, o.there]
  | _ => []

/-- **`+soft-free`** (line 5490) with fuel; `none` is a crash (`+got:by`) or the fuel out. -/
def softFreeF (blocks : Map Blob) (las : Nat) (dfn : List Nat) : Nat → List Nat → List Nat → Option Bool
  | 0, _, _ => none
  | _ + 1, [], _ => some true
  | n + 1, i :: todo, seen =>
    if i = las ∨ i ∈ seen then softFreeF blocks las dfn n todo seen else
    match HoonMap.get blocks i with
    | none => none
    | some b =>
      if b.body.any (fun op => (Opt.poleRegs op).any (· ∈ dfn)) then some false else
      if finNext b.fin = [] then some false else
      softFreeF blocks las dfn n (finNext b.fin ++ todo) (i :: seen)

/-- A block of the form `[~ ~ %hop ~ *]` (asserted): its jump. -/
def hopOf (o : Nat) : CM Map (Blob × Jmp) := fun g =>
  (HoonMap.get g.blocks o).bind fun b =>
    if b.par = [] ∧ b.body = [] then
      match b.fin with
      | Termin.hop t => if t.args = [] then some ((b, t), g) else none
      | _ => none
    else none

/-- **`+soft-emit`** (line 5323) for `%tail` and `%call` without a ring. -/
def softEmit (o : Nat) (s : SoftCall) : CM Map Unit :=
  if s.req = [] then pure () else do
  let (opsC, topsC) ← softCutsM (softAxes s.ned 1 []) s.sur s.b.less s.req ([], [])
  let ops := opsC ++ softMoves topsC
  let tries := softTriesP topsC
  let (hed, ht) ← hopOf s.head
  if tries = [] then emir s.head ⟨[], ops, hed.fin⟩ else do
  let (_, lt) ← hopOf s.last
  let tom := (topsC.map fun (q, r, _) => (q, r)).reverse
  let (kon, rub) ← softConsM tom s.ned 1 s.b.less
  if s.rin.isSome then crashM else
  let pes ← (if s.kin = 1 then emitCold ⟨[], [], Termin.jsp s.b rub⟩
    else if s.kin = 0 then do
      let proOpt ← re
      let proPes ← re
      let merged ← re
      let merge ← emit ⟨[merged], [Pole.mov merged s.pro], Termin.hop (jmp0 s.out)⟩
      emir s.plain ⟨[], [Pole.cal s.b (flattenNeed s.ned) proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
      emitCold ⟨[], [Pole.csl s.b rub proPes], Termin.hop ⟨[some proPes], merge⟩⟩
    else crashM : CM Map Nat)
  let fail ← emitCold ⟨[], kon, Termin.hop (jmp0 pes)⟩
  let dfn := (tries.map fun (_, _, n) => flattenNeed n).flatten
  let g ← get
  match softFreeF g.blocks s.last dfn 100000 [o] [] with
  | none => crashM
  | some false => do
    let _ ← softFlag s ops tries ht lt fail
    pure ()
  | some true => do
    let first ← tries.foldlM (fun nxt (_, r, n) => monoTryCall n nxt r fail) lt.there
    emir s.head ⟨[], ops, hed.fin⟩
    emir s.last ⟨[], [], Termin.hop (jmp0 first)⟩

/-- **`+soft-done`** (line 5298) with `softEmit`. -/
def softDoneL2 : List (Nat × SoftCall) → CM Map Unit
  | [] => pure ()
  | (o, s) :: rest => do softEmit o s; softDoneL2 rest

/-- `+soft-done` on a state: nothing when dropping. -/
def softDone2 (tapS : Map SoftCall → List (Nat × SoftCall)) (st : GenSf Map) : Option (Gen Map) :=
  if st.g.drop then some st.g else (softDoneL2 (tapS st.soft) st.g).map (·.2)

/-- **The final pass with soft calls, fixed**: `finishLFCS` with `runLCS2` and `softDone2`. -/
def finishLFCS2 [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (tapS : Map SoftCall → List (Nat × SoftCall)) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (runLCS2 env snd Option.none nm (CGoalL.done : CGoalL S) [] (GenSf.ofGen gen0)).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1.g).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazyLS nedFinal less nex.th.there nex.laz ⟨g2, g1.soft⟩).bind fun (_, g3) =>
        (softDone2 tapS g3).bind fun g3' =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3').bind fun (_, g4) =>
          toStraightF g4.cond g4.blocks bak.1 nex.th.there

end Comp
end SkaModel
end Formalization
