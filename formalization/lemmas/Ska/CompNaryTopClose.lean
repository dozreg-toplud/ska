import lemmas.Ska.CompNaryTop
import lemmas.Ska.CompNaryTopEx

/-!
# Closing a direct call whose callee calls

README Gaps 18.15, step 4.  With the n-ary contract of `CallTreeA`
(`finishLFC_bellContractCallTreeA`, `CompNaryTop.lean`), the table of a
bell whose nomm is any member of track C's class meets its contracts
(`tableOK_callTreeA`: the n-ary entry `finishLFC`, the whole-subject entry
`finishLUCM`), so `closed_slotCall` and `closed_slotCallFour` hold for such a
callee: `closed_treeCall`, `closed_treeCallFour`.  The callee may make
indirect calls, which the table's oracle runs by `+mink` at the fuel of its
level; the hypotheses are still on the needs only.

The `#guard`s: the callee `bellI`, `[2 [0 2] [0 3]]` on any subject (an
indirect call), its n-ary need read as the n-ary entry's, and the caller's
whole-subject code run on the table of `bellI` agrees with `+mink` on the
optimistic and the pessimistic branch, under `%4` too; and the n-ary entry
of the callee itself on the table.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The table of a bell whose nomm is in `CallTreeA` meets its
contracts**: the n-ary entry `finishLFC` (nothing baked) by
`finishLFC_bellContractCallTreeA`, the whole-subject entry `finishLUCM` by
`finishLUCM_bellContractCallTreeA`, when the bell's cape has no `[| |]`. -/
theorem tableOK_callTreeA (lib : Lib) {env : CallEnv} {bZ : Bell} {x : Bool} {nm : Nomm} (h : CallTreeA x bZ.fol nm)
    {cape : Cape} {data : Noun} (hbl : bZ.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {cN cW : Straight Map}
    (hN : finishLFC (S := S) env nm ord cape (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) env nm = some cW) :
    TableOK lib (table2 bZ cN cW) := by
  intro b m c hc
  simp only [table2] at hc
  split at hc
  · rename_i e
    subst e
    cases m with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hc
      subst hc
      exact finishLFC_bellContractCallTreeA h hbl hn (fun _ => rfl) hN _
    | true =>
      simp only [if_true, Option.some.injEq] at hc
      subst hc
      exact (finishLUCM_bellContractCallTreeA h hW _).2
  · simp at hc

/-- **A closed theorem with a direct call of a callee that calls**: the
whole-subject code of `[2 [0 1] [1 b.fol] b]`, for a bell whose nomm is any
member of `CallTreeA` (indirect calls, `%7`, `%4`, `%3`, `%5`, `%1`), run on
the interpreter's oracle on the table of `b`'s two entries, returns `p`
exactly when `+mink` does, on every subject of `b`.  Hypotheses only on the
needs and on the cape. -/
theorem closed_treeCall (lib : Lib) {env : CallEnv} {bZ : Bell} {x : Bool} {nm : Nomm} (h : CallTreeA x bZ.fol nm)
    {cape : Cape} {data : Noun} (hbl : bZ.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {cN cW c : Straight Map}
    (hN : finishLFC (S := S) env nm ord cape (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) env nm = some cW)
    (hring : env.ring bZ = Option.none) (hneed : env.need bZ = some cN.need) (hpure : env.pure bZ = false)
    (hcod : env.cod bZ = some false)
    (hc : finishLUCM (S := S) env (slotCall bZ) = some c) {s : Noun} (hs : SkaModel.Fits bZ.less s) (gul p : Noun) :
    Mink lib gul [] s (slotCallFol bZ) (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib (table2 bZ cN cW) k) () c [s] [] gul = some (Tone.zero p, ()) :=
  closed_callTreeD (S := S) lib (tableOK_callTreeA (S := S) lib h hbl hn hN hW)
    (callTreeD_slotCall lib hring hneed hpure hcod) hc hs gul p

/-- **The same under `%4`** (`%cal` / `%csl` and the merge block). -/
theorem closed_treeCallFour (lib : Lib) {env : CallEnv} {bZ : Bell} {x : Bool} {nm : Nomm}
    (h : CallTreeA x bZ.fol nm)
    {cape : Cape} {data : Noun} (hbl : bZ.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {cN cW c : Straight Map}
    (hN : finishLFC (S := S) env nm ord cape (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) env nm = some cW)
    (hring : env.ring bZ = Option.none) (hneed : env.need bZ = some cN.need) (hpure : env.pure bZ = false)
    (hcod : env.cod bZ = some false)
    (hc : finishLUCM (S := S) env (Nomm.n4 (slotCall bZ)) = some c) {s : Noun} (hs : SkaModel.Fits bZ.less s)
    (gul p : Noun) :
    Mink lib gul [] s (n2 (A 4) (slotCallFol bZ)) (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib (table2 bZ cN cW) k) () c [s] [] gul = some (Tone.zero p, ()) :=
  closed_callTreeD (S := S) lib (tableOK_callTreeA (S := S) lib h hbl hn hN hW)
    (CallTreeD.four (callTreeD_slotCall lib hring hneed hpure hcod)) hc hs gul p

/-- **The n-ary entry of a callee that calls, closed on its own table**: on
every subject of the bell that splits by the entry's need, the n-ary code run
on the table's oracle returns `p` exactly when `+mink` does. -/
theorem closed_treeNary (lib : Lib) {env : CallEnv} {bZ : Bell} {x : Bool} {nm : Nomm} (h : CallTreeA x bZ.fol nm)
    {cape : Cape} {data : Noun} (hbl : bZ.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {cN cW : Straight Map}
    (hN : finishLFC (S := S) env nm ord cape (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) env nm = some cW) {s : Noun} (hs : SkaModel.Fits bZ.less s) {args : List Noun}
    (hsp : SkaModel.split cN.need s = some args) (gul p : Noun) :
    Mink lib gul [] s bZ.fol (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib (table2 bZ cN cW) k) () cN args [] gul = some (Tone.zero p, ()) :=
  have H := finishLFC_bellContractCallTreeA (S := S) h hbl hn (fun _ => rfl) hN (Table.needs (table2 bZ cN cW))
    s hs args (by simpa using hsp)
  table_closed_zero lib (tableOK_callTreeA (S := S) lib h hbl hn hN hW) (Needs.le_refl _) H.1 H.2 gul p

end

/-! ## The instance: a callee with an indirect call -/

/-- `[2 [0 2] [0 3]]` on any subject. -/
def bellI : Bell := ⟨Sock.mk Cape.no (A 0), ind23F⟩

/-- `bellI` needs `this`, is impure, no jet, hinted. -/
def envI : CallEnv :=
  ⟨fun b => if b = bellI then some NeedOrd.this else Option.none,
   fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => some false,
   fun _ _ _ _ _ => false⟩

/-- The n-ary entry of `bellI`. -/
def iN : Option (Straight FM) :=
  finishLFC (S := LS) envI ind23 NeedOrd.this Cape.no (fun ned => (ned, []))

/-- The whole-subject entry of `bellI`. -/
def iW : Option (Straight FM) := finishLUCM (S := LS) envI ind23

/-- The caller's whole-subject code of `nm` on the table of `bellI`, against
`+mink` on `f`. -/
def iRun (nm : Nomm) (f s : Noun) : Bool :=
  match iN, iW, (finishLUCM (S := LS) envI nm : Option (Straight FM)) with
  | some cN, some cW, some c =>
      (execEntry libT (tableOracle libT (table2 bellI cN cW) 10) () c [s] [] (A 0)).map Prod.fst ==
        minkF libT (A 0) 500 [] s f
  | _, _, _ => false

/-- The callee's n-ary code on the table, against `+mink`. -/
def iRunN (s : Noun) : Bool :=
  match iN, iW with
  | some cN, some cW => match SkaModel.split cN.need s with
    | some args => (execEntry libT (tableOracle libT (table2 bellI cN cW) 10) () cN args [] (A 0)).map Prod.fst ==
        minkF libT (A 0) 500 [] s ind23F
    | Option.none => false
  | _, _ => false

#guard iN.map (·.need) == envI.need bellI
#guard iW.isSome
#guard (finishLUCM (S := LS) (Map := FM) envI (slotCall bellI)).isSome
#guard (finishLUCM (S := LS) (Map := FM) envI (Nomm.n4 (slotCall bellI))).isSome
-- `closed_treeCall`: the indirect call inside the callee runs `[0 1]`, `[4 [0 3]]`, and crashes on an atom
#guard iRun (slotCall bellI) (slotCallFol bellI) (C (C (A 5) (A 6)) (C (A 0) (A 1)))
#guard iRun (slotCall bellI) (slotCallFol bellI) (C (A 5) (C (A 4) (C (A 0) (A 1))))
#guard iRun (slotCall bellI) (slotCallFol bellI) (A 5)
#guard iRun (Nomm.n4 (slotCall bellI)) (n2 (A 4) (slotCallFol bellI)) (C (A 5) (C (A 4) (C (A 0) (A 1))))
#guard iRun (Nomm.n4 (slotCall bellI)) (n2 (A 4) (slotCallFol bellI)) (A 5)
#guard minkF libT (A 0) 500 [] (C (A 5) (C (A 4) (C (A 0) (A 1)))) (n2 (A 4) (slotCallFol bellI)) ==
  some (Tone.zero (A 7))
-- `closed_treeNary`
#guard iRunN (C (A 5) (C (A 4) (C (A 0) (A 1))))
#guard iRunN (C (C (A 1) (A 2)) (C (A 0) (A 3)))

end Comp
end SkaModel
end Formalization
