import lemmas.Ska.Theorems
import lemmas.Ska.CompDirectMTree
import lemmas.Ska.CompNestFinalP

/-!
# Closing a direct call: the interpreter on a table of code

README Gaps 18.15.  The contracts of the compiler's code are stated against
any oracle that answers its calls as `+mink` does (`ContractFwd`,
`ContractBwd`).  `Theorems.lean` closes them by the fuel induction on the
interpreter's own oracle `interp lib poke k`, from `Sound` of the whole
compiler.  Here the compiler is replaced by a fixed table of code:

* `Table`, `Table.needs`: what `%dire b m` answers, and the need of each
  entry.
* `tablePoke`, `tableOracle`: the table as a compiler that answers only
  `%dire`, and the interpreter's oracle on it: a call is `interp`'s own
  `callBody` on `tablePoke`, an indirect call is run by `+mink` with the fuel
  of the level (the table has no code for `%full`).
* `TableOK`: every entry meets `BellContract` against the table's needs.
* `table_fwd`, `table_bwd`: the fuel induction of `interp_fwd`,
  `interp_bwd` on the table.  It needs no other induction for a recursive
  bell, since every contract is stated against any oracle.
* `table_closed`, `table_closed_zero`: so code meeting both halves of its
  contract, at needs the table includes, computes on the table's oracle what
  `+mink` computes, with no hypothesis on any callee's behaviour.
* `closed_callTreeD`: for the whole-subject code of a member of `CallTreeD`.
* `tableOK_slot`, `closed_slotCall`, `closed_slotCallFour`: the first closed
  theorems with a direct call.  The callee is `[0 axe]` with both its entries
  (`finishLFC`, n-ary, and `finishLUCM`, whole-subject) in the table, the
  caller is `[2 [0 1] [1 [0 axe]] b]` (`%jmp`/`%jsp`) or `[4 [2 [0 1] [1 [0
  axe]] b]]` (`%cal`/`%csl` and the merge block).  The only hypotheses are on
  the needs: the need `+callee-need` read is the need of the n-ary entry.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel

open Nock

section
variable {Map : Type → Type} [HoonMap Map]

/-- A table of code: the answer to `%dire b m`. -/
abbrev Table (Map : Type → Type) := Bell → Bool → Option (Straight Map)

/-- The needs of a table: the need of each entry. -/
def Table.needs (T : Table Map) : Needs := fun b m => (T b m).map (·.need)

/-- The table as a compiler that answers only `%dire`. -/
def tablePoke (T : Table Map) : Unit → Ovum → Option (Prod Map × Unit)
  | _, Ovum.dire b m => (T b m).map fun c => (Prod.ir b c (A 0), ())
  | _, _ => Option.none

/-- **The interpreter's oracle on a table**, with `k` levels of calls: a call
is `interp`'s `callBody` on `tablePoke T`, an indirect call is `+mink` with
the fuel `k`. -/
def tableOracle (lib : Lib) (T : Table Map) : Nat → Oracle Unit
  | 0 => ⟨fun _ _ _ _ _ _ => Option.none, fun _ _ _ _ => Option.none⟩
  | k + 1 => ⟨callBody lib (tablePoke T) (tableOracle lib T k),
      fun st u f gul => (minkF lib gul k [] u f).map fun r => (r, st)⟩

/-- Every entry of the table meets the contract of its bell against the
table's needs. -/
def TableOK (lib : Lib) (T : Table Map) : Prop :=
  ∀ b m c, T b m = some c → BellContract lib (Table.needs T) b m c

theorem tableOracle_steps (lib : Lib) (T : Table Map) (k : Nat) :
    OracleSteps (fun _ : Unit => True) (fun _ => Table.needs T) (tableOracle lib T k) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ => ⟨trivial, Needs.le_refl _⟩,
   fun _ _ _ _ _ _ _ _ => ⟨trivial, Needs.le_refl _⟩⟩

theorem callBody_table {lib : Lib} {T : Table Map} {O : Oracle Unit} {st : Unit} {b : Bell} {m : Bool}
    {vals : List Noun} {ti : Trace} {gul : Noun} {c : Straight Map} (h : T b m = some c) :
    callBody lib (tablePoke T) O st b m vals ti gul = execEntry lib O () c vals ti gul := by
  simp [callBody, tablePoke, h]

theorem table_entry {T : Table Map} {b : Bell} {m : Bool} {s : Noun} {vals : List Noun}
    (h : argsFor (Table.needs T) b m s = some vals) :
    ∃ c, T b m = some c ∧ (if m then some [s] else SkaModel.split c.need s) = some vals := by
  obtain ⟨nd, hnd, hvals⟩ := argsFor_some h
  simp only [Table.needs, Option.map_eq_some_iff] at hnd
  obtain ⟨c, hc, rfl⟩ := hnd
  exact ⟨c, hc, hvals⟩

/-- **The fuel induction on the table, forward.** -/
theorem table_fwd (lib : Lib) {T : Table Map} (hT : TableOK lib T) :
    ∀ k, OracleFwd lib (fun _ : Unit => True) (fun _ => Table.needs T) (tableOracle lib T k) k := by
  intro k
  induction k with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _),
                   fun _ _ _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    constructor
    · intro st b m vals ti tm gul s j r _ hj hfit hargs htr hmink
      obtain ⟨c, hc, hvals⟩ := table_entry hargs
      obtain ⟨hfwd, -⟩ := hT b m c hc s hfit vals hvals
      obtain ⟨ton, st', hrun, hrel⟩ :=
        hfwd Unit (fun _ => True) (fun _ => Table.needs T) (tableOracle lib T k) j gul ti tm r
          (fun _ _ => Needs.le_refl _) (tableOracle_steps lib T k) (ih.weaken (fun _ h => h) (by omega))
          hmink () trivial htr
      refine ⟨ton, st', ?_, hrel⟩
      show callBody lib (tablePoke T) (tableOracle lib T k) st b m vals ti gul = some (ton, st')
      rw [callBody_table hc]; exact hrun
    · intro st u f gul j r _ hj hmink
      have hm := minkF_le lib gul (Nat.le_of_lt_succ hj) _ _ _ _ hmink
      refine ⟨r, st, ?_, toneRel_mink_self lib _ hmink⟩
      show (minkF lib gul k [] u f).map (fun r => (r, st)) = some (r, st)
      rw [hm]; rfl

/-- **The fuel induction on the table, backward.** -/
theorem table_bwd (lib : Lib) {T : Table Map} (hT : TableOK lib T) :
    ∀ k, OracleBwd lib (fun _ : Unit => True) (fun _ => Table.needs T) (tableOracle lib T k) := by
  intro k
  induction k with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ h => by simp [tableOracle] at h,
                   fun _ _ _ _ _ _ _ h => by simp [tableOracle] at h⟩
  | succ k ih =>
    constructor
    · intro st b m vals ti gul ton st' _ h s tm hfit hargs htr
      obtain ⟨c, hc, hvals⟩ := table_entry hargs
      obtain ⟨-, hbwd⟩ := hT b m c hc s hfit vals hvals
      have h' : execEntry lib (tableOracle lib T k) () c vals ti gul = some (ton, st') := by
        rw [← callBody_table (O := tableOracle lib T k) (st := st) hc]; exact h
      exact hbwd Unit (fun _ => True) (fun _ => Table.needs T) (tableOracle lib T k) gul ti tm
        (fun _ _ => Needs.le_refl _) (tableOracle_steps lib T k) ih () ton st' trivial htr h'
    · intro st u f gul ton st' _ h
      change (minkF lib gul k [] u f).map (fun r => (r, st)) = some (ton, st') at h
      obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      exact ⟨ton, ⟨k, hr⟩, toneRel_mink_self lib _ hr⟩

/-- **Code that meets its contract computes, on the table's oracle, what
`+mink` computes**, when the table's entries meet theirs and include the
needs the code was compiled against.  Forward: with `n` levels, every result
of `+mink` with `n` fuel.  Backward: every answer, at any level. -/
theorem table_closed (lib : Lib) {T : Table Map} (hT : TableOK lib T) {N : Needs} (hN : N ≤ Table.needs T)
    {s f : Noun} {args : List Noun} {c : Straight Map}
    (hF : ContractFwd lib N s f args c) (hB : ContractBwd lib N s f args c) (gul : Noun) :
    (∀ n r, minkF lib gul n [] s f = some r →
      ∃ ton, execEntry lib (tableOracle lib T n) () c args [] gul = some (ton, ()) ∧
        ToneRel lib (Table.needs T) ton r) ∧
    (∀ k ton, execEntry lib (tableOracle lib T k) () c args [] gul = some (ton, ()) →
      ∃ r, Mink lib gul [] s f r ∧ ToneRel lib (Table.needs T) ton r) := by
  refine ⟨fun n r hm => ?_, fun k ton h => ?_⟩
  · obtain ⟨ton, st', hrun, hrel⟩ := hF Unit (fun _ => True) (fun _ => Table.needs T) (tableOracle lib T n) n
      gul [] [] r (fun _ _ => hN) (tableOracle_steps lib T n) (table_fwd lib hT n) hm () trivial Forall2.nil
    exact ⟨ton, hrun, hrel⟩
  · exact hB Unit (fun _ => True) (fun _ => Table.needs T) (tableOracle lib T k) gul [] [] (fun _ _ => hN)
      (tableOracle_steps lib T k) (table_bwd lib hT k) () ton () trivial Forall2.nil h

/-- **`table_closed` on products**: `+mink` returns `p` exactly when the
code, run on the table's oracle with enough levels, does. -/
theorem table_closed_zero (lib : Lib) {T : Table Map} (hT : TableOK lib T) {N : Needs} (hN : N ≤ Table.needs T)
    {s f : Noun} {args : List Noun} {c : Straight Map}
    (hF : ContractFwd lib N s f args c) (hB : ContractBwd lib N s f args c) (gul p : Noun) :
    Mink lib gul [] s f (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib T k) () c args [] gul = some (Tone.zero p, ()) := by
  have H := table_closed lib hT hN hF hB gul
  constructor
  · rintro ⟨n, hm⟩
    obtain ⟨ton, hrun, hrel⟩ := H.1 n _ hm
    rw [hrel.zero_right] at hrun
    exact ⟨n, hrun⟩
  · rintro ⟨k, h⟩
    obtain ⟨r, hr, hrel⟩ := H.2 k _ h
    cases hrel
    exact hr

end

namespace Comp

open Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The whole-subject code of a member of `CallTreeD` is closed** by any
table whose entries meet their contracts and whose needs are those of the
class: on every subject of the class, `+mink` returns `p` exactly when the
code does on the table's oracle. -/
theorem closed_callTreeD (lib : Lib) {env : CallEnv} {T : Table Map} (hT : TableOK lib T)
    {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeD lib env (Table.needs T) P x f nm)
    {c : Straight Map} (hc : finishLUCM (S := S) env nm = some c) {s : Noun} (hs : P s) (gul p : Noun) :
    Mink lib gul [] s f (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib T k) () c [s] [] gul = some (Tone.zero p, ()) :=
  have H := (finishLUCM_contractCallTreeD (S := S) lib h hc).2 s hs
  table_closed_zero lib hT (Needs.le_refl _) H.1 H.2 gul p

/-- The table of one bell: its n-ary code `cN` and its whole-subject code
`cW`. -/
def table2 (bZ : Bell) (cN cW : Straight Map) : Table Map := fun b m =>
  if b = bZ then (if m then some cW else some cN) else Option.none

theorem table2_needs (bZ : Bell) (cN cW : Straight Map) :
    Table.needs (table2 bZ cN cW) bZ false = some cN.need ∧
      Table.needs (table2 bZ cN cW) bZ true = some cW.need := by
  simp [Table.needs, table2]

/-- **The table of `[0 axe]` meets its contracts**: the n-ary entry is the
final pass with calls (`finishLFC`, nothing baked), the whole-subject entry
`+compile-unary` (`finishLUCM`), for a bell whose formula is `[0 axe]` and
whose cape has no `[| |]`. -/
theorem tableOK_slot (lib : Lib) {env : CallEnv} {bZ : Bell} {axe : Nat} (hfol : bZ.fol = slot axe)
    {cape : Cape} {data : Noun} (hbl : bZ.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {cN cW : Straight Map}
    (hN : finishLFC (S := S) env (Nomm.n0 axe) ord cape (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) env (Nomm.n0 axe) = some cW) :
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
      exact finishLF_bellContractP (S := S) (code := fun _ => Option.none) (fun _ _ h => by simp at h) rfl
        (by rw [hfol]; exact Annot.n0) (FragP.frag (nm := Nomm.n0 axe) trivial) (by simp [sixCount]) hbl hn (fun _ => rfl)
        (by rw [← finishLFC_eq env (by rfl)]; exact hN) _
    | true =>
      simp only [if_true, Option.some.injEq] at hc
      subst hc
      exact (finishLUCM_bellContractCallTreeD (S := S) (x := true)
        (by rw [hfol]; exact CallTreeD.n0 axe) hW).2
  · simp at hc

/-- The direct call `[2 [0 1] [1 b.fol] b]`. -/
def slotCall (bZ : Bell) : Nomm := Nomm.n2 (Nomm.n0 1) (Nomm.n1 bZ.fol) (some (bZ, Option.none))

/-- Its formula `[2 [0 1] [1 b.fol]]`. -/
def slotCallFol (bZ : Bell) : Noun := n3 (A 2) (slot 1) (C (A 1) bZ.fol)

/-- `[0 1]` returns the subject. -/
theorem mink_slot1 {lib : Lib} {gul x y : Noun} (h : Mink lib gul [] x (slot 1) (Tone.zero y)) : y = x := by
  have e := Mink.det h ⟨1, minkStep_axis1 _ _ _ _ _⟩
  cases e; rfl

/-- **The direct call is in `CallTreeD`** at the table's needs, on the
subjects of the callee's bell, when the need `+callee-need` reads is the
need of the n-ary entry. -/
theorem callTreeD_slotCall (lib : Lib) {env : CallEnv} {bZ : Bell} {cN cW : Straight Map}
    (hring : env.ring bZ = Option.none) (hneed : env.need bZ = some cN.need) (hpure : env.pure bZ = false)
    (hcod : env.cod bZ = some false) :
    CallTreeD lib env (Table.needs (table2 bZ cN cW)) (SkaModel.Fits bZ.less) true (slotCallFol bZ)
      (slotCall bZ) :=
  CallTreeD.direct (CallTreeD.n0 1) hring hneed (table2_needs bZ cN cW).1 (table2_needs bZ cN cW).2 hpure hcod rfl
    (fun x gul y hx hm => by rw [mink_slot1 hm]; exact hx)

/-- **The first closed theorem with a direct call**: the whole-subject code
of `[2 [0 1] [1 [0 axe]] b]` (a `%jmp` to the n-ary entry when the subject
splits by its need, else a `%jsp` to the whole-subject entry), run on the
interpreter's oracle on the table that holds `b`'s two entries, returns `p`
exactly when `+mink` does, on every subject of `b`.  Hypotheses only on the
needs (the need read is the n-ary entry's, no jet, not pure, hinted) and on
the bell (its formula is `[0 axe]`, its cape has no `[| |]`). -/
theorem closed_slotCall (lib : Lib) {env : CallEnv} {bZ : Bell} {axe : Nat} (hfol : bZ.fol = slot axe)
    {cape : Cape} {data : Noun} (hbl : bZ.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {cN cW c : Straight Map}
    (hN : finishLFC (S := S) env (Nomm.n0 axe) ord cape (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) env (Nomm.n0 axe) = some cW)
    (hring : env.ring bZ = Option.none) (hneed : env.need bZ = some cN.need) (hpure : env.pure bZ = false)
    (hcod : env.cod bZ = some false)
    (hc : finishLUCM (S := S) env (slotCall bZ) = some c) {s : Noun} (hs : SkaModel.Fits bZ.less s) (gul p : Noun) :
    Mink lib gul [] s (slotCallFol bZ) (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib (table2 bZ cN cW) k) () c [s] [] gul = some (Tone.zero p, ()) :=
  closed_callTreeD (S := S) lib (tableOK_slot (S := S) lib hfol hbl hn hN hW)
    (callTreeD_slotCall lib hring hneed hpure hcod) hc hs gul p

/-- **The same under `%4`**: `[4 [2 [0 1] [1 [0 axe]] b]]`, whose code calls
the n-ary entry by `%cal` and the whole-subject entry by `%csl`, both hopping
to the merge block. -/
theorem closed_slotCallFour (lib : Lib) {env : CallEnv} {bZ : Bell} {axe : Nat} (hfol : bZ.fol = slot axe)
    {cape : Cape} {data : Noun} (hbl : bZ.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {cN cW c : Straight Map}
    (hN : finishLFC (S := S) env (Nomm.n0 axe) ord cape (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) env (Nomm.n0 axe) = some cW)
    (hring : env.ring bZ = Option.none) (hneed : env.need bZ = some cN.need) (hpure : env.pure bZ = false)
    (hcod : env.cod bZ = some false)
    (hc : finishLUCM (S := S) env (Nomm.n4 (slotCall bZ)) = some c) {s : Noun} (hs : SkaModel.Fits bZ.less s)
    (gul p : Noun) :
    Mink lib gul [] s (n2 (A 4) (slotCallFol bZ)) (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib (table2 bZ cN cW) k) () c [s] [] gul = some (Tone.zero p, ()) :=
  closed_callTreeD (S := S) lib (tableOK_slot (S := S) lib hfol hbl hn hN hW)
    (CallTreeD.four (callTreeD_slotCall lib hring hneed hpure hcod)) hc hs gul p

end Comp
end SkaModel
end Formalization
