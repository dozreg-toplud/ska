import lemmas.Compiler.PokeLinkRestCut
import lemmas.Compiler.PokeLinkSka

/-!
# The baking half `spRest` of `+ska-poke`, push by push

`spRest` runs on `spAfter` (`Compiler/SkaPoke.lean`):
`[dats [root-datum [pruned [[g regs] [root-identity T0]]]]]`, `T0` the
subject of the trap with `lon = [jets [memo [code [calls [vars seek]]]]]`.
Its cut is `spRest_cut` (`PokeLinkRestCut.lean`).  Here the subjects
between the pushes, as functions of the model's values, and the pushes
that compute nothing or only plumb:

* `spRest_three` (PROVED): pushes 0 to 2.  `dat` and `jetted` are gates
  built on the subject (their values are `[bat [bunt subject]]`, no
  computation), and `root-bell` is `[less-code.root-datum fol]`, the noun of
  the model's `E.root` (`srRootN_eq`: `(pokeEnv ..).root.toNoun`).
* `srK3_run` (PROVED): pushes 3 to 6, the `=^  baked  vars.lon` around the
  call of `+bake-graph`: once the call returns `[bk vr]`, the rest runs on
  `[bk S3']`, `S3'` the subject with `vars` replaced by `vr`.
* `srK7_run` (PROVED): push 7, `new-code` pushed.
* `srK8_run` (PROVED): pushes 8 and 9, `sccs` pushed and the loop's `lon`
  written back.

The parts that compute, with their exact statements (open):

* `BakeLinkAt`: the call of `+bake-graph` (push 4, 21 cells, the arm `5622`
  of the core, with the gates `dat` and `jetted` slammed inside it) returns
  the noun of `bakeGraph E n` at the model's fuel `n = bf E`.  An equation,
  so it includes `BakeEnds` (LEDGER 3.3): where the pill's worklist ends,
  the model's ends within the fuel `n`.  The gates' links it needs are
  `DatLinkAt` (the gate `dat` slammed on a bell is the unit of `pokeDatF`)
  and `JetLinkAt` (the gate `jetted` is `jet`).
* `NewCodeLinkAt`: push 7 (85 cells, `~(rep by baked)` with `has:by` into
  `code`) returns `newCode code baked`.
* `LoopLinkAt`: pushes 8 and 9 (`+tarjan` 188 cells and the SCC loop 243
  cells) write `code` = the old code with the new bells and the flags `fl`
  of the new table; the order `+tarjan` gives is not observable in it.
* `TailLinkAt`: pushes 10 to 13 and the end (`new-cores` 54, `jets.lon` 45,
  `seek` 106, `calls` 106, `+ska-cole-update` 45) give
  `[[root-bell (flop new.regs)] lon']` with `seek` and `calls` of the new
  table and the jets noun `jets'`.

Checked against the real compiler first (`tools/hoon/sprestdump.hoon`, 21
`%full` pokes, output `sprestdump.txt`): at every poke the root bell, the
memo, `vars`, the keys of `code`/`calls`/`seek` (old keys and the keys of
`baked`), the old entries kept, the new entries from `baked`, the closure of
the table (every callee is a key), the flags (equal to the replay of the SCC
loop over the WHOLE table, from `[| |]`), and the jets (`+ska-cole-update`
of the edited jets on the new keys) are as the model says; two pokes have an
SCC of two bells.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- The noun of an entry of `baked` / `new-code`: `[nomm calls seek]`. -/
noncomputable def varEntryNoun (e : VarEntry FinMap) : Noun :=
  C e.nomm.toNoun (C (FinMap.setNoun e.calls) e.seek.toNoun)

/-- `dat`, with the whole datum (the pill's gate returns the datum noun; the
model's `pokeDat` keeps its `core`, `pokeDat_eq`). -/
noncomputable def pokeDatF (dats : FinMap Bell (FDatum FinMap)) (memo : Memo FinMap) (b : Bell) : Option (FDatum FinMap) :=
  match Treap.get dats b with
  | some d => some d
  | none => (Treap.get (gutMi memo b.fol) b.less).map fun e => e.2

theorem pokeDat_eq (dats : FinMap Bell (FDatum FinMap)) (memo : Memo FinMap) (b : Bell) :
    pokeDat dats memo b = (pokeDatF dats memo b).map fun d => d.core := by
  unfold pokeDat pokeDatF
  cases Treap.get dats b <;> simp [Option.map_map]
  rfl

section Subjects

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- The subject of `spRest`, with `lonRest = [code [calls [vars seek]]]`. -/
noncomputable def srS0 : Noun :=
  spAfter (fun x : Noun => x) root r1 r2 r3 r4 jRest (C codeN (C callsN (C varsN seekN))) hotN gr r

/-- The gate `dat` on a subject. -/
noncomputable def datG (s : Noun) : Noun := C srDatBat (C srDatBunt s)

/-- The gate `jetted` on a subject. -/
noncomputable def jetG (s : Noun) : Noun := C srJetBat (C srJetBunt s)

/-- The noun of `root-bell`. -/
noncomputable def srRootN : Noun := Bell.toNoun ⟨r.2.2.2.1.less, root.2⟩

/-- The subject after pushes 0 to 2, `[jetted [root-bell [dat s0]]]`, with
the gates built on `g0`: the later pushes edit `s0` (the spine), not the
subjects the gates closed over. -/
noncomputable def srS3x (g0 s0 rootN : Noun) : Noun := C (jetG (C rootN (C (datG g0) g0))) (C rootN (C (datG g0) s0))

/-- The subject after pushes 0 to 2. -/
noncomputable def srS3 : Noun :=
  srS3x (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r)
    (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) (srRootN root r)

/-- `root-bell` is the root of the model's environment of `+bake-graph`. -/
theorem srRootN_eq (jt : Bell → Bool) (fold frozen : Bool) (vars : FinMap Bell (FinMap Bell Unit)) :
    srRootN root r = (pokeEnv jt fold frozen vars root r.2.1 r.2.2.1 r.2.2.2.1).root.toNoun := rfl

/-- **Pushes 0 to 2 of `spRest`**: the gates `dat` and `jetted` are built and
`root-bell` is read. -/
theorem spRest_three :
    nock (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) spRest =
      nock (srS3 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) srK3 := by
  rw [spRest_cut]
  simp only [srK0, srK1, srK2, srDat, srJet, srRoot, srS3, srS3x, datG, jetG, srRootN, srS0, spAfter, spT0,
    FDatum.toNoun, identNoun, Bell.toNoun, nock_exec, Option.bind_some]

/-- **Pushes 3 to 6** (`=^  baked  vars.lon  (bake-graph ..)`): once the
call of `+bake-graph` returns `[bk vr]`, the rest runs on `[bk S3']` with
`vars` replaced by `vr`. -/
theorem srK3_run (g0 rN bk vr : Noun)
    (hb : nock (srS3x g0 (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) rN) srBake = some (C bk vr)) :
    nock (srS3x g0 (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) rN) srK3 =
      nock (C bk (srS3x g0 (srS0 root r1 r2 r3 r4 jRest codeN callsN vr seekN hotN gr r) rN)) srK7 := by
  have e : nock (srS3x g0 (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) rN) srK3 =
      (nock (srS3x g0 (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) rN) srBake).bind fun res =>
        nock (C res (srS3x g0 (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) rN)) srK5 := by
    simp only [srK3, srK4, srBakeId, nock_exec, Option.bind_some]
  rw [e, hb, Option.bind_some]
  simp only [srK5, srK6, srVarsEd, srSwap, srS3x, srS0, spAfter, spT0, nock_exec, Option.bind_some]

/-- **Push 7**: `new-code` pushed. -/
theorem srK7_run (s ncN : Noun) (h : nock s srNew = some ncN) : nock s srK7 = nock (C ncN s) srK8 := by
  simp only [srK7, nock_exec, h, Option.bind_some]

/-- **Pushes 8 and 9**: `sccs` pushed, then the loop's product written. -/
theorem srK8_run (s q s' : Noun) (hq : nock s srSccs = some q) (hl : nock (C q s) srLoop = some s') :
    nock s srK8 = nock s' srK10 := by
  simp only [srK8, srK9, nock_exec, hq, hl, Option.bind_some]

end Subjects

/-! ## The parts that compute: exact statements (open) -/

section Parts

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- **The gate `dat`** (push 0, 101 cells: `get:by` on `dats`, `gut:mi` and
`get:by` on the memo) slammed on a bell is the unit of `pokeDatF` of the
poke's datums and memo. -/
def DatLinkAt : Prop :=
  ∀ b : Bell, nock (C srDatBat (C b.toNoun (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r)))
    srDatBat = some (unitNoun FDatum.toNoun (pokeDatF r.2.1 r.2.2.1 b))

/-- **The gate `jetted`** (push 2, 86 cells: `has:by` on `call.cole`, the gate
`dat`, `+cole-match` on `core.regs`, `arms.regs` and `hot`) slammed on a bell
is the loobean of `jt`. -/
def JetLinkAt (jt : Bell → Bool) : Prop :=
  ∀ b : Bell, nock (C srJetBat (C b.toNoun (C (srRootN root r) (C (datG (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r))
      (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r))))) srJetBat =
    some (A (if jt b then 0 else 1))

/-- The spine after push 6 with `code` and `vars` replaced by `c` and `v`, the
gates on the original subject. -/
noncomputable def srSp (c v : Noun) : Noun :=
  srS3x (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r)
    (srS0 root r1 r2 r3 r4 jRest c callsN v seekN hotN gr r) (srRootN root r)

/-- **The call of `+bake-graph`** (push 4) returns the noun of the model's
`bakeGraph E n`: `[baked vars']`.  An equation: it says both that the pill's
product is the model's, and that where the pill's worklist ends the model's
ends within the fuel `n` (`BakeEnds`, LEDGER 3.3). -/
def BakeLinkAt (E : BEnv FinMap) (n : Nat) : Prop :=
  nock (srS3 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) srBake =
    (bakeGraph E n).map fun bg => C (bg.1.toNoun varEntryNoun) (bg.2.toNoun FinMap.setNoun)

/-- **`new-code`** (push 7): on `[baked S3']`, the variants of `baked` that
`code` does not have (`code` the table `codeN` encodes). -/
def NewCodeLinkAt (code baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) : Prop :=
  nock (C (baked.toNoun varEntryNoun) (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr)) srNew =
    some ((newCode code baked).toNoun varEntryNoun)

/-- **The SCC order and the SCC loop** (pushes 8, 9): `code` becomes the
noun of the new table with the flags `fl`; nothing else in the subject
changes. -/
def LoopLinkAt (fl : Flags) (code nc baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) : Prop :=
  ∃ q, nock (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr))) srSccs = some q ∧
    nock (C q (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr)))) srLoop =
    some (C q (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r (codeNoun fl (addCode code nc)) vr))))

/-- **The tail** (pushes 10 to 13 and the end): `new-cores`, the edit of
`jets.lon`, the writes of `seek` and `calls`, `+ska-cole-update`, the
product `[[root-bell (flop new.regs)] lon']`, with the new jets noun `j'` and
the registrations' noun `newN`, on every `sccs` noun `q` (the tail does not
read it). -/
def TailLinkAt (fl : Flags) (code nc baked : FinMap Bell (VarEntry FinMap)) (vr j' newN : Noun) : Prop :=
  ∀ q, nock (C q (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r (codeNoun fl (addCode code nc)) vr)))) srK10 =
    some (C (C (srRootN root r) newN) (C j' (C (memoNoun r.2.2.1) (C (codeNoun fl (addCode code nc))
      (C ((addCode code nc).toNoun fun e => FinMap.setNoun e.calls)
        (C vr ((addCode code nc).toNoun fun e => e.seek.toNoun)))))))

/-- **`spRest` from its parts**: if the model's bake returns `bg` and the
four parts hold, `spRest` returns the product of the tail. -/
theorem spRest_of_parts (fl : Flags) (E : BEnv FinMap) (n : Nat) (code : FinMap Bell (VarEntry FinMap))
    (bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)) (j' newN : Noun)
    (hbg : bakeGraph E n = some bg)
    (hB : BakeLinkAt root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r E n)
    (hN : NewCodeLinkAt root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r code bg.1 (bg.2.toNoun FinMap.setNoun))
    (hL : LoopLinkAt root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r fl code (newCode code bg.1) bg.1
      (bg.2.toNoun FinMap.setNoun))
    (hT : TailLinkAt root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r fl code (newCode code bg.1) bg.1
      (bg.2.toNoun FinMap.setNoun) j' newN) :
    nock (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) spRest =
      some (C (C (srRootN root r) newN) (C j' (C (memoNoun r.2.2.1) (C (codeNoun fl (addCode code (newCode code bg.1)))
        (C ((addCode code (newCode code bg.1)).toNoun fun e => FinMap.setNoun e.calls)
          (C (bg.2.toNoun FinMap.setNoun) ((addCode code (newCode code bg.1)).toNoun fun e => e.seek.toNoun))))))) := by
  rw [spRest_three]
  have hb : nock (srS3 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) srBake =
      some (C (bg.1.toNoun varEntryNoun) (bg.2.toNoun FinMap.setNoun)) := by
    rw [hB, hbg]; rfl
  unfold srS3 at hb ⊢
  simp only [NewCodeLinkAt, LoopLinkAt, TailLinkAt, srSp] at hN hL hT
  rw [srK3_run root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r _ _ _ _ hb]
  rw [srK7_run _ _ hN]
  obtain ⟨q, hq, hl⟩ := hL
  rw [srK8_run _ _ _ hq hl]
  exact hT q

end Parts

end Compiler
end Formalization
