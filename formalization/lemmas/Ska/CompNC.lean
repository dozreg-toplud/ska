import lemmas.Ska.CompFragF

/-!
# One induction over the nomms that call: the class `NC` and its hypothesis

README Gaps 12.22.  The fragment `FragI` (`CompFragF.lean`) is a list of
special cases, one per goal shape met so far.  This file states ONE
induction hypothesis, `NCOK`, and the plain inductive class `NC` on which it
is proved by structural induction on the nomm (`CompNCInd.lean`).

## The raw blocks that fix the hypothesis

`tools/hoon/calldump4.hoon` (whole-subject version, subject unknown, before
`+optimize`; `vN` registers, `N` labels).

1. `+split` puts `con` at a goal entry's block.  `[7 [[0 2] [0 3]] [[2 [0 2]
   [0 6]] [0 1]]]` (`%bc1`): `q`'s run leaves the bond of `+past` at block
   `3` with the need `this v3` (the tail `[0 1]` of `q`), and the cons `p`
   runs under it.  `+split` of `this v3` puts `con v7 v8 v3` at block `3` and
   keeps both halves there, so the final block is `3: mov v0 vg, cel vg, hed
   vg vi, mov vi v7, tal vg vh, mov vh v8, con v7 v8 v3, hop 2`.  The result
   entry at `3` (made by `q`, kept by `p`) has the body `[con v7 v8 v3]`,
   which `RunOKLC.labs`, `RunOKGC.labs` and `AgreeL` (every result entry's
   block empty) exclude.  This is a run under `%done`: `UOKC` itself is false
   for this nomm.
2. `+copy` puts a `mov` at a goal entry's block.  `[7 [[0 1] [0 1]] [[2 [0 2]
   [0 6]] [[0 2] [0 3]]]]` (`%bc2`): the bond at block `5` asks `pair (this
   v4) (this v5)`, `+split` puts nothing, both halves `[0 1]` keep their
   halves at `5`, and `+copy-lazy` merges them with `mov v4 v5` at `5`:
   `5: mov v0 v4, mov v4 v5, hop 3`.
3. `+collapse-lazy-atom` reads the goal's register.  `[7 [4 [0 3]] [[2 [0 1]
   [0 1]] [0 1]]]` (`%s4t`): `q`'s result asks `this v5` (the call's subject)
   and has a bond at `3` asking `this v3`; `p = [4 [0 3]]` writes `v5`
   (`8: inc v8 v5`) and puts `mov v5 v3` at the bond block (`3: mov v5 v3`,
   behind the call `5: nok v5 v6 v4`).  The register its ops read is the
   goal's `v5`, allocated before `p`'s run, so `RunOKLC.dreg` (the witness
   allocated in the run) is false, and `q`'s `sem` would have to keep its own
   result register `v5` (strict input need) to reach the bond block.
4. `%10` at a bond: `[7 [10 [2 [0 3]] [0 1]] [[2 [0 2] [0 6]] [0 1]]]`
   (`%s10`): `3: ..., mov v8 v7, con v7 v8 v3, hop 2`, the body of 1.

What does not break the relations: `%lim` (`[8 [0 3] [[2 [0 2] [0 6]] [0
3]]]`) has the bond need `pair none (this v3)`, so `+split` puts no `con`
and the tail `[0 1]` keeps `this v3` alone (`3: mov v0 v3`); the leaves keep
or consume entries without ops (`[0 axe]`) or with constants (`[1 k]`,
`%h1`: `3: imm 7 v2`); the indirect call's `+kern` reads a fresh register;
`+collapse-lazy-atom` under a goal whose sure part asks nothing reads a
fresh register (`%h4c`, `%h3`, `%h5`: the bond block reads `v7`, `v9`).

## The hypothesis

The right hypothesis for all of `NC` is `RunOKLC` with two changes, which
the next session makes: (a) a result entry's block may have a body `B`
(`labs`: `⟨[], B, hop th⟩`; `AgreeL`: the program's block is `A ++ B`
unproxied with `A` filling the entry), as 1, 2 and 4 show; (b) the input
need may contain the run's own result registers, kept (the relaxed `InR`,
`KeepI` of `CollRunU`), as 3 shows.  Since every proof of the call
fragment uses the strict relations, this session states the hypothesis in
them, with three levels of goals:

* level `0` (`U`): `%done` and every fork-free `%next` (`UOKC`);
* level `1` (`B`): also every `%next L th` whose sure part asks nothing,
  any entries (`LOKCS`): the bond goal of a cons head behind a calling tail;
* level `2` (`L`): every `%next L th` (`LOKC`).

`NCOK lv t`: on every `Annot`, `UOKC`, `LOKCS` from level `1`, `LOKC` at
level `2`, and with `t` the jump facts `JNew` and `EntNew` (a hinted nomm's
code begins at a new block), which the cons and `[7 p q]` read of their
parts.  By 1 to 4 the cons and `%10` are at level `0` only, and `%3`, `%4`,
`%5` at level `1` only; nothing else is lost.

## The class `NC lv t`

* `[0 axe]`, `[1 k]`: any level, `t`.
* `[3 p]`: `p` at the level (under a goal that asks nothing `p` runs under
  it), level at most `1`.
* `[4 p]`, `[5 p q]`: parts at level `0`, level at most `1`.
* the cons: tail at level `0`, head at level `1` when the tail calls (the
  bond goal) and `0` else; level `0`.
* `[7 p q]`: `q` at the level, `p` at level `2` (`q`'s result may be any
  lazy need) (`sevenE`), or, at level `0`, `p` at level `0` when `q`'s run
  returns no entries (`NoEntF q`, `sevenN`).
* the indirect call `[2 p q]`: parts at level `0`, any level; `q` not the
  literal of a `%bare` formula (`bareLitQ`, the one exclusion: its nomm
  makes one `nok` of the formula itself with all of `+mink`'s fuel,
  `CompIndirectWrap.lean`).
* `[10 [a v] q]`: call-free parts (`FragU`), level `0`.
* `pure`: any call-free nomm of `FragU` (`%6` included), level `0`, no `t`.
* weakening of the level and of `t`.

## The cases (`ok` proved, `open` with the reason)

Level `0` is `UOKC` (and `t`), levels `1`, `2` are `LOKCS`, `LOKC`.

| case | level | from | status |
|---|---|---|---|
| `[0 axe]` | 0 | `uokcU`, `jNew_n0` | ok |
| `[0 axe]`, `1 ≤ axe` | 2 | `lokc_n0A` | ok |
| `[0 0]` | 2 | `+bomb` under a lazy goal | work |
| `[1 k]` | 0 | `uokcU`, `jNew_n1` | ok |
| `[1 k]` | 2 | `+mede` under a lazy goal | work |
| `[3 p]`, `p` pure | 0 | `uokcU` | ok |
| `[3 p]`, `p` calls | 0 | `+forl`, `clq` after `p`'s call | work |
| `[3 p]` | 1 | `+collapse-lazy-atom` with a fresh register | work |
| `[4 p]`, `p` pure | 0 | `uokcU` | ok |
| `[4 p]`, `p` pure | 1 | `runOKL_n4_none` | ok (assembly) |
| `[4 p]`, `p` calls | 0 | the `inc` block after `p`'s call | work |
| `[4 p]`, `p` calls | 1 | `+collapse-lazy-atom`, then the call | work |
| `[5 p q]`, pure | 0 | `uokcU` | ok |
| `[5 p q]`, calls | 0, 1 | `pairLC_ok` with `eqq` | work |
| cons | 0 | `uokc_consEA` (`BondOKC` from `LOKCS`) | ok (assembly) |
| `[7 p q]`, `sevenN` | 0 | `uokc_sevenA` | ok (assembly) |
| `[7 p q]`, `sevenE` | 0 | `uokc_sevenLA` (`n7`, `inline`, `n9`) | ok, `n8l` work |
| `[7 p q]`, `sevenE` | 1, 2 | `runOKLC_sevenM` on every form | work |
| `[2 p q]` | 0 | `uokc_indDA` | ok |
| `[2 p q]` | 2 | `lokc_indirectC` on every form | work |
| `[10 [a v] q]`, pure | 0 | `uokcU` | ok |
| `[10 [a v] q]`, calls | 0 | `+into`, `+past`, `+copy` | open |
| `JNew` of every constructor | | `+copy`'s block, `p`'s jump | work |

The work list, cheapest first: `[0 0]` at level `2`; `[2 p q]` at level
`2`; `JNew`; `[7 p q]` at levels `1`, `2`; `[4 p]` with calls; `[1 k]` at
level `2`; `[3 p]` with calls and at level `1`; `[5 p q]` with calls and
at level `1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The levels -/

/-- **Level `1`: runs under a lazy goal whose sure part asks nothing**
(`LOKC` with `L.sure.ned = none`), any entries: the bond goal of `+past`
among them. -/
structure LOKCS (lib : Lib) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    L.sure.ned = Need.none →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ th', HoonMap.get g0.blocks e.1 = some ⟨[], [], Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLC (Map := Map) lib P f L th Q g0 g1 nex) ∧ (nex.th = th ∨ g0.bo ≤ nex.th.there)

theorem LOKC.toS {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : LOKC (S := S) (Map := Map) lib env P f nm) : LOKCS (S := S) (Map := Map) lib env P f nm :=
  ⟨h.clean, fun _ hc b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed hr =>
    h.run hc b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed hr⟩

/-- **The bond goal is a goal of level `1`**: `LOKCS` gives `BondOKC`. -/
theorem LOKCS.toBond {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : LOKCS (S := S) (Map := Map) lib env P f nm) : BondOKC (S := S) (Map := Map) lib env P f nm := by
  refine ⟨fun {sup region g0 g1 nex hed b th} hr => h.clean (by simp [Sure.bunt, Clean]) hr,
    fun {sup region g0 g1 nex hed b th jb} hc b0 d0 hu hcl hcb h1 h2 ha hne hb hbb hd hen hr => ?_⟩
  have e1 : entries (Lazy.mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]) = [(b, ofSure hed)] := entries_bond1 b hed
  exact (h.run (by simp [Sure.bunt]) hc b0 d0 hu hcl hcb h1 h2 ha (by simp [Sure.bunt, Distinct])
    (fun x hx => by simp [Sure.bunt, NMem] at hx)
    (fun e he => by rw [e1] at he; simp only [List.mem_singleton] at he; subst he; exact ⟨hb, _, hbb⟩)
    (by rw [e1]; simp) (fun e he => by
      rw [e1] at he; simp only [List.mem_singleton] at he; subst he
      exact ⟨hd, fun x hx => hen x hx⟩) hr).1

theorem LOKCS.wrap {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f f' : Noun} {nm : Nomm}
    (W : WrapRel lib P f f') (B : LOKCS (S := S) (Map := Map) lib env P f nm) :
    LOKCS (S := S) (Map := Map) lib env P f' nm :=
  ⟨B.clean, fun hs hc b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed h => by
    obtain ⟨⟨Q, R⟩, j⟩ := B.run hs hc b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed h
    exact ⟨⟨Q, R.wrap W⟩, j⟩⟩

/-! ## The hypothesis -/

/-- **The induction hypothesis** at level `lv` with the jump facts when
`t`: on every `Annot` of `nm`, `UOKC`; with `t`, `JNew` and, for a hinted
nomm, `EntNew`; from level `1`, `LOKCS`; at level `2`, `LOKC`. -/
def NCOK (lib : Lib) (code : Bell → Option Nomm) (env : CallEnv) (lv : Nat) (t : Bool) (nm : Nomm) : Prop :=
  ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f nm →
    UOKC (S := S) (Map := Map) lib env P f nm ∧
    (t = true → JNew (S := S) (Map := Map) env nm ∧
      (hinted env.cod nm = some true → EntNew (S := S) (Map := Map) env nm)) ∧
    (1 ≤ lv → LOKCS (S := S) (Map := Map) lib env P f nm) ∧
    (2 ≤ lv → LOKC (S := S) (Map := Map) lib env P f nm)

theorem NCOK.weak {lib : Lib} {code : Bell → Option Nomm} {env : CallEnv} {lv lv' : Nat} {t t' : Bool}
    {nm : Nomm} (h : NCOK (S := S) (Map := Map) lib code env lv t nm) (hl : lv' ≤ lv) (ht : t' = true → t = true) :
    NCOK (S := S) (Map := Map) lib code env lv' t' nm := fun hA =>
  ⟨(h hA).1, fun e => (h hA).2.1 (ht e), fun l => (h hA).2.2.1 (by omega), fun l => (h hA).2.2.2 (by omega)⟩

/-! ## The class -/

/-- **The class of the induction**: `NC lv t nm` when `nm` meets `NCOK lv
t` by the cases of the header.  No shape condition but `bareLitQ` of the
indirect call's formula part (the `%bare` literal). -/
inductive NC : Nat → Bool → Nomm → Prop
  | n0 {lv : Nat} {axe : Nat} : NC lv true (Nomm.n0 axe)
  | n1 {lv : Nat} {k : Noun} : NC lv true (Nomm.n1 k)
  | n3 {lv : Nat} {t : Bool} {p : Nomm} : lv ≤ 1 → NC lv t p → NC lv t (Nomm.n3 p)
  | n4 {lv : Nat} {t : Bool} {p : Nomm} : lv ≤ 1 → NC 0 t p → NC lv t (Nomm.n4 p)
  | n5 {lv : Nat} {t t' : Bool} {p q : Nomm} : lv ≤ 1 → NC 0 t p → NC 0 t' q → NC lv (t && t') (Nomm.n5 p q)
  | cons {t t' : Bool} {p q : Nomm} : NC (if q.pure then 0 else 1) t p → NC 0 t' q →
      (q.pure = false → t' = true) → NC 0 t (Nomm.cons p q)
  | sevenE {lv : Nat} {t t' : Bool} {p q : Nomm} : NC lv t q → NC 2 t' p → NC lv (t && t') (Nomm.n7 p q)
  | sevenN {t t' : Bool} {p q : Nomm} : NC 0 t q → NoEntF q → NC 0 t' p → NC 0 (t && t') (Nomm.n7 p q)
  | ind {lv : Nat} {t t' : Bool} {p q : Nomm} : NC 0 t p → NC 0 t' q → bareLitQ q = false →
      NC lv true (Nomm.n2 p q Option.none)
  | ten {a : Nat} {v q : Nomm} : FragU (S := S) v → FragU (S := S) q → NC 0 true (Nomm.n10 a v q)
  | pure {nm : Nomm} : FragU (S := S) nm → NC 0 false nm
  | down {lv lv' : Nat} {t : Bool} {nm : Nomm} : NC lv t nm → lv' ≤ lv → NC lv' t nm
  | forget {lv : Nat} {nm : Nomm} : NC lv true nm → NC lv false nm

/-- A nomm with no direct call and no hint: its `+hinted` is whether it calls. -/
def NoDirect : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => NoDirect p
  | Nomm.n4 p => NoDirect p
  | Nomm.n5 p q => NoDirect p ∧ NoDirect q
  | Nomm.cons p q => NoDirect p ∧ NoDirect q
  | Nomm.n7 p q => NoDirect p ∧ NoDirect q
  | Nomm.n10 _ v q => NoDirect v ∧ NoDirect q
  | Nomm.n6 p q r => NoDirect p ∧ NoDirect q ∧ NoDirect r
  | Nomm.n2 p q Option.none => NoDirect p ∧ NoDirect q
  | _ => False

theorem hinted_noDirect (cod : Bell → Option Bool) : ∀ (nm : Nomm), NoDirect nm → hinted cod nm = some (!nm.pure)
  | Nomm.n0 _, _ => rfl
  | Nomm.n1 _, _ => rfl
  | Nomm.n3 p, h => by simp only [hinted, Nomm.pure]; exact hinted_noDirect cod p h
  | Nomm.n4 p, h => by simp only [hinted, Nomm.pure]; exact hinted_noDirect cod p h
  | Nomm.n5 p q, h => by
    simp only [hinted, Nomm.pure, hinted_noDirect cod p h.1, hinted_noDirect cod q h.2]
    cases p.pure <;> cases q.pure <;> rfl
  | Nomm.cons p q, h => by
    simp only [hinted, Nomm.pure, hinted_noDirect cod p h.1, hinted_noDirect cod q h.2]
    cases p.pure <;> cases q.pure <;> rfl
  | Nomm.n7 p q, h => by
    simp only [hinted, Nomm.pure, hinted_noDirect cod p h.1, hinted_noDirect cod q h.2]
    cases p.pure <;> cases q.pure <;> rfl
  | Nomm.n10 _ v q, h => by
    simp only [hinted, Nomm.pure, hinted_noDirect cod v h.1, hinted_noDirect cod q h.2]
    cases v.pure <;> cases q.pure <;> rfl
  | Nomm.n6 p q r, h => by
    simp only [hinted, Nomm.pure, hinted_noDirect cod p h.1, hinted_noDirect cod q h.2.1,
      hinted_noDirect cod r h.2.2]
    cases p.pure <;> cases q.pure <;> cases r.pure <;> rfl
  | Nomm.n2 p q Option.none, h => by simp only [hinted, Nomm.pure]; rfl

end Comp
end SkaModel
end Formalization
