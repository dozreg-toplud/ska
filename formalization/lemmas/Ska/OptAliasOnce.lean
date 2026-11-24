import lemmas.Ska.OptAliasFirst

/-!
# `DefOnceB` of the blocks `+alias` returns, and what is left of the field

## `DefOnceB` of the result is false in general

`DefOnceB` lets a register have, besides its one definition that counts, dead
fills: `%imm` ops in a block ending in `%bom`, followed by `%imm` ops only,
with every reachable read of the register in that block before the fill.  The
read condition is about the blocks before `+alias`.  After the pass a register
`x` whose definition was dropped is read as `old x`, which can be the filled
register in a block that is not the fill's, so the fill is no longer dead and
the register has two definitions that count.  Witness (`nargs = 2`, registers
`0`, `1` the arguments, `topo = [0, 1, 2]`, `rev = revCfg`, any `pick` that
picks a member):

* block `0`: `[%inc 0 2] [%inc 0 3]`, `[%brn 1 [~ 1] [~ 2]]`;
* block `1`: `[%cel 2] [%imm 0 2]`, `[%bom ~]` (a dead fill of `2`, the fill of
  `+crash-need` on the register of the `%inc`);
* block `2`: no op, `[%don 3]`.

The blocks have `DInvS` and `TopoInvR` (`2` has the definition that counts
`(0, 0)` and the dead fill `(1, 1)`, its only read is `[%cel 2]` before the
fill).  `aliasWalk` keeps `[%inc 0 2]` and drops `[%inc 0 3]` (`decOf` of `0`
is `2`), so `old 3 = 2`; block `1` keeps both ops (no immediate `0` is known);
block `2` becomes `[%don 2]`.  In the result `(1, 1)` is no dead fill (block
`2` reads `2`), so `2` has two definitions that count, `(0, 0)` and `(1, 1)`:
`DefOnceB` fails, and with it `AliasRestSSAB` (`AliasSSAB` of the result).
The same happens with `%imm 5` in place of the `%inc` ops.  `+remove-dead-code`
does not restore it: its `saw` is one set for the whole walk over the
reversed `topo`, so the `%imm 0 2` of block `1` is kept once block `2` has put
`2` in it.  The code after is still right, but a later call of `+alias` that
knows an immediate `0` at the fill drops it and renames the read of block `2`:
`OptAliasWitness.lean` checks the witness in Lean (`not_aliasOnceB`, on the
order `[0 2 1]` of `+bb-topo`) and gives blocks with `DInvS` on which the
model of `+optimize` returns `0` where the code before returns `s + 1`
(`w_dinvS`, `w_opt`).

## What holds

* **`alias_restB`**: `PassOK`, `DownPar`, some `TrimBr` and `DefFirst` of the
  result, under `DInvS`, `TopoInvR` and `hpick` alone.
* **`alias_onceB`**: `DefOnceB` of the result when no register with a dead
  fill in a reachable block has a definition that counts (`FillFresh`): a
  definition after maps to one before (`alias_live_op`), and a dead fill before stays one after
  (`alias_fill`, through `DefFirst` of the result: a read after would need a
  definition after before it, which is a definition that counts before, or a
  dead fill before followed by `%imm` ops only).
* **`alias_fillFresh`**: `+alias` keeps `FillFresh` (the op before of a dead
  fill after is a definition that counts, so a definition that counts after
  would be that op).
* **`AliasOnceB`**: `DefOnceB` of the result on every input with `DInvS`,
  the one conjunct left; **`aliasRestSSAB_of_once`** and the driver theorem
  **`optimize_keeps_aliasO`** with `hpick` and `AliasOnceB`.  `AliasOnceB` is
  false (`not_aliasOnceB`), and the conclusion of the driver theorem itself
  fails on blocks with `DInvS` (`w_opt`), so no field closes it: the driver
  needs a stronger invariant of the raw blocks, such as `FillFresh` kept by
  every pass (false on raw `+comp` output, whose fills write a register that
  has a definition), or a change of the Hoon (see the README, Gaps 12.8).
  Both are done since: every pass keeps plain single assignment
  (`OptAliasPlain.lean`, driver `optimize_keeps_plain_pickR` in
  `OptAliasPlainDriver.lean`) and `FillFresh` (`OptAliasFresh.lean`,
  `optimize_keeps_fresh_pickR`), and both hold on raw `+comp` output once
  `+crash-need` stops filling the register it tests.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- No register with a dead fill in a reachable block has a definition that
counts. -/
def FillFresh (bl : Map Blob) : Prop := ∀ r o i, Reach bl o → DeadFill bl r o i → ∀ s, ¬ LiveDef bl r s

/-- The ops kept of a prefix of a body are a prefix of the ops kept of a
longer prefix. -/
theorem abody_take_mono {pick : List Nat → Nat} {ops : List Pole} {st : ABody} {k k' : Nat} (hk : k ≤ k')
    {oa oa' : List Pole} {sa sa' : ABody} (h : aliasBody pick (ops.take k) st = some (oa, sa))
    (h' : aliasBody pick (ops.take k') st = some (oa', sa')) : oa.length ≤ oa'.length := by
  have e := (List.take_append_drop k (ops.take k')).symm
  rw [List.take_take, Nat.min_eq_left hk] at e
  rw [e, aliasBody_append, h, Option.bind_some] at h'
  obtain ⟨⟨o2, s2⟩, -, e2⟩ := Option.map_eq_some_iff.mp h'
  simp only [Prod.mk.injEq] at e2
  rw [← e2.1, List.length_append]
  omega

/-- **The walk of a body split at the `i`-th op kept**: the op `k` it comes
from, the walk of the first `k` ops (which keep `i` ops) and of the rest. -/
theorem abody_split {pick : List Nat → Nat} {ops : List Pole} {st : ABody} {rb : List Pole × ABody}
    (h : aliasBody pick ops st = some rb) {i : Nat} {op' : Pole} (hi : rb.1[i]? = some op') :
    ∃ (k : Nat) (op : Pole) (sta : ABody) (outa outb : List Pole) (st1 st' : ABody), ops[k]? = some op ∧
      aliasBody pick (ops.take k) st = some (outa, sta) ∧ outa.length = i ∧
      aliasOp pick sta op = some (some op', st1) ∧ aliasBody pick (ops.drop k) sta = some (outb, st') ∧
      rb.1 = outa ++ outb := by
  obtain ⟨k, op, sta, outa, st1, hk, hba, hl, hop⟩ := abody_at ops st rb.1 rb.2 h i op' hi
  have hs := h
  rw [← List.take_append_drop k ops, aliasBody_append, hba, Option.bind_some] at hs
  obtain ⟨⟨outb, st'⟩, hbb, es⟩ := Option.map_eq_some_iff.mp hs
  exact ⟨k, op, sta, outa, outb, st1, st', hk, hba, hl, hop, hbb, by rw [← es]⟩

theorem afin_bom {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {u : Option Nat}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o (Termin.bom u) = some r) :
    r.1 = Termin.bom u := by
  simp only [aliasFin, Option.some.injEq] at h; rw [← h]

section
variable {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
  {rev : Map (List Nat)} {gF : AGen Map}

/-- A block after: its block before, the walk of its body, its end. -/
theorem alias_blk (hT : TopoInvR bl topo rev) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF)
    {o : Nat} {b' : Blob} (hb' : HoonMap.get gF.new o = some b') :
    ∃ (b : Blob) (st0 : ABody) (rb : List Pole × ABody) (rf : Termin × (Nat → List Nat) × Bool),
      HoonMap.get bl o = some b ∧ aliasBody pick b.body st0 = some rb ∧
      b' = { par := b.par, body := rb.1, fin := rf.1 } ∧ (∀ u, b.fin = Termin.bom u → rf.1 = Termin.bom u) ∧
      (∀ j' ∈ getJmps rf.1, ∃ j ∈ getJmps b.fin, j.there = j'.there) := by
  obtain ⟨_pre, _l, _g1, _g2, b, st0, rb, rf, _e1, _e2, _e3, _e4, _e5, hb, _e7, hrb, hrf, _e10, hbe⟩ :=
    aw_new hT.1.1 hT.2 h hb'
  exact ⟨b, st0, rb, rf, hb, hrb, hbe, fun u hu => by rw [hu] at hrf; exact afin_bom hrf,
    fun j' hj' => (afin_jmps hrf hj').1⟩

/-- **A dead fill before stays one after** when no register with a dead fill
has a definition that counts: the filled register is then read nowhere after
(`DefFirst` of the result would need a definition after before the read, a
parameter, an op of a block that jumps, or a dead fill followed by `%imm` ops
only, all ruled out). -/
theorem alias_fill (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) (hF : FillFresh bl)
    {o i k r : Nat} {b' b : Blob} {rb : List Pole × ABody} {rf : Termin × (Nat → List Nat) × Bool}
    (hb' : HoonMap.get gF.new o = some b') (hb : HoonMap.get bl o = some b)
    (hbe : b' = { par := b.par, body := rb.1, fin := rf.1 }) (hrf : ∀ u, b.fin = Termin.bom u → rf.1 = Termin.bom u)
    {op : Pole} {sta : ABody} {outa outb : List Pole} {st1 st' : ABody} {op' : Pole} (hk : b.body[k]? = some op)
    (hl : outa.length = i) (hop : aliasOp pick sta op = some (some op', st1))
    (hbb : aliasBody pick (b.body.drop k) sta = some (outb, st')) (hcat : rb.1 = outa ++ outb)
    (hi : rb.1[i]? = some op') (hdf : DeadFill bl r o k) : DeadFill gF.new r o i := by
  have hfirst := alias_defFirst hpick hD hT h
  have hGs := alias_targetsSub hT h
  have hRo : Reach bl o := aliasWalk_reach hT.1.1 hT.2 h o (by rw [hb']; rfl)
  have hdf0 := hdf
  obtain ⟨b5, hb5, ⟨u, hu⟩, ⟨n, hn⟩, himm, -⟩ := hdf
  rw [hb] at hb5; cases hb5
  rw [hk] at hn; cases hn
  have e := aop_rename hop
  subst e
  subst hbe
  have hdrop : rb.1.drop i = outb := by rw [hcat, ← hl]; exact List.drop_left
  have hrG : r ∈ allDefs gF.new :=
    bdef_allDefs hb' (List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hi, rfl⟩))
  refine ⟨_, hb', ⟨u, hrf u hu⟩, ⟨n, hi⟩, fun op2 hop2 => ?_, fun o3 b3 j hR3 hb3 hread => ?_⟩
  · simp only at hop2
    rw [hdrop] at hop2
    obtain ⟨op0, hop0, σ, rfl⟩ := abody_kept _ sta outb st' hbb op2 hop2
    obtain ⟨n0, d0, rfl⟩ := himm op0 hop0
    exact ⟨n0, d0, rfl⟩
  · exfalso
    obtain ⟨p, hπ⟩ := awi_reach_bpath hR3
    have hR3b : Reach bl o3 := reach_sub hGs hR3
    obtain ⟨b3b, st3, rb3, rf3, hb3b, hrb3, hbe3, hrf3, -⟩ := alias_blk hT h hb3
    rcases hfirst o3 p b3 hπ hb3 j r hread hrG with hm | hm | ⟨o', ho', b'', hb'', hm⟩
    · rw [hbe3] at hm
      exact hF r o k hRo hdf0 (o3, none) (awi_par_live hR3b hb3b hm)
    · rw [hbe3] at hm
      obtain ⟨op2, hop2, hd2⟩ := List.mem_filterMap.mp hm
      obtain ⟨j2, hj2⟩ := List.mem_iff_getElem?.mp hop2
      rw [List.getElem?_take] at hj2
      split at hj2
      case isFalse => cases hj2
      rename_i hj2j
      obtain ⟨k2, op3, sta3, outa3, outb3, st13, st3', hk2, hba3, hl3, hop3, -, -⟩ := abody_split hrb3 hj2
      have hd3 : aliasDst op3 = some r := by rw [← hd2, aop_rename hop3, aliasDst_rename]
      by_cases hdf3 : DeadFill bl r o3 k2
      · obtain ⟨b6, hb6, ⟨u3, hu3⟩, -, himm3, -⟩ := hdf3
        rw [hb3b] at hb6; cases hb6
        rw [hbe3] at hread
        rcases hread with hread | ⟨-, hfr⟩
        · simp only at hread
          rw [List.head?_drop] at hread
          cases hx : rb3.1[j]? with
          | none => rw [hx] at hread; simp at hread
          | some op4 =>
            rw [hx] at hread
            simp only [Option.map_some, Option.getD_some] at hread
            obtain ⟨kj, op5, sta5, outa5, outb5, st15, st5', hk5, hba5, hl5, hop5, -, -⟩ := abody_split hrb3 hx
            rw [aop_rename hop5] at hread
            by_cases hkk : k2 ≤ kj
            · have hmem : (b3b.body.drop k2)[kj - k2]? = some op5 := by
                rw [List.getElem?_drop, show k2 + (kj - k2) = kj by omega]; exact hk5
              obtain ⟨n5, d5, rfl⟩ := himm3 op5 (List.mem_of_getElem? hmem)
              simp [renameP, aliasReads, aliasDst, poleRegs] at hread
            · have := abody_take_mono (by omega : kj ≤ k2) hba5 hba3
              omega
        · simp only at hfr
          rw [hrf3 u3 hu3] at hfr
          simp [finRegs] at hfr
      · exact hF r o k hRo hdf0 (o3, some k2) ⟨hR3b, ⟨b3b, op3, hb3b, hk2, hd3⟩, fun i0 hi0 hd => by
          cases hi0; exact hdf3 hd⟩
    · have hRo' : Reach gF.new o' := ssk_bpath_reach hπ o' (List.mem_cons_of_mem _ ho')
      have hRo'b : Reach bl o' := reach_sub hGs hRo'
      obtain ⟨b8, j8, hb8, hj8⟩ := bdef_jumps hπ rfl o' ho'
      rw [hb''] at hb8; cases hb8
      obtain ⟨bo, sto, rbo, rfo, hbo, hrbo, hbeo, -, hjmo⟩ := alias_blk hT h hb''
      rw [hbeo] at hj8 hm
      obtain ⟨j9, hj9, -⟩ := hjmo j8 hj8
      rcases List.mem_append.mp hm with hm | hm
      · exact hF r o k hRo hdf0 (o', none) (awi_par_live hRo'b hbo hm)
      · obtain ⟨i9, op9, hi9, he9⟩ := bdef_idx (abody_dsts hrbo hm)
        exact hF r o k hRo hdf0 (o', some i9) (awi_jump_live hRo'b hbo hj9 hi9 he9)

/-- **A definition that counts after at an op** is one before, at the op it
was kept from. -/
theorem alias_live_op (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) (hF : FillFresh bl)
    {o i r : Nat} {b' b : Blob} {st0 : ABody} {rb : List Pole × ABody} {rf : Termin × (Nat → List Nat) × Bool}
    (hb' : HoonMap.get gF.new o = some b') (hb : HoonMap.get bl o = some b)
    (hrb : aliasBody pick b.body st0 = some rb) (hbe : b' = { par := b.par, body := rb.1, fin := rf.1 })
    (hrf : ∀ u, b.fin = Termin.bom u → rf.1 = Termin.bom u) (hlive : LiveDef gF.new r (o, some i)) :
    ∃ k outa sta, aliasBody pick (b.body.take k) st0 = some (outa, sta) ∧ outa.length = i ∧
      LiveDef bl r (o, some k) := by
  obtain ⟨hR, ⟨b2, op', hb2, hi, hd⟩, hnf⟩ := hlive
  rw [hb'] at hb2; cases hb2
  subst hbe
  obtain ⟨k, op, sta, outa, outb, st1, st', hk, hba, hlen, hop, hbb, hcat⟩ := abody_split hrb hi
  refine ⟨k, outa, sta, hba, hlen, reach_sub (alias_targetsSub hT h) hR, ⟨b, op, hb, hk, ?_⟩, fun i0 hi0 hdf => ?_⟩
  · rw [← hd, aop_rename hop, aliasDst_rename]
  · cases hi0
    exact hnf i rfl (alias_fill hpick hD hT h hF hb' hb rfl hrf hk hlen hop hbb hcat hi hdf)

/-- **`DefOnceB` of the result** when no register with a dead fill has a
definition that counts. -/
theorem alias_onceB (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) (hF : FillFresh bl) : DefOnceB gF.new := by
  have hS : AliasSSAB bl := hD.2.1
  have hGs := alias_targetsSub hT h
  -- a parameter after is a parameter before
  have livePar : ∀ r o, LiveDef gF.new r (o, none) → LiveDef bl r (o, none) := by
    rintro r o ⟨hR, ⟨b', hb', hm⟩, -⟩
    obtain ⟨b, st0, rb, rf, hb, -, hbe, -, -⟩ := alias_blk hT h hb'
    rw [hbe] at hm
    exact awi_par_live (reach_sub hGs hR) hb hm
  have liveOp : ∀ r o i, LiveDef gF.new r (o, some i) → ∃ k, LiveDef bl r (o, some k) := by
    intro r o i hl
    obtain ⟨-, ⟨b', -, hb', -, -⟩, -⟩ := id hl
    obtain ⟨b, st0, rb, rf, hb, hrb, hbe, hrf, -⟩ := alias_blk hT h hb'
    obtain ⟨k, -, -, -, -, hk⟩ := alias_live_op hpick hD hT h hF hb' hb hrb hbe hrf hl
    exact ⟨k, hk⟩
  rintro r ⟨o, _ | i⟩ ⟨o', _ | i'⟩ hs hs'
  · exact hS.1 r _ _ (livePar r o hs) (livePar r o' hs')
  · obtain ⟨k', hk'⟩ := liveOp r o' i' hs'
    have := hS.1 r _ _ (livePar r o hs) hk'
    simp at this
  · obtain ⟨k, hk⟩ := liveOp r o i hs
    have := hS.1 r _ _ hk (livePar r o' hs')
    simp at this
  · obtain ⟨k, hk⟩ := liveOp r o i hs
    obtain ⟨k', hk'⟩ := liveOp r o' i' hs'
    have e := hS.1 r _ _ hk hk'
    simp only [Prod.mk.injEq, Option.some.injEq] at e
    obtain ⟨rfl, -⟩ := e
    -- both in block `o`: the same walk of its body places both
    obtain ⟨-, ⟨b', -, hb', -, -⟩, -⟩ := id hs
    obtain ⟨b, st0, rb, rf, hb, hrb, hbe, hrf, -⟩ := alias_blk hT h hb'
    obtain ⟨k1, outa1, sta1, hba1, hl1, hk1⟩ := alias_live_op hpick hD hT h hF hb' hb hrb hbe hrf hs
    obtain ⟨k2, outa2, sta2, hba2, hl2, hk2⟩ := alias_live_op hpick hD hT h hF hb' hb hrb hbe hrf hs'
    have e2 := hS.1 r _ _ hk1 hk2
    simp only [Prod.mk.injEq, Option.some.injEq, true_and] at e2
    subst e2
    rw [hba1] at hba2
    simp only [Option.some.injEq, Prod.mk.injEq] at hba2
    rw [← hl1, ← hl2, hba2.1]

/-- **`+alias` keeps `FillFresh`**: the op before of a dead fill after is a
definition that counts (were it a dead fill, the register would have none
before, yet a definition that counts after is one before), so a definition
that counts after is that same op, which is a dead fill after. -/
theorem alias_fillFresh (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl)
    (hT : TopoInvR bl topo rev) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) (hF : FillFresh bl) :
    FillFresh gF.new := by
  have hS : AliasSSAB bl := hD.2.1
  have hGs := alias_targetsSub hT h
  intro r o i _ hdf s hs
  obtain ⟨b', hb', -, ⟨n, hn⟩, -, -⟩ := id hdf
  obtain ⟨b, st0, rb, rf, hb, hrb, hbe, hrf, -⟩ := alias_blk hT h hb'
  have hR : Reach bl o := aliasWalk_reach hT.1.1 hT.2 h o (by rw [hb']; rfl)
  have hn' : rb.1[i]? = some (Pole.imm n r) := by rw [hbe] at hn; exact hn
  obtain ⟨k, op, sta, outa, outb, st1, st', hk, hba, hl, hop, -, -⟩ := abody_split hrb hn'
  have hd : aliasDst op = some r := by rw [← aliasDst_rename sta.old op, ← aop_rename hop]; rfl
  -- the parameter case and the op case of `s`, as a definition that counts before
  have hpar : ∀ o', LiveDef gF.new r (o', none) → LiveDef bl r (o', none) := by
    intro o' hl
    obtain ⟨hR', ⟨b2, hb2, hm⟩, -⟩ := hl
    obtain ⟨b3, st3, rb3, rf3, hb3, -, hbe3, -, -⟩ := alias_blk hT h hb2
    rw [hbe3] at hm
    exact awi_par_live (reach_sub hGs hR') hb3 hm
  have hop' : ∀ o' i', LiveDef gF.new r (o', some i') → ∃ k', LiveDef bl r (o', some k') := by
    intro o' i' hl
    obtain ⟨-, ⟨b2, -, hb2, -, -⟩, -⟩ := id hl
    obtain ⟨b3, st3, rb3, rf3, hb3, hrb3, hbe3, hrf3, -⟩ := alias_blk hT h hb2
    obtain ⟨k', -, -, -, -, hk'⟩ := alias_live_op hpick hD hT h hF hb2 hb3 hrb3 hbe3 hrf3 hl
    exact ⟨k', hk'⟩
  by_cases hdf0 : DeadFill bl r o k
  · obtain ⟨o', _ | i'⟩ := s
    · exact hF r o k hR hdf0 _ (hpar o' hs)
    · obtain ⟨k', hk'⟩ := hop' o' i' hs
      exact hF r o k hR hdf0 _ hk'
  · have hl0 : LiveDef bl r (o, some k) := ⟨hR, ⟨b, op, hb, hk, hd⟩, fun i0 hi0 => by cases hi0; exact hdf0⟩
    obtain ⟨o', _ | i'⟩ := s
    · have := hS.1 r _ _ hl0 (hpar o' hs)
      simp at this
    · obtain ⟨k', hk'⟩ := hop' o' i' hs
      have e := hS.1 r _ _ hl0 hk'
      simp only [Prod.mk.injEq] at e
      rw [← e.1] at hs
      obtain ⟨k2, outa2, sta2, hba2, hl2, hk2⟩ := alias_live_op hpick hD hT h hF hb' hb hrb hbe hrf hs
      have e2 := hS.1 r _ _ hl0 hk2
      simp only [Prod.mk.injEq, Option.some.injEq, true_and] at e2
      rw [← e2, hba] at hba2
      simp only [Option.some.injEq, Prod.mk.injEq] at hba2
      have hii : i' = i := by rw [← hl2, ← hl, hba2.1]
      rw [hii] at hs
      exact hs.2.2 i rfl hdf

/-! ## What is left of the field -/

/-- **`PassOK`, `DownPar`, `TrimBr` and `DefFirst` of the result**, the true
part of `AliasRestSSAB`, under `DInvS`, `TopoInvR` and `hpick` alone. -/
theorem alias_restB (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) :
    PassOK gF.new ∧ DownPar gF.new ∧ (∃ K, TrimBr gF.new K) ∧ DefFirst gF.new :=
  ⟨alias_passOK hpick hD hT h, alias_downPar hpick hD hT h, alias_trimBr hpick hD hT h, alias_defFirst hpick hD hT h⟩

/-- **The conclusion of `AliasRestSSAB`** on inputs where no register with a
dead fill in a reachable block has a definition that counts. -/
theorem alias_restSSAB_fresh (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl)
    (hT : TopoInvR bl topo rev) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) (hF : FillFresh bl) :
    PassOK gF.new ∧ DownPar gF.new ∧ (∃ K, TrimBr gF.new K) ∧ AliasSSAB gF.new :=
  ⟨alias_passOK hpick hD hT h, alias_downPar hpick hD hT h, alias_trimBr hpick hD hT h,
    alias_onceB hpick hD hT h hF, alias_defFirst hpick hD hT h⟩

end

/-- **The one conjunct of `AliasRestSSAB` left**: `DefOnceB` of the result of
the model on every input with `DInvS` and `TopoInvR`.  False in general (the
header). -/
def AliasOnceB (Map : Type → Type) [HoonMap Map] [MapKeys Map] (pick : List Nat → Nat) : Prop :=
  ∀ n (bl : Map Blob) topo rev (g : AGen Map), DInvS bl → TopoInvR bl topo rev →
    aliasWalk pick n bl topo (aliasInit rev) = some g → DefOnceB g.new

theorem aliasRestSSAB_of_once {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    (H : AliasOnceB Map pick) : AliasRestSSAB Map pick := by
  intro n bl topo rev g hD hT h
  obtain ⟨h1, h2, h3, h4⟩ := alias_restB hpick hD hT h
  exact ⟨h1, h2, h3, H n bl topo rev g hD hT h, h4⟩

/-- **`+optimize` with the model of `+alias` keeps the code** on blocks with
`DInvS`, given `hpick` and `AliasOnceB` (`DefOnceB` of the result of every
call of the model). -/
theorem optimize_keeps_aliasO {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (H : AliasOnceB Map pick)
    (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints) (hs : P.switch = switchChains sfuel)
    {s s' : Straight Map} (hb : DInvS s.blocks) (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps_alias hpick (aliasRestSSAB_of_once hpick H) ha ht hs hb h

/-- `optimize_keeps_aliasO` with the choice of the Hoon (`pickR`). -/
theorem optimize_keeps_aliasO_pickR (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat} {P : Passes Map}
    (H : AliasOnceB Map (Ana.pickR M)) (ha : P.alias = aliasM (Ana.pickR M)) (ht : P.trim = trimTraceHints)
    (hs : P.switch = switchChains sfuel) {s s' : Straight Map} (hb : DInvS s.blocks)
    (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps_aliasO (fun l hl => Ana.pickR_mem l hl) H ha ht hs hb h

end Opt
end SkaModel
end Formalization
