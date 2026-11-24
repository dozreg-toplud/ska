import lemmas.Ska.OptAliasLti

/-!
# Single assignment as the compiler has it, carried by the driver

## What the real compiler does (`tools/hoon/ssacheck.hoon`)

`AliasSSA` of `OptAliasField.lean` was checked on raw `+comp` output and after
every pass of every round of `+optimize` (so at every call of `+alias`), over
the 143 cases of `optcheck.hoon`, the 41 formulas of `aliascheck.hoon`, and
`thread-a/b/c.hoon` with the subject unknown and known: 553 compiles, 955
calls of `+alias`.

* `DefFirst` holds everywhere (56085 reads of registers with a definition
  checked on raw code, 72162 at the calls).
* `DefOnce` is false: it fails on 32 raw compiles and at 26 calls, always on
  the fill of `+crash-need`.  A need for the parts of an atom makes the block
  `[%cel a] [%imm 0 x1] .. [%imm 0 xk]` and `[%bom ~]`, the `%cel` always
  crashing, and `x1` is often `a` itself, which already has a definition (a
  parameter of the block before, or the destination of an `%inc`).  The
  smallest formulas are `[10 [6 0 1] 5 [0 6] 0 1]` (raw blocks `4` with
  parameter `9`, then `3` = `[%cel 9] [%imm 0 9] [%imm 0 10]`, `[%bom ~]`) and
  `[7 [5 [0 14] 1 5] 10 [2 0 3] 0 1]`; `+eval-blob` of the optimized code
  agrees with `+mock` on them (both crash), and the thread cases agree too, so
  no miscompile comes of it.

The property that holds everywhere (raw, every pass, every call of `+alias`)
is `DefOnceB`: on the blocks reachable from `0`, a register has at most one
definition that is not a *dead fill*, a dead fill of `r` being an `%imm` into
`r` in a block that ends in `%bom`, followed there by `%imm` ops only, with
every read of `r` in a reachable block in that block before it.  Both
restrictions are needed: without reachability it fails on raw code (blocks
that no jump reaches read the register), and without "followed by `%imm` ops
only" it fails after `+remove-hops` merges the `%inc` into the fill's block
(the `%inc` is then itself an op of a `%bom` block followed by a read).

## Why `DefOnceB` is what `+alias` needs

`+alias` keeps `old` global to the walk, so a dropped `%imm 0 x` of a fill
(when another register is known to hold `0` there) renames every later read of
`x`.  Under `DefOnceB` a register with a dead fill is read nowhere but in the
fill's block, before the fill, so no read follows the rename; the ops after the
fill are `%imm` ops whose facts nobody reads, since the block ends in `%bom`
and has no successor.  `AliasFieldSSAB` is `AliasFieldSSA` with `AliasSSAB`
(`DefOnceB` and `DefFirst`) in place of `AliasSSA`.

## The driver

`DInvS` is `DInvT`, `AliasSSAB` and `NoLti` (no end is `%lti`, which
`aliasFin` does not rename; `OptAliasLti.lean`).  `SSAKeep fuel` lists, one field per pass,
that `+remove-hops`, `+remove-useless-branching`, `+remove-empty-middle`,
`+trim-trace-hints` and `+remove-dead-code` keep `AliasSSAB` (the field
`alias` of `DriverRestSSA` gives it back for `+alias`).  **`optimize_keeps_ssa`**:
`optimizeF` keeps the code on blocks with `DInvS`, given `DriverRestSSA` (the
field `alias` at `DInvS`, the real trim pass, the model switch pass) and
`SSAKeep`.  With the model of `+alias` the first is `AliasFieldSSAB`
(`driverRestSSA_of_aliasM`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- A read of `r` at place `i` of block `b`: by its op `i`, or by its end when
`i = |body|` (the reads of `DefFirst`). -/
def ReadAt (b : Blob) (i r : Nat) : Prop :=
  r ∈ ((b.body.drop i).head?.map aliasReads).getD [] ∨ (i = b.body.length ∧ r ∈ finRegs b.fin)

/-- A place that defines `r`: a parameter of block `o` (`(o, none)`) or its
op `i` (`(o, some i)`). -/
def DefSite (bl : Map Blob) (r : Nat) : Nat × Option Nat → Prop
  | (o, none) => ∃ b, HoonMap.get bl o = some b ∧ r ∈ b.par
  | (o, some i) => ∃ b op, HoonMap.get bl o = some b ∧ b.body[i]? = some op ∧ aliasDst op = some r

/-- **A dead fill** of `r` (`+crash-need`): op `i` of block `o` is an `%imm`
into `r`, the block ends in `%bom`, every op from `i` on is an `%imm`, and every
read of `r` in a block reachable from `0` is in block `o` before `i`. -/
def DeadFill (bl : Map Blob) (r o i : Nat) : Prop :=
  ∃ b, HoonMap.get bl o = some b ∧ (∃ u, b.fin = Termin.bom u) ∧
    (∃ n, b.body[i]? = some (Pole.imm n r)) ∧
    (∀ op ∈ b.body.drop i, ∃ n d, op = Pole.imm n d) ∧
    ∀ o' b' j, Reach bl o' → HoonMap.get bl o' = some b' → ReadAt b' j r → o' = o ∧ j < i

/-- A definition that counts: at a reachable block, and not a dead fill. -/
def LiveDef (bl : Map Blob) (r : Nat) (s : Nat × Option Nat) : Prop :=
  Reach bl s.1 ∧ DefSite bl r s ∧ ∀ i, s.2 = some i → ¬ DeadFill bl r s.1 i

/-- **`DefOnceB`**: every register has at most one definition that counts
(checked on the real compiler: `tools/hoon/ssacheck.hoon`). -/
def DefOnceB (bl : Map Blob) : Prop :=
  ∀ r s s', LiveDef bl r s → LiveDef bl r s' → s = s'

/-- **Single assignment as the compiler has it**: `DefOnceB` and `DefFirst`. -/
def AliasSSAB (bl : Map Blob) : Prop := DefOnceB bl ∧ DefFirst bl

/-- **The field `alias` under `AliasSSAB`**, for the model (open). -/
def AliasFieldSSAB (Map : Type → Type) [HoonMap Map] [MapKeys Map] (pick : List Nat → Nat) : Prop :=
  ∀ n (bl : Map Blob) topo rev f bl', DInvT bl → AliasSSAB bl → NoLti bl → TopoInv bl topo rev →
    RevSound bl topo rev → aliasM pick n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ DInvT bl' ∧ AliasSSAB bl' ∧ NoLti bl' ∧
      TopoInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))

/-- The block invariant the driver carries: `DInvT`, single assignment, and
no `%lti` end (`OptAliasLti.lean`). -/
def DInvS (bl : Map Blob) : Prop := DInvT bl ∧ AliasSSAB bl ∧ NoLti bl

/-- **Each pass of the loop keeps single assignment** (one field per pass;
`+alias` is the field `alias` of `DriverRestSSA`). -/
structure SSAKeep (Map : Type → Type) [HoonMap Map] [MapKeys Map] (fuel : Nat) : Prop where
  hops : ∀ (bl : Map Blob) topo rev ch bl', DInvT bl → TopoInv bl topo rev → AliasSSAB bl →
    removeHops fuel bl rev topo = some (ch, bl') → AliasSSAB bl'
  rub : ∀ (bl : Map Blob) ch bl', DInvT bl → AliasSSAB bl → removeUselessBranching bl = some (ch, bl') →
    AliasSSAB bl'
  middle : ∀ (bl : Map Blob) ch bl', DInvT bl → AliasSSAB bl → removeEmptyMiddle fuel bl = some (ch, bl') →
    AliasSSAB bl'
  trim : ∀ (bl : Map Blob) topo rev bl', DInvT bl → TopoInv bl topo rev → AliasSSAB bl →
    trimTraceHints bl topo rev = some bl' → AliasSSAB bl'
  dead : ∀ (bl : Map Blob) topo rev bl', DInvT bl → TopoInv bl topo rev → AliasSSAB bl →
    removeDeadCode bl topo.reverse = some bl' → AliasSSAB bl'

/-- **What the driver assumes of `+alias`**, at `DInvS`: it keeps the code,
`DInvS`, `TopoInv` of the filtered `topo`; the trim pass is the real one; the
switch pass is the model. -/
structure DriverRestSSA (fuel sfuel : Nat) (P : Passes Map) : Prop where
  alias : ∀ n (bl : Map Blob) topo rev f bl', DInvS bl → TopoInv bl topo rev → RevSound bl topo rev →
    P.alias n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ DInvS bl' ∧
      TopoInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))
  trim : P.trim = trimTraceHints
  switch : P.switch = switchChains sfuel

/-- The field for the model gives `DriverRestSSA` with the model as the pass. -/
theorem driverRestSSA_of_aliasM {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (h : AliasFieldSSAB Map pick) (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints)
    (hs : P.switch = switchChains sfuel) : DriverRestSSA fuel sfuel P :=
  ⟨fun n bl topo rev f bl' hb hi hr hp => by
    rw [ha] at hp
    obtain ⟨k, d, s, l, t⟩ := h n bl topo rev f bl' hb.1 hb.2.1 hb.2.2 hi hr hp
    exact ⟨k, ⟨d, s, l⟩, t⟩, ht, hs⟩

/-- The invariant of `topo` and `rev` the driver carries: `TopoInv` and
`RevSound`. -/
abbrev TopoInvR (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)) : Prop :=
  TopoInv bl topo rev ∧ RevSound bl topo rev

theorem driverHypS_of {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestSSA fuel sfuel P)
    (K : SSAKeep Map fuel) : DriverHyp fuel P DInvS TopoInvR where
  topo := fun bl topo hb h => ⟨topo_field hb.1.1 h, revCfg_sound bl topo⟩
  hops := fun bl topo rev ch bl' hb hi h => by
    obtain ⟨k, d, t⟩ := hops_fieldD hb.1.1 hi.1 h
    obtain ⟨Kt, hK⟩ := hb.1.2
    refine ⟨k, ⟨⟨d, Kt, hops_trimBr hi.1.1.1 hi.1.1.2.1 h hK⟩, K.hops bl topo rev ch bl' hb.1 hi.1 hb.2.1 h,
      nolti_hops hb.2.2 hi.1.1.1 hi.1.1.2.1 h⟩, fun e => ⟨t e, ?_⟩⟩
    subst e
    exact rvs_eq hi.2 (hops_same hi.1.1.1 h).1
  rub := fun bl topo rev ch bl' hb h => by
    obtain ⟨k, d, t⟩ := rub_fieldD hb.1.1 h
    obtain ⟨Kt, hK⟩ := hb.1.2
    refine ⟨k, ⟨⟨d, Kt, rub_trimBr h hK⟩, K.rub bl ch bl' hb.1 hb.2.1 h, nolti_rub hb.2.2 h⟩,
      fun hi e => ⟨t hi.1 e, ?_⟩⟩
    subst e
    exact rvs_rub hi.2 h
  middle := fun bl topo rev ch bl' hb h => by
    obtain ⟨k, d, t⟩ := middle_fieldD hb.1.1 h
    obtain ⟨Kt, hK⟩ := hb.1.2
    refine ⟨k, ⟨⟨d, Kt, mid_trimBr h hK⟩, K.middle bl ch bl' hb.1 hb.2.1 h, nolti_mid hb.2.2 h⟩,
      fun hi e => ⟨t hi.1 e, ?_⟩⟩
    subst e
    exact rvs_eq hi.2 fun k _ => mid_same h k
  alias := fun n bl topo rev f bl' hb hi h => by
    obtain ⟨k, d, t⟩ := H.alias n bl topo rev f bl' hb hi.1 hi.2 h
    exact ⟨k, d, t, revCfg_sound _ _⟩
  trim := fun bl topo rev bl' hb hi h => by
    rw [H.trim] at h
    obtain ⟨k, d, t⟩ := trim_fieldT hb.1 hi.1 h
    have hs := trim_shape h
    exact ⟨k, ⟨d, K.trim bl topo rev bl' hb.1 hi.1 hb.2.1 h, nolti_shape hb.2.2 hs.1⟩, t,
      rvs_shape hi.2 hs.1 fun k hk => by rw [hs.2 k]; exact hi.1.1.2.2.1 k hk⟩
  dead := fun bl topo rev bl' hb hi h => by
    obtain ⟨Kt, hK⟩ := hb.1.2
    obtain ⟨d, t⟩ := dead_inv hb.1.1 hi.1 h
    have hs := dead_shape h
    exact ⟨fun c hc => by subst hc; exact dead_keeps c hi.1.1 h,
      ⟨⟨d, Kt, dead_trimBr hi.1.1 h hK⟩, K.dead bl topo rev bl' hb.1 hi.1 hb.2.1 h, nolti_shape hb.2.2 hs.1⟩, t,
      rvs_shape hi.2 hs.1 fun k hk => hs.2 k (List.mem_reverse.mpr hk)⟩
  switch := fun bl bl' hb h => by rw [H.switch] at h; exact switch_fieldT _ hb.1 h

/-- **`+optimize` keeps the code** on blocks with `DInvS` (`DInv`, bracketed
trace hints, single assignment as the compiler has it), with the real
`+trim-trace-hints` and the model of `+switch-chains`, given that `+alias`
keeps the code and the invariants (`DriverRestSSA.alias`) and that each pass
of the loop keeps single assignment (`SSAKeep`). -/
theorem optimize_keeps_ssa {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestSSA fuel sfuel P)
    (K : SSAKeep Map fuel) {s s' : Straight Map} (hb : DInvS s.blocks) (h : optimizeF fuel P s = some s') :
    Keeps s s' :=
  optimize_keeps (driverHypS_of H K) hb h

end Opt
end SkaModel
end Formalization
