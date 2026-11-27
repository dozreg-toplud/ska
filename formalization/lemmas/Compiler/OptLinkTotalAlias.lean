import lemmas.Compiler.OptLinkTotalSwitch
import lemmas.Ska.OptAliasWitness

/-!
# `+alias` returns: the places where the model crashes

## A finding: `AliasRet` is false as stated

`AliasRet pick ρ L` (`OptLinkTotalPass.lean`) asks the model of `+alias` to
return for every number of arguments `n`, on blocks with `StInv`, `DInvR`
and `TopoInvR`.  It does not (`not_aliasRet`): the one block
`[%cel 1] [%bom ~]` (`wBl`) has `DInvR` (it defines no register, so
`DefFirst` and `DefOnceR` hold vacuously), but `+alias` with `n = 1` looks
up the facts of register `1`, which neither the entry (`0 .. n-1`) nor any
definition gives, and crashes (`got:by`), as the Hoon does.  `DefFirst`
speaks only of registers in `allDefs`; the registers below `n` are the
arguments of the entry (`entryInfo`), and nothing in `DInvR` relates the
registers read to `n`.  So `opt_gate_total`, which assumes `AliasRet`, holds
vacuously.  The field missing is **`ReadsIn n bl`**: every register that a
reachable block reads is defined in the map or is below `n`.  The examples
of the audit have it (`xbBlocks` reads the argument `1` with `n = 2`).

Also: with a `pick` that does not pick a member, the model crashes on
`[%imm 5 1] [%imm 5 2] [%inc 2 3]` (the `%inc` reads the register `pick`
gave for `2`), so the corrected statement `AliasRetN` is for a `pick` that
picks a member.

## The places where the model returns `none`

In `aliasBlock` (block `o` of `topo`, `pre = g.rev o`):
* `B1`, `B4`: `got` of `o` in the blocks (`TopoOK`: every member is a block);
* `S1`: the facts `g.info p` of every `p ∈ pre` (walked before `o`);
* `S2`: the block `g.new p` of the one predecessor;
* `S3`, `S5`: a one-predecessor `%brn` / `%clq` with no target `o`;
* `S3`, `S4`, `S5`: the `jab` of the test register in the facts of `p`;
* `B3`: the immediates `g.imms p` of every `p ∈ pre`;
* `E1`: `g.new p` of every `p ∈ pre` (`aliasEdges`);
* `I1`: an edge with fewer arguments than `o` has parameters (`aliasIn`);
* `I2`, `I3`: the facts of `p` and of the register an edge passes;
* `O1` .. `O6`: the facts of the register a `%inc`, `%con` (two),
  `%hed`, `%tal`, `%cel`, `%lob` reads, under `old` (`aliasOp`);
* `F1`: a two-way end with arguments (`aliasFin`);
* `F2` .. `F4`: the facts of the test register of a `%clq`, `%brn`, `%brz`.

Proved here, per op and per end: `aliasOp_some` (`O1` .. `O6`: the op
returns once every register it reads has a fact under `old`) and
`aliasFin_some` (`F1` .. `F4`: the end returns once a two-way end passes no
arguments, `TwoNA` of the input, and its test register has a fact).  What
is left is the walk invariant that gives those facts (see Gaps 13).
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-- **The field `DInvR` lacks**: every register a reachable block reads is
defined in the map or is an argument of the entry (below `n`). -/
def ReadsIn (n : Nat) (bl : Map Blob) : Prop :=
  ∀ o b i r, Opt.Reach bl o → HoonMap.get bl o = some b → Opt.ReadAt b i r → r ∈ Opt.allDefs bl ∨ r < n

/-- **`AliasRet`, corrected** (open): with `ReadsIn n`, for a `pick` that
picks a member. -/
def AliasRetN (pick : List Nat → Nat) (ρ : Nat → Nat) (L : List Nat) : Prop :=
  ∀ n (bl : Map Blob) topo rev, StInv ρ L bl → Opt.DInvR bl → ReadsIn n bl → Opt.TopoInvR bl topo rev →
    (Opt.aliasM pick n bl rev topo).isSome

end

/-! ## The witness -/

namespace AliasWit
open Opt

def wB : Blob := ⟨[], [Pole.cel 1], Termin.bom none⟩
def wBl : LM Blob := ⟨[(0, wB)]⟩

theorem wget {o : Nat} {b : Blob} (h : HoonMap.get wBl o = some b) : o = 0 ∧ b = wB := by
  by_cases e : o = 0
  · subst e
    have : HoonMap.get wBl 0 = some wB := rfl
    rw [this] at h; exact ⟨rfl, (Option.some.inj h).symm⟩
  · have : HoonMap.get wBl o = none := by
      simp only [HoonMap.get, LM.find, wBl, List.find?, Ne.symm e, decide_false, Option.map_none]
    rw [this] at h; cases h

theorem wjmp {o : Nat} {b : Blob} {j : Jmp} (h : HoonMap.get wBl o = some b) : j ∉ getJmps b.fin := by
  obtain ⟨-, rfl⟩ := wget h; simp [wB, getJmps]

theorem wnosite (r : Nat) (s : Nat × Option Nat) : ¬ DefSite wBl r s := by
  rcases s with ⟨o, _ | i⟩
  · rintro ⟨b, h, hr⟩; obtain ⟨-, rfl⟩ := wget h; simp [wB] at hr
  · rintro ⟨b, op, h, hi, hd⟩
    obtain ⟨-, rfl⟩ := wget h
    cases i with
    | zero => simp only [wB, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; simp [aliasDst] at hd
    | succ i => simp [wB] at hi

theorem wdefs : allDefs wBl = [] := by decide

theorem wDInvR : DInvR wBl := by
  refine ⟨⟨⟨⟨?_, ?_⟩, ⟨fun _ => 0, ?_⟩, ?_⟩, ⟨fun _ => [], rfl, ?_⟩⟩, ?_, ?_, ?_⟩
  · intro o b h; obtain ⟨-, rfl⟩ := wget h; exact List.nodup_nil
  · intro o b j _ h hj; exact absurd hj (wjmp h)
  · intro o b j h hj; exact absurd hj (wjmp h)
  · intro y b j h hj; exact absurd hj (wjmp h)
  · intro o b _ h; obtain ⟨-, rfl⟩ := wget h; exact ⟨[], rfl, fun j hj => by simp [wB, getJmps] at hj⟩
  · intro o p b _ _ i r _ hr; rw [wdefs] at hr; cases hr
  · intro o b h n s z o'; obtain ⟨-, rfl⟩ := wget h; simp [wB]
  · intro r s s' _ hs; exact absurd hs (wnosite r s)

theorem wStInv (ρ : Nat → Nat) : StInv ρ [0] wBl where
  rank := fun _ _ _ h hj => absurd hj (wjmp h)
  closed := fun _ _ _ h hj => absurd hj (wjmp h)
  arity := fun _ _ _ _ h hj => absurd hj (wjmp h)
  zero := rfl
  two := fun _ _ _ h _ hj => absurd hj (wjmp h)
  keys := fun o h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    rw [(wget hb).1]; simp

theorem wTopo : TopoInvR wBl [0] (revCfg wBl [0]) := by
  have ht : bbTopo 2 wBl = some [0] := rfl
  exact ⟨⟨bbTopo_ok ⟨fun _ => 0, fun _ _ _ h hj => absurd hj (wjmp h)⟩ ht,
    fun _ _ _ _ h hj => absurd hj (wjmp h)⟩, revCfg_sound wBl [0]⟩

theorem wAlias (pick : List Nat → Nat) : aliasM pick 1 wBl (revCfg wBl [0]) [0] = none := rfl

end AliasWit

/-- **`AliasRet` is false**, for every `pick` and `ρ`: the block map `wBl`
has `StInv ρ [0]`, `DInvR` and `TopoInvR`, and the model of `+alias` with one
argument crashes on it. -/
theorem not_aliasRet (pick : List Nat → Nat) (ρ : Nat → Nat) : ¬ AliasRet (Map := Opt.LM) pick ρ [0] := by
  intro h
  have := h 1 AliasWit.wBl [0] (Opt.revCfg AliasWit.wBl [0]) (AliasWit.wStInv ρ) AliasWit.wDInvR AliasWit.wTopo
  rw [AliasWit.wAlias] at this; cases this

/-! ## The ops and the ends -/

theorem mem_erase2 (s d : Nat) : s ∈ [s, d].erase d := by
  by_cases h : s = d
  · subst h; simp
  · simp [List.erase_cons, Ne.symm h, h]

theorem mem_erase3 (h t d : Nat) : h ∈ [h, t, d].erase d ∧ t ∈ [h, t, d].erase d := by
  by_cases e1 : h = d
  · subst e1; simp
  · by_cases e2 : t = d
    · subst e2; simp [List.erase_cons, e1]
    · simp [List.erase_cons, e1, e2, Ne.symm e1, Ne.symm e2]

theorem jabA_isSome {m : Opt.AInfo} {k : Nat} {g : Opt.InfoReg → Opt.InfoReg} (h : (m k).isSome) :
    (Opt.jabA m k g).isSome := by
  simp only [Opt.jabA, Option.isSome_map]; exact h

theorem updA_isSome {m : Opt.AInfo} {k d : Nat} {v : Opt.InfoReg} (h : (m k).isSome) :
    (Opt.updA m d (some v) k).isSome := by
  simp only [Opt.updA]; split <;> simp_all

theorem bind_isSome2 {α β : Type} {x : Option α} {f : α → Option β} (hx : x.isSome)
    (hf : ∀ a, x = some a → (f a).isSome) : (x.bind f).isSome := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hx
  rw [ha, Option.bind_some]; exact hf a ha

theorem jabA_keys {m m' : Opt.AInfo} {k : Nat} {g : Opt.InfoReg → Opt.InfoReg} (h : Opt.jabA m k g = some m')
    (x : Nat) (hx : (m x).isSome) : (m' x).isSome := by
  simp only [Opt.jabA, Option.map_eq_some_iff] at h
  obtain ⟨v, -, rfl⟩ := h
  simp only [Opt.updA]; split <;> simp_all

/-- **`O1` .. `O6`**: an op returns once every register it reads has a fact
under `old`. -/
theorem aliasOp_some (pick : List Nat → Nat) (st : Opt.ABody) (op : Pole)
    (h : ∀ r ∈ Opt.aliasReads op, (st.loc (st.old r)).isSome) : (Opt.aliasOp pick st op).isSome := by
  cases op with
  | inc s d =>
    have hs := h s (by simp only [Opt.aliasReads, Opt.aliasDst]; exact mem_erase2 s d)
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    split
    · rfl
    · simp only [Option.isSome_map]; exact jabA_isSome (updA_isSome hs)
  | con hh t d =>
    have hm := mem_erase3 hh t d
    have h1 := h hh (by simp only [Opt.aliasReads, Opt.aliasDst]; exact hm.1)
    have h2 := h t (by simp only [Opt.aliasReads, Opt.aliasDst]; exact hm.2)
    obtain ⟨hi, ehi⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨ti, eti⟩ := Option.isSome_iff_exists.1 h2
    simp only [Opt.aliasOp, ehi, eti, Option.bind_some]
    split
    · rfl
    · refine bind_isSome2 (jabA_isSome (updA_isSome h1)) fun l1 el1 => ?_
      rw [Option.isSome_map]; exact jabA_isSome (jabA_keys el1 _ (updA_isSome h2))
  | hed s d =>
    have hs := h s (by simp only [Opt.aliasReads, Opt.aliasDst]; exact mem_erase2 s d)
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    split
    · rfl
    · simp only [Option.isSome_map]; exact jabA_isSome (updA_isSome hs)
  | tal s d =>
    have hs := h s (by simp only [Opt.aliasReads, Opt.aliasDst]; exact mem_erase2 s d)
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    split
    · rfl
    · simp only [Option.isSome_map]; exact jabA_isSome (updA_isSome hs)
  | cel p =>
    have hs := h p (by simp [Opt.aliasReads, Opt.aliasDst, Opt.poleRegs])
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    split
    · rfl
    · simp only [Option.isSome_map]; exact jabA_isSome hs
  | lob p =>
    have hs := h p (by simp [Opt.aliasReads, Opt.aliasDst, Opt.poleRegs])
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    split
    · rfl
    · simp only [Option.isSome_map]; exact jabA_isSome hs
  | _ => (simp only [Opt.aliasOp]) <;> (try split) <;> rfl

/-- **`F1` .. `F4`**: an end returns once a two-way end passes no arguments
and the test register of a `%clq`, `%brn`, `%brz` has a fact under `old`. -/
theorem aliasFin_some (old : Nat → Nat) (loc : Opt.AInfo) (rev : Nat → List Nat) (f : Bool) (o : Nat)
    (fin : Termin) (h2 : twoWay fin = true → ∀ j ∈ Opt.getJmps fin, j.args = [])
    (hs : ∀ s, s ∈ (Opt.finRegs fin).head? → twoWay fin = true → (∀ l r z o', fin ≠ Termin.eqq l r z o') →
      (loc (old s)).isSome) :
    (Opt.aliasFin old loc rev f o fin).isSome := by
  cases fin with
  | clq s z o' =>
    have hz := h2 rfl z (by simp [Opt.getJmps]); have ho := h2 rfl o' (by simp [Opt.getJmps])
    simp only [Opt.aliasFin, hz, ho, ne_eq, not_true_eq_false, or_self, if_false, Option.isSome_map]
    exact hs s (by simp [Opt.finRegs]) rfl (fun _ _ _ _ e => by cases e)
  | eqq l r z o' =>
    have hz := h2 rfl z (by simp [Opt.getJmps]); have ho := h2 rfl o' (by simp [Opt.getJmps])
    simp only [Opt.aliasFin, hz, ho, ne_eq, not_true_eq_false, or_self, if_false]
    split <;> rfl
  | brn s z o' =>
    have hz := h2 rfl z (by simp [Opt.getJmps]); have ho := h2 rfl o' (by simp [Opt.getJmps])
    simp only [Opt.aliasFin, hz, ho, ne_eq, not_true_eq_false, or_self, if_false, Option.isSome_map]
    exact hs s (by simp [Opt.finRegs]) rfl (fun _ _ _ _ e => by cases e)
  | brz s z o' =>
    have hz := h2 rfl z (by simp [Opt.getJmps]); have ho := h2 rfl o' (by simp [Opt.getJmps])
    simp only [Opt.aliasFin, hz, ho, ne_eq, not_true_eq_false, or_self, if_false, Option.isSome_map]
    exact hs s (by simp [Opt.finRegs]) rfl (fun _ _ _ _ e => by cases e)
  | _ => rfl

end Compiler
end Formalization
