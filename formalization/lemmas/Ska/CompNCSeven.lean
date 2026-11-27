import lemmas.Ska.CompNC

/-!
# `[7 p q]` at every level of `NC`

README Gaps 12.22, the case `sevenE` of `CompNC.lean` at levels `1` and `2`
and the jump facts of `[7 p q]`.  Under a lazy goal `%next L th`, `q` runs
under `L` and `p` under the lazy need `q`'s run returns (any entries), so
`p` meets `LOKC` and `q` the relation of the level (`LOKCS` when `L`'s sure
part asks nothing, `LOKC` else); `runOKLC_sevenM` composes them for any
formula with `MinkC7`, `p`'s state hypotheses coming from `q`'s `RunOKLC`
(as in `bondOKC_sevenC`, whose bond goal is a goal of level `1`).

* `lokc_seven_core`: `p`'s run under `q`'s result and the composition.
* `lokc_sevenC`, `lokcs_sevenC`: `[7 p q]` meets `LOKC`, `LOKCS`.
* `lokcLv_sevenA`: the same on the forms `n7`, `inline`, `n9` of `Annot`
  and the wrappers (in the forms of `[8 b c]` the `p` part is a cons or a
  literal, which `hpc` excludes, as in `uokc_sevenLA`).
* `jNew_sevenC` (`q`'s result without entries, `p`'s `JNew`) and
  `jNew_sevenL` (`p`'s `LOKC`): the jump of `[7 p q]` is the goal's or new
  when `q`'s is.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`p` under `q`'s lazy result, and the composition**: from `q`'s
`RunOKLC` under `%next L th` (a goal with the hypotheses of `LOKC`) and
`p`'s `LOKC`, `RunOKLC` of `[7 p q]` and its jump. -/
theorem lokc_seven_core {lib : Lib} {env : CallEnv} {p : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC7 lib P f fb fc) {sup : Option Nomm} {L : Lazy S}
    {th : Jmp} {region : List Nat} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (hc : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0)
    (hcb : CondBelow g0) (ha : th.args = [])
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ th', HoonMap.get g0.blocks e.1 = some ⟨[], [], Termin.hop th'⟩)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    {Qq : Wit} (Rq : RunOKLC (Map := Map) lib (Img lib P fb) fc L th Qq g0 g1 nx)
    (hp : runLC env sup p nx.goal region g1 = some (nex, g2)) :
    (∃ Q, RunOKLC (Map := Map) lib P f L th Q g0 g2 nex) ∧
      ((nx.th = th ∨ g0.bo ≤ nx.th.there) → (nex.th = th ∨ g0.bo ≤ nex.th.there)) := by
  have r1 := Rq.re
  have o1 := Rq.bo
  have hi1 := Rq.hi
  obtain ⟨⟨Qp, Rp⟩, hj⟩ := Lp.run hc (by omega) (Rq.drop.trans d0) (Rq.grow.up hu) (hcl.growU Rq.grow)
    (Rq.cfr.below hcb) Rq.lo Rq.hi (nextArgs_nil Rq.ent ha) Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with h' | h'
      · have := (hsl x h').1; omega
      · exact h'.2, Rq.ncond x hx⟩)
    (fun e he => ⟨by
      rcases (Rq.labs e he).1 with h' | h'
      · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h'
        have := (hlab e0 he0).1; omega
      · omega, (Rq.labs e he).2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨by
      rcases (Rq.eregs e he).2 x hx with ⟨e0, he0, h0⟩ | h' | h'
      · have := ((hed e0 he0).2 x h0).1; omega
      · have := (hsl x h').1; omega
      · exact h'.2, Rq.econd e he x hx⟩⟩) hp
  refine ⟨⟨_, runOKLC_sevenM M Rq Rp ?_ (fun r hr => (hsl r hr).1) (fun e he => (hlab e he).1)⟩, ?_⟩
  · rcases hj with e | e
    · rw [e]; exact Nat.le_refl _
    · omega
  · intro jq
    rcases hj with e | e
    · rw [e]; exact jq
    · right; omega

/-- **`[7 p q]` with `p` and `q` meeting `LOKC` meets `LOKC`.** -/
theorem lokc_sevenC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p) (Lq : LOKC (S := S) (Map := Map) lib env (Img lib P fb) fc q)
    (M : MinkC7 lib P f fb fc) : LOKC (S := S) (Map := Map) lib env P f (Nomm.n7 p q) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc h => ?_, fun {sup L th region g0 g2 nex} hc b0 d0 hu hcl hcb h1 h2 ha
    hsd hsl hlab hnd hed h => ?_⟩
  · rw [runLC_n7] at h
    obtain ⟨nx, g1', hq, hp⟩ := bind_some h
    exact Lp.clean (Lq.clean hc hq) hp
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  have hcnt : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hc; omega
  obtain ⟨⟨Qq, Rq⟩, jq⟩ := Lq.run hcnt.2 b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed hq
  have C := lokc_seven_core Lp M hcnt.1 b0 d0 hu hcl hcb ha hsl hlab hed Rq hp
  exact ⟨C.1, C.2 jq⟩

/-- **`[7 p q]` with `p` meeting `LOKC` and `q` meeting `LOKCS` meets
`LOKCS`**: `q` runs under the goal, whose sure part asks nothing. -/
theorem lokcs_sevenC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p) (Lq : LOKCS (S := S) (Map := Map) lib env (Img lib P fb) fc q)
    (M : MinkC7 lib P f fb fc) : LOKCS (S := S) (Map := Map) lib env P f (Nomm.n7 p q) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc h => ?_, fun {sup L th region g0 g2 nex} hs ht hc b0 d0 hu hcl hcb h1 h2
    ha hsd hsl hlab hnd hed h => ?_⟩
  · rw [runLC_n7] at h
    obtain ⟨nx, g1', hq, hp⟩ := bind_some h
    exact Lp.clean (Lq.clean hc hq) hp
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  have hcnt : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hc; omega
  obtain ⟨Qq, Rq⟩ := Lq.run hs ht hcnt.2 b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed hq
  exact (lokc_seven_core Lp M hcnt.1 b0 d0 hu hcl hcb ha hsl hlab hed Rq hp).1

/-- **`[7 p q]` at levels `1` and `2` on every `Annot`**: the forms `n7`,
`inline`, `n9` and the wrappers; `hpc` excludes the forms of `[8 b c]`
(their `p` part is a cons or a literal). -/
theorem lokcLv_sevenA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {lv : Nat} {p q : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → LOKC (S := S) (Map := Map) lib env P f p)
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q →
      (1 ≤ lv → LOKCS (S := S) (Map := Map) lib env P f q) ∧ (2 ≤ lv → LOKC (S := S) (Map := Map) lib env P f q))
    (hpc : (∀ a b, p ≠ Nomm.cons a b) ∧ ∀ k, p ≠ Nomm.n1 k)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n7 p q → (1 ≤ lv → LOKCS (S := S) (Map := Map) lib env P f nm) ∧
      (2 ≤ lv → LOKC (S := S) (Map := Map) lib env P f nm) := by
  induction hA with
  | n7 hb hc _ _ =>
    intro e; cases e
    exact ⟨fun l => lokcs_sevenC lib env (ihp hb) ((ihq hc).1 l) (minkC7_seven lib _ _ _),
      fun l => lokc_sevenC lib env (ihp hb) ((ihq hc).2 l) (minkC7_seven lib _ _ _)⟩
  | inline hb hc hg _ _ =>
    intro e; cases e
    exact ⟨fun l => lokcs_sevenC lib env (ihp hb) ((ihq hg).1 l) (minkC7_inline lib hc),
      fun l => lokc_sevenC lib env (ihp hb) ((ihq hg).2 l) (minkC7_inline lib hc)⟩
  | n9 hc hr _ _ =>
    intro e; cases e
    exact ⟨fun l => lokcs_sevenC lib env (ihp hc) ((ihq hr).1 l) (minkC7_nine lib _ _ _),
      fun l => lokc_sevenC lib env (ihp hc) ((ihq hr).2 l) (minkC7_nine lib _ _ _)⟩
  | n8 => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8g => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8l => intro e; cases e; exact absurd rfl (hpc.2 _)
  | memo hm _ ih' =>
    intro e
    exact ⟨fun l => LOKCS.wrap (wrapRel_memo hm) ((ih' e).1 l), fun l => LOKC.wrap (wrapRel_memo hm) ((ih' e).2 l)⟩
  | six0 hb' _ ih' =>
    intro e
    exact ⟨fun l => LOKCS.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) ((ih' e).1 l),
      fun l => LOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) ((ih' e).2 l)⟩
  | six1 hb' _ ih' =>
    intro e
    exact ⟨fun l => LOKCS.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) ((ih' e).1 l),
      fun l => LOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) ((ih' e).2 l)⟩
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | n11c => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | bareLit => intro e; cases e

/-! ## The jump of `[7 p q]` -/

/-- **`[7 p q]` meets `JNew` when `q`'s result has no entries and both
parts meet `JNew`.** -/
theorem jNew_sevenC {lib : Lib} {env : CallEnv} {p q : Nomm} {Pq : Noun → Prop} {fc : Noun}
    (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q) (Nq : NoEnt (S := S) (Map := Map) env q)
    (Jp : JNew (S := S) (Map := Map) env p) (Jq : JNew (S := S) (Map := Map) env q) :
    JNew (S := S) (Map := Map) env (Nomm.n7 p q) := by
  intro sup sur th region g0 g2 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  obtain ⟨nx, g1, Rq, _, hq, hp, _, a1, j1, o1, c1, n1, b1, d1, u1, l1, cb1, k1⟩ :=
    sevenC_parts (goal := CGoal.next sur th) Uq Nq trivial hth hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have q2 := Rq.ext.2.1
  rcases Jp j1 a1 o1 c1 n1 b1 d1 u1 l1 cb1 k1 hp with e | e
  · rw [e]
    have hc : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
    exact Jq hj hth hok hcl hc b0 d0 hu hcl0 hcb hkg hq
  · right; omega

/-- **`[7 p q]` with `p` meeting `LOKC` meets `JNew` when `q` does.** -/
theorem jNew_sevenL {lib : Lib} {env : CallEnv} {p q : Nomm} {P Pq : Noun → Prop} {fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q)
    (Jq : JNew (S := S) (Map := Map) env q) : JNew (S := S) (Map := Map) env (Nomm.n7 p q) := by
  intro sup sur th region g0 g2 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  obtain ⟨nx, g1, Q, Rq, hq, Rp, hjp, _⟩ :=
    sevenL_parts (goal := CGoal.next sur th) Lp Uq trivial hth hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have q2 := Rq.ext.2.1
  rcases hjp with e | e
  · rw [e]
    have hc : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
    exact Jq hj hth hok hcl hc b0 d0 hu hcl0 hcb hkg hq
  · right; omega

end Comp
end SkaModel
end Formalization
