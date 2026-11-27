import lemmas.Ska.CompFourTop
import lemmas.Ska.CompPairLSX

/-!
# `LOKSX`: `LOKS` with the goal's entries apart from its sure registers

README Gaps 12.33.  What `pairLSX_ok` asks of the parts of a cons with
flagged parts (`hG`, `hPH`) is not in `LOKS`: the goal's entries apart from
its sure registers (G), and the result's entries at the goal's labels apart
from the goal's sure registers (P2).  Both were run on the executable model
first (`CompPairLSXCheck.lean`).

* `GApart` (fact G of a lazy need), `AtGoalRegs` (fact P3: a result entry at
  a goal label reads only the goal entry at its label and registers the run
  allocated), `AtGoalRegs.p2` (P3 and G give P2).
* `ApartS`: P3 of every run under the premises of `LOKS.run` (it does not
  need G, mention the flag nor the semantics).
* `LOKSX`: `LOKS` with G among the premises of `run` and P3 among its
  conclusions; `LOKS.toX` (`LOKS` and `ApartS` give `LOKSX`).

G of the result is not among the conclusions: a result is a goal again only
as the goal of the `p` of `[7 p q]`, and there `p` meets `LOKS false`, which
does not assume G.  It holds on every run of the checker.
* `apartS_n0`, `apartS_n1`: `[0 axe]` (`axe ≥ 1`: the result entry is the goal
  entry seen at `axe`) and `[1 k]` (no entry); `lokSX_n0`, `lokSX_n1`.
* `apartS_seven`: `[7 p q]` from its parts' `LOKS` and `ApartS`; `lokSX_seven`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Fact G**: the entries of a lazy need are apart from its sure registers. -/
def GApart (L : Lazy S) : Prop := ∀ e ∈ entries L, ∀ z, NMem L.sure.ned z → ¬ NMem e.2.sure.ned z

/-- **Fact P3**: a result entry at a goal label reads only registers of the
goal's entry at that label and registers from the run's start to its end. -/
def AtGoalRegs (L : Lazy S) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ e1 ∈ entries nex.laz, e1.1 ∈ (entries L).map Prod.fst → ∀ r, NMem e1.2.sure.ned r →
    (∃ e0 ∈ entries L, e0.1 = e1.1 ∧ NMem e0.2.sure.ned r) ∨ (g0.re ≤ r ∧ r < g1.re)

/-- **P3 and G give P2**: a result entry at a goal label is apart from the
goal's sure registers, when these are below the run's start. -/
theorem AtGoalRegs.p2 {L : Lazy S} {g0 g1 : Gen Map} {nex : NextL S} (h : AtGoalRegs L g0 g1 nex)
    (hG : GApart L) (hsl : ∀ z, NMem L.sure.ned z → z < g0.re) :
    ∀ e ∈ entries L, ∀ e1 ∈ entries nex.laz, e1.1 = e.1 → ∀ z, NMem L.sure.ned z → ¬ NMem e1.2.sure.ned z := by
  intro e he e1 he1 el z hz hz1
  rcases h e1 he1 (el ▸ List.mem_map_of_mem he) z hz1 with ⟨e0, he0, -, hm⟩ | ⟨lo, -⟩
  · exact hG e0 he0 z hz hm
  · have := hsl z hz; omega

/-- **P3 of every run** under the premises of `LOKS.run`. -/
def ApartS (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → th.there ∉ (entries L).map Prod.fst → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    Flat L → Clean L.sure.ned → (∀ e ∈ entries L, Clean e.2.sure.ned) →
    runLC (Map := Map) env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → AtGoalRegs L g0 g1 nex

/-- **`LOKS` with fact G**: G of the goal among the premises of `run`, P3 of
the result (`AtGoalRegs`, which gives P2 by `AtGoalRegs.p2`) among its
conclusions. -/
structure LOKSX (x : Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → th.there ∉ (entries L).map Prod.fst → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    Flat L → Clean L.sure.ned → (∀ e ∈ entries L, Clean e.2.sure.ned) → GApart L →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ((∃ Q, RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      (nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ Flat nex.laz ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned)) ∧
    AtGoalRegs L g0 g1 nex

/-- **`LOKS` and `ApartS` give `LOKSX`.** -/
theorem LOKS.toX {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS (S := S) (Map := Map) x lib N env P f nm) (A : ApartS (S := S) (Map := Map) env nm) :
    LOKSX (S := S) (Map := Map) x lib N env P f nm :=
  ⟨H.clean, fun hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hG hr =>
    ⟨H.run hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr,
      A hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr⟩⟩

/-- A result with no entry at a goal label meets P3. -/
theorem apart_of_new {L : Lazy S} {g0 g1 : Gen Map} {nex : NextL S}
    (h : ∀ e1 ∈ entries nex.laz, e1.1 ∉ (entries L).map Prod.fst) : AtGoalRegs L g0 g1 nex :=
  fun e1 he1 hl => absurd hl (h e1 he1)

/-- A result with no entry meets P3. -/
theorem apart_of_nil {L : Lazy S} {g0 g1 : Gen Map} {nex : NextL S} (h : entries nex.laz = []) :
    AtGoalRegs L g0 g1 nex :=
  apart_of_new fun e he => (by rw [h] at he; cases he)

/-! ## `[0 axe]` and `[1 k]` -/

/-- **`[0 axe]`, `axe ≥ 1`, meets `ApartS`**: its result is the goal (`[0 1]`)
or `+from` of it, entry by entry at the same labels. -/
theorem apartS_n0 (env : CallEnv) {axe : Nat} (ha : 1 ≤ axe) : ApartS (S := S) (Map := Map) env (Nomm.n0 axe) := by
  intro sup L th region g0 g1 nex _ b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl _ hce hr
  rw [runLC_eq env _ rfl] at hr
  have eL : entries L = L.bond := entries_flat hfl
  rcases Nat.lt_or_ge axe 2 with lt | ge
  · obtain rfl : axe = 1 := by omega
    rw [runL_n01_next] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact fun e1 he1 _ r hr => Or.inl ⟨e1, he1, rfl, hr⟩
  · rw [runL_n0_next ge] at hr
    cases hf : fromL axe L with
    | none => rw [hf] at hr; cases hr
    | some L' =>
      rw [hf] at hr
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨f1, e1, m1⟩ := fromL_flat hfl hf
      have eL' : entries L' = L'.bond := entries_flat f1
      -- each result entry is the `+from` of the goal entry at its label
      have back : ∀ e1 ∈ L'.bond, ∃ e ∈ L.bond, e.1 = e1.1 ∧ ∀ r, NMem e1.2.sure.ned r → NMem e.2.sure.ned r := by
        intro e1' he1
        have hl : e1'.1 ∈ L.bond.map Prod.fst := by rw [← e1]; exact List.mem_map_of_mem he1
        obtain ⟨e, he, el⟩ := List.mem_map.mp hl
        obtain ⟨s', hs', hm⟩ := m1 e he
        have nd' : (L'.bond.map Prod.fst).Nodup := by rw [e1, ← eL]; exact hnd
        have := eq_of_label nd' hm he1 el
        subst this
        exact ⟨e, he, rfl, fun r hr => nmem_fromSure hs' (by simpa [ofSure] using hr)⟩
      intro e1' he1 _ r hr
      simp only at he1
      rw [eL'] at he1
      obtain ⟨e0, he0, el, hb⟩ := back e1' he1
      exact Or.inl ⟨e0, by rw [eL]; exact he0, el, hb r hr⟩

/-- **`[1 k]` meets `ApartS`**: its result has no entry. -/
theorem apartS_n1 (env : CallEnv) {k : Noun} : ApartS (S := S) (Map := Map) env (Nomm.n1 k) := by
  intro sup L th region g0 g1 nex _ b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl _ hce hr
  rw [runLC_eq env _ rfl] at hr
  simp only [runL] at hr
  obtain ⟨o, g', _, h'⟩ := bind_some hr
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  exact apart_of_nil (entries_ofSure _)

theorem lokSX_n0 (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {axe : Nat} (ha : 1 ≤ axe)
    (M : MinkEq lib P f (Nomm.n0 axe)) : LOKSX (S := S) (Map := Map) false lib N env P f (Nomm.n0 axe) :=
  (lokS_n0 lib env ha M).toX (apartS_n0 env ha)

theorem lokSX_n1 (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {k : Noun}
    (M : MinkEq lib P f (Nomm.n1 k)) : LOKSX (S := S) (Map := Map) false lib N env P f (Nomm.n1 k) :=
  (lokS_n1 lib env M).toX (apartS_n1 env)

/-! ## `[7 p q]` -/

/-- **`[7 p q]` meets `ApartS`** when its parts meet `LOKS` (any flags) and
`ApartS`: a result entry of `p` at a goal label of the `%7` is at a label of
`q`'s result (`p`'s new labels are above the start), so it reads `q`'s entry
there or `p`'s registers, and `q`'s entry reads the goal's entry there or
`q`'s registers. -/
theorem apartS_seven {xp xq : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun}
    {p q : Nomm} (Lq : LOKS (S := S) (Map := Map) xq lib N env (Img lib P fb) fc q)
    (Lp : LOKS (S := S) (Map := Map) xp lib N env P fb p)
    (Aq : ApartS (S := S) (Map := Map) env q) (Ap : ApartS (S := S) (Map := Map) env p) :
    ApartS (S := S) (Map := Map) env (Nomm.n7 p q) := by
  intro sup L th region g0 g2 nex hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr
  rw [runLC_n7] at hr
  obtain ⟨nx, g1, hq, hp⟩ := bind_some hr
  have cq : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have cp : sixCount p ≤ 255 := by simp only [sixCount] at hcount; omega
  obtain ⟨⟨Qq, Rq⟩, qne, qj, qfl, qec⟩ :=
    Lq.run cq b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hq
  have Pq := Aq cq b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hq
  have qc := Lq.clean hcl' hq
  have hargs : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · simp only [GoalJ] at e; rw [e]; exact hta
  have q1 := Rq.re
  have q2 := Rq.bo
  have Pp := Ap (sup := sup) (L := nx.laz) (th := nx.th) (region := region) cp
    (by omega) (Rq.drop.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb)
    Rq.lo Rq.hi hargs qne Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with h | h
      · have := (hsl x h).1; omega
      · exact h.2, Rq.ncond x hx⟩)
    (fun e he => ⟨by
      rcases (Rq.labs e he).1 with h | h
      · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
        have := (hlab e0 he0).1; rw [e1] at this; omega
      · exact h.2, (Rq.labs e he).2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨by
      rcases (Rq.eregs e he).2 x hx with ⟨e0, he0, h⟩ | h | h
      · have := ((hed e0 he0).2 x h).1; omega
      · have := (hsl x h).1; omega
      · exact h.2, Rq.econd e he x hx⟩⟩) qfl qc qec hp
  obtain ⟨⟨Qp, Rp⟩, -, -, -, -⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region) cp
    (by omega) (Rq.drop.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb)
    Rq.lo Rq.hi hargs qne Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with h | h
      · have := (hsl x h).1; omega
      · exact h.2, Rq.ncond x hx⟩)
    (fun e he => ⟨by
      rcases (Rq.labs e he).1 with h | h
      · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
        have := (hlab e0 he0).1; rw [e1] at this; omega
      · exact h.2, (Rq.labs e he).2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨by
      rcases (Rq.eregs e he).2 x hx with ⟨e0, he0, h⟩ | h | h
      · have := ((hed e0 he0).2 x h).1; omega
      · have := (hsl x h).1; omega
      · exact h.2, Rq.econd e he x hx⟩⟩) qfl qc qec hp
  have p1 := Rp.re
  intro e1 he1 hl r hr
  obtain ⟨e, he, el⟩ := List.mem_map.mp hl
  have hlt := (hlab e he).1
  -- `p`'s result entry is at a label of `q`'s result
  rcases (Rp.labs e1 he1).1 with hl1 | hl1
  · rcases Pp e1 he1 hl1 r hr with ⟨e0, he0, e01, hm⟩ | h
    · have hl0 : e0.1 ∈ (entries L).map Prod.fst := by rw [e01]; exact hl
      rcases Pq e0 he0 hl0 r hm with ⟨e00, he00, e001, hm0⟩ | h
      · exact Or.inl ⟨e00, he00, e001.trans e01, hm0⟩
      · exact Or.inr ⟨h.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · exfalso; rw [← el] at hl1; omega

/-- **`[7 p q]` in `LOKSX`**: `lokS_seven` and `apartS_seven`. -/
theorem lokSX_seven {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun} {p q : Nomm}
    (Lq : LOKS (S := S) (Map := Map) false lib N env (Img lib P fb) fc q)
    (Lp : LOKS (S := S) (Map := Map) false lib N env P fb p)
    (Aq : ApartS (S := S) (Map := Map) env q) (Ap : ApartS (S := S) (Map := Map) env p) :
    LOKSX (S := S) (Map := Map) false lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q) :=
  (lokS_seven Lq Lp).toX (apartS_seven Lq Lp Aq Ap)

end Comp
end SkaModel
end Formalization
