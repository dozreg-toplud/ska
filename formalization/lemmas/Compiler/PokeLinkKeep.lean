import lemmas.Compiler.PokeLinkGood2
import lemmas.Ska.BakeFinal

/-!
# The model's `+ska-poke` keeps the table closed

`CodeClosed` (`PokeLinkGood2.lean`) after a `%full`: every callee in
`calls` and every `%2` info bell of a new entry is a key of the new table.
The new entries are those of `+bake-graph`'s final pass (`finalStep`): the
nomm is `+know` under `bakeRes`, `calls` is `(silt vs)` for `vs` the
`bakeRes` of the sites.  So:

* `knowGo_infos`: every info bell of the nomm `+know` returns is `res` of a
  site it lists (the `%2` case puts the site `(b, k)` and the info `v` with
  `res b k = some v`), and the sites only grow;
* `pick_vars`: the variant `+pick` returns is listed in `vars` for its code
  bell; `bakeRes_cases`: `bakeRes` returns a variant of `vars` or the bake
  `[s fol]` of a bell with a bake `s`;
* `finalFold_calls`: an entry of the final pass has `calls = silt vs` of the
  `bakeRes` of its `+know` sites;
* `bakeGraph_closed`: every callee and info bell of an entry of `bakeGraph`
  is a variant of `E.vars` or a key of the result; `bakeGraph_vars`: every
  variant of the new `vars` is one of `E.vars` or a key of the result;
* `skaPokeB_closed`: with `VarsKeys` (every variant listed in `vars` is a
  key of `code`: checked by `tools/hoon/invdump2.hoon` as `%vars`, 32 mixed
  pokes), `skaPokeB` keeps `CodeClosed` and `VarsKeys`, and old entries;
  `skaCodeKeeps_of_armP`: the same for `anaArmP`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-! ## `+know` -/

/-- **The info bells of `+know`'s nomm are `res` of its sites.** -/
theorem knowGo_infos (fold : Bool) (dat : Bell → Option Datum) (res : Bell → Sock → Option Bell) :
    ∀ (n : Nomm) (sub : Anno) (st : List Site) (r : (Nomm × Anno) × List Site),
      knowGo fold dat res n sub st = some r →
      (∀ s ∈ st, s ∈ r.2) ∧ ∀ c ∈ nommInfos r.1.1, ∃ s ∈ r.2, res s.1 s.2 = some c := by
  intro n
  induction n with
  | cons p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r', hr', h⟩ := h
    obtain ⟨a1, a2⟩ := ihp sub st l hl
    obtain ⟨b1, b2⟩ := ihq sub l.2 r' hr'
    split at h <;> (cases h; refine ⟨fun s hs => b1 s (a1 s hs), ?_⟩)
    · intro c hc; simp [nommInfos] at hc
    · intro c hc
      simp only [nommInfos, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s hs, e⟩
      · exact b2 c hc
  | n0 p =>
    intro sub st r h
    simp only [knowGo] at h
    split at h
    · cases h; exact ⟨fun s hs => hs, fun c hc => by simp [nommInfos] at hc⟩
    · obtain ⟨prod, _, h⟩ := Option.map_eq_some_iff.1 h
      split at h <;> (cases h; exact ⟨fun s hs => hs, fun c hc => by simp [nommInfos] at hc⟩)
  | n1 p =>
    intro sub st r h
    simp only [knowGo, Option.some.injEq] at h
    cases h; exact ⟨fun s hs => hs, fun c hc => by simp [nommInfos] at hc⟩
  | n2 p q info ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨s1, hs1, f, hf, h⟩ := h
    obtain ⟨a1, a2⟩ := ihp sub st s1 hs1
    obtain ⟨b1, b2⟩ := ihq sub s1.2 f hf
    have hold : ∀ c, c ∈ nommInfos s1.1.1 ∨ c ∈ nommInfos f.1.1 → ∃ s ∈ f.2, res s.1 s.2 = some c := by
      rintro c (hc | hc)
      · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s hs, e⟩
      · exact b2 c hc
    split at h
    · cases h
      refine ⟨fun s hs => b1 s (a1 s hs), fun c hc => ?_⟩
      simp only [nommInfos, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact hold c (Or.inl hc)
      · exact hold c (Or.inr hc)
      · simp at hc
    · obtain ⟨v, hv, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      refine ⟨fun s hs => List.mem_cons_of_mem _ (b1 s (a1 s hs)), fun c hc => ?_⟩
      simp only [nommInfos, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · obtain ⟨s, hs, e⟩ := hold c (Or.inl hc); exact ⟨s, List.mem_cons_of_mem _ hs, e⟩
      · obtain ⟨s, hs, e⟩ := hold c (Or.inr hc); exact ⟨s, List.mem_cons_of_mem _ hs, e⟩
      · simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨_, List.mem_cons_self, hv⟩
  | n3 p ihp =>
    intro sub st r h
    simp only [knowGo] at h
    obtain ⟨r', hr', h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihp sub st r' hr'
    split at h <;> (cases h; refine ⟨a1, fun c hc => ?_⟩)
    · simp [nommInfos] at hc
    · exact a2 c (by simpa [nommInfos] using hc)
  | n4 p ihp =>
    intro sub st r h
    simp only [knowGo] at h
    obtain ⟨r', hr', h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihp sub st r' hr'
    split at h <;> (cases h; refine ⟨a1, fun c hc => ?_⟩)
    · simp [nommInfos] at hc
    · exact a2 c (by simpa [nommInfos] using hc)
  | n5 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hpp, h⟩ := h
    obtain ⟨qq, hqq, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihp sub st pp hpp
    obtain ⟨b1, b2⟩ := ihq sub pp.2 qq hqq
    split at h <;> (cases h; refine ⟨fun s hs => b1 s (a1 s hs), fun c hc => ?_⟩)
    · simp [nommInfos] at hc
    · simp only [nommInfos, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s hs, e⟩
      · exact b2 c hc
  | n6 p q r ihp ihq ihr =>
    intro sub st res' h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hpp, h⟩ := h
    obtain ⟨a1, a2⟩ := ihp sub st pp hpp
    split at h
    · obtain ⟨b1, b2⟩ := ihq sub pp.2 res' h
      exact ⟨fun s hs => b1 s (a1 s hs), b2⟩
    · obtain ⟨b1, b2⟩ := ihr sub pp.2 res' h
      exact ⟨fun s hs => b1 s (a1 s hs), b2⟩
    · obtain ⟨qq, hqq, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨rr, hrr, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨b1, b2⟩ := ihq sub pp.2 qq hqq
      obtain ⟨c1, c2⟩ := ihr sub qq.2 rr hrr
      cases h
      refine ⟨fun s hs => c1 s (b1 s (a1 s hs)), fun c hc => ?_⟩
      simp only [nommInfos, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, c1 s (b1 s hs), e⟩
      · obtain ⟨s, hs, e⟩ := b2 c hc; exact ⟨s, c1 s hs, e⟩
      · exact c2 c hc
  | n7 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hpp, h⟩ := h
    obtain ⟨qq, hqq, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihp sub st pp hpp
    obtain ⟨b1, b2⟩ := ihq pp.1.2 pp.2 qq hqq
    split at h <;> (cases h; refine ⟨fun s hs => b1 s (a1 s hs), fun c hc => ?_⟩)
    · exact b2 c hc
    · simp only [nommInfos, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s hs, e⟩
      · exact b2 c hc
  | n10 ax v q ihv ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨dn, hdn, rc, hrc, h⟩ := h
    obtain ⟨a1, a2⟩ := ihv sub st dn hdn
    obtain ⟨b1, b2⟩ := ihq sub dn.2 rc hrc
    split at h
    · cases h; exact ⟨fun s hs => b1 s (a1 s hs), fun c hc => by simp [nommInfos] at hc⟩
    · obtain ⟨s', _, h⟩ := Option.map_eq_some_iff.1 h
      cases h
      refine ⟨fun s hs => b1 s (a1 s hs), fun c hc => ?_⟩
      simp only [nommInfos, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s hs, e⟩
      · exact b2 c hc
  | n11s tag q body ihq =>
    intro sub st r h
    simp only [knowGo] at h
    obtain ⟨qq, hqq, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihq sub st qq hqq
    split at h <;> (cases h; refine ⟨a1, fun c hc => ?_⟩)
    · exact a2 c hc
    · exact a2 c (by simpa [nommInfos] using hc)
  | n11d tag hn q body ihh ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨hh, hhh, h⟩ := h
    obtain ⟨qq, hqq, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihh sub st hh hhh
    obtain ⟨b1, b2⟩ := ihq sub hh.2 qq hqq
    split at h <;> (cases h; refine ⟨fun s hs => b1 s (a1 s hs), fun c hc => ?_⟩)
    · exact b2 c hc
    · simp only [nommInfos, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s hs, e⟩
      · exact b2 c hc
  | n12 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hpp, h⟩ := h
    obtain ⟨qq, hqq, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihp sub st pp hpp
    obtain ⟨b1, b2⟩ := ihq sub pp.2 qq hqq
    cases h
    refine ⟨fun s hs => b1 s (a1 s hs), fun c hc => ?_⟩
    simp only [nommInfos, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s hs, e⟩
    · exact b2 c hc
  | mean p b q body k ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hpp, v, _, h⟩ := h
    obtain ⟨qq, hqq, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := ihp sub st pp hpp
    obtain ⟨b1, b2⟩ := ihq sub _ qq hqq
    cases h
    refine ⟨fun s hs => b1 s (List.mem_cons_of_mem _ (a1 s hs)), fun c hc => ?_⟩
    simp only [nommInfos, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨s, hs, e⟩ := a2 c hc; exact ⟨s, b1 s (List.mem_cons_of_mem _ hs), e⟩
    · exact b2 c hc

theorem know_infos {fold : Bool} {nm : Nomm} {sub : Sock} {dat : Bell → Option Datum}
    {res : Bell → Sock → Option Bell} {nm' : Nomm} {sites : List Site}
    (h : know fold nm sub dat res = some (nm', sites)) :
    ∀ c ∈ nommInfos nm', ∃ s ∈ sites, res s.1 s.2 = some c := by
  unfold know at h
  obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.1 h
  cases e
  exact (knowGo_infos fold dat res nm _ [] r hr).2

/-! ## `+pick` and `bakeRes` -/

variable {M : Type → Type → Type} [Treap M]

theorem pickGate_foldl (k : Sock) (P : Bell → Prop) :
    ∀ (l : List Bell) (acc : Option (Option Bell)), (∀ u, acc = some (some u) → P u) → (∀ v ∈ l, P v) →
      ∀ v, l.foldl (pickGate k) acc = some (some v) → P v
  | [], acc, h0, _, v, h => h0 v h
  | x :: l, acc, h0, hl, v, h => by
    simp only [List.foldl_cons] at h
    refine pickGate_foldl k P l _ ?_ (fun w hw => hl w (List.mem_cons_of_mem _ hw)) v h
    intro u hu
    simp only [pickGate, Option.bind_eq_some_iff] at hu
    obtain ⟨best, hb, hv, _, hu⟩ := hu
    split at hu
    · split at hu
      · cases hu; exact hl x List.mem_cons_self
      · obtain ⟨hh, _, e⟩ := Option.map_eq_some_iff.1 hu
        split at e
        · cases e; exact hl x List.mem_cons_self
        · cases e; exact h0 u (by subst hb; rfl)
    · cases hu; exact h0 u (by subst hb; rfl)

/-- **`+pick` returns a variant listed in `vars`.** -/
theorem pick_vars {vars : M Bell (M Bell Unit)} {c v : Bell} {k : Sock} (h : Bake.pick vars c k = some (some v)) :
    Treap.has (Treap.gut vars c Treap.empty) v = true := by
  unfold Bake.pick at h
  obtain ⟨hh, _, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · refine pickGate_foldl k (fun w => Treap.has (Treap.gut vars c Treap.empty) w = true) _ _
      (fun u hu => by cases hu) (fun w hw => ?_) v h
    obtain ⟨⟨w', u⟩, hw', rfl⟩ := List.mem_map.1 hw
    rw [has_iff]
    exact ⟨u, (Treap.mem_rap _ _ _).1 hw'⟩
  · cases h

/-- **`bakeRes` returns a variant of `vars` or the bake of a bell with one.** -/
theorem bakeRes_cases {E : BEnv M} {st : BSt M} {c : Bell} {k : Sock} {v : Bell}
    (h : bakeRes E st c k = some v) :
    Treap.has (Treap.gut E.vars c Treap.empty) v = true ∨ ∃ s, Treap.get st.bak c = some s ∧ v = ⟨s, c.fol⟩ := by
  unfold bakeRes at h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  cases p with
  | some w => cases h; exact Or.inl (pick_vars hp)
  | none =>
    obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 h
    exact Or.inr ⟨s, hs, e.symm⟩

theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ l, f x = some y
  | [], ys, h, y, hy => by simp at h; subst h; simp at hy
  | x :: l, ys, h, y, hy => by
    cases ha : f x with
    | none => simp [List.mapM_cons, ha] at h
    | some a =>
      cases has : l.mapM f with
      | none => simp [List.mapM_cons, ha, has] at h
      | some as =>
        simp [List.mapM_cons, ha, has] at h
        subst h
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, ha⟩
        · obtain ⟨x', hx', e⟩ := mapM_mem f l as has y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', e⟩

/-! ## The final pass with `calls` -/

/-- **An entry of the final pass**: `calls` is `silt` of the `bakeRes` of
the sites of its `+know`. -/
theorem finalFold_calls (E : BEnv M) (st : BSt M) :
    ∀ (l : List (Bell × Sock)) (out0 out : M Bell (VarEntry M)) (vars0 vars : M Bell (M Bell Unit)),
      l.foldl (finalStep E st) (some (out0, vars0)) = some (out, vars) →
      ∀ v ve, Treap.get out v = some ve → Treap.get out0 v = some ve ∨
        ∃ e ∈ l, ∃ d sites vs, E.dat e.1 = some d ∧
          know E.fold d.nomm e.2 E.dat (bakeRes E st) = some (ve.nomm, sites) ∧
          sites.mapM (fun s => bakeRes E st s.1 s.2) = some vs ∧ ve.calls = Treap.silt vs
  | [], out0, out, vars0, vars, h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun _ _ h => Or.inl h
  | e :: l, out0, out, vars0, vars, h => by
    simp only [List.foldl_cons] at h
    cases h1 : finalStep E st (some (out0, vars0)) e with
    | none => rw [h1, finalFold_none] at h; cases h
    | some p =>
    obtain ⟨out1, vars1⟩ := p
    rw [h1] at h
    have a1 := finalFold_calls E st l out1 out vars1 vars h
    simp only [finalStep, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h1
    obtain ⟨d, hd, ⟨nomm, sites⟩, hk, vs, hvs, he⟩ := h1
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    intro v ve hv
    rcases a1 v ve hv with h | ⟨e', he', h⟩
    · rw [Treap.get_put] at h
      split at h
      · rename_i hv'
        cases h
        exact Or.inr ⟨e, List.mem_cons_self, d, sites, vs, hd, hk, hvs, rfl⟩
      · exact Or.inl h
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h⟩

/-- **The variants of `+bake-graph` call variants of `vars` or of the
result**, and so do their info bells. -/
theorem bakeGraph_closed {E : BEnv M} {n : Nat} {bg : M Bell (VarEntry M) × M Bell (M Bell Unit)}
    (h : bakeGraph E n = some bg) :
    ∀ v ve, Treap.get bg.1 v = some ve →
      ∀ c, (Treap.has ve.calls c = true ∨ c ∈ nommInfos ve.nomm) →
        (∃ c', Treap.has (Treap.gut E.vars c' Treap.empty) c = true) ∨ (Treap.get bg.1 c).isSome := by
  unfold bakeGraph at h
  obtain ⟨st, _, hf⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨out, vars⟩ := bg
  have hall := (finalFold_spec E st _ Treap.empty out E.vars vars hf).2.2.1
  have hres : ∀ c0 k c, bakeRes E st c0 k = some c →
      (∃ c', Treap.has (Treap.gut E.vars c' Treap.empty) c = true) ∨ (Treap.get out c).isSome := by
    intro c0 k c hr
    rcases bakeRes_cases hr with hv | ⟨s, hs, rfl⟩
    · exact Or.inl ⟨c0, hv⟩
    · exact Or.inr (hall (c0, s) ((Treap.mem_rap _ _ _).2 hs))
  intro v ve hv c hc
  rcases finalFold_calls E st _ Treap.empty out E.vars vars hf v ve hv with h0 | ⟨e, _, d, sites, vs, _, hk, hvs, hcalls⟩
  · rw [Treap.get_empty] at h0; cases h0
  · rcases hc with hc | hc
    · rw [hcalls, Treap.has_silt] at hc
      obtain ⟨s, _, hs⟩ := mapM_mem _ sites vs hvs c hc
      exact hres _ _ _ hs
    · obtain ⟨s, _, hs⟩ := know_infos hk c hc
      exact hres _ _ _ hs

/-- **The new `vars`**: a variant listed is one of `E.vars` or a key of the
result. -/
theorem bakeGraph_vars {E : BEnv M} {n : Nat} {bg : M Bell (VarEntry M) × M Bell (M Bell Unit)}
    (h : bakeGraph E n = some bg) :
    ∀ c v, Treap.has (Treap.gut bg.2 c Treap.empty) v = true →
      Treap.has (Treap.gut E.vars c Treap.empty) v = true ∨ (Treap.get bg.1 v).isSome := by
  unfold bakeGraph at h
  obtain ⟨st, _, hf⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨out, vars⟩ := bg
  have hs := finalFold_spec E st _ Treap.empty out E.vars vars hf
  intro c v hv
  rcases hs.2.2.2 c v hv with h1 | ⟨e, he, rfl, rfl⟩
  · exact Or.inl h1
  · exact Or.inr (hs.2.2.1 e he)

/-! ## `+ska-poke` keeps the table closed -/

/-- **Every variant listed in `vars` is a key of `code`** (the key part of
`VarsOK` of `InvB`; `%vars` of `tools/hoon/invdump2.hoon`). -/
def VarsKeys (vars : FinMap Bell (FinMap Bell Unit)) (code : FinMap Bell (VarEntry FinMap)) : Prop :=
  ∀ c v, Treap.has (Treap.gut vars c Treap.empty) v = true → ∃ e, FinMap.get code v = some e

theorem tget_fin {κ ν : Type} [DecidableEq κ] [TKey κ] (m : FinMap κ ν) (k : κ) :
    Treap.get m k = FinMap.get m k := rfl

/-- **The table after a bake is closed** when the old one is and `vars`
lists keys only; the new `vars` lists keys only; old entries stay. -/
theorem addCode_closed {code : FinMap Bell (VarEntry FinMap)} {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)}
    (hc : CodeClosed code) (hv : VarsKeys E.vars code) (h : bakeGraph E n = some bg) :
    CodeClosed (addCode code (newCode code bg.1)) ∧ VarsKeys bg.2 (addCode code (newCode code bg.1)) ∧
      ∀ b e, FinMap.get code b = some e → FinMap.get (addCode code (newCode code bg.1)) b = some e := by
  have hold : ∀ b e, FinMap.get code b = some e → FinMap.get (addCode code (newCode code bg.1)) b = some e := by
    intro b e hb
    rw [← tget_fin, addCode_get, tget_fin, hb]
  have hk : ∀ c, ((∃ c', Treap.has (Treap.gut E.vars c' Treap.empty) c = true) ∨ (Treap.get bg.1 c).isSome) →
      ∃ e', FinMap.get (addCode code (newCode code bg.1)) c = some e' := by
    rintro c (⟨c', hc'⟩ | hs)
    · obtain ⟨e, he⟩ := hv c' c hc'
      exact ⟨e, hold c e he⟩
    · rw [← tget_fin, addCode_get]
      cases hcc : Treap.get code c with
      | some e => exact ⟨e, rfl⟩
      | none => exact Option.isSome_iff_exists.1 hs
  refine ⟨fun b e hb => ?_, fun c v hcv => ?_, hold⟩
  · rw [← tget_fin, addCode_get] at hb
    cases hcb : Treap.get code b with
    | some e0 =>
      rw [hcb] at hb
      have he : e0 = e := Option.some.inj hb
      subst he
      obtain ⟨h1, h2⟩ := hc b e0 hcb
      exact ⟨fun c hc' => by obtain ⟨e', he'⟩ := h1 c hc'; exact ⟨e', hold c e' he'⟩,
        fun c hc' => by obtain ⟨e', he'⟩ := h2 c hc'; exact ⟨e', hold c e' he'⟩⟩
    | none =>
      rw [hcb] at hb
      have hcl := bakeGraph_closed h b e hb
      refine ⟨fun c hc' => hk c (hcl c (Or.inl ?_)), fun c hc' => hk c (hcl c (Or.inr hc'))⟩
      rw [has_iff]; exact ⟨(), hc'⟩
  · rcases bakeGraph_vars h c v hcv with h1 | h1
    · exact hk v (Or.inl ⟨c, h1⟩)
    · exact hk v (Or.inr h1)

/-- **`skaPokeB` keeps the table closed**, `vars` on keys, old entries. -/
theorem skaPokeB_closed {R : Type} (env : Env R) (jet : (Bell → Option Datum) → R → Bell → Bool) (fold frozen : Bool)
    (n : Nat) (bf : BEnv FinMap → Nat) (root : Ident) (L : LongB FinMap) (reg : R)
    (r : Bell × LongB FinMap × R) (hc : CodeClosed L.code) (hv : VarsKeys L.vars L.code)
    (h : skaPokeB env jet fold frozen n bf root L reg = some r) :
    CodeClosed r.2.1.code ∧ VarsKeys r.2.1.vars r.2.1.code ∧
      ∀ b e, FinMap.get L.code b = some e → FinMap.get r.2.1.code b = some e := by
  unfold skaPokeB at h
  obtain ⟨a, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨bg, hbg, rfl⟩ := Option.map_eq_some_iff.1 h
  exact addCode_closed hc hv hbg

/-- **The model's `+ska-poke` keeps the table closed** (with `vars` on
keys, and every old entry). -/
def SkaCodeKeeps (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) : Prop :=
  ∀ (st : PSt) s f r, CodeClosed st.long.code → VarsKeys st.long.vars st.long.code →
    Ar.skaPoke s f st.long st.jets st.hot = some r →
    CodeClosed r.2.1.code ∧ VarsKeys r.2.1.vars r.2.1.code ∧
      ∀ b e, FinMap.get st.long.code b = some e → FinMap.get r.2.1.code b = some e

/-- **`SkaCodeKeeps` of `anaArmP`**, with no hypothesis. -/
theorem skaCodeKeeps_of_armP (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) : SkaCodeKeeps Ar := by
  intro st s f r hc hv e
  rw [hA] at e
  unfold anaArmP at e
  split at e
  · cases e
  · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 e
    exact skaPokeB_closed env _ fold frozen _ bf _ st.long _ r' hc hv hr'

end Compiler
end Formalization
