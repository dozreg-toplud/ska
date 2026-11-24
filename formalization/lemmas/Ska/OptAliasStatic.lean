import lemmas.Ska.OptAliasResult

/-!
# The walk invariant of `+alias` free of executions

`AWInv` of `OptAliasAll.lean` keeps `ABInv` at the end of a walked block only
along executions, through `EndOK`.  The static properties of the blocks
`+alias` returns (`PassOK`, `DownPar`) need it at the end of every walked
block whatever path leads there.  Since `DefW` (the registers with no
definition or a definition that counts in the walked part of `topo`) does not
depend on the path, the invariant can drop paths altogether:

* **`DoneW bl pre`**: the registers whose `old` the walk tracks at the point
  `pre`: no definition, or a definition that counts in a walked block that is a
  parameter or an op of a block that jumps; in `ClR`; no dead fill walked.
* **`SInv`**: `ARev`, `OldW`, the edges of the blocks not walked yet still
  listed, the blocks of `new` walked, every listed edge of a walked block a
  jump of its end after (`live`), the global `old` mapping `DoneW` into `DefW`
  (`glob`), and at the end of every walked jumping block the facts and
  immediates stored for it naming only `DefW` registers, with every register
  its end after reads in `DefW` (`ends`).

At the start of a block, `ABInv` comes from `ends` at one listed predecessor
(`aedge_abinv`) or from `entryInfo`, with `Done` = `DoneW` and the parameters
(`sst_start`); along the body of a jumping block `sst_body` (`ab_op` without
values) keeps it, `BodyOK` coming from `awi_bodyOK` along any path of blocks to
the block (every register `DoneS` holds along a path is in `DoneW`).
**`sst_step`**, **`sst_walk`**: the induction over `topo`; **`sst_at`**: the
invariant right after each walked block.

Also: **`afin_regs`** (every register the end after reads is `old` of one the
end before reads) and **`afin_rev_tgt`** (an edge `aliasFin` leaves listed in
`rev` is a jump of the end after).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-! ## The body without values -/

/-- **`aliasBody` keeps `ABInv`** along a body that meets `BodyOK` (the
structural half of `as_body`, without values). -/
theorem sst_body {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {Cl : Nat → Prop} :
    ∀ (ops : List Pole) (st : ABody) (Def Done : Nat → Prop) (out : List Pole) (st' : ABody),
    aliasBody pick ops st = some (out, st') → ABInv st Def Done Cl → BodyOK Cl ops Def Done →
    ABInv st' (bodyDef ops Def) (bodyDone Cl ops Done) Cl
  | [], st, Def, Done, out, st', h, hi, _ => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hi
  | op :: l, st, Def, Done, out, st', h, hi, hb => by
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    obtain ⟨hsrc, hdst, hb⟩ := hb
    exact sst_body hpick l st1 _ _ out2 st2 h2 (ab_op hpick h1 hi hsrc hdst) hb

theorem sst_bodyDone_mono {Cl : Nat → Prop} : ∀ (l : List Pole) (D D' : Nat → Prop), (∀ x, D x → D' x) →
    ∀ x, bodyDone Cl l D x → bodyDone Cl l D' x
  | [], _, _, h, x, hx => h x hx
  | _ :: l, _, _, h, x, hx => sst_bodyDone_mono l _ _ (fun y hy => hy.imp_left (h y)) x hx

/-! ## The end after -/

theorem sst_jmpRegs_nil {j : Jmp} (h : j.args = []) : jmpRegs j = [] := by simp [jmpRegs, h]

theorem sst_args_nil {z o : Jmp} (h : ¬ (z.args ≠ [] ∨ o.args ≠ [])) : z.args = [] ∧ o.args = [] :=
  ⟨Classical.byContradiction fun hc => h (Or.inl hc), Classical.byContradiction fun hc => h (Or.inr hc)⟩

/-- **The registers the end after reads** are `old` of registers the end
before reads (all of them, the arguments of a hop included). -/
theorem afin_regs {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r)
    (hnl : ∀ n s z o', fin ≠ Termin.lti n s z o') : ∀ x ∈ finRegs r.1, ∃ y ∈ finRegs fin, x = old y := by
  have fold : ∀ rv go cut, ∀ x ∈ finRegs (aliasFold rv o go cut).1, ∃ y ∈ finRegs fin, x = old y := by
    intro rv go cut x hx; simp [aliasFold, finRegs, jmpRegs] at hx
  have one : ∀ s, s ∈ finRegs fin → ∀ x, x = old s → ∃ y ∈ finRegs fin, x = old y :=
    fun s hs x hx => ⟨s, hs, hx⟩
  cases fin with
  | clq s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · rename_i hargs
      obtain ⟨hz, ho⟩ := sst_args_nil hargs
      obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact fold _ _ _
      · split at e
        · subst e; exact fold _ _ _
        · subst e
          intro x hx
          simp only [finRegs, sst_jmpRegs_nil hz, sst_jmpRegs_nil ho, List.append_nil, List.mem_singleton] at hx
          exact one s (by simp [finRegs]) x hx
  | eqq l r' z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · rename_i hargs
      obtain ⟨hz, ho⟩ := sst_args_nil hargs
      split at h
      · cases h
        intro x hx
        simp only [finRegs, sst_jmpRegs_nil hz, sst_jmpRegs_nil ho, List.append_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx
        · exact one l (by simp [finRegs]) x hx
        · exact one r' (by simp [finRegs]) x hx
      · cases h; exact fold _ _ _
  | brn s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · rename_i hargs
      obtain ⟨hz, ho⟩ := sst_args_nil hargs
      obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      have two : ∀ x, x ∈ finRegs (Termin.brz (old s) z o') ∨ x ∈ finRegs (Termin.brn (old s) z o') →
          ∃ y ∈ finRegs (Termin.brn s z o'), x = old y := by
        intro x hx
        simp only [finRegs, sst_jmpRegs_nil hz, sst_jmpRegs_nil ho, List.append_nil, List.mem_singleton,
          or_self] at hx
        exact one s (by simp [finRegs]) x hx
      split at e
      · split at e
        · subst e; exact fun x hx => two x (Or.inl hx)
        · subst e; exact fun x hx => two x (Or.inr hx)
      · subst e; exact fold _ _ _
      · subst e; exact fold _ _ _
      · subst e; intro x hx; simp [finRegs] at hx
  | brz s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · rename_i hargs
      obtain ⟨hz, ho⟩ := sst_args_nil hargs
      obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e
        intro x hx
        simp only [finRegs, sst_jmpRegs_nil hz, sst_jmpRegs_nil ho, List.append_nil, List.mem_singleton] at hx
        exact one s (by simp [finRegs]) x hx
      · subst e; exact fold _ _ _
      · subst e; exact fold _ _ _
  | hop t =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx
    simp only [finRegs, jmpRegs, List.mem_filterMap, List.mem_map, id] at hx
    obtain ⟨a, ⟨a0, ha0, rfl⟩, ha⟩ := hx
    cases a0 with
    | none => cases ha
    | some y =>
      simp only [Option.map_some, Option.some.injEq] at ha
      exact ⟨y, by simp only [finRegs, jmpRegs, List.mem_filterMap, id]; exact ⟨_, ha0, rfl⟩, ha.symm⟩
  | jmp a v =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx
    simp only [finRegs, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  | jmf a v n =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx
    simp only [finRegs, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  | jsp a s =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx; simp only [finRegs, List.mem_singleton] at hx; exact one s (by simp [finRegs]) x hx
  | jsf a s n =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx; simp only [finRegs, List.mem_singleton] at hx; exact one s (by simp [finRegs]) x hx
  | don s =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    intro x hx; simp only [finRegs, List.mem_singleton] at hx; exact one s (by simp [finRegs]) x hx
  | bom u =>
    simp only [aliasFin, Option.some.injEq] at h; subst h; intro x hx; simp [finRegs] at hx
  | lti n s z o' => exact absurd rfl (hnl n s z o')

/-- **An edge `aliasFin` leaves listed is a jump of the end after**: the end
after keeps the targets of the end before, but a fold, which deletes the edge
to the side it cuts, and `[%bom ~]`, which deletes both. -/
theorem afin_rev_tgt {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r) (hn : ∀ o', (rev o').Nodup)
    {x : Nat} (hx : o ∈ r.2.1 x) (hj : ∃ j ∈ getJmps fin, j.there = x) : ∃ j' ∈ getJmps r.1, j'.there = x := by
  have fold : ∀ go cut, (x = go ∨ x = cut) → o ∈ (aliasFold rev o go cut).2.1 x →
      ∃ j' ∈ getJmps (aliasFold rev o go cut).1, j'.there = x := by
    intro go cut hgc hm
    by_cases hg : x = go
    · subst hg; exact ⟨{ args := [], there := x }, by simp [aliasFold, getJmps], rfl⟩
    · have hc : x = cut := hgc.resolve_left hg
      subst hc
      simp only [aliasFold] at hm
      rw [if_neg (fun e => hg e.symm)] at hm
      exact absurd hm (awr_del_gone hn)
  obtain ⟨j, hjm, hjx⟩ := hj
  have two : ∀ z o' : Jmp, j ∈ [z, o'] → (x = z.there ∨ x = o'.there) := by
    intro z o' hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inl hjx.symm
    · exact Or.inr hjx.symm
  have same : ∀ z o' : Jmp, j ∈ [z, o'] → ∃ j' ∈ [z, o'], j'.there = x := fun z o' hm => ⟨j, hm, hjx⟩
  cases fin with
  | clq s z o' =>
    simp only [getJmps] at hjm
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact fold _ _ (two z o' hjm) hx
      · split at e
        · subst e; exact fold _ _ ((two z o' hjm).symm) hx
        · subst e; exact same z o' hjm
  | eqq l r' z o' =>
    simp only [getJmps] at hjm
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h; exact same z o' hjm
      · cases h; exact fold _ _ (two z o' hjm) hx
  | brn s z o' =>
    simp only [getJmps] at hjm
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · split at e
        · subst e; exact same z o' hjm
        · subst e; exact same z o' hjm
      · subst e; exact fold _ _ (two z o' hjm) hx
      · subst e; exact fold _ _ ((two z o' hjm).symm) hx
      · subst e
        exfalso
        simp only at hx
        rcases two z o' hjm with rfl | rfl
        · exact awr_del_gone (awr_del_nodup hn) hx
        · exact awr_del_gone hn (awr_del_sub hx)
  | brz s z o' =>
    simp only [getJmps] at hjm
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact same z o' hjm
      · subst e; exact fold _ _ (two z o' hjm) hx
      · subst e; exact fold _ _ ((two z o' hjm).symm) hx
  | hop t =>
    simp only [getJmps, List.mem_singleton] at hjm
    subst hjm
    simp only [aliasFin, Option.some.injEq] at h; subst h
    exact ⟨{ j with args := j.args.map (Option.map old) }, by simp only [getJmps]; exact List.mem_singleton_self _, hjx⟩
  | lti n s z o' =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    exact ⟨j, hjm, hjx⟩
  | jmp => simp [getJmps] at hjm
  | jmf => simp [getJmps] at hjm
  | jsp => simp [getJmps] at hjm
  | jsf => simp [getJmps] at hjm
  | don => simp [getJmps] at hjm
  | bom => simp [getJmps] at hjm

/-! ## The static invariant -/

theorem sst_pars_nil {g : AGen Map} : ∀ (ps : List Nat) (loc loc0 : AInfo), aliasPars g ps [] loc = some loc0 →
    ∀ r i, loc0 r = some i → loc r = some i ∨ (r ∈ ps ∧ i = {})
  | [], loc, loc0, h, r, i, hr => by
    simp only [aliasPars, Option.some.injEq] at h; subst h; exact Or.inl hr
  | x :: ps, loc, loc0, h, r, i, hr => by
    simp only [aliasPars, List.mapM_nil, List.map_nil] at h
    rcases sst_pars_nil ps _ loc0 h r i hr with h1 | ⟨h1, h2⟩
    · by_cases e : r = x
      · subst e; rw [as_upd_self] at h1; cases h1
        exact Or.inr ⟨List.mem_cons_self, by simp [paramInfo]⟩
      · rw [as_upd_other _ _ e] at h1; exact Or.inl h1
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- `rev` only shrinks along the walk. -/
theorem sst_rev_sub {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') (hn : ∀ o', (g.rev o').Nodup) {x q : Nat} (hq : q ∈ g'.rev x) :
    q ∈ g.rev x := by
  unfold aliasBlock at h
  dsimp only at h
  split at h
  · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (awr_drop o (getJmps b.fin) g.rev hn).2.1 x q hq
  · obtain ⟨info, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨imms, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨edges, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨loc0, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rb, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rf, hf, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (awr_fin hf hn).2 x q hq

/-- A dropped block leaves no edge of its own listed. -/
theorem sst_drop_gone {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') (hd : g.rev o = [] ∧ o ≠ 0) (hn : ∀ o', (g.rev o').Nodup)
    (hs : ∀ x, o ∈ g.rev x → ∃ b j, HoonMap.get bl o = some b ∧ j ∈ getJmps b.fin ∧ j.there = x)
    (x : Nat) : o ∉ g'.rev x := by
  unfold aliasBlock at h
  dsimp only at h
  rw [if_pos hd] at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨-, n2, n3⟩ := awr_drop o (getJmps b.fin) g.rev hn
  intro hm
  obtain ⟨b2, j, hb2, hj, hjx⟩ := hs x (n2 x o hm)
  rw [hb] at hb2; cases hb2
  rw [← hjx] at hm
  exact n3 j hj hm

theorem sst_drop_new {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') (hd : g.rev o = [] ∧ o ≠ 0) : g'.new = g.new := by
  unfold aliasBlock at h
  dsimp only at h
  rw [if_pos hd] at h
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

section
variable [MapKeys Map]

/-- **The registers whose `old` the static invariant tracks** at the point
`pre`: no definition, or a definition that counts in a walked block, a
parameter or an op of a block that jumps; in `ClR`; no dead fill walked. -/
def DoneW (bl : Map Blob) (pre : List Nat) (x : Nat) : Prop :=
  (x ∉ allDefs bl ∨ ∃ s, LiveDef bl x s ∧ s.1 ∈ pre ∧
    (s.2 = none ∨ ∃ b j, HoonMap.get bl s.1 = some b ∧ j ∈ getJmps b.fin)) ∧
  ClR bl x ∧ ∀ o' i, DeadFill bl x o' i → o' ∉ pre

theorem sst_doneW_defW {bl : Map Blob} {pre : List Nat} {x : Nat} (h : DoneW bl pre x) : DefW bl pre x := by
  rcases h.1 with h1 | ⟨s, hs, hp, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨s, hs, hp⟩

/-- **The walk invariant of `+alias` free of executions**, at the point `pre`
of the walk over `topo` with state `g`. -/
structure SInv (bl : Map Blob) (topo pre : List Nat) (g : AGen Map) : Prop where
  rev : ARev bl topo pre g
  oldw : OldW bl pre g
  pend : ∀ q b j, q ∈ topo → q ∉ pre → HoonMap.get bl q = some b → j ∈ getJmps b.fin → q ∈ g.rev j.there
  news : ∀ k, (HoonMap.get g.new k).isSome → k ∈ pre
  live : ∀ x q, q ∈ g.rev x → q ∈ pre →
    ∃ pb j, HoonMap.get g.new q = some pb ∧ j ∈ getJmps pb.fin ∧ j.there = x
  glob : ∀ d, DoneW bl pre d → DefW bl pre (g.old d)
  ends : ∀ q b j pb, q ∈ pre → HoonMap.get bl q = some b → j ∈ getJmps b.fin → HoonMap.get g.new q = some pb →
    ∃ lq mq, g.info q = some lq ∧ g.imms q = some mq ∧ (∀ x ∈ finRegs pb.fin, DefW bl pre x) ∧
      ALoc (DefW bl pre) lq ∧ ∀ n r, r ∈ mq n → DefW bl pre r

theorem sst_init {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR bl topo rev) :
    SInv bl topo [] (aliasInit (Map := Map) rev) where
  rev := arev_init hT.2
  oldw := fun _ hd => (hd rfl).elim
  pend := fun q b j hq _ hb hj => awr_dedup_mem.mpr (hT.1.2 q b j hq hb hj)
  news := fun k hk => by simp [aliasInit, HoonMap.get_empty] at hk
  live := fun _ _ _ hq => absurd hq List.not_mem_nil
  glob := fun d hd => by
    rcases hd.1 with h | ⟨s, -, hs, -⟩
    · exact Or.inl h
    · exact absurd hs List.not_mem_nil
  ends := fun _ _ _ _ hq => absurd hq List.not_mem_nil

/-- The blocks of a path to the next block of `topo` were walked. -/
theorem sst_path_pre {bl : Map Blob} {pre l : List Nat} {o : Nat} (ht : TopoOK bl (pre ++ o :: l)) (hopre : o ∉ pre)
    {p : List Nat} (hπ : BPath bl (o :: p)) : ∀ o' ∈ p, o' ∈ pre := by
  intro o' ho'
  have hlt := (awi_bpath_idx ht hπ rfl).2 o' ho'
  rw [idxOf_pre hopre] at hlt
  exact mem_pre_of_idx (l := o :: l) hlt

/-- A block after `o` in `topo` is not walked at `o`. -/
theorem sst_not_pre {pre l : List Nat} {o x : Nat} (hnd : (pre ++ o :: l).Nodup)
    (hlt : (pre ++ o :: l).idxOf o < (pre ++ o :: l).idxOf x) : x ∉ pre ++ [o] := by
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp hnd).2.2 o h' o List.mem_cons_self rfl
  intro hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [idxOf_pre hopre, List.idxOf_append, if_pos hx] at hlt
    have := List.idxOf_lt_length_of_mem hx
    omega
  · rw [List.mem_singleton] at hx; rw [hx] at hlt; exact Nat.lt_irrefl _ hlt

/-- **What `DoneS` holds along a path to the next block is in `DoneW`** or a
parameter of the block. -/
theorem sst_doneS {bl : Map Blob} {pre l : List Nat} {o : Nat} (ht : TopoOK bl (pre ++ o :: l)) (hopre : o ∉ pre)
    {p : List Nat} {b : Blob} (hπ : BPath bl (o :: p)) {x : Nat} (hx : DoneS bl pre p b x) :
    DoneW bl pre x ∨ (x ∈ b.par ∧ ClR bl x) := by
  obtain ⟨hd, hc, hf⟩ := hx
  rcases hd with hd | hd | ⟨o', ho', b', hb', hd⟩
  · exact Or.inl ⟨Or.inl hd, hc, hf⟩
  · exact Or.inr ⟨hd, hc⟩
  · left
    have hR' : Reach bl o' := ssk_bpath_reach hπ o' (List.mem_cons_of_mem _ ho')
    have hpre' := sst_path_pre ht hopre hπ o' ho'
    obtain ⟨b'', j, hb'', hj⟩ := bdef_jumps hπ rfl o' ho'
    rw [hb'] at hb''; cases hb''
    refine ⟨Or.inr ?_, hc, hf⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact ⟨(o', none), awi_par_live hR' hb' hd, hpre', Or.inl rfl⟩
    · obtain ⟨i, op, hi, he⟩ := bdef_idx hd
      exact ⟨(o', some i), awi_jump_live hR' hb' hj hi he, hpre', Or.inr ⟨b', j, hb', hj⟩⟩

/-- **`ABInv` at the start of a walked block**, from `ends` at a listed
predecessor or from `entryInfo` at block `0`, with `Def` the registers of
`DefW` and the parameters, `Done` those of `DoneW` and the parameters of
`ClR`. -/
theorem sst_start {bl : Map Blob} (hS : AliasSSAB bl) {nargs : Nat} {pre l : List Nat} {o : Nat} {g : AGen Map}
    (ht : TopoOK bl (pre ++ o :: l)) (hI : SInv bl (pre ++ o :: l) pre g) {b : Blob}
    (hb : HoonMap.get bl o = some b) (hR : Reach bl o)
    {info : AInfo} {imms : AImms} {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : (if g.rev o = [] then some (entryInfo nargs) else aliasStart g o (g.rev o)) = some info)
    (him : aliasStartImms g (g.rev o) = some imms) (hed : aliasEdges g o (g.rev o) = some edges)
    (hpa : aliasPars g b.par edges info = some loc0) :
    ABInv ⟨g.old, loc0, imms⟩ (fun x => DefW bl pre x ∨ x ∈ b.par)
      (fun x => DoneW bl pre x ∨ (x ∈ b.par ∧ ClR bl x)) (ClR bl) := by
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have npar : ∀ x ∈ b.par, ¬ DefW bl pre x := fun x hx => awi_par_notDefW hS.1 hR hb hx hopre
  have hself : ∀ d, ¬ (DefW bl pre d ∨ d ∈ b.par) → ClR bl d → g.old d = d :=
    fun d hn hc => awi_self hS ht hI.oldw hc (fun h => hn (Or.inl h))
  have hparold : ∀ x ∈ b.par, ClR bl x → g.old x = x := fun x hx hc => awi_self hS ht hI.oldw hc (npar x hx)
  by_cases h0 : g.rev o = []
  · rw [if_pos h0] at hst
    cases hst
    rw [h0] at him hed
    simp only [aliasStartImms, Option.some.injEq] at him
    subst him
    simp [aliasEdges] at hed
    subst hed
    have hloc : ∀ r i, loc0 r = some i → i = {} := by
      intro r i hr
      rcases sst_pars_nil b.par _ loc0 hpa r i hr with hr | ⟨-, hr⟩
      · simp only [entryInfo] at hr
        split at hr
        · cases hr; rfl
        · cases hr
      · exact hr
    refine ⟨fun n r hr => absurd hr List.not_mem_nil, ⟨fun r i x hr hx => ?_, fun r i hr => Or.inl (hloc r i hr)⟩,
      fun d hd => ?_, fun d hd => ?_, hself⟩
    · rw [hloc r i hr] at hx; exact absurd hx ab_nm_empty
    · show DefW bl pre (g.old d) ∨ g.old d ∈ b.par
      rcases hd with hd | hd
      · exact Or.inl (hI.glob d hd)
      · rw [hparold d hd.1 hd.2]; exact Or.inr hd.1
    · rcases hd with hd | hd
      · exact Or.inl (sst_doneW_defW hd)
      · exact Or.inr hd.1
  · rw [if_neg h0] at hst
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h0
    obtain ⟨hqT, bq, jq, hbq, hjq, hjqo⟩ := hI.rev.sound o q hq
    have hqpre : q ∈ pre := awr_pre ht hqT hbq hjq hjqo
    obtain ⟨pb, j, hpb, hj, hjo⟩ := hI.live o q hq hqpre
    obtain ⟨lq, mq, hlq, hmq, hfr, hal, him'⟩ := hI.ends q bq jq pb hqpre hbq hjq hpb
    have hab : ABInv ⟨g.old, lq, mq⟩ (DefW bl pre) (DoneW bl pre) (ClR bl) :=
      ⟨him', hal, fun d hd => hI.glob d hd, fun d hd => sst_doneW_defW hd,
        fun d hn hc => awi_self hS ht hI.oldw hc hn⟩
    exact aedge_abinv hst him hed hpa hq hlq hmq hpb hab hj hjo (fun x h => Or.inl h) (fun x h => Or.inr h)
      (fun x hx => hfr x (awk_finReads_sub hx))
      (fun x hx => hx.imp (fun h => ⟨h, rfl⟩) (fun h => ⟨h.1, hparold x h.1 h.2⟩)) hself

end

/-! ## The induction over `topo` -/

section
variable [MapKeys Map]

/-- **One block of the walk keeps `SInv`.** -/
theorem sst_step {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    {bl : Map Blob} (hD : DInvS bl) {pre l : List Nat} {o : Nat} {g g' : AGen Map}
    (ht : TopoOK bl (pre ++ o :: l)) (hI : SInv bl (pre ++ o :: l) pre g)
    (h : aliasBlock pick nargs bl g o = some g') : SInv bl (pre ++ o :: l) (pre ++ [o]) g' := by
  have hS : AliasSSAB bl := hD.2.1
  have hA : Acyclic bl := hD.1.1.2.1
  have hnl : NoLti bl := hD.2.2
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hoo : o ∈ pre ++ [o] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hmono : ∀ x, DefW bl pre x → DefW bl (pre ++ [o]) x :=
    fun x => DefW.mono fun a ha => List.mem_append_left _ ha
  obtain ⟨hrev', hcase⟩ := arev_step ht hI.rev h
  have hw' := awi_old_step ht hI.rev hI.oldw h
  have pend' : ∀ q b j, q ∈ pre ++ o :: l → q ∉ pre ++ [o] → HoonMap.get bl q = some b → j ∈ getJmps b.fin →
      q ∈ g'.rev j.there := by
    intro q b j hq hqp hb hj
    have hqo : q ≠ o := fun e => hqp (by rw [e]; exact hoo)
    exact awa_rev_keep h (hI.pend q b j hq (fun h' => hqp (List.mem_append_left _ h')) hb hj) hqo
  -- a register of `DoneW` at the next point that `DefW` held before
  have notDst : ∀ d s b, DoneW bl (pre ++ [o]) d → LiveDef bl d s → (∀ k, s ≠ (o, some k)) → Reach bl o →
      HoonMap.get bl o = some b → d ∉ b.body.filterMap aliasDst := by
    intro d s b hd hs hne hR hb hm
    obtain ⟨k, op, hk, he⟩ := bdef_idx hm
    by_cases hdf : DeadFill bl d o k
    · exact hd.2.2 o k hdf hoo
    · exact hne k (hS.1 d _ _ hs ⟨hR, ⟨b, op, hb, hk, he⟩, fun i hi => by cases hi; exact hdf⟩)
  have globA : ∀ d, DoneW bl (pre ++ [o]) d → DefW bl pre d → DoneW bl pre d ∧
      ∀ b, Reach bl o → HoonMap.get bl o = some b → d ∉ b.body.filterMap aliasDst := by
    intro d hd hdw
    obtain ⟨h1, hc, hf⟩ := hd
    refine ⟨⟨?_, hc, fun o' i hdf ho' => hf o' i hdf (List.mem_append_left _ ho')⟩, fun b hR hb => ?_⟩
    · rcases h1 with h1 | ⟨s, hs, -, hsj⟩
      · exact Or.inl h1
      · rcases hdw with hdw | ⟨s0, hs0, hs0p⟩
        · exact Or.inl hdw
        · have e := hS.1 d _ _ hs hs0
          subst e
          exact Or.inr ⟨s, hs, hs0p, hsj⟩
    · rcases hdw with hdw | ⟨s0, hs0, hs0p⟩
      · intro hm; exact hdw (bdef_allDefs hb (List.mem_append_right _ hm))
      · exact notDst d s0 b ⟨h1, hc, hf⟩ hs0 (fun k e => hopre (by rw [e] at hs0p; exact hs0p)) hR hb
  have globB : ∀ d, DoneW bl (pre ++ [o]) d → ¬ DefW bl pre d →
      g.old d = d ∧ ∃ s, LiveDef bl d s ∧ s.1 = o ∧
        (s.2 = none ∨ ∃ b j, HoonMap.get bl o = some b ∧ j ∈ getJmps b.fin) := by
    intro d hd hdw
    refine ⟨awi_self hS ht hI.oldw hd.2.1 hdw, ?_⟩
    rcases hd.1 with h1 | ⟨s, hs, hsp, hsj⟩
    · exact absurd (Or.inl h1) hdw
    · rcases List.mem_append.mp hsp with hsp | hsp
      · exact absurd (Or.inr ⟨s, hs, hsp⟩) hdw
      · have e : s.1 = o := List.mem_singleton.mp hsp
        refine ⟨s, hs, e, ?_⟩
        rw [e] at hsj; exact hsj
  by_cases hd : g.rev o = [] ∧ o ≠ 0
  · -- the block is dropped
    have hold : g'.old = g.old := awi_block_drop h hd.1 hd.2
    have hnew : g'.new = g.new := sst_drop_new h hd
    have hgn : HoonMap.get g.new o = none := by
      cases e : HoonMap.get g.new o with
      | none => rfl
      | some _ => exact absurd (hI.news o (by rw [e]; rfl)) hopre
    refine ⟨hrev', hw', pend', fun k hk => ?_, fun x q hq hqp => ?_, fun d hd' => ?_,
      fun q b j pb hq hb hj hpb => ?_⟩
    · rw [hnew] at hk; exact List.mem_append_left _ (hI.news k hk)
    · rcases List.mem_append.mp hqp with hqp | hqp
      · obtain ⟨pb, j, hpb, hj, hjo⟩ := hI.live x q (sst_rev_sub h hI.rev.nodup hq) hqp
        exact ⟨pb, j, by rw [hnew]; exact hpb, hj, hjo⟩
      · have e := List.mem_singleton.mp hqp
        subst e
        exact absurd hq (sst_drop_gone h hd hI.rev.nodup (fun x hm => (hI.rev.sound x q hm).2) x)
    · rw [hold]
      by_cases hdw : DefW bl pre d
      · exact hmono _ (hI.glob d (globA d hd' hdw).1)
      · obtain ⟨e, s, hs, hso, -⟩ := globB d hd' hdw
        rw [e]; exact Or.inr ⟨s, hs, by rw [hso]; exact hoo⟩
    · rw [hnew] at hpb
      rcases List.mem_append.mp hq with hq | hq
      · have hqo : q ≠ o := fun e => hopre (e ▸ hq)
        obtain ⟨c1, c2, -⟩ := (awk_block h).2 q hqo
        obtain ⟨lq, mq, h1, h2, h3, h4, h5⟩ := hI.ends q b j pb hq hb hj hpb
        exact ⟨lq, mq, c1.trans h1, c2.trans h2, fun x hx => hmono x (h3 x hx), ab_loc_mono h4 hmono,
          fun n r hr => hmono r (h5 n r hr)⟩
      · have e := List.mem_singleton.mp hq
        subst e
        rw [hgn] at hpb; cases hpb
  · -- the block is walked
    have hR : Reach bl o := by
      rcases hcase with ⟨h0, ho0, -⟩ | ⟨hR, -⟩
      · exact absurd ⟨h0, ho0⟩ hd
      · exact hR
    obtain ⟨info, imms, b, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ := awa_block_parts h hd
    have hab0 := sst_start hS ht hI e3 hR e1 e2 e4 e5
    have hnewo : HoonMap.get g'.new o = some { par := b.par, body := rb.1, fin := rf.1 } := by
      rw [e8]; simp only [HoonMap.get_put, if_true]
    have hnewk : ∀ k, k ≠ o → HoonMap.get g'.new k = HoonMap.get g.new k := fun k hk => by
      rw [e8]; simp only [HoonMap.get_put, hk, if_false]
    have hold' : g'.old = rb.2.old := by rw [e8]
    have hinfo : g'.info o = some rb.2.loc := by rw [e8]; exact as_upd_self _ _ _
    have himms : g'.imms o = some rb.2.imml := by rw [e8]; exact as_upd_self _ _ _
    have hrevf : g'.rev = rf.2.1 := by rw [e8]
    have news' : ∀ k, (HoonMap.get g'.new k).isSome → k ∈ pre ++ [o] := by
      intro k hk
      by_cases ek : k = o
      · rw [ek]; exact hoo
      · rw [hnewk k ek] at hk; exact List.mem_append_left _ (hI.news k hk)
    have live' : ∀ x q, q ∈ g'.rev x → q ∈ pre ++ [o] →
        ∃ pb j, HoonMap.get g'.new q = some pb ∧ j ∈ getJmps pb.fin ∧ j.there = x := by
      intro x q hq hqp
      rcases List.mem_append.mp hqp with hqp | hqp
      · have hqo : q ≠ o := fun e => hopre (e ▸ hqp)
        obtain ⟨pb, j, hpb, hj, hjo⟩ := hI.live x q (sst_rev_sub h hI.rev.nodup hq) hqp
        exact ⟨pb, j, by rw [hnewk q hqo]; exact hpb, hj, hjo⟩
      · have e := List.mem_singleton.mp hqp
        subst e
        rw [hrevf] at hq
        obtain ⟨-, b2, j, hb2, hj, hjx⟩ := hI.rev.sound x q ((awr_fin e7 hI.rev.nodup).2 x q hq)
        rw [e3] at hb2; cases hb2
        obtain ⟨j', hj', hjx'⟩ := afin_rev_tgt e7 hI.rev.nodup hq ⟨j, hj, hjx⟩
        exact ⟨_, j', hnewo, hj', hjx'⟩
    have endsPre : ∀ q b j pb, q ∈ pre → HoonMap.get bl q = some b → j ∈ getJmps b.fin →
        HoonMap.get g'.new q = some pb →
        ∃ lq mq, g'.info q = some lq ∧ g'.imms q = some mq ∧ (∀ x ∈ finRegs pb.fin, DefW bl (pre ++ [o]) x) ∧
          ALoc (DefW bl (pre ++ [o])) lq ∧ ∀ n r, r ∈ mq n → DefW bl (pre ++ [o]) r := by
      intro q b j pb hq hb hj hpb
      have hqo : q ≠ o := fun e => hopre (e ▸ hq)
      obtain ⟨c1, c2, c3⟩ := (awk_block h).2 q hqo
      rw [c3] at hpb
      obtain ⟨lq, mq, h1, h2, h3, h4, h5⟩ := hI.ends q b j pb hq hb hj hpb
      exact ⟨lq, mq, c1.trans h1, c2.trans h2, fun x hx => hmono x (h3 x hx), ab_loc_mono h4 hmono,
        fun n r hr => hmono r (h5 n r hr)⟩
    have globPre : ∀ d, DoneW bl (pre ++ [o]) d → DefW bl pre d → DefW bl (pre ++ [o]) (g'.old d) := by
      intro d hd' hdw
      obtain ⟨hdn, hnd⟩ := globA d hd' hdw
      rw [hold', awk_body_old b.body _ rb.1 rb.2 e6 d (hnd b hR e3)]
      exact hmono _ (hI.glob d hdn)
    have globPar : ∀ d, DoneW bl (pre ++ [o]) d → LiveDef bl d (o, none) → g.old d = d →
        DefW bl (pre ++ [o]) (g'.old d) := by
      intro d hd' hs he
      rw [hold', awk_body_old b.body _ rb.1 rb.2 e6 d (notDst d _ b hd' hs (fun k e => by cases e) hR e3)]
      dsimp only
      rw [he]
      exact Or.inr ⟨(o, none), hs, hoo⟩
    by_cases hjmp : ∃ j, j ∈ getJmps b.fin
    · -- a jumping block: `ABInv` along its body
      obtain ⟨j0, hj0⟩ := hjmp
      obtain ⟨p, hπ⟩ := awi_reach_bpath hR
      have hnodf : ∀ k r, k < b.body.length → ¬ DeadFill bl r o k := fun k r _ hdf => by
        obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
        rw [e3] at hb3; cases hb3; rw [hu] at hj0; simp [getJmps] at hj0
      have hBO := awi_bodyOK hS hA hπ e3 hnodf hopre
        (Done := fun x => DoneW bl pre x ∨ (x ∈ b.par ∧ ClR bl x))
        (fun x h1 h2 h3 => sst_doneS ht hopre hπ (awi_doneS_body hopre x h1 h2 h3))
      rw [List.take_length] at hBO
      have habE := sst_body hpick b.body _ _ _ rb.1 rb.2 e6 hab0 hBO
      have hsubF : ∀ x, bodyDef b.body (fun x => DefW bl pre x ∨ x ∈ b.par) x → DefW bl (pre ++ [o]) x := by
        intro x hx
        rcases awa_bodyDef_cases _ _ x hx with (h' | h') | h'
        · exact hmono x h'
        · exact Or.inr ⟨(o, none), awi_par_live hR e3 h', hoo⟩
        · obtain ⟨i, op, hi, he⟩ := bdef_idx h'
          exact Or.inr ⟨(o, some i), awi_jump_live hR e3 hj0 hi he, hoo⟩
      have habE' := awa_abinv_mono habE hsubF (fun _ h' => h')
      have hfin : ∀ y ∈ finRegs b.fin,
          bodyDone (ClR bl) b.body (fun x => DoneW bl pre x ∨ (x ∈ b.par ∧ ClR bl x)) y := by
        intro y hy
        have := awa_read_done (k := b.body.length) hS hπ e3 hopre (x := y) (Or.inr ⟨rfl, hy⟩)
        rw [List.take_length] at this
        exact sst_bodyDone_mono _ _ _ (fun x hx => sst_doneS ht hopre hπ hx) y this
      refine ⟨hrev', hw', pend', news', live', fun d hd' => ?_, fun q b2 j pb hq hb2 hj hpb => ?_⟩
      · by_cases hdw : DefW bl pre d
        · exact globPre d hd' hdw
        · obtain ⟨e, s, hs, hso, -⟩ := globB d hd' hdw
          obtain ⟨o1, k1⟩ := s
          simp only at hso
          subst hso
          cases k1 with
          | none => exact globPar d hd' hs e
          | some k =>
            obtain ⟨b3, op, hb3, hk, hdst⟩ := hs.2.1
            rw [e3] at hb3; cases hb3
            have hm : d ∈ b.body.filterMap aliasDst := List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hk, hdst⟩
            rw [hold']
            exact habE'.old d (awa_bodyDone_dst _ _ _ hm hd'.2.1)
      · rcases List.mem_append.mp hq with hq | hq
        · exact endsPre q b2 j pb hq hb2 hj hpb
        · have e := List.mem_singleton.mp hq
          subst e
          rw [hnewo] at hpb; cases hpb
          refine ⟨rb.2.loc, rb.2.imml, hinfo, himms, fun x hx => ?_, habE'.loc, habE'.imm⟩
          obtain ⟨y, hy, rfl⟩ := afin_regs e7 (hnl q b e3) x hx
          exact habE'.old y (hfin y hy)
    · -- a block that does not jump: only its parameters are tracked
      refine ⟨hrev', hw', pend', news', live', fun d hd' => ?_, fun q b2 j pb hq hb2 hj hpb => ?_⟩
      · by_cases hdw : DefW bl pre d
        · exact globPre d hd' hdw
        · obtain ⟨e, s, hs, hso, hsj⟩ := globB d hd' hdw
          obtain ⟨o1, k1⟩ := s
          simp only at hso
          subst hso
          cases k1 with
          | none => exact globPar d hd' hs e
          | some k =>
            rcases hsj with hsj | ⟨b3, j3, hb3, hj3⟩
            · cases hsj
            · rw [e3] at hb3; cases hb3; exact absurd ⟨j3, hj3⟩ hjmp
      · rcases List.mem_append.mp hq with hq | hq
        · exact endsPre q b2 j pb hq hb2 hj hpb
        · have e := List.mem_singleton.mp hq
          subst e
          rw [e3] at hb2; cases hb2
          exact absurd ⟨j, hj⟩ hjmp

/-- **`SInv` along a part of the walk.** -/
theorem sst_walk_part {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    {bl : Map Blob} (hD : DInvS bl) : ∀ (l pre r : List Nat) (g g' : AGen Map), TopoOK bl (pre ++ l ++ r) →
      SInv bl (pre ++ l ++ r) pre g → aliasWalk pick nargs bl l g = some g' →
      SInv bl (pre ++ l ++ r) (pre ++ l) g'
  | [], pre, r, g, g', _, hI, h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    simpa using hI
  | o :: l, pre, r, g, g', ht, hI, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have ht0 : TopoOK bl (pre ++ o :: (l ++ r)) := by simpa using ht
    have hI0 : SInv bl (pre ++ o :: (l ++ r)) pre g := by simpa using hI
    have hI1 := sst_step hpick hD ht0 hI0 h1
    have ht' : TopoOK bl ((pre ++ [o]) ++ l ++ r) := by simpa using ht
    have hI1' : SInv bl ((pre ++ [o]) ++ l ++ r) (pre ++ [o]) g1 := by simpa using hI1
    have := sst_walk_part hpick hD l (pre ++ [o]) r g1 g' ht' hI1' h
    simpa using this

/-- **`SInv` right after a walked block** of the walk over the whole `topo`. -/
theorem sst_at {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {nargs : Nat}
    {bl : Map Blob} (hD : DInvS bl) {topo : List Nat} {rev : Map (List Nat)} (hT : TopoInvR bl topo rev)
    {pre l : List Nat} {o : Nat} {g1 g2 : AGen Map} (hto : topo = pre ++ o :: l)
    (h1 : aliasWalk pick nargs bl pre (aliasInit rev) = some g1) (h2 : aliasBlock pick nargs bl g1 o = some g2) :
    SInv bl topo (pre ++ [o]) g2 := by
  subst hto
  have hI : SInv bl (pre ++ o :: l) pre g1 := by
    have := sst_walk_part hpick hD pre [] (o :: l) _ g1 (by simpa using hT.1.1)
      (by simpa using sst_init (Map := Map) hT) h1
    simpa using this
  exact sst_step hpick hD hT.1.1 hI h2

end

end Opt
end SkaModel
end Formalization
