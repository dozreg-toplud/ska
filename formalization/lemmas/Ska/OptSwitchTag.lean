import lemmas.Ska.OptSwitchSim

/-!
# `+switch-chains`: one tagged chain replaced keeps the code

The macro step of `OptSwitchSim.lean` for a tagged chain, and with it
**`tag_keeps_of`**: one application of `switchTag` keeps the code
(`Keeps`), given the facts on the chain that `TagHyp` lists.

* `tag_walk`: the code before, from the end of the head (a `%clq s` to the
  yes side of the first test and to its no side), walks the chain: on an atom
  it follows the no sides to the final miss; on a cell it runs each test
  (`%hed s d`, `%imm c r`, `%eqq` of `d` and `r`) until the first whose
  constant is the head, whose hit it takes (`tagTarget`, `chainPick`).  It
  changes only the registers `d` and `r` of the tests it runs.
* `treeGo_good`: the code after runs its search tree from the root as a path
  of good configurations (its reads are of the head register, which holds the
  value, and of the leaf register, which the leaf has just set) to the block
  `treeGo` names, with one leaf register set.
* `tag_head`: the macro step at the head: on an atom the code after jumps to
  the final miss at once, on a cell it jumps to the yes side of the first
  test, does the `%hed` there and runs the tree; both arrive at the same block
  with registers that agree off the registers of the chain.

`TagHyp` is what is left to derive from `chainOf`, `testOf`, `DInv` and
`TopoOK` (not done here): the shape of the chain's blocks (`TagBlocks`), the
hypotheses of `tag_tree` (distinct labels, leaf registers other than the
head), the hits and the final miss outside the region and other than the
head, no reachable block outside the region jumping into it, no reachable
block outside it mentioning a register of a test, and block `0` outside it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- The block the chain takes on the value of `s`: on a cell the hit of the
first test whose constant is its head, else the final miss. -/
def tagTarget (cs : List STest) (mis : Nat) : Noun → Nat
  | Noun.cell h _ => chainPick cs mis h
  | Noun.atom _ => mis

/-- The registers the tests of a chain write. -/
def tagRegs (cs : List STest) : List Nat := cs.flatMap fun t => [t.d, t.r]

/-- The blocks of a tagged chain on `s` with final miss `mis`: the yes side
of each test (no parameters, a `%hed s d` and an `%imm c r` in either order,
an `%eqq` of `d` and `r` to its hit and its no side), and the no side of each
test but the last (no parameters, no body, the `%clq s` of the next test). -/
def TagBlocks (M : Map Blob) (s mis : Nat) : List STest → Prop
  | [] => False
  | t :: rest => t.s = s ∧ t.d ≠ t.r ∧ s ≠ t.d ∧ s ≠ t.r ∧
      (∃ l r body, HoonMap.get M t.y = some ⟨[], body, Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩⟩ ∧
        ((l = t.d ∧ r = t.r) ∨ (l = t.r ∧ r = t.d)) ∧
        (body = [Pole.hed s t.d, Pole.imm (A t.c) t.r] ∨ body = [Pole.imm (A t.c) t.r, Pole.hed s t.d])) ∧
      (match rest with
       | [] => t.miss = mis
       | t2 :: _ => HoonMap.get M t.miss = some ⟨[], [], Termin.clq s ⟨[], t2.y⟩ ⟨[], t2.miss⟩⟩) ∧
      (rest ≠ [] → TagBlocks M s mis rest)

theorem chainPick_cons (t : STest) (rest : List STest) (mis : Nat) (h : Noun) :
    chainPick (t :: rest) mis h = if h = A t.c then t.hit else chainPick rest mis h := by
  unfold chainPick
  by_cases e : h = A t.c <;> simp [List.find?_cons, e]

section
variable {σ : Type}

theorem execPole_imm (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (n : Noun) (d : Nat)
    (regs : Map (Option Noun)) (t : Trace) :
    execPole lib O gul st (Pole.imm n d) regs t = some (Tone.zero (A 0), store d n regs, t, st) := by
  simp [execPole, localPole]

theorem execPole_hed (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) {s d : Nat} {regs : Map (Option Noun)}
    {h tl : Noun} (hs : read s regs = some (Noun.cell h tl)) (t : Trace) :
    execPole lib O gul st (Pole.hed s d) regs t = some (Tone.zero (A 0), store d h regs, t, st) := by
  simp [execPole, localPole, hs]

theorem get_store_ne {r k : Nat} (h : k ≠ r) (v : Noun) (regs : Map (Option Noun)) :
    HoonMap.get (store r v regs) k = HoonMap.get regs k := by
  simp [store, HoonMap.get_put, h]

/-- **The code before walks the chain** from the end of a block whose `%clq s`
goes to the yes side and the no side of the first test. -/
theorem tag_walk (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (s mis : Nat)
    (hm : (HoonMap.get c.blocks mis).isSome) :
    ∀ (cs : List STest) (x : Cfg σ Map) (vs : Noun), TagBlocks c.blocks s mis cs →
      (∀ t ∈ cs, (HoonMap.get c.blocks t.hit).isSome) →
      (∃ t ∈ cs.head?, x.b.fin = Termin.clq s ⟨[], t.y⟩ ⟨[], t.miss⟩) →
      x.params = [] → x.b.par = [] → x.b.body = [] → read s x.regs = some vs → Reach c.blocks x.lab →
      (∃ b, HoonMap.get c.blocks x.lab = some b ∧ b.fin = x.b.fin) →
      ∃ es R' bT, HoonMap.get c.blocks (tagTarget cs mis vs) = some bT ∧
        Steps lib O c gul x es ⟨tagTarget cs mis vs, bT, [], R', x.t, x.st⟩ ∧
        Reach c.blocks (tagTarget cs mis vs) ∧ ∀ k, k ∉ tagRegs cs → HoonMap.get R' k = HoonMap.get x.regs k
  | [], _, _, hb, _, _, _, _, _, _, _, _ => absurd hb id
  | t :: rest, x, vs, hb, hhit, ⟨t', ht', hfin⟩, hp, hq, hbd, hs, hreach, ⟨bx, hbx, hbxf⟩ => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ht'
    subst ht'
    obtain ⟨hts, hdr, hsd, hsr, ⟨l, r, body, hby, hlr, hbody⟩, hnext, hrest⟩ := hb
    have hregs : ∀ k, k ∉ tagRegs (t :: rest) → k ≠ t.d ∧ k ≠ t.r ∧ k ∉ tagRegs rest := by
      intro k hk
      simp only [tagRegs, List.flatMap_cons, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hk
      exact ⟨hk.1.1, hk.1.2, hk.2⟩
    -- the jump to the no side of `t`, from a configuration whose end is the `%clq` or the `%eqq`
    have tail : ∀ (z : Cfg σ Map) (bz : Blob), z.params = [] → z.b.par = [] → z.b.body = [] →
        taken z.regs z.b.fin = some ⟨[], t.miss⟩ → read s z.regs = some vs → Reach c.blocks z.lab →
        HoonMap.get c.blocks z.lab = some bz → bz.fin = z.b.fin →
        ⟨[], t.miss⟩ ∈ getJmps bz.fin →
        ∃ es R' bT, HoonMap.get c.blocks (tagTarget rest mis vs) = some bT ∧
          Steps lib O c gul z es ⟨tagTarget rest mis vs, bT, [], R', z.t, z.st⟩ ∧
          Reach c.blocks (tagTarget rest mis vs) ∧
          ∀ k, k ∉ tagRegs rest → HoonMap.get R' k = HoonMap.get z.regs k := by
      intro z bz zp zq zb ztk zs zr hbz hbzf hj
      have hr2 : Reach c.blocks t.miss := Reach.jump zr hbz hj
      cases rest with
      | nil =>
        simp only at hnext
        subst hnext
        obtain ⟨bm, hbm⟩ := Option.isSome_iff_exists.mp hm
        have e1 : tagTarget [] t.miss vs = t.miss := by cases vs <;> rfl
        rw [e1]
        exact ⟨_, z.regs, bm, hbm, Steps.step (Step.jump zp zq zb ztk hbm) (Steps.refl _), hr2,
          fun _ _ => rfl⟩
      | cons t2 rest2 =>
        simp only at hnext
        have s1 := Step.jump (lib := lib) (O := O) (gul := gul) zp zq zb ztk hnext
        obtain ⟨es, R', bT, hbT, hsT, hrT, hfr⟩ := tag_walk lib O c gul s mis hm (t2 :: rest2)
          ⟨t.miss, ⟨[], [], Termin.clq s ⟨[], t2.y⟩ ⟨[], t2.miss⟩⟩, [], z.regs, z.t, z.st⟩ vs
          (hrest (List.cons_ne_nil _ _)) (fun u hu => hhit u (List.mem_cons_of_mem _ hu))
          ⟨t2, rfl, rfl⟩ rfl rfl rfl zs hr2 ⟨_, hnext, rfl⟩
        exact ⟨_, R', bT, hbT, Steps.step s1 hsT, hrT, hfr⟩
    cases vs with
    | atom a =>
      have htk : taken x.regs x.b.fin = some ⟨[], t.miss⟩ := by rw [hfin]; simp [taken, hs]
      obtain ⟨es, R', bT, hbT, hsT, hrT, hfr⟩ := tail x bx hp hq hbd htk hs hreach hbx hbxf
        (by rw [hbxf, hfin]; simp [getJmps])
      refine ⟨es, R', bT, hbT, hsT, hrT, fun k hk => hfr k (hregs k hk).2.2⟩
    | cell h tl =>
      have htk : taken x.regs x.b.fin = some ⟨[], t.y⟩ := by rw [hfin]; simp [taken, hs]
      have hjy : (⟨[], t.y⟩ : Jmp) ∈ getJmps bx.fin := by rw [hbxf, hfin]; simp [getJmps]
      have s1 := Step.jump (lib := lib) (O := O) (gul := gul) hp hq hbd htk hby
      have hry : Reach c.blocks t.y := Reach.jump hreach hbx hjy
      -- the two ops of the yes side
      have hR2 : ∃ es2 R2, Steps lib O c gul ⟨t.y, ⟨[], body, Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩⟩, [], x.regs,
          x.t, x.st⟩ es2 ⟨t.y, ⟨[], [], Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩⟩, [], R2, x.t, x.st⟩ ∧
          read t.d R2 = some h ∧ read t.r R2 = some (A t.c) ∧ read s R2 = some (Noun.cell h tl) ∧
          ∀ k, k ≠ t.d → k ≠ t.r → HoonMap.get R2 k = HoonMap.get x.regs k := by
        rcases hbody with rfl | rfl
        · refine ⟨[] ++ ([] ++ []), _, Steps.step (Step.op rfl rfl rfl (execPole_hed lib O gul x.st hs x.t))
            (Steps.step (Step.op rfl rfl rfl (execPole_imm lib O gul x.st _ _ _ x.t)) (Steps.refl _)),
            by rw [read_store_other hdr, read_store_self], read_store_self _ _ _,
            by rw [read_store_other hsr, read_store_other hsd]; exact hs,
            fun k h1 h2 => by rw [get_store_ne h2, get_store_ne h1]⟩
        · have hs' : read s (store t.r (A t.c) x.regs) = some (Noun.cell h tl) := by
            rw [read_store_other hsr]; exact hs
          refine ⟨[] ++ ([] ++ []), _, Steps.step (Step.op rfl rfl rfl (execPole_imm lib O gul x.st _ _ _ x.t))
            (Steps.step (Step.op rfl rfl rfl (execPole_hed lib O gul x.st hs' x.t)) (Steps.refl _)),
            read_store_self _ _ _, by rw [read_store_other (Ne.symm hdr), read_store_self],
            by rw [read_store_other hsd]; exact hs',
            fun k h1 h2 => by rw [get_store_ne h1, get_store_ne h2]⟩
      obtain ⟨es2, R2, hs2, rd, rr, rs2, hfr2⟩ := hR2
      have htk2 : taken R2 (Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩) =
          some (if h = A t.c then ⟨[], t.hit⟩ else ⟨[], t.miss⟩) := by
        rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [taken, rd, rr]
        · simp only [taken, rd, rr, Option.bind_some, Option.map_some]
          by_cases e : h = A t.c
          · simp [e]
          · simp [e, Ne.symm e]
      have hje : ∀ j, j = (if h = A t.c then (⟨[], t.hit⟩ : Jmp) else ⟨[], t.miss⟩) →
          j ∈ getJmps (Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩) := by
        intro j hj; subst hj; split <;> simp [getJmps]
      by_cases e : h = A t.c
      · rw [if_pos e] at htk2
        obtain ⟨bh, hbh⟩ := Option.isSome_iff_exists.mp (hhit t List.mem_cons_self)
        have tgt : tagTarget (t :: rest) mis (Noun.cell h tl) = t.hit := by
          simp only [tagTarget, chainPick_cons, if_pos e]
        rw [tgt]
        refine ⟨_, R2, bh, hbh, Steps.step s1 (steps_trans hs2 (Steps.step (Step.jump rfl rfl rfl htk2 hbh)
          (Steps.refl _))), Reach.jump (j := ⟨[], t.hit⟩) hry hby (by simp [getJmps]), fun k hk => hfr2 k (hregs k hk).1 (hregs k hk).2.1⟩
      · rw [if_neg e] at htk2
        obtain ⟨es3, R', bT, hbT, hsT, hrT, hfr⟩ := tail ⟨t.y, ⟨[], [], Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩⟩, [], R2,
          x.t, x.st⟩ _ rfl rfl rfl htk2 rs2 hry hby rfl (by simp [getJmps])
        have tgt : tagTarget (t :: rest) mis (Noun.cell h tl) = tagTarget rest mis (Noun.cell h tl) := by
          simp only [tagTarget, chainPick_cons, if_neg e]
        rw [tgt]
        refine ⟨_, R', bT, hbT, Steps.step s1 (steps_trans hs2 hsT), hrT, fun k hk => ?_⟩
        rw [hfr k (hregs k hk).2.2]
        exact hfr2 k (hregs k hk).1 (hregs k hk).2.1

/-- **The code after runs its tree as a path of good configurations.** -/
theorem treeGo_good (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) {d : Nat} {rs : List Nat}
    {v : Noun} : ∀ (n lab : Nat) (b : Blob) (regs : Map (Option Noun)) (t : Trace) (st : σ) (k : Nat) (bk : Blob),
      read d regs = some v → treeGo c.blocks d rs v n b = some k → HoonMap.get c.blocks k = some bk →
      ∃ r ∈ rs, ∃ w, GoodTo lib O c gul ⟨lab, b, [], regs, t, st⟩ ⟨k, bk, [], store r w regs, t, st⟩
  | 0, _, b, _, _, _, _, _, _, h, _ => by simp [treeGo] at h
  | n + 1, lab, b, regs, t, st, k, bk, hv, h, hbk => by
    rw [treeGo.eq_def] at h
    split at h
    · simp at h
    · rename_i n' c0 d' l r heq
      obtain rfl : n = n' := Nat.succ.inj heq
      by_cases hd' : d' = d
      · subst hd'
        simp only [if_true] at h
        cases hg : HoonMap.get c.blocks (if ltOf c0 v then l else r) with
        | none => simp [hg] at h
        | some b'' =>
        simp only [hg, Option.bind_some] at h
        obtain ⟨r', hr', w, hgo⟩ := treeGo_good lib O c gul n (if ltOf c0 v then l else r) b'' regs t st k bk hv h hbk
        refine ⟨r', hr', w, GoodTo.step ?_ (Step.jump (j := ⟨[], if ltOf c0 v then l else r⟩) rfl rfl rfl ?_ hg) hgo⟩
        · refine ⟨fun k hk => ?_, fun k hk => by simp at hk, fun p rest _ _ hb => by simp at hb⟩
          obtain ⟨-, -, hk⟩ := hk
          rcases hk with ⟨p, rest, hb, -⟩ | ⟨-, hk⟩
          · simp at hb
          · simp only [finReads, List.mem_singleton] at hk
            subst hk; exact ⟨v, hv⟩
        · simp only [taken, hv, Option.map_some, Option.some.injEq]
          cases v with
          | cell _ _ => simp [ltOf]
          | atom a => by_cases ha : a < c0 <;> simp [ltOf, ha]
      · simp [hd'] at h
    · rename_i n' c0 r0 d' r' hit mis heq
      by_cases hc : d' = d ∧ r' = r0 ∧ r0 ≠ d ∧ r0 ∈ rs
      · obtain ⟨rfl, rfl, hne, hin⟩ := hc
        simp only [hne, hin, ne_eq, not_false_eq_true, and_self, if_true, Option.some.injEq] at h
        refine ⟨r', hin, A c0, ?_⟩
        have hv' : read d' (store r' (A c0) regs) = some v := by rw [read_store_other (Ne.symm hne)]; exact hv
        have hr0 : read r' (store r' (A c0) regs) = some (A c0) := read_store_self _ _ _
        refine GoodTo.step ?_ (Step.op rfl rfl rfl (execPole_imm lib O gul st _ _ _ t)) ?_
        · refine ⟨fun k hk => ?_, fun k hk => by simp at hk, fun p rest _ _ hb _ => ?_⟩
          · obtain ⟨-, -, hk⟩ := hk
            rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, -⟩
            · simp only [List.cons.injEq] at hb; obtain ⟨rfl, -⟩ := hb; simp [poleReads] at hk
            · simp at hb
          · simp only [List.cons.injEq] at hb; obtain ⟨rfl, -⟩ := hb; simp [execPole_imm]
        · have htk : taken (store r' (A c0) regs) (Termin.eqq d' r' ⟨[], hit⟩ ⟨[], mis⟩) =
              some ⟨[], if v = A c0 then hit else mis⟩ := by
            simp only [taken, hv', hr0, Option.bind_some, Option.map_some]
            by_cases e : v = A c0 <;> simp [e]
          subst h
          refine GoodTo.step ?_ (Step.jump rfl rfl rfl htk hbk) (GoodTo.here _)
          refine ⟨fun k hk => ?_, fun k hk => by simp at hk, fun p rest _ _ hb => by simp at hb⟩
          obtain ⟨-, -, hk⟩ := hk
          rcases hk with ⟨p, rest, hb, -⟩ | ⟨-, hk⟩
          · simp at hb
          · simp only [finReads, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl
            · exact ⟨v, hv'⟩
            · exact ⟨_, hr0⟩
      · simp [hc] at h
    · simp at h

theorem tagTarget_mem (cs : List STest) (mis : Nat) (vs : Noun) :
    tagTarget cs mis vs = mis ∨ ∃ t ∈ cs, tagTarget cs mis vs = t.hit := by
  cases vs with
  | atom _ => exact Or.inl rfl
  | cell h _ =>
    simp only [tagTarget, chainPick]
    cases e : cs.find? (fun t => decide (h = A t.c)) with
    | none => exact Or.inl rfl
    | some t => exact Or.inr ⟨t, List.mem_of_find?_eq_some e, rfl⟩

end

/-- The labels inside a tagged chain's region: the yes side of the first
test and `tagIds`. -/
def TagIn (t0 : STest) (tl : List STest) (k : Nat) : Prop := k = t0.y ∨ k ∈ tagIds (t0 :: tl)

/-- **What one application of `switchTag` at `o` needs of the chain**, all
of it about the blocks before. -/
structure TagHyp (M : Map Blob) (o : Nat) (t0 : STest) (tl : List STest) : Prop where
  nd : (tagIds (t0 :: tl)).Nodup
  hy : t0.y ∉ tagIds (t0 :: tl)
  ho : o ∉ tagIds (t0 :: tl)
  hoy : o ≠ t0.y
  hr : ∀ t ∈ t0 :: tl, t.r ≠ t0.d
  blocks : TagBlocks M t0.s (tagMiss t0 tl) (t0 :: tl)
  headFin : ∃ b, HoonMap.get M o = some b ∧ b.fin = Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], t0.miss⟩
  hits : ∀ t ∈ t0 :: tl, (HoonMap.get M t.hit).isSome ∧ ¬ TagIn t0 tl t.hit ∧ t.hit ≠ o
  miss : (HoonMap.get M (tagMiss t0 tl)).isSome ∧ ¬ TagIn t0 tl (tagMiss t0 tl) ∧ tagMiss t0 tl ≠ o
  noI : ∀ k b j, Reach M k → ¬ TagIn t0 tl k → k ≠ o → HoonMap.get M k = some b → j ∈ getJmps b.fin →
    ¬ TagIn t0 tl j.there
  ment : ∀ k b, Reach M k → ¬ TagIn t0 tl k → HoonMap.get M k = some b → ∀ r ∈ blobMentions b,
    r ∉ tagRegs (t0 :: tl)
  zero : ¬ TagIn t0 tl 0

section
variable {M out' : Map Blob} {fuel o : Nat} {t0 : STest} {tl : List STest} {done done' : List Nat}

/-- The region of one tagged chain. -/
theorem tag_region (h : switchTag M M fuel o (t0 :: tl) done = some (out', done')) (H : TagHyp M o t0 tl) :
    RegionHyp M out' (TagIn t0 tl) (· = o) (fun k => k ∈ tagRegs (t0 :: tl)) := by
  obtain ⟨b, nb, nf, hb, hbo, -, -, hfr, -⟩ := tag_tree h H.nd H.hy H.ho H.hoy H.hr
  obtain ⟨b1, hb1, hf1⟩ := H.headFin
  rw [hb] at hb1; cases hb1
  refine ⟨fun k hk hh => ?_, fun k hk => ?_, fun k b j hr hk hh hb hj => H.noI k b j hr hk hh hb hj,
    fun k b hr hk hb r hm => H.ment k b hr hk hb r hm, H.zero⟩
  · exact hfr k hh (fun e => hk (Or.inl e)) (fun e => hk (Or.inr e))
  · subst hk
    refine ⟨fun e => e.elim H.hoy H.ho, b, t0.s, _, _, _, _, hb, hf1, hbo⟩

/-- **The macro step at the head of a tagged chain.** -/
theorem tag_head {σ : Type} (lib : Lib) (O : Oracle σ) (gul : Noun) (c : Straight Map) (hc : c.blocks = M)
    (h : switchTag M M fuel o (t0 :: tl) done = some (out', done')) (H : TagHyp M o t0 tl) :
    HeadStep lib O gul c (withBlocks c out') (TagIn t0 tl) (· = o) (fun k => k ∈ tagRegs (t0 :: tl)) := by
  subst hc
  obtain ⟨b, nb, nf, hb, hbo, hby, hgo, hfr, -⟩ := tag_tree h H.nd H.hy H.ho H.hoy H.hr
  obtain ⟨b1, hb1, hf1⟩ := H.headFin
  rw [hb] at hb1; cases hb1
  have hR := tag_region h H
  intro x x' hA hh hp hq hbd htk
  have hA0 := hA
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  rw [hh] at hb0 hb0'
  rw [hb] at hb0; cases hb0
  have hb0'' : HoonMap.get out' o = some b0' := hb0'
  rw [hbo] at hb0''; cases hb0''
  have hs_ment : t0.s ∉ tagRegs (t0 :: tl) :=
    H.ment o b (hh ▸ hreach) (hh ▸ hI) hb t0.s (mentions_fin b t0.s (by rw [hf1]; simp [finRegs, jmpRegs]))
  have hfx : x.b.fin = Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], t0.miss⟩ := by rw [hf, hf1]
  have hfx' : x'.b.fin = Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], tagMiss t0 tl⟩ := by rw [hb']
  have hrd : read t0.s x'.regs = read t0.s x.regs := hag.rd hs_ment
  obtain ⟨vs, hvs⟩ : ∃ vs, read t0.s x.regs = some vs := by
    rcases htk with h1 | h1
    · rw [hfx] at h1; simp only [taken, Option.isSome_map] at h1
      exact Option.isSome_iff_exists.mp h1
    · rw [hfx'] at h1; simp only [taken, Option.isSome_map, hrd] at h1
      exact Option.isSome_iff_exists.mp h1
  have hvs' : read t0.s x'.regs = some vs := by rw [hrd]; exact hvs
  obtain ⟨es, R', bT, hbT, hsT, hrT, hfrT⟩ := tag_walk lib O c gul t0.s (tagMiss t0 tl) H.miss.1 (t0 :: tl) x vs
    H.blocks (fun t ht => (H.hits t ht).1) ⟨t0, rfl, hfx⟩ hp hq hbd hvs hreach ⟨b, hh ▸ hb, by rw [hfx, hf1]⟩
  have hTI : ¬ TagIn t0 tl (tagTarget (t0 :: tl) (tagMiss t0 tl) vs) ∧
      tagTarget (t0 :: tl) (tagMiss t0 tl) vs ≠ o := by
    rcases tagTarget_mem (t0 :: tl) (tagMiss t0 tl) vs with e | ⟨t, ht, e⟩
    · rw [e]; exact H.miss.2
    · rw [e]; exact (H.hits t ht).2
  generalize hT : tagTarget (t0 :: tl) (tagMiss t0 tl) vs = T at hbT hsT hrT hTI
  have hbT' : HoonMap.get (withBlocks c out').blocks T = some bT := by
    show HoonMap.get out' T = some bT
    rw [hR.same T hTI.1 hTI.2]; exact hbT
  -- the relation at the target, for any registers after that agree off the chain
  have atT : ∀ R'' : Map (Option Noun), (∀ k, k ∉ tagRegs (t0 :: tl) → HoonMap.get R'' k = HoonMap.get x'.regs k) →
      SwA c.blocks (withBlocks c out').blocks (TagIn t0 tl) (fun k => k ∈ tagRegs (t0 :: tl))
        (⟨T, bT, [], R', x.t, x.st⟩ : Cfg σ Map) ⟨T, bT, [], R'', x'.t, x'.st⟩ := by
    intro R'' hR''
    refine ⟨rfl, rfl, ht, hst, hrT, hTI.1, ⟨bT, bT, hbT, hbT', rfl, rfl, fun _ h => h⟩, fun k hk => by simp at hk,
      fun k hk => ?_⟩
    rw [hfrT k hk, hR'' k hk]
    exact hag k hk
  have good0 : GoodAt lib O gul x' := by
    refine ⟨fun k hk => ?_, fun k hk => by rw [hpe, hp] at hk; simp at hk, fun p rest _ _ hb2 => ?_⟩
    · obtain ⟨-, -, hk⟩ := hk
      rcases hk with ⟨p, rest, hb2, -⟩ | ⟨-, hk⟩
      · rw [hb'] at hb2; rw [hbd] at hb2; cases hb2
      · rw [hfx'] at hk; simp only [finReads, List.mem_singleton] at hk; subst hk; exact ⟨vs, hvs'⟩
    · rw [hb'] at hb2; rw [hbd] at hb2; cases hb2
  have hp' : x'.params = [] := by rw [hpe, hp]
  have hq' : x'.b.par = [] := by rw [hb']; exact hq
  have hbd' : x'.b.body = [] := by rw [hb']; exact hbd
  have hne : T ≠ x.lab := by rw [hh]; exact hTI.2
  cases vs with
  | atom a =>
    obtain rfl : tagMiss t0 tl = T := hT
    have htk' : taken x'.regs x'.b.fin = some ⟨[], tagMiss t0 tl⟩ := by rw [hfx']; simp [taken, hvs']
    refine ⟨_, ⟨tagMiss t0 tl, bT, [], x'.regs, x'.t, x'.st⟩, es, hsT,
      GoodTo.step good0 (Step.jump hp' hq' hbd' htk' hbT') (GoodTo.here _), atT x'.regs (fun _ _ => rfl), hne,
      by rw [hl]; exact hne⟩
  | cell hh0 tl0 =>
    have htk' : taken x'.regs x'.b.fin = some ⟨[], t0.y⟩ := by rw [hfx']; simp [taken, hvs']
    have hby' : HoonMap.get (withBlocks c out').blocks t0.y = some ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩ := hby
    have s1 := Step.jump (lib := lib) (O := O) (gul := gul) hp' hq' hbd' htk' hby'
    have hhed := execPole_hed lib O gul x'.st (d := t0.d) hvs' x'.t
    have s2 := Step.op (lib := lib) (O := O) (c := withBlocks c out') (gul := gul)
      (x := ⟨t0.y, ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩, [], x'.regs, x'.t, x'.st⟩) rfl rfl rfl hhed
    have good1 : GoodAt lib O gul (⟨t0.y, ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩, [], x'.regs, x'.t, x'.st⟩ : Cfg σ Map) := by
      refine ⟨fun k hk => ?_, fun k hk => by simp at hk, fun p rest _ _ hb2 _ => ?_⟩
      · obtain ⟨-, -, hk⟩ := hk
        rcases hk with ⟨p, rest, hb2, hk⟩ | ⟨hb2, -⟩
        · simp only [List.cons.injEq] at hb2; obtain ⟨rfl, -⟩ := hb2
          simp only [poleReads, List.mem_singleton] at hk; subst hk; exact ⟨_, hvs'⟩
        · cases hb2
      · simp only [List.cons.injEq] at hb2; obtain ⟨rfl, -⟩ := hb2
        rw [hhed]; rfl
    have hrd0 : read t0.d (store t0.d hh0 x'.regs) = some hh0 := read_store_self _ _ _
    obtain ⟨r, hr, w, hg⟩ := treeGo_good lib O (withBlocks c out') gul fuel t0.y ⟨[], nb, nf⟩
      (store t0.d hh0 x'.regs) x'.t x'.st T bT hrd0 (by rw [← hT]; exact hgo hh0) hbT'
    have hrZ : r ∈ tagRegs (t0 :: tl) := by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      simp only [tagRegs, List.mem_flatMap]
      exact ⟨t, ht, by simp⟩
    have hdZ : t0.d ∈ tagRegs (t0 :: tl) := by simp [tagRegs]
    refine ⟨_, ⟨T, bT, [], store r w (store t0.d hh0 x'.regs), x'.t, x'.st⟩, es, hsT,
      GoodTo.step good0 s1 (GoodTo.step good1 s2 hg), atT _ (fun k hk => ?_), hne, by rw [hl]; exact hne⟩
    have h1 : k ≠ r := fun e => hk (by rw [e]; exact hrZ)
    have h2 : k ≠ t0.d := fun e => hk (by rw [e]; exact hdZ)
    rw [get_store_ne h1, get_store_ne h2]

end

/-- **One application of `switchTag` keeps the code**, given `TagHyp`. -/
theorem tag_keeps_of (c : Straight Map) {out' : Map Blob} {fuel o : Nat} {t0 : STest} {tl : List STest}
    {done done' : List Nat} (h : switchTag c.blocks c.blocks fuel o (t0 :: tl) done = some (out', done'))
    (H : TagHyp c.blocks o t0 tl) : Keeps c (withBlocks c out') :=
  region_keeps c out' (tag_region h H) (fun lib _ O gul => tag_head lib O gul c rfl h H)

end Opt
end SkaModel
end Formalization
