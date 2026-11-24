import lemmas.Ska.CompLBFour

/-!
# `[4 p]` with a calling `p` under a lazy goal whose sure part asks nothing

README Gaps 12.23, the case `%h4c` of `tools/hoon/calldump4.hoon`
(`[[4 [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]`): the head `[4 p]` with a calling
`p` runs under the bond goal `mk bunt [] [(3, this v1)]` behind the tail's
call.  `+collapse-lazy-atom` takes a fresh register `r` (the goal's sure
part asks nothing), puts `mov` of a proxy of `r` at the bond block, then the
block of the increment writes `r` and `p` runs under `%next (lazy-from-reg
arg)` into it: `8: inc v8 v6`, `3: mov v7 v1` with `v7` a proxy of `v6`.
This is `kerfLC` with `+collapse-lazy-atom` (`CollPre`, `CollP`) in place
of `+kerf` (`KernPW`).

* `collWit r`: the witness of the collapse, `r` holding the product (an
  atom).
* `collLC`: `CollPre` under a goal whose sure part is the bunt, and
  `RunOKGC` of the rest under `%next (lazy-from-reg r) th`, give `RunOKLC`
  under the goal.
* `four_runBond`: `[4 p]` with an operand meeting `UOKC` under such a goal
  (`collapsePre_spec`, the block of the increment, `unaryGC_ok`, `collLC`).
* `bondOKC_fourC`, `bondOKC_fourA`: `[4 p]` as a head under the bond goal.
* `h4c_example`: `[[4 [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]`, both halves (its
  raw blocks are the `#guard` `%h4c` of `CompRunOKLC.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The witness of `+collapse-lazy-atom`**: `r` holds the product, an
atom. -/
def collWit (r : Nat) : Wit := fun _ v d w => (∃ m, v = A m) ∧ d = Need.this r ∧ w = v

/-- **`+collapse-lazy-atom` and the rest, under a goal whose sure part is the
bunt** (`kerfLC` for the collapse): `CollPre` from `g0` to `g2` with the
register `r`, and `RunOKGC` of the rest under `%next (lazy-from-reg r)` at
the label the collapse picked, give `RunOKLC` with the witness `collWit r`.
`hatom`: the formula's products are atoms. -/
theorem collLC {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {g0 g2 g1 : Gen Map}
    {r there : Nat} {nex : NextL S} (CP : CollPre L th g0 g2 r there) (hL : L.sure = Sure.bunt)
    (hu : UpBelow g0) (h2 : th.there < g0.bo) (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (hec : ∀ e ∈ entries L, ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hatom : ∀ s gul n tm p, P s → minkF lib gul n tm s f = some (Tone.zero p) → ∃ m, p = A m)
    (R : RunOKGC lib P f (CGoal.next (lazyReg r : Sure S) (jmp0 there)) g2 g1 nex) :
    RunOKLC (Map := Map) lib P f L th (collWit r) g0 g1 nex := by
  have Re := R.ext
  have rl := R.ext.1
  have bl := R.ext.2.1
  have c1 := CP.le
  have c2 := CP.bo1
  have rlt := CP.rlt
  have rge : g0.re ≤ r := CP.rreg.resolve_left (fun h => by rw [hL] at h; exact h)
  have hth : th.args = [] := CP.args
  -- the shape: every atom fits the bunt, so the collapse hops to `th`
  have hthere : there = th.there := by
    rcases CP.shape with ⟨e, _⟩ | ⟨_, _, nf, _⟩
    · exact e
    · exact absurd (by rw [hL]; exact fitsS_bunt (A 0)) (nf 0)
  have hj : jmp0 there = th := by rw [hthere]; exact jmp0_of_args hth
  have lab' : ∀ e ∈ entries nex.laz, g2.bo ≤ e.1 := fun e he => (R.labs e he).1
  have nR : ∀ x, NMem L.sure.ned x → False := fun x hx => by rw [hL] at hx; exact hx
  have hcf2 : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ x, x < g2.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun cf hcf x hx =>
    (hcf x (by omega)).trans (R.cfr.get_lt hx)
  -- the conversion of the rest's goal into the goal's
  have conv : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop)
      (ν : σ → Needs) (O : Oracle σ) (gul : Noun) (st : σ) (t tm : Trace) (s : Noun) (regs : Map (Option Noun)),
      (∀ x, NMem ned x → g1.re ≤ x) → ∀ rt, (∀ p, rt = Tone.zero p → ∃ m, p = A m) →
      GoalSemCM lib O c gul Inv ν (fun x => (x < g2.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg r : Sure S)
        (jmp0 there)) x) st regs t tm nex.th (CGoal.next (lazyReg r : Sure S) (jmp0 there)) rt →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
        L.sure th (collWit r s) rt := by
    intro cf c ned σ Inv ν O gul st t tm s regs hned rt hat G
    cases rt with
    | one q => exact G
    | two t' => exact G
    | zero p =>
      obtain ⟨st1, R1, hI1, hν1, hp1, k1, e1⟩ := G.1 (fitsS_lazyReg _ p)
      refine ⟨fun _ => ⟨st1, R1, Need.this r, p, hI1, hν1, ⟨hat p rfl, rfl, rfl⟩, by rw [hL]; trivial, hp1,
        fun x ⟨x1, x2⟩ => k1 x ⟨x1.elim (fun h => Or.inl (by omega)) Or.inr, fun e => ?_⟩, by rw [e1, hj]⟩,
        fun nf => absurd (by rw [hL]; exact fitsS_bunt p) nf⟩
      simp only [GMem, lazyReg, NMem] at e
      subst e
      rcases x1 with h | h
      · omega
      · have := hned x h; omega
  have agR : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (t : Trace) (s0 s : Noun), (∀ st' : σ, AgreeL lib O c gul st' t cf ned g0 g1 nex.laz s0 s) →
      ∀ st' : σ, AgreeU lib O c gul st' t cf ned g2 g1 nex.laz s0 s :=
    fun cf c ned σ O gul t s0 s ag st' =>
      ⟨fun o h0 h1' hn' => (ag st').1 o (by omega) h1' hn', fun e he => (ag st').2 e he (by have := lab' e he; omega)⟩
  refine ⟨by omega, by omega, Re.2.2.1.trans CP.drop, fun o ho hn' => by rw [Re.2.2.2 o (by omega), CP.other o ho hn'],
    (CP.grow.toU hu).trans R.grow, CP.pfor.1.trans R.cfr, R.lo, R.hi, ?_, fun x hx => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun x hx => Or.inr (Or.inr ⟨by
      rcases ((R.eregs e he).2 x hx).1 with h | h
      · simp only [GMem, lazyReg, NMem] at h; omega
      · omega, ((R.eregs e he).2 x hx).2⟩)⟩,
    fun e he => ⟨Or.inr ⟨by have := (R.labs e he).1; omega, (R.labs e he).2.1⟩, (R.labs e he).2.2⟩, R.nodup,
    fun s v d w x hq hx => ?_, fun s hs hf => ?_, R.ncond, R.econd, fun e he => ?_, ?_, ?_⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      exact Or.inr (by rw [e, hj]; rfl)
  · rcases R.regs x hx with h | h
    · simp only [GMem, lazyReg, NMem] at h; subst h; exact Or.inr ⟨rge, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · obtain ⟨_, rfl, _⟩ := hq
    simp only [NMem] at hx; subst hx; exact ⟨rge, by omega⟩
  · obtain ⟨N1, N2⟩ := R.nec s hs hf
    have bad : ∀ {tm : Trace} {rt : Tone}, BadC (CGoal.next (lazyReg r : Sure S) (jmp0 there)) tm rt →
        BadC (CGoal.next L.sure th) tm rt := fun h => by
      rcases h with e | ⟨q, _, nq⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg _ q) nq
    exact ⟨fun gul n tm rt hm => bad (N1 gul n tm rt hm), fun gul tm => by
      obtain ⟨rt, hm, hb⟩ := N2 gul tm; exact ⟨rt, hm, bad hb⟩⟩
  · obtain ⟨A0, hA, hP⟩ := CP.at_ e he
    have hlt := hlab e he
    refine ⟨A0, fun B fin hb => by rw [Re.2.2.2 _ (by omega)]; exact hA B fin hb,
      fun cf hcf => Or.inr ⟨fun hm => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := lab' e' he'; omega, ?_⟩⟩
    intro lib σ O c gul st t ned A1 s0 s v d w hned hq hf0
    obtain ⟨⟨m, rfl⟩, rfl, rfl⟩ := hq
    have FP := collP_fillSem hP (by rw [hcf2 cf hcf r rlt]; exact CP.rkey)
      (fun x hx => by
        have hx1 := hec e he x hx
        rw [hcf2 cf hcf x (by omega), CP.pfor.1.get_lt hx1.1]; exact hx1.2)
      (fun k hk => hcf2 cf hcf k hk) lib O c gul st t ned g0.re s0 m
    exact fillSem_bunt_append hf0 (fun x hx => by have : x = r := hx; subst this; omega) (by omega) FP
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s rt hI htr hs hm ag hned regs hh hn
    exact conv cf c ned σ Inv ν O gul st t tm s regs hned rt (fun p e => hatom s gul n tm p hs (e ▸ hm))
      (R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s rt hI htr hs hm (agR cf c ned σ O gul t s0 s ag) hned
        regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rt, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs
      (agR cf c ned σ O gul t s0 s ag) hned regs hh hn res hres
    exact ⟨rt, hm, conv cf c ned σ Inv ν O gul st t tm s regs hned rt (fun p e => by
      obtain ⟨n, hn'⟩ := hm; exact hatom s gul n tm p hs (e ▸ hn')) G⟩

/-- **`[4 p]` with a calling `p` under a lazy goal whose sure part is the
bunt** (`%h4c`'s head under the bond goal): `+collapse-lazy-atom` takes a
fresh register `r` and puts its ops at the entries (`collapsePre_spec`), the
block of the increment and `p` give `RunOKGC` under `%next (lazy-from-reg r)`
(`unaryGC_ok`), and `collLC` composes. -/
theorem four_runBond (lib : Lib) {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC4 lib P f fb) {sup : Option Nomm}
    {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hL : L.sure = Sure.bunt) (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hnd : (th.there :: (entries L).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hec : ∀ e ∈ entries L, ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (h : runLC env sup (Nomm.n4 p) (CGoalL.next L th) region g0 = some (nex, g1)) :
    ∃ r, RunOKLC (Map := Map) lib P f L th (collWit r) g0 g1 nex := by
  have e4 : (runLC env sup (Nomm.n4 p) (CGoalL.next L th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨L, th⟩
      let (pro, th') ← collPick th a
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runLC
    rfl
  have nR : ∀ x, NMem L.sure.ned x → False := fun x hx => by rw [hL] at hx; exact hx
  rw [e4] at h
  obtain ⟨a, gA, hc2, h⟩ := bind_some h
  obtain ⟨⟨r, th'⟩, g2, hm, h⟩ := bind_some h
  have CP := collapsePre_spec hc2 hm d0 hcb (fun x hx => absurd hx (nR x)) (fun x hx => absurd hx (nR x)) hnd hlab
    (fun e he x hx => (hec e he x hx).1)
  refine ⟨r, ?_⟩
  have rge : g0.re ≤ r := CP.rreg.resolve_left (nR r)
  have rlt := CP.rlt
  have hthere : th' = th.there := by
    rcases CP.shape with ⟨e, _⟩ | ⟨_, _, nf, _⟩
    · exact e
    · exact absurd (by rw [hL]; exact fitsS_bunt (A 0)) (nf 0)
  subst hthere
  have d2 : g2.drop = false := CP.drop.trans d0
  have c2 := CP.bo1
  have r2 := CP.le
  have G2 : GrowU g0 g2 := CP.grow.toU hu
  have u2 : UpBelow g2 := G2.up hu
  have cb2 : CondBelow g2 := CP.pfor.1.below hcb
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [Pole.inc g2.re r], Termin.hop (jmp0 th.there)⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = ({ g2 with re := g2.re + 1 } : Gen Map).emitted blk := ⟨_, rfl⟩
  rw [← hblk, ← hgE] at h
  have hboE : gE.bo = g2.bo + 1 := by rw [hgE]; rfl
  have hreE : gE.re = g2.re + 1 := by rw [hgE]; rfl
  have hcnE : gE.cond = g2.cond := by rw [hgE]; rfl
  have hdE : gE.drop = false := by rw [hgE]; exact d2
  have hbE : HoonMap.get gE.blocks g2.bo = some blk := by
    rw [hgE]; exact emitted_get ({ g2 with re := g2.re + 1 } : Gen Map) blk d2
  have EE : Ext g2 gE := by rw [hgE]; exact (ext_re _).trans (ext_emit _ _)
  have GE : GrowU g2 gE := by
    rw [hgE]
    exact ((grow_re g2).trans (grow_emit (by rw [hblk]; exact jumpsBelow_hop h1 (by show th.there < g2.bo; omega)))).toU u2
  have Rp := Up.run (goal := CGoal.next (lazyReg g2.re) (jmp0 g2.bo)) trivial rfl
    ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩
    (by exact ⟨trivial, fun x hx => by simp [lazyReg, NMem] at hx; subst hx; omega⟩) (by exact trivial)
    hcount (by omega) hdE (GE.up u2) ((hcl0.growU G2).growU GE)
    (by rw [show gE = ({ g2 with re := g2.re + 1 } : Gen Map).emitted blk from hgE]
        exact CondFresh.below (condFresh_of_eq (g0 := g2) (Nat.le_succ _) rfl) cb2)
    (fun x hx => by
      simp only [lazyReg, NMem] at hx; subst hx
      rw [hcnE]; exact condBelow_none cb2 (Nat.le_refl _)) h
  have hatom : ∀ s gul n tm q, P s → minkF lib gul n tm s f = some (Tone.zero q) → ∃ m, q = A m := by
    intro s gul n tm q hs hm'
    obtain ⟨n', _, rb, _, e⟩ := M.fwd hs hm'
    cases rb with
    | zero x =>
      cases x with
      | atom k => simp only [incTone] at e; cases e; exact ⟨k + 1, rfl⟩
      | cell _ _ => simp [incTone] at e
    | one _ => simp [incTone] at e
    | two _ => simp [incTone] at e
  have R := unaryGC_ok (goal := CGoal.next (lazyReg r : Sure S) (jmp0 th.there)) M EE GE hcnE
    ⟨Nat.le_refl _, by omega⟩ (by omega) (by rw [hgE]; exact fresh_emitted d2 (by rw [hblk]) (j := jmp0 g2.bo) rfl)
    Rp
    (fun cf hcf k k0 k1 => by
      obtain rfl : k = g2.bo := by omega
      rw [hbE, hblk]
      have u1 : unproxy cf g2.re = g2.re := unproxy_none (by
        rw [hcf _ (by omega)]; exact condBelow_none cb2 (Nat.le_refl _))
      have u2 : unproxy cf r = r := unproxy_none (by rw [hcf _ (by omega)]; exact CP.rkey)
      simp [unproxyBlob, renBlob, renPole, renFin, u1, u2, renJmp_nil _ (show (jmp0 th.there).args = [] from rfl)])
    ?_
  · exact collLC CP hL hu h2 (fun e he => (hlab e he).1) hec hatom R
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb : HoonMap.get c.blocks g2.bo = some blk := by rw [hc _ (Nat.le_refl _) (by omega)]; exact hbE
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [hblk] at hj'
  cases x with
  | atom n =>
    rw [show [Pole.inc g2.re r] = [Pole.inc g2.re r] ++ [] from rfl, runs_inc hx, execBlob_hop] at hj'
    refine goalSemC_of_goalSem hI htr (CGoal.next (lazyReg r : Sure S) (jmp0 th.there)) (some (A (n + 1)))
      ⟨fun _ => ⟨store r (A (n + 1)) regs, read_store_eq _ _ _, fun y hy => read_store_ne (fun e => ?_) _ _, hj'⟩,
        fun nf => absurd (fitsS_lazyReg r _) nf⟩
    obtain ⟨_, hy2⟩ := hy
    subst e
    exact hy2 rfl
  | cell u v =>
    rw [show [Pole.inc g2.re r] = [Pole.inc g2.re r] ++ [] from rfl, crashes_inc hx] at hj'
    exact ⟨Tone.two t, st, hI, Needs.le_refl _, hj', ToneRel.two htr⟩

/-- **`[4 p]` with an operand meeting `UOKC` meets `BondOKC`** (a head under
the bond goal): `four_runBond` with the goal `mk bunt [] [(b, hed)]`. -/
theorem bondOKC_fourC (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC4 lib P f fb) :
    BondOKC (S := S) (Map := Map) lib env P f (Nomm.n4 p) := by
  refine ⟨fun {sup region g0 g1 nex hed b th} h => ?_, fun {sup region g0 g1 nex hed b th jb} hc b0 d0 hu hcl hcb
    h1 h2 ha hne hb hbb hd hen h => ?_⟩
  · obtain ⟨arg, o, gX, h'⟩ := runLC_n4_last (fun z o e => by cases e) h
    exact Up.clean (goal := CGoal.next (lazyReg arg) (jmp0 o)) trivial trivial h'
  · have E := entries_bond1 b hed
    obtain ⟨r, R⟩ := four_runBond lib Up M (L := mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]) rfl
      (by simpa [sixCount] using hc) b0 d0 hu hcl hcb h1 h2
      (by rw [E]; simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]; exact fun e => hne e.symm)
      (by rw [E]; intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨hb, [], _, hbb⟩)
      (by rw [E]; intro e he; simp only [List.mem_singleton] at he; subst he; exact hen) h
    exact ⟨_, R⟩

/-- **`[4 p]` with an operand meeting `UOKC` meets `BondOKC` on every
`Annot`** (`bondOKC_fourC` with `minkC4_four`, the wrappers by
`BondOKC.wrap`). -/
theorem bondOKC_fourA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n4 p → BondOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | n4 hb _ => intro e; cases e; exact bondOKC_fourC lib env (ihp hb) (minkC4_four lib _ _)
  | memo hm _ ih' => intro e; exact BondOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact BondOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact BondOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | _ => intro e; cases e

/-- **`[[4 [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]` end to end** (`%h4c` of
`tools/hoon/calldump4.hoon`): the head `[4 p]` with a calling `p` runs under
the bond goal behind the tail's call (`bondOKC_fourA`), the cons composes
(`uokc_consEA`), both halves of the contract (`finishLUC_contractG`). -/
theorem h4c_example {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = C (n2 (A 4) (n3 (A 2) (slot 3) (slot 2))) (n3 (A 2) (slot 3) (slot 2))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.cons (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))
      (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.cons (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2)
      Option.none)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) := by
    rw [hfol]
    exact Annot.cons (Annot.n4 (Annot.indirect Annot.n0 Annot.n0)) (Annot.indirect Annot.n0 Annot.n0)
  have leaf : ∀ (axe : Nat) {P : Noun → Prop} {f : Noun}, Annot lib code P f (Nomm.n0 axe) →
      UOKC (S := S) (Map := Map) lib env P f (Nomm.n0 axe) := fun axe {P f} hA' =>
    uokcU hok env (FragU.x (FragX.frag (nm := Nomm.n0 axe) fun _ => trivial)) hA'
  have ind : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) →
      UOKC (S := S) (Map := Map) lib env P f (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) ∧
      EntNew (S := S) (Map := Map) env (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) := fun hA' =>
    uokc_indDA env (fun h => leaf 3 h) (fun h => leaf 2 h) rfl hA' rfl
  have U := (uokc_consEA env (fun hA' => uokc_fourA env (fun h => (ind h).1) rfl hA' rfl)
    (fun hA' _ => bondOKC_fourA env (fun h => (ind h).1) hA' rfl) (fun h => ⟨(ind h).1, fun _ => (ind h).2⟩) rfl
    hA rfl).1
  have H := finishLUC_contractG lib U (by decide) h N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

end Comp
end SkaModel
end Formalization
