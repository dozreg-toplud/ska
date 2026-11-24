import lemmas.Compiler.CompSixHelp

/-!
# The case `%6` of `+run`: the tail of phase S

Phase S of the case `%6` (`cr6S0` ... `cr6S9`, `CompRunSixN.lean`) ends,
after the run of the test `p`, with the test `(lazy-big (soft-less lazy))`
(`cr6S9`): on `|` the `+copy` of `nex-cond` and `lazy`, on `&` the `+emit` of
`[~ ~ %hop then.nex-cond]` as `o`, `+lazy-shut` at `o` and the `+copy` of
`nex-cond(then ~^o)`.  The model is the end of `sixNextSimpleC` and of the
`%done`, `%pick` branch of `runLC` (`sixTail`).

`cr6s_tail`: the Nock of `cr6S9` on its subject is `sixTail`, given that the
registers of `nex-cond` and of `lazy` are below the counter and apart (the
side condition of `+copy`) and that no sure need of `lazy` looks at axis `0`
(the walk of `+kern` in `+lazy-shut`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The tail of phase S in the model. -/
noncomputable def sixTail (nexCond : NextL CSet) (lazy : Lazy CSet) : CM (TreapMap mugF) (NextL CSet) :=
  if !(Lazy.lazyBig (Lazy.softLess Lazy.noSoft lazy)) then copyL nexCond lazy else do
    let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
    let lazy ← lazyShut o lazy
    copyL ⟨nexCond.laz, jmp0 o⟩ lazy

theorem km_kernG (r o oLaz : Nat) (sur : Sure CSet) : KM (kernG r o oLaz sur) := by
  unfold kernG
  refine KM.bind' (km_sureRequireLook _) fun ned => KM.ite' _ (KM.pure' _) ?_
  refine KM.bind' (KM.ite' _ (KM.pure' _) (KM.proxy' _ _)) fun src => KM.ite' _ KM.fail ?_
  exact KM.bind' (km_kernLoop _ _ _) fun _ => KM.addOps' _ _

theorem get_apply' (g : Gen (TreapMap mugF)) : (get : CM (TreapMap mugF) (Gen (TreapMap mugF))) g = some (g, g) := rfl

/-- `+kern` takes the counter as its register and moves the counter past it. -/
theorem kern_reg {o : Nat} {laz : Lazy CSet} {g g' : Gen (TreapMap mugF)} {r : Nat}
    (h : kern o laz g = some (r, g')) : r = g.re ∧ g.re < g'.re := by
  rw [kern_eq, bind_apply, re_apply, Option.bind_some, bind_apply, get_apply', Option.bind_some] at h
  by_cases hd : g.drop = true
  · rw [if_pos hd, pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  · rw [if_neg hd, bind_apply] at h
    obtain ⟨⟨u, g2⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rw [pure_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    have := ((km_walkLazy (fun o' s => km_kernG g.re o o' s) o laz).keep _ u _ h1).1
    exact ⟨rfl, by simp at this; omega⟩

theorem pf_noun (n : NextL CSet) (o : Nat) :
    (⟨n.laz, jmp0 o⟩ : NextL CSet).goal.toNoun = C (A 0x7478656e) (C n.laz.toNoun (C (A 0) (A o))) := by
  simp [NextL.goal, CGoalL.toNoun, Jmp.toNoun, jmp0, listNoun]

/-- **The tail of phase S** (`cr6S9`): the test `(lazy-big (soft-less
lazy))`, then `+copy`, or `+emit`, `+lazy-shut` and `+copy`, on the subject
of phase S after the run of the test, given the side conditions of `+copy`
(the registers of `nex-cond` and `lazy` below the counter and apart) and no
look at axis `0` in `lazy`. -/
theorem cr6s_tail (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF))
    (nexCond : NextL CSet) (lazy : Lazy CSet) (Y V6 V5 V4 V3 V2 V1 V0 B1 B2 SAM : Noun)
    (hf : ∀ r ∈ lregs nexCond.laz, r < g.re) (hs : ∀ r ∈ lregs lazy, r < g.re)
    (ap : ∀ r ∈ lregs nexCond.laz, r ∉ lregs lazy) (hl : LAll CrLok lazy) :
    nock (C nexCond.goal.toNoun (C (C lazy.toNoun Y) (C V6 (C V5 (C V4 (C V3 (C V2 (C V1 (C V0
      (C B1 (C B2 (C SAM (compCore g x ctx))))))))))))) cr6S9
      = (sixTail nexCond lazy g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hsl := sl_all hc x hx g lazy
  have hlg := lg_gate lazy
  have hD1 := sl_at
  have hD2 := comp_cp_at
  have hD3 := comp_emit_at
  have hD4 := lsh_at
  unfold sixTail
  rw [Lazy.softLess_noSoft]
  simp only [compCore] at hsl ⊢
  cases eb : Lazy.lazyBig lazy
  · have hcp := comp_copy_all h7 x g nexCond lazy (copyH_of_regs hf hs ap)
    simp only [compCore] at hcp
    generalize comp.door = Dr at hsl hD1 hD2 hD3 hD4 hcp ⊢
    unfold cr6S9
    simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD2, cr_cp_arm, hcp]
  · have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop nexCond.th⟩
    simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
    have hre := cf_emitG_re ⟨[], [], Termin.hop nexCond.th⟩ g
    generalize hg1 : cfEmitG ⟨[], [], Termin.hop nexCond.th⟩ g = g1 at he hre
    have hsh := comp_lazy_shut h7 x hx g1 g.bo lazy (walk_mdP hx _ hl)
    simp only [compCore] at hsh
    unfold lazyShut at hsh
    rw [Lazy.softLess_noSoft, eb] at hsh
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at hsh
    cases ek : kern g.bo lazy g1 with
    | none =>
      rw [bind_apply, ek] at hsh
      generalize comp.door = Dr at hsl hD1 hD2 hD3 hD4 he hsh ⊢
      unfold cr6S9
      simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD3, comp_emit_arm, he, hD4,
        lsh_arm, hsh, cf_emit_g, hg1, bind, StateT.bind, lazyShut, Lazy.softLess_noSoft, ek, NextL.goal, CGoalL.toNoun]
    | some rk =>
      obtain ⟨r, g2⟩ := rk
      obtain ⟨er, lr⟩ := kern_reg ek
      rw [bind_apply, ek] at hsh
      simp only [Option.bind_some, pure_apply, Option.map_some] at hsh
      have hcp := comp_copy_all h7 x g2 ⟨nexCond.laz, jmp0 g.bo⟩ (Lazy.ofSure ⟨Need.this r, HoonSet.empty⟩)
        (copyH_of_regs (fun y hy => by have := hf y hy; omega)
          (fun y hy => by
            have e : lregs (Lazy.ofSure (⟨Need.this r, HoonSet.empty⟩ : Sure CSet)) = [r] := lregs_reg r
            rw [e] at hy; simp at hy; omega)
          (fun y hy hy' => by
            have e : lregs (Lazy.ofSure (⟨Need.this r, HoonSet.empty⟩ : Sure CSet)) = [r] := lregs_reg r
            rw [e] at hy'; simp at hy'; have := hf y hy; omega))
      simp only [compCore, pf_noun] at hcp
      generalize comp.door = Dr at hsl hD1 hD2 hD3 hD4 he hsh hcp ⊢
      unfold cr6S9
      simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD3, comp_emit_arm, he, hD4,
        lsh_arm, hsh, cf_emit_g, hg1, bind, StateT.bind, lazyShut, Lazy.softLess_noSoft, ek, hD2, cr_cp_arm, hcp,
        NextL.goal, CGoalL.toNoun, pure, StateT.pure]

/-! ## `+past-fork` keeps the invariant -/

theorem pastFork_cod {cod : Bell → Option Bool} {nom : Nomm} (h : hinted cod nom = hinted noCode nom)
    (laz : Lazy CSet) : Lazy.pastFork cod laz nom = Lazy.pastFork noCode laz nom := by
  simp only [Lazy.pastFork, h]

/-- The forks of `+past-fork` when the test is hinted. -/
theorem pastFork_some {cod : Bell → Option Bool} {laz laz' : Lazy CSet} {nom : Nomm}
    (h : Lazy.pastFork cod laz nom = some laz') :
    laz' = laz ∨ laz' = Lazy.mk laz.sure (laz.fork.map pfE) laz.bond := by
  unfold Lazy.pastFork at h
  split at h
  · cases h
  · cases h; exact Or.inl rfl
  · cases h; exact Or.inr rfl

theorem fregs_pf : ∀ f : List (Lazy.ForkE CSet), fregs (f.map pfE) = fregs f
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp [fregs, pfE, lregs, bregs, flattenNeed, Sure.bunt, fregs_pf rest]

theorem walkPF_pf {Q : Sure CSet → Prop} (hb : Q Sure.bunt) : ∀ f : List (Lazy.ForkE CSet),
    WalkPF (fun _ s => Q s) f → WalkPF (fun _ s => Q s) (f.map pfE)
  | [], _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩ =>
    ⟨⟨hb, trivial, hy, trivial⟩, ⟨hb, trivial, hn, trivial⟩, walkPF_pf hb rest hr⟩

theorem flabs_pf : ∀ (f : List (Lazy.ForkE CSet)) (o : Nat), o ∈ flabs (f.map pfE) → o ∈ flabs f
  | [], o, h => by simp [flabs] at h
  | ((oy, y), (on, n)) :: rest, o, h => by
    simp only [List.map_cons, pfE, flabs, llabs, blabs, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false, false_or, List.append_nil] at h ⊢
    rcases h with h | h | (h | h) | (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (flabs_pf rest o h))))

theorem fkeys_pf : ∀ f : List (Lazy.ForkE CSet), FKeys f → FKeys (f.map pfE)
  | [], _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩ => by
    simp only [List.map_cons, pfE, FKeys, LKeys, BKeys, List.map_nil, List.nodup_nil, List.map_cons,
      List.nodup_cons, List.not_mem_nil, not_false_eq_true, and_self, true_and, and_true]
    exact ⟨hy, hn, fkeys_pf rest hr⟩

/-- **`+past-fork` keeps the registers.** -/
theorem lregs_pastFork {cod : Bell → Option Bool} {laz laz' : Lazy CSet} {nom : Nomm}
    (h : Lazy.pastFork cod laz nom = some laz') : lregs laz' = lregs laz := by
  rcases pastFork_some h with rfl | rfl
  · rfl
  · obtain ⟨s, f, b⟩ := laz
    simp [lregs, fregs_pf]

/-- **`+past-fork` keeps `LAll` of a predicate that the bunt meets.** -/
theorem lall_pastFork {cod : Bell → Option Bool} {laz laz' : Lazy CSet} {nom : Nomm} {Q : Sure CSet → Prop}
    (hb : Q Sure.bunt) (h : Lazy.pastFork cod laz nom = some laz') (hl : LAll Q laz) : LAll Q laz' := by
  rcases pastFork_some h with rfl | rfl
  · exact hl
  · obtain ⟨s, f, b⟩ := laz
    exact ⟨hl.1, walkPF_pf hb f hl.2.1, hl.2.2⟩

/-- **`+past-fork` keeps `LInv`.** -/
theorem linv_pastFork {cod : Bell → Option Bool} {laz laz' : Lazy CSet} {nom : Nomm} {kr kb : Nat}
    (h : Lazy.pastFork cod laz nom = some laz') (hl : LInv kr kb laz) : LInv kr kb laz' := by
  obtain ⟨h1, h2, h3, h4⟩ := hl
  refine ⟨lall_pastFork (linv_bunt kr kb).1.1 h h1, by rw [lregs_pastFork h]; exact h2, ?_, ?_⟩
  · rcases pastFork_some h with rfl | rfl
    · exact h3
    · obtain ⟨s, f, b⟩ := laz
      obtain ⟨a1, a2, a3, a4⟩ := h3
      refine ⟨?_, a2, fkeys_pf f a3, a4⟩
      have : (f.map pfE).map (fun e => e.1.1) = f.map (fun e => e.1.1) := by
        simp [Function.comp_def, pfE]
      simpa only [Lazy.fork, this] using a1
  · rcases pastFork_some h with rfl | rfl
    · exact h4
    · obtain ⟨s, f, b⟩ := laz
      intro o ho
      simp only [llabs, List.mem_append] at ho h4
      rcases ho with ho | ho
      · exact h4 o (Or.inl (flabs_pf f o ho))
      · exact h4 o (Or.inr ho)

/-! ## From `+past-fork` on -/

/-- Phase S from `+past-fork` on, in the model. -/
noncomputable def sixPM (env : CallEnv) (msup : Option Nomm) (p : Nomm) (region : List Nat) (lazy : Lazy CSet)
    (yes nuh : Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let lazy ← liftO (Lazy.pastFork env.cod lazy p)
  let nexCond ← runLC env msup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
  sixTail nexCond lazy

theorem pick_noun (yes nuh : Nat) : (CGoalL.pick (jmp0 yes) (jmp0 nuh) : CGoalL CSet).toNoun
    = C (A 0x6b636970) (C (C (A 0) (A yes)) (C (A 0) (A nuh))) := by
  simp [CGoalL.toNoun, cr_jmp0]

/-- **Phase S from `+past-fork` on** (`cr6S7`): `+past-fork` over `p`, the
run of `p` for `[%pick ~^yes ~^nuh]`, and the tail (`cr6s_tail`), given the
link of `p` on that goal and what its runs return, the registers of `lazy`
below the counter and no look at axis `0` in it. -/
theorem cr6s_p (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (hpc : hinted env.cod p = hinted noCode p) (hpn : hinted noCode p ≠ Option.none)
    (yes nuh : Nat)
    (hP : ∀ g' : Gen (TreapMap mugF), g'.drop = false →
      CompRunAtR (runLC env msup) ctx p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region g')
    (hR : ResFor env msup p region)
    (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF)) (hd : g.drop = false)
    (lazy : Lazy CSet) (hlz : ∀ y ∈ lregs lazy, y < g.re) (hlok : LAll CrLok lazy)
    (mono goalN sup V6 V5 V4 V3 V2 V1 V0 : Noun) :
    nock (C (C lazy.toNoun (C (A yes) (A nuh))) (C V6 (C V5 (C V4 (C V3 (C V2 (C V1 (C V0
      (crSubj mono (Nomm.n6 p q r).toNoun goalN (listNoun A region) sup (compCore g x ctx)))))))))) cr6S7
      = (sixPM env msup p region lazy yes nuh g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hpf := comp_past_fork h7 hcode (genNoun g x) lazy p hpn
  have hD1 := pf_at
  unfold sixPM
  rw [pastFork_cod hpc]
  simp only [compCore] at hpf ⊢
  cases e1 : Lazy.pastFork noCode lazy p with
  | none =>
    rw [e1] at hpf
    generalize comp.door = Dr at hpf hD1 ⊢
    unfold cr6S7
    simp [nock_exec, crSubj, Nomm.toNoun, hD1, pf_arm, hpf, liftO, bind, StateT.bind]
  | some lazy' =>
    rw [e1] at hpf
    simp only [Option.map_some] at hpf
    have hq1 := hP g hd x mono sup hx
    rw [pick_noun] at hq1
    simp only [crSubj, compCore] at hq1
    cases e2 : runLC (S := CSet) (Map := TreapMap mugF) env msup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region g with
    | none =>
      rw [e2] at hq1
      generalize comp.door = Dr at hpf hD1 hq1 ⊢
      unfold cr6S7 cr6S8
      simp [nock_exec, crSubj, Nomm.toNoun, hD1, pf_arm, hpf, liftO, bind, StateT.bind, hq1, e2, cr_bat_dol]
    | some rr =>
      obtain ⟨nexCond, g'⟩ := rr
      rw [e2] at hq1
      simp only [Option.map_some] at hq1
      obtain ⟨l1, -, gi, fr⟩ := hR (CGoalL.pick (jmp0 yes) (jmp0 nuh)) g g' nexCond
        (show GInv g (CGoalL.pick (jmp0 yes) (jmp0 nuh)) from ⟨hd, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) e2
      have hf : ∀ y ∈ lregs nexCond.laz, y < g'.re := lnb_regs gi.1.1
      have hs' : ∀ y ∈ lregs lazy', y < g'.re := fun y hy => by
        rw [lregs_pastFork e1] at hy; have := hlz y hy; omega
      have ap : ∀ y ∈ lregs nexCond.laz, y ∉ lregs lazy' := fun y hy hy' => by
        rw [lregs_pastFork e1] at hy'
        have := hlz y hy'
        rcases fr y hy with h | h
        · omega
        · simp [gregs] at h
      have ht := cr6s_tail h7 x hx g' nexCond lazy' (C (A yes) (A nuh)) V6 V5 V4 V3 V2 V1 V0 crBat crB
        (C mono (C (Nomm.n6 p q r).toNoun (C goalN (C (listNoun A region) sup)))) hf hs' ap
        (lall_pastFork (fun y hy => by simp [Sure.bunt] at hy; exact absurd hy (HoonSet.mem_empty y)) e1 hlok)
      simp only [compCore, Nomm.toNoun] at ht
      generalize comp.door = Dr at hpf hD1 hq1 ht ⊢
      unfold cr6S7 cr6S8
      simp [nock_exec, crSubj, Nomm.toNoun, hD1, pf_arm, hpf, liftO, bind, StateT.bind, hq1, e2, cr_bat_dol, ht]

/-! ## The pair of `%hop` blocks under `%done` and `%pick` -/

/-- The state after `+set-tag`. -/
def stG (o : Nat) (region : List Nat) (g : Gen (TreapMap mugF)) : Gen (TreapMap mugF) :=
  if g.drop then g else { g with tags := HoonMap.put g.tags o region }

theorem st_apply (o : Nat) (region : List Nat) (g : Gen (TreapMap mugF)) :
    (setTag o region g : Option (Unit × Gen (TreapMap mugF))) = some ((), stG o region g) := rfl

theorem stG_re (o : Nat) (region : List Nat) (g : Gen (TreapMap mugF)) : (stG o region g).re = g.re := by
  unfold stG; split <;> rfl

theorem stG_bo (o : Nat) (region : List Nat) (g : Gen (TreapMap mugF)) : (stG o region g).bo = g.bo := by
  unfold stG; split <;> rfl

theorem stG_drop (o : Nat) (region : List Nat) (g : Gen (TreapMap mugF)) : (stG o region g).drop = g.drop := by
  unfold stG; split <;> rfl

/-- Phase S under `%done` and `%pick` from the two runs on: the two `%hop`
blocks, their tags, the asserts, and the rest from `+past-fork` on. -/
noncomputable def sixLynDP (env : CallEnv) (msup : Option Nomm) (p : Nomm) (region : List Nat)
    (nex0 nex1 : NextL CSet) : CM (TreapMap mugF) (NextL CSet) := do
  let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
  let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
  setTag yes region
  setTag nuh region
  if nex0.th.args ≠ [] then fun _ => Option.none else
  if nex1.th.args ≠ [] then fun _ => Option.none else
  sixPM env msup p region (Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) yes nuh

theorem cgl_next_noun6 (laz : Lazy CSet) (args : List (Option Nat)) (there : Nat) :
    (CGoalL.next laz ⟨args, there⟩ : CGoalL CSet).toNoun
      = C (A 0x7478656e) (C laz.toNoun (C (listNoun (unitNoun A) args) (A there))) := rfl

theorem lyn_lazy_noun (yes nuh : Nat) (l0 l1 : Lazy CSet) :
    (Lazy.mk Sure.bunt [((yes, l0), (nuh, l1))] [] : Lazy CSet).toNoun
      = C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (C (C (C (A yes) l0.toNoun) (C (A nuh) l1.toNoun)) (A 0)) (A 0)) := by
  rw [lazy_toNoun_mk]
  simp [forkE, Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none, HoonSet.toNoun_empty, listN]

/-- **The pair of `%hop` blocks under `%done` and `%pick`** (`cr6S6`, its
non-`%next` branch, then `cr6S7`). -/
theorem cr6s_lyn_dp (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (hpc : hinted env.cod p = hinted noCode p) (hpn : hinted noCode p ≠ Option.none)
    (hP : ∀ (yes nuh : Nat) (g' : Gen (TreapMap mugF)), g'.drop = false →
      CompRunAtR (runLC env msup) ctx p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region g')
    (hR : ResFor env msup p region)
    (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF)) (hd : g.drop = false)
    (nex0 nex1 : NextL CSet) (h0 : LAll (LNB g.re) nex0.laz) (h1 : LAll (LNB g.re) nex1.laz)
    (mono grest sup cbw cb RB GG LEP : Noun) (tag : Nat) (htag : tag ≠ 0x7478656e) :
    nock (C nex0.goal.toNoun (C cbw (C nex1.goal.toNoun (C cb (C RB (C GG (C LEP
      (crSubj mono (Nomm.n6 p q r).toNoun (C (A tag) grest) (listNoun A region) sup (compCore g x ctx))))))))) cr6S6
      = (sixLynDP env msup p region nex0 nex1 g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have htag' : ¬ ((0x7478656e : Nat) = tag) := fun h => htag h.symm
  obtain ⟨l0, ⟨a0, t0⟩⟩ := nex0
  obtain ⟨l1, ⟨a1, t1⟩⟩ := nex1
  simp only [NextL.goal, cgl_next_noun6]
  have he1 := cf_emit (x := x) hc g ⟨[], [], Termin.hop ⟨a0, t0⟩⟩
  generalize hg1 : cfEmitG ⟨[], [], Termin.hop ⟨a0, t0⟩⟩ g = g1 at he1
  have he2 := cf_emit (x := x) hc g1 ⟨[], [], Termin.hop ⟨a1, t1⟩⟩
  generalize hg2 : cfEmitG ⟨[], [], Termin.hop ⟨a1, t1⟩⟩ g1 = g2 at he2
  have hst1 := comp_set_tag x hc g2 g.bo region
  have hst2 := comp_set_tag x hc (stG g.bo region g2) g1.bo region
  have r1 : g1.re = g.re := by rw [← hg1, cf_emitG_re]
  have r2 : g2.re = g.re := by rw [← hg2, cf_emitG_re, r1]
  have d1 : g1.drop = false := by rw [← hg1, cf_emitG_drop]; exact hd
  have d2 : g2.drop = false := by rw [← hg2, cf_emitG_drop]; exact d1
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop, Jmp.toNoun] at he1 he2
  simp only [st_apply, Option.map_some] at hst1 hst2
  have hD1 := comp_emit_at
  have hD2 := comp_set_tag_at
  unfold sixLynDP
  simp only [bind_apply, cf_emit_g, hg1, hg2, Option.bind_some, st_apply]
  generalize hg4 : stG g1.bo region (stG g.bo region g2) = g4 at hst2 ⊢
  have d4 : g4.drop = false := by rw [← hg4, stG_drop, stG_drop]; exact d2
  have r4 : g4.re = g.re := by rw [← hg4, stG_re, stG_re]; exact r2
  rcases a0 with _ | ⟨a0h, a0t⟩
  · rcases a1 with _ | ⟨a1h, a1t⟩
    · simp only [listNoun] at he1 he2
      have hlz : ∀ y ∈ lregs (Lazy.mk Sure.bunt [((g.bo, l0), (g1.bo, l1))] [] : Lazy CSet), y < g4.re := by
        intro y hy
        simp only [lregs, fregs, bregs, flattenNeed, Sure.bunt, List.nil_append, List.append_nil,
          List.mem_append] at hy
        rw [r4]
        rcases hy with hy | hy
        · exact lnb_regs h0 y hy
        · exact lnb_regs h1 y hy
      have hlok : LAll CrLok (Lazy.mk Sure.bunt [((g.bo, l0), (g1.bo, l1))] [] : Lazy CSet) :=
        ⟨fun y hy => by simp [Sure.bunt] at hy; exact absurd hy (HoonSet.mem_empty y),
          ⟨by rw [walkP_irrel]; exact lall_mono (fun _ h => h.1) h0,
           by rw [walkP_irrel]; exact lall_mono (fun _ h => h.1) h1, trivial⟩, trivial⟩
      have hpm := cr6s_p h7 hcode env msup p q r region hpc hpn g.bo g1.bo (hP g.bo g1.bo) hR x hx g4 d4
        _ hlz hlok mono (C (A tag) grest) sup
        (C (A 0x7478656e) (C l0.toNoun (C (A 0) (A t0)))) cbw
        (C (A 0x7478656e) (C l1.toNoun (C (A 0) (A t1)))) cb RB GG LEP
      rw [lyn_lazy_noun] at hpm
      simp only [crSubj, compCore] at hpm hst1 hst2 ⊢
      generalize comp.door = Dr at he1 he2 hst1 hst2 hD1 hD2 hpm ⊢
      unfold cr6S6 cr6SA6
      simp only [Nomm.toNoun, NextL.goal] at hpm
      simp [nock_exec, htag, htag', hD1, comp_emit_arm, he1, he2, hD2, comp_set_tag_arm, hst1, hst2, hpm,
        listNoun, Nomm.toNoun, NextL.goal]
    · simp only [listNoun] at he1 he2
      simp only [crSubj, compCore] at hst1 hst2 ⊢
      generalize comp.door = Dr at he1 he2 hst1 hst2 hD1 hD2 ⊢
      unfold cr6S6 cr6SA6
      simp [nock_exec, htag, htag', hD1, comp_emit_arm, he1, he2, hD2, comp_set_tag_arm, hst1, hst2, listNoun,
        Nomm.toNoun]
  · simp only [listNoun] at he1 he2
    simp only [crSubj, compCore] at hst1 hst2 ⊢
    generalize comp.door = Dr at he1 he2 hst1 hst2 hD1 hD2 ⊢
    unfold cr6S6 cr6SA6
    simp [nock_exec, htag, htag', hD1, comp_emit_arm, he1, he2, hD2, comp_set_tag_arm, hst1, hst2, listNoun,
      Nomm.toNoun]

/-! ## The two runs of the branches -/

/-- The noun of `cond`. -/
noncomputable def condN (g : Gen (TreapMap mugF)) : Noun := HoonMap.toNoun condValNoun g.cond

/-- **The two runs of the branches** (`cr6S2` to `cr6S5`): `cond-before`,
the run of `r` for `goal-1` in `region-branch`, `cond-between`, the run of
`q` for `goal-0`, then a continuation `K` from `cr6S6` on, given the links
of the two runs. -/
theorem cr6s_mid (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (rb : List Nat)
    (goal0 goal1 : CGoalL CSet) (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF))
    (mono goalN regionN sup LEP : Noun)
    (K : TreapMap mugF (Nat × List Nat) → TreapMap mugF (Nat × List Nat) → NextL CSet → NextL CSet →
      CM (TreapMap mugF) (NextL CSet))
    (hr : CompRunAtR (runLC env msup) ctx r goal1 rb g)
    (hq : ∀ nex1 g1, runLC env msup r goal1 rb g = some (nex1, g1) → CompRunAtR (runLC env msup) ctx q goal0 rb g1)
    (hK : ∀ nex1 g1 nex0 g2, runLC env msup r goal1 rb g = some (nex1, g1) →
      runLC env msup q goal0 rb g1 = some (nex0, g2) →
      nock (C nex0.goal.toNoun (C (condN g1) (C nex1.goal.toNoun (C (condN g) (C (listNoun A rb)
        (C (C goal0.toNoun goal1.toNoun) (C LEP
          (crSubj mono (Nomm.n6 p q r).toNoun goalN regionN sup (compCore g2 x ctx))))))))) cr6S6
        = (K g.cond g1.cond nex0 nex1 g2).map fun p => C p.1.goal.toNoun (genNoun p.2 x)) :
    nock (C (listNoun A rb) (C (C goal0.toNoun goal1.toNoun) (C LEP
      (crSubj mono (Nomm.n6 p q r).toNoun goalN regionN sup (compCore g x ctx))))) cr6S2
      = ((do
          let cb ← getCond
          let nex1 ← runLC env msup r goal1 rb
          let cbw ← getCond
          let nex0 ← runLC env msup q goal0 rb
          K cb cbw nex0 nex1 : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hr1 := hr x mono sup hx
  simp only [crSubj, compCore, genNoun] at hr1
  simp only [bind_apply, getCond, Option.bind_some]
  cases e1 : runLC (S := CSet) (Map := TreapMap mugF) env msup r goal1 rb g with
  | none =>
    rw [e1] at hr1
    unfold cr6S2 cr6S3
    simp [nock_exec, crSubj, compCore, Nomm.toNoun, cr_bat_dol, hr1, genNoun]
  | some rr =>
    obtain ⟨nex1, g1⟩ := rr
    rw [e1] at hr1
    simp only [Option.map_some] at hr1
    have hq1 := hq nex1 g1 e1 x mono sup hx
    simp only [crSubj, compCore, genNoun] at hq1
    cases e2 : runLC (S := CSet) (Map := TreapMap mugF) env msup q goal0 rb g1 with
    | none =>
      rw [e2] at hq1
      unfold cr6S2 cr6S3 cr6S4 cr6S5
      simp [nock_exec, crSubj, compCore, Nomm.toNoun, cr_bat_dol, hr1, hq1, genNoun, e2]
    | some rr =>
      obtain ⟨nex0, g2⟩ := rr
      rw [e2] at hq1
      simp only [Option.map_some] at hq1
      have hk := hK nex1 g1 nex0 g2 e1 e2
      simp only [crSubj, compCore, condN, genNoun, Nomm.toNoun] at hk
      unfold cr6S2 cr6S3 cr6S4 cr6S5
      simp [nock_exec, crSubj, compCore, Nomm.toNoun, cr_bat_dol, hr1, hq1, hk, genNoun, e2]

end Compiler
end Formalization
