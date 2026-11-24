import lemmas.Compiler.CompMedeGen
import lemmas.Compiler.CompKerfLink

/-!
# `+kern` and `+kerf` on every lazy need

`+kern` (door arm `7167`) takes a fresh register `r` and, out of `%drop`
mode, walks the lazy need from `o` with the gate `kernGB`: `+sure-require-
look`, nothing on `%none`, else the source register (`r` at the block `o`
itself, `(proxy r o-laz)` at any other block: a fresh register recorded in
`cond` with the region of `o-laz`, `comp_proxy`), the test `(~(has by
soft.gen) o-laz)`, `+kern-need` from the source and `+add-ops` at `o-laz`.
The model `kern` of `Ska/CompLazyRun.lean` walks with the same gate, in the
same order (the proxy before the test of `soft`).  No departure.

`kern_gate_all`: the gate at every visited block; `comp_kern_all` and
`comp_kerf_all`: the arms on every lazy need (forks and bonds to any depth)
whose every visited block is not a key of `soft` and whose sure needs look
at no axis `0` (`WalkP mdP`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The gate the model's `kern` walks with. -/
noncomputable def kernG (r o : Nat) (oLaz : Nat) (sur : Sure CSet) : CM (TreapMap mugF) Unit := do
  let ned ← sureRequireLook sur
  if ned = Need.none then pure () else do
  let src ← (if oLaz = o then pure r else proxy r oLaz : CM (TreapMap mugF) Nat)
  if Lazy.noSoft oLaz then fun _ => Option.none else do
  let ops ← kernNeed src ned
  addOps oLaz ops

/-- **The gate of `+kern`** at every block `oLaz` that is not a key of
`soft`, with no look at axis `0`: through a proxy of `r` at a block other
than `o`. -/
theorem kern_gate_all (hc : CompIn ctx) (hl : CompLib ctx) (x : GenRest) (G0 LAZ : Noun) (o oLaz r : Nat)
    (sur : Sure CSet) (g : Gen (TreapMap mugF)) (hs : x.SoftOut oLaz)
    (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C kernGB (C (C (A oLaz) (C sur.toNoun (genNoun g x)))
      (C (A r) (C kernBat (C (C (A o) LAZ) (C comp.door (C G0 ctx))))))) kernGB
      = (kernG r o oLaz sur g).map fun p => genNoun p.2 x := by
  by_cases ho : oLaz = o
  · subst ho
    rw [kern_gate hc hl x G0 LAZ oLaz r sur g hs h0]
    cases e : sureRequireLook sur g with
    | none => simp [kernG, e, bind, StateT.bind]
    | some p =>
      obtain ⟨ned, g1⟩ := p
      by_cases hn : ned = Need.none
      · simp [kernG, e, hn, bind, StateT.bind, pure, StateT.pure]
      · simp [kernG, e, hn, bind, StateT.bind, pure, StateT.pure, Lazy.noSoft]
  · have hsrl := comp_sure_require_look (x := x) hc hl g sur h0
    have hD := comp_srl_at
    have hD2 := comp_add_ops_at
    have hD3 := comp_kn_at
    have hD4 := comp_px_at
    have hhas := crn_has x oLaz hs
    simp only [compCore] at hsrl
    cases e : sureRequireLook sur g with
    | none =>
      rw [e] at hsrl
      nock_open kernGB
      generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl ⊢
      simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, kernG]
    | some p =>
      obtain ⟨ned, g1⟩ := p
      rw [e] at hsrl
      simp only [Option.map_some] at hsrl
      by_cases hn : ned = Need.none
      · subst hn
        nock_open kernGB
        generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl ⊢
        simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, Need.toNoun, Tag.none, pure,
          StateT.pure, kernG]
      · obtain ⟨a, b, hab, hne⟩ := kern_head ned hn
        have hpx := comp_proxy hc x g1 r oLaz
        simp only [compCore] at hpx
        simp only [hab] at hsrl
        cases ep : proxy r oLaz g1 with
        | none =>
          rw [ep] at hpx
          nock_open kernGB
          generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx ⊢
          simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, hne, hn, ho, hD4, comp_px_arm,
            hpx, ep, kernG]
        | some q =>
          obtain ⟨src, g2⟩ := q
          rw [ep] at hpx
          have hkn := comp_kern_need x ctx src ned g2
          simp only [compCore, hab] at hkn
          cases e2 : kernNeed src ned g2 with
          | none =>
            rw [e2] at hkn
            nock_open kernGB
            generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hkn ⊢
            simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, hne, hn, ho, hD4, comp_px_arm,
              hpx, ep, hD3, comp_kn_arm, hkn, e2, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas,
              kernG, Lazy.noSoft]
          | some q2 =>
            obtain ⟨ops, g3⟩ := q2
            rw [e2] at hkn
            simp only [Option.map_some] at hkn
            have hao := comp_add_ops x hc g3 oLaz ops
            simp only [compCore] at hao
            nock_open kernGB
            generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hkn hao ⊢
            generalize listNoun Pole.toNoun ops = N at hkn hao ⊢
            simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, hne, hn, ho, hD4, comp_px_arm,
              hpx, ep, hD3, comp_kn_arm, hkn, e2, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas,
              hD2, comp_add_ops_arm, hao, kernG, Lazy.noSoft]

/-- The model's `kern`, with its gate named. -/
theorem kern_eq (o : Nat) (laz : Lazy CSet) (g : Gen (TreapMap mugF)) :
    kern o laz g = (do
      let r ← re
      let g ← get
      if g.drop then pure r else do
        Lazy.walkLazy (kernG r o) o laz
        pure r : CM (TreapMap mugF) Nat) g := rfl

/-- **`+kern` on every lazy need** (forks and bonds to any depth), where
every block the walk visits from `o` is not a key of `soft` and no sure need
looks at axis `0`. -/
theorem comp_kern_all (hc : CompIn ctx) (hl : CompLib ctx) (hm : CompMolds ctx) (x : GenRest)
    (g : Gen (TreapMap mugF)) (o : Nat) (laz : Lazy CSet) (hP : WalkP (mdP x) o laz) :
    nock (C kernBat (C (C (A o) laz.toNoun) (compCore g x ctx))) kernBat
      = (kern o laz g).map fun p => C (A p.1) (genNoun p.2 x) := by
  have hm' := hm
  obtain ⟨hm191, ⟨Q, a2, M2, m2, v2, hQ, ha2, hM2, hm2, hv2⟩⟩ := hm'
  have hre := comp_re' ctx x g
  obtain ⟨bunt, hwa⟩ := comp_wl_arm hm comp.door (genNoun { g with re := g.re + 1 } x)
  have hwl := comp_walk_lazy_all (ctx := ctx) hc hm191 x kernGB
    (C (A 0) (C v2 (genNoun { g with re := g.re + 1 } x)))
    (C (A g.re) (C kernBat (C (C (A o) laz.toNoun) (C comp.door (C (genNoun { g with re := g.re + 1 } x) ctx)))))
    comp.door (kernG g.re o) (mdP x)
    (fun oLaz s g' hp => kern_gate_all hc hl x _ laz.toNoun o oLaz g.re s g' hp.1 hp.2)
    laz o { g with re := g.re + 1 } hP
  have hD := comp_re_at
  have hD1 := comp_drop_at
  have hD3 := comp_wl_at
  rw [kern_eq]
  simp only [compCore] at hwa hre ⊢
  generalize comp.door = Dr at hD hD1 hD3 hwa hwl hre ⊢
  cases hdr : g.drop
  · simp only [hdr] at hwa hre
    cases ew : Lazy.walkLazy (kernG g.re o) o laz { g with re := g.re + 1 } with
    | none =>
      rw [ew] at hwl
      simp only [hdr] at hwl
      have ew' := ew
      simp only [hdr] at ew'
      nock_open kernBat
      simp [nock_exec, hD, hre, hD1, dropArm, cgModeNoun, hdr, hD3, hwa, hwl, hQ, ha2, hM2, hm2, hv2, ew, ew',
        re, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    | some u =>
      rw [ew] at hwl
      simp only [hdr] at hwl
      have ew' := ew
      simp only [hdr] at ew'
      nock_open kernBat
      simp [nock_exec, hD, hre, hD1, dropArm, cgModeNoun, hdr, hD3, hwa, hwl, hQ, ha2, hM2, hm2, hv2, ew, ew',
        re, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
  · nock_open kernBat
    simp [nock_exec, hD, hre, hD1, dropArm, cgModeNoun, hdr, re, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, pure, StateT.pure]

/-- **`+kerf` on every `next`**: `+emit` of `[~ ~ %hop then]`, then `+kern`
at the new block (`comp_kern_all`). -/
theorem comp_kerf_all (hc : CompIn ctx) (hl : CompLib ctx) (hm : CompMolds ctx) (x : GenRest)
    (g : Gen (TreapMap mugF)) (n : NextL CSet) (hP : WalkP (mdP x) g.bo n.laz) :
    nock (C kerfBat (C (C (A 0x7478656e) (C n.laz.toNoun n.th.toNoun)) (compCore g x ctx))) kerfBat
      = (kerf n g).map fun p => C (C (A p.1.1) (A p.1.2)) (genNoun p.2 x) := by
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop n.th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
  have hk := comp_kern_all hc hl hm x (cfEmitG ⟨[], [], Termin.hop n.th⟩ g) g.bo n.laz hP
  have hD1 := comp_emit_at
  have hD2 := comp_kern_at
  simp only [compCore] at hk ⊢
  generalize comp.door = Dr at hD1 hD2 he hk ⊢
  cases e : kern g.bo n.laz (cfEmitG ⟨[], [], Termin.hop n.th⟩ g) with
  | none =>
    rw [e] at hk
    nock_open kerfBat
    simp [nock_exec, hD1, comp_emit_arm, he, hD2, comp_kern_arm, hk, kerf, cf_emit_g, bind,
      StateT.bind, e]
  | some p =>
    obtain ⟨r, g2⟩ := p
    rw [e] at hk
    nock_open kerfBat
    simp [nock_exec, hD1, comp_emit_arm, he, hD2, comp_kern_arm, hk, kerf, cf_emit_g, bind,
      StateT.bind, e, pure, StateT.pure]

end Compiler
end Formalization
