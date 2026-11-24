import lemmas.Compiler.CompKernNeed

/-!
# `+kern` and `+kerf` of the door of `+comp`, on a fork-free lazy need

`+kern` (door arm `7167`, `comp_kern_at`) takes a fresh register `r`, and
out of `%drop` mode runs `+walk-lazy` from `o` on `laz` with the gate
`kernGB`: `gen` set to `gen-init`, `+sure-require-look`, nothing on
`%none`, else the source `r` (the walk is at `o` itself, `[5 [0 28] [0
252]]`, so no `+proxy`), the test `(~(has by soft.gen) o-laz)` (false where
`o` is not a key of `soft`, `crn_has`), `+kern-need` (`comp_kern_need`,
from `kn_at`) and `+add-ops`.  On `lazyNoun s` the walk is one slam of the
gate (`comp_walk_lazy`), so `+kern` is the model's `kern o (ofSure s)`
(`comp_kern`).  `+kerf` (door arm `27572`) is `+emit` of `[~ ~ %hop
then]` and `+kern` at the new block (`comp_kerf`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

def kernGB : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 27))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1399) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 0) (A 510)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 28)) (C (A 0) (A 252)))) (C (C (C (A 0) (A 30)) (C (A 0) (A 510))) (C (A 8) (C (C (A 9) (C (A 0xabb5a) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 0) (A 60)))) (C (A 0) (A 2))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0x2aabe) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 6)) (C (A 0) (A 14))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x555df6) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))))))))))))))))))))))))))))))))))

def kernBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 7)))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 15)))) (C (C (C (A 0) (A 2)) (C (A 0) (A 62))) (C (C (A 0) (A 2)) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 61)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (C (A 7) (C (C (A 9) (C (A 4) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 62)))) (C (C (A 1) kernGB) (C (A 0) (A 1)))))))))) (C (A 0) (A 2))))))))))))))))))))

def kernArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) kernBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6e72656b2d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

def kerfBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 59)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bff) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 122)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 6)) (C (A 0) (A 2))) (C (A 0) (A 126)))))))))))))))))))

def kerfArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0))))) (C (C (A 1) kerfBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6672656b2d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

theorem comp_kern_at : slot? 7167 comp.door = some kernArm := by kernel_rfl
theorem comp_kerf_at : slot? 27572 comp.door = some kerfArm := by kernel_rfl

/-- The arm `kern-need` builds its gate. -/
theorem comp_kn_arm (d : Noun) : nock d knArm = some (C knBat (C (C (A 0) (C (A 0x656e6f6e) (A 0))) d)) := by
  unfold knArm; simp only [nock_exec]

/-- **`+kern-need`** is `kernNeed`, on every need. -/
theorem comp_kern_need (x : GenRest) (ctx : Noun) (r : Nat) (ned : Need) (g : Gen (TreapMap mugF)) :
    nock (C knBat (C (C (A r) ned.toNoun) (compCore g x ctx))) knBat
      = (kernNeed r ned g).map fun p => C (listNoun Pole.toNoun p.1) (genNoun p.2 x) := by
  have h := kn_at x ctx ned r [] g
  unfold knT at h
  rw [kernNeed, ← h]
  nock_open knBat
  simp [nock_exec, listNoun]

/-- The head of the noun of a need other than `%none` is not `%none`. -/
theorem kern_head (ned : Need) (hn : ned ≠ Need.none) :
    ∃ a b, ned.toNoun = C a b ∧ eqCode (A 0x656e6f6e) a = A 1 := by
  cases ned with
  | none => exact absurd rfl hn
  | this d => exact ⟨_, _, rfl, by simp [eqCode, Tag.this]⟩
  | both d h t => exact ⟨_, _, rfl, by simp [eqCode, Tag.both]⟩
  | pair p q =>
    obtain ⟨u, v, hp⟩ := cd_need_cell p
    exact ⟨_, _, by rw [Need.toNoun, hp], by simp [eqCode]⟩

/-- **The gate of `+kern`** at the block `o` it was called with, where `o`
is not a key of `soft` and no looked-at axis is `0`. -/
theorem kern_gate (hc : CompIn ctx) (hl : CompLib ctx) (x : GenRest) (G0 LAZ : Noun) (o r : Nat)
    (sur : Sure CSet) (g : Gen (TreapMap mugF)) (hs : x.SoftOut o)
    (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C kernGB (C (C (A o) (C sur.toNoun (genNoun g x)))
      (C (A r) (C kernBat (C (C (A o) LAZ) (C comp.door (C G0 ctx))))))) kernGB
      = ((do
          let ned ← sureRequireLook sur
          if ned = Need.none then pure () else do
          let ops ← kernNeed r ned
          addOps o ops : CM (TreapMap mugF) Unit) g).map fun p => genNoun p.2 x := by
  have hsrl := comp_sure_require_look (x := x) hc hl g sur h0
  have hD := comp_srl_at
  have hD2 := comp_add_ops_at
  have hD3 := comp_kn_at
  have hhas := crn_has x o hs
  simp only [compCore] at hsrl
  cases e : sureRequireLook sur g with
  | none =>
    rw [e] at hsrl
    nock_open kernGB
    generalize comp.door = Dr at hD hD2 hD3 hsrl ⊢
    simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind]
  | some p =>
    obtain ⟨ned, g1⟩ := p
    rw [e] at hsrl
    simp only [Option.map_some] at hsrl
    by_cases hn : ned = Need.none
    · subst hn
      nock_open kernGB
      generalize comp.door = Dr at hD hD2 hD3 hsrl ⊢
      simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, Need.toNoun, Tag.none, pure,
        StateT.pure]
    · obtain ⟨a, b, hab, hne⟩ := kern_head ned hn
      have hkn := comp_kern_need x ctx r ned g1
      simp only [compCore, hab] at hkn hsrl
      cases e2 : kernNeed r ned g1 with
      | none =>
        rw [e2] at hkn
        nock_open kernGB
        generalize comp.door = Dr at hD hD2 hD3 hsrl hkn ⊢
        simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, hne, hn, hD3, comp_kn_arm, hkn,
          e2, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas]
      | some q =>
        obtain ⟨ops, g2⟩ := q
        rw [e2] at hkn
        simp only [Option.map_some] at hkn
        have hao := comp_add_ops x hc g2 o ops
        simp only [compCore] at hao
        nock_open kernGB
        generalize comp.door = Dr at hD hD2 hD3 hsrl hkn hao ⊢
        generalize listNoun Pole.toNoun ops = N at hkn hao ⊢
        simp [nock_exec, hD, comp_srl_arm, hsrl, e, bind, StateT.bind, hne, hn, hD3, comp_kn_arm, hkn,
          e2, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas, hD2, comp_add_ops_arm, hao]

/-- The arm `kern` builds its gate. -/
theorem comp_kern_arm (d : Noun) : nock d kernArm =
    some (C kernBat (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) d)) := by
  unfold kernArm; simp only [nock_exec]

/-- The model's `kern` on a fork-free lazy need, written out. -/
theorem kern_ofSure (o : Nat) (s : Sure CSet) (g : Gen (TreapMap mugF)) :
    kern o (Lazy.ofSure s) g = if g.drop then some (g.re, { g with re := g.re + 1 }) else
      ((do
          let ned ← sureRequireLook s
          if ned = Need.none then pure () else do
          let ops ← kernNeed g.re ned
          addOps o ops : CM (TreapMap mugF) Unit) { g with re := g.re + 1 }).map fun p => (g.re, p.2) := by
  cases hd : g.drop
  · simp only [kern, Lazy.ofSure, Lazy.walkLazy, re, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Option.bind_some, hd, Bool.false_eq_true, if_false, Lazy.noSoft,
      List.isEmpty_nil, Bool.and_self, if_true]
    cases e1 : sureRequireLook s { g with re := g.re + 1 } with
    | none => simp only [hd] at e1; simp [e1]
    | some p =>
      obtain ⟨ned, g2⟩ := p
      simp only [hd] at e1
      by_cases hn : ned = Need.none
      · simp [e1, hn, StateT.pure, StateT.bind]
      · cases e2 : kernNeed g.re ned g2 with
        | none => simp [e1, hn, e2, StateT.pure, StateT.bind]
        | some q =>
          obtain ⟨ops, g3⟩ := q
          cases e3 : addOps o ops g3 with
          | none => simp [e1, hn, e2, e3, StateT.pure, StateT.bind]
          | some u => simp [e1, hn, e2, e3, StateT.pure, StateT.bind]
  · simp [kern, re, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, hd]

/-- **`+kern` on `lazyNoun s`** is `kern o (ofSure s)`, where `o` is not a
key of `soft` and no looked-at axis of `s` is `0`. -/
theorem comp_kern (hc : CompIn ctx) (hl : CompLib ctx) (hm : CompMolds ctx) (x : GenRest)
    (g : Gen (TreapMap mugF)) (o : Nat) (s : Sure CSet) (hs : x.SoftOut o)
    (h0 : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0) :
    nock (C kernBat (C (C (A o) (lazyNoun s)) (compCore g x ctx))) kernBat
      = (kern o (Lazy.ofSure s) g).map fun p => C (A p.1) (genNoun p.2 x) := by
  have hm' := hm
  obtain ⟨_, ⟨Q, a2, M2, m2, v2, hQ, ha2, hM2, hm2, hv2⟩⟩ := hm'
  have hre := comp_re' ctx x g
  obtain ⟨bunt, hwa⟩ := comp_wl_arm hm comp.door (genNoun { g with re := g.re + 1 } x)
  have hgate := kern_gate hc hl x (genNoun { g with re := g.re + 1 } x) (lazyNoun s) o g.re s
    { g with re := g.re + 1 } hs h0
  have hD := comp_re_at
  have hD1 := comp_drop_at
  have hD3 := comp_wl_at
  rw [kern_ofSure]
  simp only [compCore] at hwa hre ⊢
  generalize comp.door = Dr at hD hD1 hD3 hwa hgate hre ⊢
  generalize ((do
          let ned ← sureRequireLook s
          if ned = Need.none then pure () else do
          let ops ← kernNeed g.re ned
          addOps o ops : CM (TreapMap mugF) Unit) { g with re := g.re + 1 }) = OUT at hgate ⊢
  cases hdr : g.drop
  · have hw := comp_walk_lazy (ctx := ctx) Dr kernGB (C (A 0) (C v2 (genNoun { g with re := g.re + 1 } x)))
      (C (A g.re) (C kernBat (C (C (A o) (lazyNoun s)) (C Dr (C (genNoun { g with re := g.re + 1 } x) ctx)))))
      (genNoun { g with re := g.re + 1 } x) o s _ hgate
    simp only [hdr] at hwa hre hw
    nock_open kernBat
    cases OUT with
    | none =>
      simp [nock_exec, hD, hre, hD1, dropArm, cgModeNoun, hdr, hD3, hwa, hw, hQ, ha2, hM2, hm2, hv2]
    | some u =>
      simp [nock_exec, hD, hre, hD1, dropArm, cgModeNoun, hdr, hD3, hwa, hw, hQ, ha2, hM2, hm2, hv2]
  · nock_open kernBat
    simp [nock_exec, hD, hre, hD1, dropArm, cgModeNoun, hdr]

/-- The arm `kerf` builds its gate. -/
theorem comp_kerf_arm (d : Noun) : nock d kerfArm =
    some (C kerfBat (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))
      (C (A 0) (A 0)))) d)) := by
  unfold kerfArm; simp only [nock_exec]

/-- **`+kerf` on a fork-free `next`** is `kerf`, where the new block is not a
key of `soft` and no looked-at axis is `0`. -/
theorem comp_kerf (hc : CompIn ctx) (hl : CompLib ctx) (hm : CompMolds ctx) (x : GenRest)
    (g : Gen (TreapMap mugF)) (n : Next CSet) (hs : x.SoftOut g.bo)
    (h0 : ∀ y ∈ HoonSet.toList n.laz.lok, y ≠ 0) :
    nock (C kerfBat (C (C (A 0x7478656e) (C (lazyNoun n.laz) n.th.toNoun)) (compCore g x ctx))) kerfBat
      = (kerf (Next.toL n) g).map fun p => C (C (A p.1.1) (A p.1.2)) (genNoun p.2 x) := by
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop n.th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
  have hk := comp_kern hc hl hm x (cfEmitG ⟨[], [], Termin.hop n.th⟩ g) g.bo n.laz hs h0
  have hD1 := comp_emit_at
  have hD2 := comp_kern_at
  simp only [compCore] at hk ⊢
  generalize comp.door = Dr at hD1 hD2 he hk ⊢
  cases e : kern g.bo (Lazy.ofSure n.laz) (cfEmitG ⟨[], [], Termin.hop n.th⟩ g) with
  | none =>
    rw [e] at hk
    nock_open kerfBat
    simp [nock_exec, hD1, comp_emit_arm, he, hD2, comp_kern_arm, hk, kerf, cf_emit_g, bind,
      StateT.bind, e, Next.toL]
  | some p =>
    obtain ⟨r, g2⟩ := p
    rw [e] at hk
    nock_open kerfBat
    simp [nock_exec, hD1, comp_emit_arm, he, hD2, comp_kern_arm, hk, kerf, cf_emit_g, bind,
      StateT.bind, e, Next.toL, pure, StateT.pure]

end Compiler
end Formalization
