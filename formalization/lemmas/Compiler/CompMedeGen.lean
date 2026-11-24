import lemmas.Compiler.CompSplitGen

/-!
# `+mede` on every lazy need

`+mede` (door arm `27307`, `mdBat` of `CompMedeLink.lean`) emits `[~ ~ %hop
then]` as block `o`, and out of `%drop` mode walks the lazy need from `o`
with the gate `mdGate`: `gen` set to `gen-init`, `+sure-require-look`, then
the loop that puts the constant into the registers of the need (or crashes
the block where it wants parts of an atom), all at the block the walk visits
(the gate's own sample `o`).  The model `medeL` of `Ska/CompLazyRun.lean`
walks with the same gate (`walkLazy`).  No departure.

`comp_mede_all`: the arm on every lazy need (forks and bonds to any depth)
whose every visited block is not a key of `soft` and whose sure needs look
at no axis `0` (`WalkP mdP`), from `comp_walk_lazy_all` and `md_gate`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- What the gates of the walks need at a visited block: it is not a key of
`soft`, and the sure need looks at no axis `0`. -/
def mdP (x : GenRest) (o : Nat) (s : Sure CSet) : Prop := x.SoftOut o ∧ lok0 o s

/-- **`+mede` on every lazy need** (forks and bonds to any depth), where
every block the walk visits from the new block is not a key of `soft` and
no sure need looks at axis `0`. -/
theorem comp_mede_all (hc : CompIn ctx) (hl : CompLib ctx) (hm : CompMolds ctx) (x : GenRest)
    (g : Gen (TreapMap mugF)) (th : Jmp) (som : Noun) (laz : Lazy CSet) (hP : WalkP (mdP x) g.bo laz) :
    nock (C mdBat (C (C th.toNoun (C som laz.toNoun)) (compCore g x ctx))) mdBat
      = (medeL th som laz g).map fun p => C (A p.1) (genNoun p.2 x) := by
  have hm' := hm
  obtain ⟨hm191, ⟨Q, a2, M2, m2, v2, hQ, ha2, hM2, hm2, hv2⟩⟩ := hm'
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
  have hd : (cfEmitG ⟨[], [], Termin.hop th⟩ g).drop = g.drop := by unfold cfEmitG; split <;> rfl
  obtain ⟨bunt, hwa⟩ := comp_wl_arm hm comp.door (genNoun (cfEmitG ⟨[], [], Termin.hop th⟩ g) x)
  have hwl := comp_walk_lazy_all (ctx := ctx) hc hm191 x mdGate
    (C (A 0) (C v2 (genNoun (cfEmitG ⟨[], [], Termin.hop th⟩ g) x)))
    (C (A g.bo) (C mdBat (C (C th.toNoun (C som laz.toNoun))
      (C comp.door (C (genNoun (cfEmitG ⟨[], [], Termin.hop th⟩ g) x) ctx)))))
    comp.door (fun o sur => do let ned ← sureRequireLook sur; medeLoop o som ned) (mdP x)
    (fun o s g' hp => md_gate hc hl x _ mdBat th.toNoun laz.toNoun g.bo o som s g' hp.1 hp.2)
    laz g.bo (cfEmitG ⟨[], [], Termin.hop th⟩ g) hP
  have hD1 := comp_drop_at
  have hD2 := comp_emit_at
  have hD3 := comp_wl_at
  simp only [compCore] at hwa ⊢
  generalize comp.door = Dr at hD1 hD2 hD3 he hwa hwl ⊢
  cases hdr : g.drop
  · cases ew : Lazy.walkLazy (fun o sur => do let ned ← sureRequireLook sur; medeLoop o som ned) g.bo laz
        (cfEmitG ⟨[], [], Termin.hop th⟩ g) with
    | none =>
      rw [ew] at hwl
      have ew' := ew
      simp only [bind] at ew'
      nock_open mdBat
      simp [nock_exec, hD1, hD2, hD3, comp_emit_arm, he, hd, hdr, dropArm, cgModeNoun, hwa, hwl, hQ,
        ha2, hM2, hm2, hv2, medeL, cf_emit_g, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, ew, ew']
    | some p =>
      obtain ⟨u, g3⟩ := p
      rw [ew] at hwl
      have ew' := ew
      simp only [bind] at ew'
      nock_open mdBat
      simp [nock_exec, hD1, hD2, hD3, comp_emit_arm, he, hd, hdr, dropArm, cgModeNoun, hwa, hwl, hQ,
        ha2, hM2, hm2, hv2, medeL, cf_emit_g, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, ew, ew']
  · nock_open mdBat
    simp [nock_exec, hD1, hD2, comp_emit_arm, he, hd, hdr, dropArm, cgModeNoun, medeL, cf_emit_g,
      bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]

end Compiler
end Formalization
