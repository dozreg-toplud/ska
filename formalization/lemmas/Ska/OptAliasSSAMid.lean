import lemmas.Ska.OptAliasSSARub
import lemmas.Ska.OptMiddleWalk
import lemmas.Ska.OptDownPar

/-!
# `+remove-empty-middle` keeps single assignment

**`ssk_mid`** (the field `middle` of `SSAKeepR`).  The pass changes ends only.
A new jump goes from an old jump's target through a chain of bypassed blocks
(`SskChain`: empty bodies, ends that hop, parameters that only their own block
mentions, `Byp`), so `Reach` after is `Reach` before, and a path after lifts to
a path before with the bypassed blocks inserted (`ssk_mid_lift`).  A read
after is a read before at the same place, or a read of the substituted
arguments of a new hop: a register that the end of a bypassed block `m` read and
that is not a parameter of `m` (`ssk_mfin`, from `ssk_rh`).  A definition found
before in a bypassed block is of a parameter that only that block mentions, so
it is no definition for a read elsewhere (`byp_owner`).  A block ending in
`%bom` is unchanged and reads nothing at its end, so a dead fill before is one
after.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- A chain of bypassable blocks from `x` to `m` (the blocks before `m`, last
first). -/
inductive SskChain (bl : Map Blob) : Nat → List Nat → Nat → Prop
  | refl (x : Nat) : SskChain bl x [] x
  | step {x : Nat} {bx : Blob} {t : Jmp} {l : List Nat} {m : Nat} :
      HoonMap.get bl x = some bx → bx.body = [] → bx.fin = Termin.hop t → (∀ k ∈ bx.par, Byp bl k) →
      SskChain bl t.there l m → SskChain bl x (l ++ [x]) m

/-- A bypassable block: empty body, parameters that only it mentions. -/
def SskByp (bl : Map Blob) (x : Nat) : Prop :=
  ∃ bx, HoonMap.get bl x = some bx ∧ bx.body = [] ∧ ∀ k ∈ bx.par, Byp bl k

theorem ssk_chain_reach {bl : Map Blob} {x : Nat} {l : List Nat} {m : Nat} (hc : SskChain bl x l m) :
    Reach bl x → Reach bl m := by
  induction hc with
  | refl => exact id
  | @step x bx t l m hx _ ht _ _ ih =>
    exact fun hr => ih (Reach.jump (j := t) hr hx (by rw [ht]; simp [getJmps]))

theorem ssk_chain_bpath {bl : Map Blob} {x : Nat} {l : List Nat} {m : Nat} (hc : SskChain bl x l m) :
    ∀ Q, BPath bl (x :: Q) → BPath bl (m :: (l ++ Q)) := by
  induction hc with
  | refl => exact fun _ h => h
  | @step x bx t l m hx _ ht _ _ ih =>
    intro Q hQ
    have := ih (x :: Q) (BPath.step hQ hx (by rw [ht]; simp [getJmps]))
    simpa using this

theorem ssk_chain_byp {bl : Map Blob} {x : Nat} {l : List Nat} {m : Nat} (hc : SskChain bl x l m) :
    ∀ y ∈ l, SskByp bl y := by
  induction hc with
  | refl => intro y hy; cases hy
  | @step x bx t l m hx hb _ hp _ ih =>
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ih y hy
    · rw [List.mem_singleton.mp hy]; exact ⟨bx, hx, hb, hp⟩

theorem ssk_mkSub_dom : ∀ (P : List Nat) (V : List (Option Nat)) (s0 s : Nat → Option (Option Nat)),
    mkSub P V s0 = some s → ∀ q, (q ∈ P ∨ (s0 q).isSome) → (s q).isSome
  | [], [], s0, s, h, q, hq => by
    simp only [mkSub, Option.some.injEq] at h; subst h
    rcases hq with hq | hq
    · cases hq
    · exact hq
  | [], _ :: _, _, _, h, _, _ => by simp [mkSub] at h
  | _ :: _, [], _, _, h, _, _ => by simp [mkSub] at h
  | p :: ps, a :: as, s0, s, h, q, hq => by
    simp only [mkSub] at h
    refine ssk_mkSub_dom ps as _ s h q ?_
    by_cases e : q = p
    · right; simp [e]
    · rcases hq with hq | hq
      · left; exact (List.mem_cons.mp hq).resolve_left e
      · right; simp [e, hq]

section
variable {bl : Map Blob}

/-- `rewrite-jump` walks a chain of bypassable blocks (with no parameters). -/
theorem ssk_rj : ∀ (n : Nat) (j j' : Jmp), rewriteJump bl n j = some j' →
    (∃ l, SskChain bl j.there l j'.there) ∧ j'.args = j.args
  | 0, _, _, h => by simp [rewriteJump] at h
  | n + 1, j, j', h => by
    simp only [rewriteJump] at h
    split at h
    · cases h; exact ⟨⟨[], SskChain.refl _⟩, rfl⟩
    · rename_i ha
      obtain ⟨nex, hn, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · cases h
      · rename_i hp
        split at h
        · cases h; exact ⟨⟨[], SskChain.refl _⟩, rfl⟩
        · rename_i hb
          split at h
          · rename_i t ht
            split at h
            · cases h; exact ⟨⟨[], SskChain.refl _⟩, rfl⟩
            · rename_i hta
              obtain ⟨⟨l, hl⟩, he⟩ := ssk_rj n t j' h
              have hp' : nex.par = [] := by simpa using hp
              refine ⟨⟨l ++ [j.there], SskChain.step hn (by simpa using hb) ht (fun k hk => ?_) hl⟩, ?_⟩
              · rw [hp'] at hk; cases hk
              · rw [he]; simp only [ne_eq, Decidable.not_not] at hta ha; rw [hta, ha]
          · cases h; exact ⟨⟨[], SskChain.refl _⟩, rfl⟩

/-- `rewrite-hop` walks a chain of bypassable blocks; an argument after is an
argument before, or a register the end of a bypassed block reads that is not
its parameter. -/
theorem ssk_rh : ∀ (n : Nat) (j j' : Jmp), rewriteHop bl (readersOf bl) n j = some j' →
    (∃ l, SskChain bl j.there l j'.there) ∧
    ∀ r, some r ∈ j'.args → some r ∈ j.args ∨ ∃ l m bm, SskChain bl j.there l m ∧ HoonMap.get bl m = some bm ∧
      bm.body = [] ∧ r ∈ finRegs bm.fin ∧ r ∉ bm.par
  | 0, _, _, h => by simp [rewriteHop] at h
  | n + 1, j, j', h => by
    simp only [rewriteHop] at h
    obtain ⟨nex, hn, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; exact ⟨⟨[], SskChain.refl _⟩, fun r hr => Or.inl hr⟩
    · rename_i hb
      split at h
      · rename_i t ht
        split at h
        · cases h; exact ⟨⟨[], SskChain.refl _⟩, fun r hr => Or.inl hr⟩
        · rename_i hall
          obtain ⟨s, hsub, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨l, hl⟩, hrd⟩ := ssk_rh n _ j' h
          have hbody : nex.body = [] := by simpa using hb
          have hall' : (nex.par.all fun p => (readersOf bl p).all (· = j.there)) = true := by simpa using hall
          have hbyp : ∀ k ∈ nex.par, Byp bl k := fun k hk => ⟨j.there, nex, t, hn, hbody, ht, hk, hall'⟩
          refine ⟨⟨l ++ [j.there], SskChain.step hn hbody ht hbyp hl⟩, fun r hr => ?_⟩
          rcases hrd r hr with h1 | ⟨l1, m, bm, hc, hbm, hbe, hrm, hnp⟩
          · simp only [List.mem_map] at h1
            obtain ⟨a, ha, hpa⟩ := h1
            obtain ⟨a0, rfl, h2 | ⟨h2, e⟩⟩ := passArg_some hpa
            · rcases mkSub_mem _ _ _ s hsub a0 _ h2 with h3 | h3
              · exact Or.inl h3
              · cases h3
            · subst e
              refine Or.inr ⟨[], j.there, nex, SskChain.refl _, hn, hbody, ?_, fun hp => ?_⟩
              · rw [ht]; exact mem_jmpRegs.mpr ha
              · have := ssk_mkSub_dom _ _ _ s hsub r (Or.inl hp)
                rw [h2] at this; simp at this
          · exact Or.inr ⟨l1 ++ [j.there], m, bm, SskChain.step hn hbody ht hbyp hc, hbm, hbe, hrm, hnp⟩
      · cases h; exact ⟨⟨[], SskChain.refl _⟩, fun r hr => Or.inl hr⟩

/-- The new end of a block: its jumps go through chains from old targets, its
reads are old reads or reads of the ends of bypassed blocks. -/
theorem ssk_mfin {fuel : Nat} {f f' : Termin} (h : middleFin bl (readersOf bl) fuel f = some f') :
    (∀ j' ∈ getJmps f', ∃ j ∈ getJmps f, ∃ l, SskChain bl j.there l j'.there) ∧
    ∀ r ∈ finRegs f', r ∈ finRegs f ∨ ∃ j ∈ getJmps f, ∃ l m bm, SskChain bl j.there l m ∧
      HoonMap.get bl m = some bm ∧ bm.body = [] ∧ r ∈ finRegs bm.fin ∧ r ∉ bm.par := by
  cases f with
  | hop t =>
    simp only [middleFin, Option.map_eq_some_iff] at h
    obtain ⟨t', ht', rfl⟩ := h
    obtain ⟨⟨l, hl⟩, hrd⟩ := ssk_rh fuel t t' ht'
    have htm : t ∈ getJmps (Termin.hop t) := by simp [getJmps]
    refine ⟨fun j' hj' => ?_, fun r hr => ?_⟩
    · simp only [getJmps, List.mem_singleton] at hj'
      subst hj'; exact ⟨t, htm, l, hl⟩
    · rcases hrd r (mem_jmpRegs.mp hr) with h1 | h1
      · exact Or.inl (mem_jmpRegs.mpr h1)
      · exact Or.inr ⟨t, htm, h1⟩
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    obtain ⟨⟨lz, hlz⟩, haz⟩ := ssk_rj fuel z z' hz
    obtain ⟨⟨lo, hlo⟩, hao⟩ := ssk_rj fuel o o' ho
    refine ⟨fun j' hj' => ?_, fun r hr => Or.inl ?_⟩
    · simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl
      · exact ⟨z, by simp [getJmps], lz, hlz⟩
      · exact ⟨o, by simp [getJmps], lo, hlo⟩
    · simpa [finRegs, jmpRegs, haz, hao] using hr
  | _ =>
    simp only [middleFin, Option.some.injEq] at h
    subst h
    exact ⟨fun j' hj' => ⟨j', hj', [], SskChain.refl _⟩, fun r hr => Or.inl hr⟩

end

/-- A register read at a place of a block is one it mentions. -/
theorem ssk_readAt_regs {b : Blob} {i r : Nat} (h : ReadAt b i r) : r ∈ blobRegs b := by
  rcases h with h | ⟨-, h⟩
  · unfold blobRegs; apply List.mem_append_right
    cases e : (b.body.drop i).head? with
    | none => rw [e] at h; simp at h
    | some op =>
      rw [e] at h
      have hop : op ∈ b.body := List.mem_of_mem_drop (List.mem_of_mem_head? e)
      refine List.mem_flatMap.mpr ⟨op, hop, ?_⟩
      simp only [Option.map_some, Option.getD_some, aliasReads] at h
      split at h
      · exact List.mem_of_mem_erase h
      · exact h
  · exact fin_blobRegs h

section mid
variable {fuel : Nat} {bl bl' : Map Blob} (hM : MidBlocks fuel bl bl')
include hM

theorem ssk_mid_reach {o : Nat} (h : Reach bl' o) : Reach bl o := by
  induction h with
  | zero => exact Reach.zero
  | jump _ hb hj ih =>
    obtain ⟨b, f', hb0, hf, rfl⟩ := hM.back hb
    obtain ⟨j, hj0, l, hl⟩ := (ssk_mfin hf).1 _ hj
    exact ssk_chain_reach hl (Reach.jump (j := j) ih hb0 hj0)

/-- A path after lifts to a path before with bypassable blocks inserted. -/
theorem ssk_mid_lift {L : List Nat} (h : BPath bl' L) :
    ∀ o p, L = o :: p → ∃ q, BPath bl (o :: q) ∧ ∀ x ∈ q, x ∈ p ∨ SskByp bl x := by
  induction h with
  | start => intro o p e; cases e; exact ⟨[], BPath.start, fun x hx => by cases hx⟩
  | @step p0 o0 b' j' _ hb hj ih =>
    intro o p e
    cases e
    obtain ⟨q, hq, hqm⟩ := ih o0 p0 rfl
    obtain ⟨b, f', hb0, hf, rfl⟩ := hM.back hb
    obtain ⟨j, hj0, l, hl⟩ := (ssk_mfin hf).1 _ hj
    refine ⟨l ++ o0 :: q, ssk_chain_bpath hl _ (BPath.step hq hb0 hj0), fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ssk_chain_byp hl x hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl List.mem_cons_self
      · rcases hqm x hx with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem ssk_mid_site {r : Nat} {s : Nat × Option Nat} (h : DefSite bl' r s) : DefSite bl r s := by
  obtain ⟨o, _ | i⟩ := s
  · obtain ⟨b', hb', hm⟩ := h
    obtain ⟨b, f', hb, -, rfl⟩ := hM.back hb'
    exact ⟨b, hb, hm⟩
  · obtain ⟨b', op, hb', hop, hd⟩ := h
    obtain ⟨b, f', hb, -, rfl⟩ := hM.back hb'
    exact ⟨b, op, hb, hop, hd⟩

theorem ssk_mid_fill {r o i : Nat} (h : DeadFill bl r o i) : DeadFill bl' r o i := by
  obtain ⟨b, hb, ⟨u, hu⟩, hn, himm, hrd⟩ := h
  obtain ⟨f', hf', hb'⟩ := (hM o).2 b hb
  have hfe : f' = b.fin := by
    rw [hu] at hf' ⊢; simp only [middleFin, Option.some.injEq] at hf'; exact hf'.symm
  subst hfe
  refine ⟨b, hb', ⟨u, hu⟩, hn, himm, fun o' b' j hr' hb'' hj => ?_⟩
  obtain ⟨b0, f0, hb0, hf0, rfl⟩ := hM.back hb''
  have hr0 := ssk_mid_reach hM hr'
  rcases hj with hj | ⟨hj1, hj2⟩
  · exact hrd o' b0 j hr0 hb0 (Or.inl hj)
  · rcases (ssk_mfin hf0).2 r hj2 with h1 | ⟨jj, hjj, l, m, bm, hc, hbm, hbe, hrm, -⟩
    · exact hrd o' b0 j hr0 hb0 (Or.inr ⟨hj1, h1⟩)
    · have hrm' := ssk_chain_reach hc (Reach.jump (j := jj) hr0 hb0 hjj)
      obtain ⟨hmo, -⟩ := hrd m bm 0 hrm' hbm (Or.inr ⟨by rw [hbe]; rfl, hrm⟩)
      subst hmo
      rw [hb] at hbm; cases hbm
      rw [hu] at hrm; cases hrm

theorem ssk_mid_live {r : Nat} {s : Nat × Option Nat} (h : LiveDef bl' r s) : LiveDef bl r s :=
  ⟨ssk_mid_reach hM h.1, ssk_mid_site hM h.2.1, fun i hi hf => h.2.2 i hi (ssk_mid_fill hM hf)⟩

theorem ssk_mid_all {r : Nat} (h : r ∈ allDefs bl') : r ∈ allDefs bl := by
  unfold allDefs at h ⊢
  obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp h
  have hks : (HoonMap.get bl' k).isSome := (MapKeys.mem_keys bl' k).mp hk
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hks
  obtain ⟨b, f', hb, -, rfl⟩ := hM.back hb'
  rw [hb'] at hmem
  refine List.mem_flatMap.mpr ⟨k, (MapKeys.mem_keys bl k).mpr (by rw [hb]; rfl), ?_⟩
  rw [hb]
  exact hmem

end mid

/-- **`+remove-empty-middle` keeps `AliasSSAB`** (the field `middle` of
`SSAKeepR`). -/
theorem ssk_mid {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (hs : AliasSSAB bl) : AliasSSAB bl' := by
  have hM := mid_blocks h
  obtain ⟨h1, h2⟩ := hs
  refine ⟨fun r s s' hs hs' => h1 r s s' (ssk_mid_live hM hs) (ssk_mid_live hM hs'),
    fun o pth b' hpath hb' i r hread hr => ?_⟩
  obtain ⟨b, f', hb, hf, rfl⟩ := hM.back hb'
  obtain ⟨q, hq, hqm⟩ := ssk_mid_lift hM hpath o pth rfl
  have hr0 := ssk_mid_all hM hr
  -- a definition in a block of `q` that is in `pth`
  have hin : ∀ x ∈ pth, ∀ bx, HoonMap.get bl x = some bx → r ∈ blockDefs bx →
      ∃ o' ∈ pth, ∃ b'', HoonMap.get bl' o' = some b'' ∧ r ∈ blockDefs b'' := by
    intro x hx bx hbx hm
    obtain ⟨f'', -, hbx'⟩ := (hM x).2 bx hbx
    exact ⟨x, hx, _, hbx', hm⟩
  -- a definition in a bypassable block is of a parameter only that block mentions
  have hbyp : ∀ x, SskByp bl x → ∀ bx, HoonMap.get bl x = some bx → r ∈ blockDefs bx → Byp bl r := by
    intro x ⟨bx', hbx', hbe, hpar⟩ bx hbx hm
    rw [hbx] at hbx'; cases hbx'
    simp only [blockDefs, hbe, List.filterMap_nil, List.append_nil] at hm
    exact hpar r hm
  rcases hread with hrd | ⟨hi, hrf⟩
  · -- a read by an op: the same read before
    rcases h2 o q b hq hb i r (Or.inl hrd) hr0 with h | h | ⟨x, hx, bx, hbx, hm⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hqm x hx with hxp | hxb
      · exact Or.inr (Or.inr (hin x hxp bx hbx hm))
      · exact Or.inl (show r ∈ b.par from byp_owner (hbyp x hxb bx hbx hm) hb (ssk_readAt_regs (Or.inl hrd)))
  · rcases (ssk_mfin hf).2 r hrf with hrf | ⟨j, hj, l, m, bm, hc, hbm, hbe, hrm, hnp⟩
    · rcases h2 o q b hq hb i r (Or.inr ⟨hi, hrf⟩) hr0 with h | h | ⟨x, hx, bx, hbx, hm⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · rcases hqm x hx with hxp | hxb
        · exact Or.inr (Or.inr (hin x hxp bx hbx hm))
        · exact Or.inl (show r ∈ b.par from byp_owner (hbyp x hxb bx hbx hm) hb (fin_blobRegs (b := b) hrf))
    · -- a substituted argument: read before at the end of the bypassed block `m`
      have hpm := ssk_chain_bpath hc _ (BPath.step hq hb hj)
      have hno : ∀ x, SskByp bl x → ∀ bx, HoonMap.get bl x = some bx → r ∈ blockDefs bx → False :=
        fun x hx bx hbx hm => hnp (byp_owner (hbyp x hx bx hbx hm) hbm (fin_blobRegs hrm))
      rcases h2 m (l ++ o :: q) bm hpm hbm 0 r (Or.inr ⟨by rw [hbe]; rfl, hrm⟩) hr0 with
        h | h | ⟨x, hx, bx, hbx, hm⟩
      · exact absurd h hnp
      · simp at h
      · rcases List.mem_append.mp hx with hx | hx
        · exact (hno x (ssk_chain_byp hc x hx) bx hbx hm).elim
        · rcases List.mem_cons.mp hx with rfl | hx
          · rw [hb] at hbx; cases hbx
            simp only [blockDefs, List.mem_append] at hm
            rcases hm with hm | hm
            · exact Or.inl hm
            · right; left
              simp only at hi
              rw [hi, List.take_length]; exact hm
          · rcases hqm x hx with hxp | hxb
            · exact Or.inr (Or.inr (hin x hxp bx hbx hm))
            · exact (hno x hxb bx hbx hm).elim

end Opt
end SkaModel
end Formalization
