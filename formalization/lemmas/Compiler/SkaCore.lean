import lemmas.Compiler.FolLoopConv
import lemmas.Compiler.Mi
import lemmas.Hoon.DelBy
import lemmas.Pill.Arm.Ska_cg

/-!
# The `|%` core of `+ska-callgraph`

The core `K` in which `+analyze` and `+run` run is
`[K_bat [st' [cg_bat [cg_sample ana]]]]`: its battery `ska_cg.k_bat` (K_bat) holds
`+pop` at slot `2`, `+cull` at `6`, `+above` at `14`, `+analyze` at `60`,
`+sweep` at `61`, `+dirty` at `62` and `+run` at `63`, so they are the arms
`4`, `10`, `22`, `92`, `93`, `94`, `95` of `K`.

The nouns are the generated `ska_cg.*` of `Pill/Arm/Ska_cg.lean`.  The
generated facts do not place `K_bat` in `ana`, so `kc_bat_at` does: `K_bat`
is the noun at axis `2799357` of `ana`, inside the gate `+ska-callgraph` (arm
`341` of `ana`).

`runRest_kc` gives the layout facts `hana`, `hK`, `hKa` of `FolLoopConv.lean`
for the rest of the trap's subject as `+run` builds it.  `above_gate`: the
gate `+above` computes `Ana.above` on every stack, in every context.
`pop_gate'`: the gate `+pop` computes `Ana.pop` on every state, in every
context `K` with `ana` at axis `31`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-! ## Their place in the pill -/

/-- `K_bat` is the pill's: the noun at axis `2799357` of `ana`. -/
theorem kc_bat_at : slot? 2799357 ana = some ska_cg.k_bat := by kernel_rfl

theorem kc_analyze_at : slot? 60 ska_cg.k_bat = some ska_analyze.arm := by kernel_rfl

theorem kc_run_at : slot? 63 ska_cg.k_bat = some ska_run.arm := by kernel_rfl

/-- The layout facts of `FolLoopConv.lean` for the rest of the trap's subject
that `+run` builds in the core `K`. -/
theorem runRest_kc (bus data runBat idn stK cgBat cgS : Noun) :
    slot? 511 (runRest bus data runBat idn ska_cg.k_bat stK cgBat cgS) = some ana ∧
    slot? 31 (runRest bus data runBat idn ska_cg.k_bat stK cgBat cgS)
      = some (C ska_cg.k_bat (C stK (C cgBat (C cgS ana)))) ∧
    slot? 92 (C ska_cg.k_bat (C stK (C cgBat (C cgS ana)))) = some ska_analyze.arm :=
  ⟨runRest_ana .., runRest_K .., runRest_Ka kc_analyze_at _⟩

/-! ## `+above` -/

theorem identNoun_eq_iff (a b : Ident) : identNoun a = identNoun b ↔ a = b :=
  ⟨TKey.enc_inj a b, fun h => h ▸ rfl⟩

/-- `+above`: the functions on the stack above and including `id`, latest
first, as `Ana.above`; it crashes when `id` is not on the stack.  It reads
nothing from its context `c`. -/
theorem above_gate (c : Noun) (id : Ident) : ∀ stk : List Ident,
    nock (C ska_cg.above.battery (C (C (identNoun id) (listNoun identNoun stk)) c)) ska_cg.above.battery
      = (Ana.above id stk).map (listNoun identNoun)
  | [] => by
    nock_open ska_cg.above.battery
    simp [nock_exec, listNoun, Ana.above]
  | i :: stk => by
    have ih := above_gate c id stk
    nock_open ska_cg.above.battery
    by_cases h : id = i
    · subst h
      simp [nock_exec, listNoun, Ana.above, eqCode]
    · have h' : identNoun id ≠ identNoun i := fun e => h ((identNoun_eq_iff _ _).1 e)
      simp [nock_exec, listNoun, Ana.above, eqCode, h, h', ih]
      cases Ana.above id stk <;> simp [listNoun]

/-! ## `+pop` -/

/-- Layer 2 in the core `K`, through `ana` at its axis `31`. -/
theorem K_layer2 {K : Noun} (h : slot? 31 K = some ana) : slot? 131071 K = some layer2 := by
  have h' : slot? 31 K = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 12
  simp only [show 2 ^ 12 * (31 + 1) - 1 = 131071 from rfl,
    show 2 ^ 12 * (1 + 1) - 1 = 8191 from rfl] at this
  rw [this]; exact ana_layer2

set_option maxHeartbeats 1000000 in
/-- `+pop`: the loop over the stack (`Ana.popGo`), which the gate runs by
kicking itself on the state it changed, on every stack `l` of the state.  It
reads `+git-g`, `+put:mi` and `+put:by`, `+del:by` of layer 2 through `ana` at
axis `31` of its context `K`. -/
theorem pop_gate (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (id : Ident) :
    ∀ (l : List Ident) (st : SkaState FinMap R), st.stk = l →
    nock (C ska_cg.pop.battery (C (C (identNoun id) (st.toNoun regsNoun)) K)) ska_cg.pop.battery
      = (Ana.popGo id l st).map (SkaState.toNoun regsNoun)
  | [], st, hs => by
    obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
    simp only at hs; subst hs
    nock_open ska_cg.pop.battery
    simp [nock_exec, SkaState.toNoun, listNoun, Ana.popGo]
  | top :: rest, st, hs => by
    obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
    simp only at hs; subst hs
    have hl2 := K_layer2 hK
    have hdo : nock (C by.del.battery (C (identNoun top) (C by.battery (C (Treap.toNoun A order) layer2))))
        by.del.battery = some (Treap.toNoun A (Treap.del order top)) :=
      del_gate layer2 gorIn_morIn_layer2 _ _ _ (FinMap.delF_toNoun A order top)
    have hdt : nock (C by.del.battery (C (identNoun top) (C by.battery
        (C (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) ticks) layer2))))
        by.del.battery = some (Treap.toNoun (fun p : Nat × Nat => C (A p.1) (A p.2)) (Treap.del ticks top)) :=
      del_gate layer2 gorIn_morIn_layer2 _ _ _ (FinMap.delF_toNoun _ ticks top)
    have hgg := git_g_pill g top
    have hpg : ∀ d' : FDatum FinMap, nock (C by.put.battery (C (C (identNoun top) d'.toNoun)
        (C by.battery (C (Treap.toNoun FDatum.toNoun g) layer2)))) by.put.battery
        = some (Treap.toNoun FDatum.toNoun (Treap.put g top d')) := fun d' =>
      put_gate layer2 gorIn_morIn_layer2 _ _ _ _ (FinMap.putF_toNoun FDatum.toNoun g top d')
    have hpm := fun d' => mi_put_pill done top d'
    have hsv : Sock.void.toNoun = A 0x64696f76 := rfl
    have hdun : Sock.dunno.toNoun = C (A 1) (A 0) := rfl
    have hsm : ∀ c n, (Sock.mk c n).toNoun = C c.toNoun n := fun _ _ => rfl
    generalize hd : Ana.gitG g top = d at hgg ⊢
    obtain ⟨dc, dn, dl, di, ds, dp, dm, da⟩ := d
    nock_open ska_cg.pop.battery
    cases dp with
    | void =>
      have h1 := hpg ⟨dc, dn, dl, di, ds, Sock.dunno, dm, da⟩
      have h2 := hpm ⟨dc, dn, dl, di, ds, Sock.dunno, dm, da⟩
      have ih := pop_gate regsNoun K hK id rest ⟨Treap.put g top ⟨dc, dn, dl, di, ds, Sock.dunno, dm, da⟩, putMi done top ⟨dc, dn, dl, di, ds, Sock.dunno, dm, da⟩,
        Treap.del order top, rest, next, moved, tick, Treap.del ticks top, regs, stats⟩ rfl
      simp only [SkaState.toNoun] at ih
      simp only [FDatum.toNoun, hdun, hsv] at h1 h2 hgg ih
      by_cases ht : top = id
      · subst ht
        simp [nock_exec, SkaState.toNoun, listNoun, Ana.popGo, hK, hl2, by_arm, by.del.arm_at, hdo, hdt,
          git_g.arm_at, git_g_arm, hgg, hd, by.put.arm_at, h1, mi.arm_at,
          mi_arm, mi.put.arm_at, mi_put_arm, h2, eqCode]
      · have h' : identNoun top ≠ identNoun id := fun e => ht ((identNoun_eq_iff _ _).1 e)
        simp [nock_exec, SkaState.toNoun, listNoun, Ana.popGo, hK, hl2, by_arm, by.del.arm_at, hdo, hdt,
          git_g.arm_at, git_g_arm, hgg, hd, by.put.arm_at, h1, mi.arm_at,
          mi_arm, mi.put.arm_at, mi_put_arm, h2, eqCode, ht, h', ih]
    | mk c n =>
      have h1 := hpg ⟨dc, dn, dl, di, ds, Sock.mk c n, dm, da⟩
      have h2 := hpm ⟨dc, dn, dl, di, ds, Sock.mk c n, dm, da⟩
      have ih := pop_gate regsNoun K hK id rest ⟨Treap.put g top ⟨dc, dn, dl, di, ds, Sock.mk c n, dm, da⟩, putMi done top ⟨dc, dn, dl, di, ds, Sock.mk c n, dm, da⟩,
        Treap.del order top, rest, next, moved, tick, Treap.del ticks top, regs, stats⟩ rfl
      simp only [SkaState.toNoun] at ih
      simp only [FDatum.toNoun, hsm] at h1 h2 hgg ih
      by_cases ht : top = id
      · subst ht
        simp [nock_exec, SkaState.toNoun, listNoun, Ana.popGo, hK, hl2, by_arm, by.del.arm_at, hdo, hdt,
          git_g.arm_at, git_g_arm, hgg, hd, by.put.arm_at, h1, mi.arm_at,
          mi_arm, mi.put.arm_at, mi_put_arm, h2, eqCode]
      · have h' : identNoun top ≠ identNoun id := fun e => ht ((identNoun_eq_iff _ _).1 e)
        simp [nock_exec, SkaState.toNoun, listNoun, Ana.popGo, hK, hl2, by_arm, by.del.arm_at, hdo, hdt,
          git_g.arm_at, git_g_arm, hgg, hd, by.put.arm_at, h1, mi.arm_at,
          mi_arm, mi.put.arm_at, mi_put_arm, h2, eqCode, ht, h', ih]

/-- `+pop` against `Ana.pop`. -/
theorem pop_gate' (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (id : Ident)
    (st : SkaState FinMap R) :
    nock (C ska_cg.pop.battery (C (C (identNoun id) (st.toNoun regsNoun)) K)) ska_cg.pop.battery
      = (Ana.pop id st).map (SkaState.toNoun regsNoun) :=
  pop_gate regsNoun K hK id st.stk st rfl

end Compiler
end Formalization
