import lemmas.Compiler.CompMember

/-!
# The gate `member` of `+compile-scc-in` against the model

The parts of `CompMember.lean` put together with the links of the calls:
`+run` (`comp_run_entry`, on a pure nomm with no `%6` whose `%10` axes are
not `0`), `+collapse-shape` (`cs_gate`, given `hsc` on `+shape-collapse`),
`+bake-need` (`fin_bak`, under `NoBake`), `+need-to-ordered` (`nta_gate`),
`+sure-of` (`so_gate`) and the gate `finish` (`fin_gate_finishLF`).

* `mem_to_finish`: the gate on its final pass, from its sample to the push of
  `finish`: the subject there is `finCtx` with the tuple of the pass, the
  state of `+need-ord-alloc-regs`, and the rest `memS3 ..` whose cache has the
  new `sure.cache`; `mem_rest_slots` gives the four slots that `finish` reads.
* `mem_gate`: with `map-local` and `top` empty, the gate returns
  `[chg (~(put by ~) b straight) cache]` with `straight` the noun of
  `finishLF nm ord cape (fun n => (n, []))`, and crashes when it is `none`.

The hypotheses that stay: `+inlined` returns `[nm cache]` (`hinl`), the run
succeeds (`hrunL`, the case of `fin_after_cs`) with a fork-free `laz`
(`hlaz`), `+shape-collapse` gives `ord` (`hsc`), `args.then` is `~` and
`+need-ord-alloc-regs` succeeds (`hargs`, `hnoar`, without which the gate
crashes in `+collapse-shape`), nothing is baked (`hb`), `+sure-of` succeeds
(`hsur`: `sureOf` is `none` only on an axis `0` in `lok`), and `sure.cache`
is a map where `+get:by` finds `was` and `+put:by` gives `SURE'` (`hwas`,
`hw`, `hput`, nouns given by `getF` and `putF`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `mode.gen` set to `%run` on the entry state, where it is `%run` already. -/
theorem mem_mode_noop (x : GenRest) (S : Noun) :
    edit? 46 (A 0x6e7572) (C (genNoun (genEntry : Gen (TreapMap mugF)) x) S)
      = some (C (genNoun (genEntry : Gen (TreapMap mugF)) x) S) := by
  simp [genNoun, genEntry, cgModeNoun, nock_exec]

theorem gen0_eq : (gen0 : Gen (TreapMap mugF)) = genEntry := rfl

/-- The subject at the push of `finish` on the final pass. -/
def memFC (keep : Bool) (WAS SUR NN LZ NF : Noun) (o : Nat) (G2 NM DCTX B ML TOP CA CTX : Noun) : Noun :=
  finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS NN LZ NF NF (A 0) o SUR G2
    (memS3 NM DCTX (memS0 B (loob keep) ML TOP CA CTX))

/-- **The gate `member` on its final pass, up to the push of `finish`.**
From the sample `[b %done keep map-local top cache]` (with `b` the noun of a
bell whose `less` is `[cape data]`) in the context `memCtx`, the gate runs
`+inlined`, the run, `+collapse-shape`, `+bake-need`, `+sure-of`, the
updates of `sure.cache`, and pushes `finish` on the subject `memFC`. -/
theorem mem_to_finish (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = nock (C (C finBody (C (A 0) (memFC keep WAS sur.toNoun (needToOrd nedF).toNoun nex.laz.toNoun nedF.toNoun
            nex.th.there (genNoun g2 (cuRest (cacheN C1 C2 C3 C4 SURE))) nm.toNoun
            (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML TOP
            (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))))
          (memFC keep WAS sur.toNoun (needToOrd nedF).toNoun nex.laz.toNoun nedF.toNoun
            nex.th.there (genNoun g2 (cuRest (cacheN C1 C2 C3 C4 SURE))) nm.toNoun
            (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML TOP
            (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memProd := by
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some compK := rfl
  have hcode : slot? 52 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some CODE := by
    simp [memDCtx, nock_exec]
  rw [mem_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, rfl⟩ hinl, mem_r3, mem_res]
  -- the run
  have hrunN := comp_run_entry h7 hcode nm hpu h6 ht (cuRest (cacheN C1 C2 C3 C4 SURE)) (A 1) (A 0)
    (cu_entry_nosoft _)
  rw [← gen0_eq, show (CGoal.toL CGoal.done : CGoalL CSet) = CGoalL.done from rfl, hrunL] at hrunN
  rw [show (CGoalL.done : CGoalL CSet) = CGoal.toL CGoal.done from rfl, cu_done_noun, gen0_eq] at hrunN
  simp only [listNoun, Option.map_some, compCore] at hrunN
  -- +collapse-shape
  have hcsN := cs_gate _ h7 (cuRest (cacheN C1 C2 C3 C4 SURE)) g1 nex cape.toNoun ord hsc
  simp only [hargs, ne_eq, not_true_eq_false, if_false, hnoar, Option.map_some, compCore] at hcsN
  have hlz : nex.laz.toNoun = C (C s.ned.toNoun (HoonSet.toNoun s.lok)) (C (A 0) (A 0)) := by
    rw [hlaz, Lazy.toNoun_ofSure]; rfl
  rw [hlz] at hcsN
  -- the calls of K
  have hbn := fin_bak ord g1 g2 nedF (Sock.mk cape DATA) hnoar hb
  simp only [Sock.toNoun] at hbn
  have hn1 := nta_gate compK s.ned
  have hso := so_gate (needToOrd s.ned) s.lok cape
  rw [hsur, Option.map_some] at hso
  have hn2 := nta_gate compK nedF
  rw [mem_final (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN) (hbn := hbn) (hn1 := hn1) (hso := hso)
    (hn2 := hn2)]
  simp only [Option.bind_some]
  rw [mem_after (keep := keep) (hG2 := cu_gen_cache _ _) (hwas := hwas) (hw := hw) (hput := hput)]
  rw [hlz]
  rfl

/-! ## The rest of the subject at `finish` -/

/-- **The four slots of the rest that `finish` reads**: the door `comp` at
`6` (on `cuBunt` and the context `memDCtx`, whose axis `7` is `K`), `done`
at `14`, `cape.less.b` at `496`, `layer2` at `0x3ffffff`. -/
theorem mem_rest_slots (NM SCC LONG JH ML TOP CAPE DATA FOL KEEP CA DN KIDS ML0 CB CACHE0 : Noun) :
    slot? 6 (memS3 NM (memDCtx SCC LONG JH ML TOP (C (C CAPE DATA) FOL))
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))
      = some (C comp.door (C cuBunt (memDCtx SCC LONG JH ML TOP (C (C CAPE DATA) FOL)))) ∧
    slot? 14 (memS3 NM (memDCtx SCC LONG JH ML TOP (C (C CAPE DATA) FOL))
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = some (A 0) ∧
    slot? 496 (memS3 NM (memDCtx SCC LONG JH ML TOP (C (C CAPE DATA) FOL))
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = some CAPE ∧
    slot? 0x3ffffff (memS3 NM (memDCtx SCC LONG JH ML TOP (C (C CAPE DATA) FOL))
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = some layer2 := by
  have hL := compK_layer2
  unfold memS3 memS0 memSam memCtx
  generalize compK = KC at hL
  simp [nock_exec, hL]

/-- On a pure nomm with no `%6`, the run from `gen0` leaves `cond` empty. -/
theorem mem_cond_frag (nm : Nomm) (hpu : nm.pure = true) (h6 : noSix nm = true) (nex : NextL CSet)
    (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    ∀ k, HoonMap.get g1.cond k = Option.none := by
  rw [show (CGoalL.done : CGoalL CSet) = CGoal.toL CGoal.done from rfl, runL_toL nm hpu h6] at hrunL
  cases e : run (S := CSet) (Map := TreapMap mugF) nm CGoal.done gen0 with
  | none => simp [e, Functor.map, StateT.map] at hrunL
  | some q =>
    obtain ⟨nex0, g0⟩ := q
    simp [e, Functor.map, StateT.map] at hrunL
    obtain ⟨rfl, rfl⟩ := hrunL
    have hc1 : g0.cond = (gen0 : Gen (TreapMap mugF)).cond := (kc_run nm CGoal.done).keep _ _ _ e
    intro k
    rw [hc1]
    exact gen0_cond_none k

/-- On a pure nomm with no `%6`, the run's `laz` is fork-free. -/
theorem mem_laz_frag (nm : Nomm) (hpu : nm.pure = true) (h6 : noSix nm = true) (nex : NextL CSet)
    (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    ∃ s : Sure CSet, nex.laz = Lazy.ofSure s := by
  rw [show (CGoalL.done : CGoalL CSet) = CGoal.toL CGoal.done from rfl, runL_toL nm hpu h6] at hrunL
  cases e : run (S := CSet) (Map := TreapMap mugF) nm CGoal.done gen0 with
  | none => simp [e, Functor.map, StateT.map] at hrunL
  | some q =>
    obtain ⟨nex0, g0⟩ := q
    simp [e, Functor.map, StateT.map] at hrunL
    obtain ⟨rfl, rfl⟩ := hrunL
    exact ⟨nex0.laz, rfl⟩

/-! ## The gate -/

/-- **The gate `member` on the final pass of an SCC of one bell** (`mode`
`%done`, `map-local` and `top` empty): it returns `[chg (~(put by ~) b
straight) cache]`, where `straight` is the noun of `finishLF nm ord cape (fun
n => (n, []))`, `cache` is the cache of `+inlined` with `sure.cache` put at
`b` (`SURE'`), and `chg` is `memChgN` of `moved` and `need-new`; it crashes
when `finishLF` is `none`.  The hypotheses are those of `mem_to_finish`;
`cond` empty and the fork-free `laz` come from the fragment
(`mem_cond_frag`, `mem_laz_frag`). -/
theorem mem_gate (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) (A 0) (A 0) CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = (finishLF (S := CSet) (Map := TreapMap mugF) nm ord cape (fun n => (n, []))).map fun st =>
          C (memChgN (memMovedN keep WAS sur.toNoun) (needToOrd nedF).toNoun)
            (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN C1 C2 C3 C4 SURE')) := by
  rw [mem_to_finish cape DATA FOL keep (A 0) (A 0) CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm C1 C2 C3 C4 SURE
    hinl hpu h6 ht nex g1 hrunL s hlaz ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput]
  have hmv : memMovedN keep WAS sur.toNoun = A 0 ∨ memMovedN keep WAS sur.toNoun = A 1 := by
    unfold memMovedN; split <;> simp
  have hnn : ∃ p q, (needToOrd nedF).toNoun = C p q := nord_cell _
  unfold memFC
  rw [mem_prod_new (hmv := hmv) (hnn := hnn)]
  obtain ⟨hs6, hs14, hs496, hl2⟩ := mem_rest_slots nm.toNoun SCC (C CODE LSR) JH (A 0) (A 0) cape.toNoun DATA FOL
    (loob keep) (cacheN C1 C2 C3 C4 SURE') DN KIDS ML0 CB CACHE0
  have hf := fin_gate_finishLF (rfl : slot? 7 (memDCtx SCC (C CODE LSR) JH (A 0) (A 0) (C (C cape.toNoun DATA) FOL))
      = some compK) (memMovedN keep WAS sur.toNoun) (memSurKN keep WAS sur.toNoun) WAS (needToOrd nedF).toNoun
    sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 (cuRest (cacheN C1 C2 C3 C4 SURE)) rfl nm ord nex g1 g2
    nedF s hrunL hargs hlaz (mem_cond_frag nm hpu h6 nex g1 hrunL) hnoar
  rw [hf, Option.map_map]
  rfl

end Compiler
end Formalization
