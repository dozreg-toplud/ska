import lemmas.Compiler.OptLinkAlStartRef

/-!
# `+alias`: the start of a block's turn, assembled (phases 9 and 10 of the plan, README Gaps 13)

```hoon
  =^  info=(map @uvre info-reg)  gen
    ?~  pre  ...entry...
    :_  gen
    ...join, refinement...
  =/  imms=(jug * @uvre)  ...
  =.  info-local.gen  info
  =.  imms-local.gen  imms
```

* `alStartF K`: the formula of the walk from the `=^  info  gen` to the
  second `=.`, then `K`; `alWalk_start`: the walk's branch after the test of an
  unreachable block is `alStartF` of `[8 alBob X]`.
* `al_info`: **`alInfo`** on the Hoon's `pre`: `[info gen]` with `gen`
  unchanged and `info` the model's facts at the start on that list (the
  entry trap `al_ent`; the `+roll` `al_jnroll`; the `?^ t.pre` test; the
  refinement `al_jnref`).
* `al_start`: **the start of a block's turn**: from the subject after `pre`
  to the subject before `bob`, `gen` related by `GenRelL` to the model's
  `aliasStart g o (g.rev o)` (or `entryInfo`) and `aliasStartImms g (g.rev o)`,
  moved from the Hoon's order by `aliasStart_perm`, `aliasStartImms_perm`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The walk from `=^  info  gen` (`alInfo`) through `imms` (`alImms`) and the
two `=.` (`info-local` at axis `2014`, `imms-local` at `4030`), then `K`. -/
def alStartF (K : Noun) : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alInfo (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1))))
    (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C alImms (C (A 7) (C (C (A 10) (C (C (A 2014)
    (C (A 0) (A 6))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 4030) (C (A 0) (A 2))) (C (A 0) (A 1))))
    K)))))))))))))

/-- The walk, cut at `alStartF`: after `pre` and the test of an unreachable
block, `alStartF` of the rest from `bob` on. -/
theorem alWalk_start : ∃ X, alWalk = C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 247))))
    (C (C (C (A 0) (A 895)) (C (A 0) (A 12))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alPre
    (C (A 6) (C alUnT (C alUnB (alStartF (C (A 8) (C alBob X)))))))))))) := ⟨_, rfl⟩

/-- The empty map of facts. -/
theorem infoMapRel_nil : InfoMapRel (A 0) (fun _ => none) :=
  ⟨IsMap.nil, fun _ _ h => absurd h Get_atom, fun _ _ h => by cases h⟩

/-- **`alInfo`**: the facts at the start, on the Hoon's list `pre`; `gen`
is unchanged. -/
theorem al_info {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (hb : Opt.BrzInv g) (nargs : Nat)
    (BL REV T : Noun) (o : Nat) (preH : List Nat) {info : Opt.AInfo}
    (hi : (if preH = [] then some (Opt.entryInfo nargs) else Opt.aliasStart g o preH) = some info) :
    ∃ INFO, nock (C (listNoun A preH) (alWS GEN (A nargs) BL REV (C (A o) T))) alInfo = some (C INFO GEN) ∧
      InfoMapRel INFO info := by
  cases preH with
  | nil =>
    simp only [if_true, Option.some.injEq] at hi
    subst hi
    obtain ⟨I', h1, h2⟩ := al_ent (listNoun A []) GEN BL REV (C (A o) T) nargs nargs 0 (by omega) (A 0)
      (by simpa using infoMapRel_nil)
    refine ⟨I', ?_, h2⟩
    simp only [listNoun] at h1
    simp [nock_exec, alInfo, alEntry_cut, alEntryC, listNoun, h1]
  | cons p t =>
    rw [if_neg (List.cons_ne_nil p t)] at hi
    cases h0 : g.info p with
    | none => simp [Opt.aliasStart, h0] at hi
    | some i0 =>
      cases hf : t.foldlM (fun acc o1 => (g.info o1).map fun i1 => Opt.joinInfoA acc i1) i0 with
      | none => simp [Opt.aliasStart, h0, hf] at hi
      | some info0 =>
        obtain ⟨N0, hroll, hN0⟩ := al_jnroll hg (A nargs) BL REV (C (A o) T) p t i0 info0 h0 hf
        obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, hO, hI, hM, hR⟩ := hg
        cases t with
        | nil =>
          simp only [List.foldlM_nil, pure, Option.some.injEq] at hf
          subst hf
          obtain ⟨N, hN, hrel⟩ := al_jnref hb hN0 p o h0 hi OLD INFO IMMS LOC IMML R (flag g.folded) (A nargs) BL
            REV T
          refine ⟨N, ?_, hrel⟩
          simp only [listNoun] at hroll hN
          simp [nock_exec, alInfo, alJoin, listNoun, hroll, hN]
        | cons q t' =>
          simp only [Opt.aliasStart, h0, Option.bind_some, hf] at hi
          simp at hi
          subst hi
          refine ⟨N0, ?_, hN0⟩
          simp only [listNoun] at hroll
          simp [nock_exec, alInfo, alJoin, listNoun, hroll]

/-- **The start of a block's turn** (phases 9 and 10): on a `gen` noun
related to the model's state `g` (with `BrzInv`, `RevNodup` of `aliasM_inv`)
and the Hoon's `pre` (`al_pre`), the facts at the start, `imms` and the two
`=.` leave `gen` related by `GenRelL` to the facts and immediates that
`aliasBlock` binds, on `g.rev o`. -/
theorem al_start {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (hb : Opt.BrzInv g)
    (hn : Opt.RevNodup g.rev) (nargs : Nat) (BL REV T : Noun) (o : Nat) (preH : List Nat) (hd : preH.Nodup)
    (hm : ∀ x, x ∈ preH ↔ x ∈ g.rev o) {info : Opt.AInfo} {imms : Opt.AImms}
    (hi : (if g.rev o = [] then some (Opt.entryInfo nargs) else Opt.aliasStart g o (g.rev o)) = some info)
    (hj : Opt.aliasStartImms g (g.rev o) = some imms) (K : Noun) :
    ∃ GEN' INFO IMMS, GenRelL g info imms GEN' ∧ InfoMapRel INFO info ∧ ImmsRel IMMS imms ∧
      nock (C (listNoun A preH) (alWS GEN (A nargs) BL REV (C (A o) T))) (alStartF K) =
        nock (C IMMS (C INFO (C (listNoun A preH) (alWS GEN' (A nargs) BL REV (C (A o) T))))) K := by
  have hp := al_pre_perm hn hd hm
  obtain ⟨info', hi', he⟩ : ∃ info', (if preH = [] then some (Opt.entryInfo nargs) else Opt.aliasStart g o preH)
      = some info' ∧ Opt.AInfoEq info' info := by
    by_cases e : g.rev o = []
    · have e' : preH = [] := by rw [e] at hp; exact hp.eq_nil
      rw [if_pos e] at hi
      rw [if_pos e']
      exact ⟨info, hi, Opt.aInfoEq_equiv.refl _⟩
    · have e' : preH ≠ [] := fun h => e (by rw [h] at hp; exact hp.nil_eq.symm)
      rw [if_neg e] at hi
      rw [if_neg e']
      have h := Opt.aliasStart_perm g o hp
      rw [hi] at h
      cases h' : Opt.aliasStart g o preH with
      | none => rw [h'] at h; exact absurd h (by simp)
      | some a => rw [h'] at h; exact ⟨a, rfl, h⟩
  obtain ⟨imms', hj', hje⟩ : ∃ imms', Opt.aliasStartImms g preH = some imms' ∧ Opt.ImmsEq imms' imms := by
    have h := Opt.aliasStartImms_perm g hp
    rw [hj] at h
    cases h' : Opt.aliasStartImms g preH with
    | none => rw [h'] at h; exact absurd h (by simp)
    | some a => rw [h'] at h; exact ⟨a, rfl, h⟩
  obtain ⟨INFO, hI1, hIr⟩ := al_info hg hb nargs BL REV T o preH hi'
  obtain ⟨IMMS, hM1, hMr⟩ := al_imms hg (A nargs) BL REV (C (A o) T) INFO preH imms' hj'
  have hIr' := infoMapRel_of_aInfoEq hIr he
  have hMr' := immsRel_of_immsEq hMr hje
  obtain ⟨OLD, INFOS, IMMSS, LOC, IMML, R, rfl, hO, hIS, hMS, hR⟩ := hg
  refine ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFOS IMMSS INFO IMMS R (flag g.folded), INFO, IMMS,
    ⟨OLD, INFOS, IMMSS, INFO, IMMS, R, rfl, hO, hIS, hMS, hR, hIr', hMr'⟩, hIr', hMr', ?_⟩
  unfold alWS genN at hI1 hM1 ⊢
  simp [nock_exec, alStartF, hI1, hM1]

end Compiler
end Formalization
