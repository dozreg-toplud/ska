import lemmas.Ska.CompUnproxy

/-!
# Entering what `+to-straight` makes from blocks with proxies

`toStraightF_entryU`: the variant of `toStraight_entryR` for the whole of
`+to-straight` (`toStraightF`) on a run of inputs, with or without proxy
registers.  The program `c` the code is compared with holds the Gen blocks
unproxied (`unproxyBlob cond`) outside the entry label `o`; entering what
`+to-straight` makes does what the unproxied start block does in `c` from
registers that hold the subject as the input need asks.

* `hasProxies_none`: `hasProxies` false means an empty `cond`, so the
  renaming of the map path, `proxRen cond (hasProxies cond) ren`, is
  `ren ∘ unproxy cond` in both cases (`proxRen_eq`).
* The simulation `Sim` is taken with the map of the unproxied blocks, the
  start block at `0` (`HoonMap.put (HoonMap.del c.blocks o) 0 (unproxyBlob cond start)`),
  and the injective `renReg`; its `kept` comes from `renameBlocks_ren` with the
  rank of `rankDown_start`.

The input registers need not be outside the keys of `cond` here: the
statement is about the unproxied program.  That they are not keys is what a
caller needs to read the fill ops of the final pass, which read the inputs,
as unchanged by the unproxying.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- `hasProxies` false: no register is a key of `cond`. -/
theorem hasProxies_none [HoonMapKeys Map] {cond : Map (Nat × List Nat)} (h : hasProxies cond = false) :
    ∀ k, HoonMap.get cond k = Option.none := by
  intro k
  unfold hasProxies at h
  cases e : HoonMap.get cond k with
  | none => rfl
  | some v =>
    have hm := (HoonMapKeys.mem_keys cond k).mpr (by simp [e])
    cases hk : HoonMapKeys.keys cond with
    | nil => rw [hk] at hm; cases hm
    | cons _ _ => rw [hk] at h; simp at h

/-- **The renaming of the map path on a run of inputs is `ren ∘ unproxy`**,
with or without proxies. -/
theorem proxRen_eq [HoonMapKeys Map] (cond : Map (Nat × List Nat)) (ren : Nat → Nat) :
    proxRen cond (hasProxies cond) ren = ren ∘ unproxy cond := by
  funext r
  cases hp : hasProxies cond with
  | true => rfl
  | false =>
    simp only [proxRen, Bool.false_eq_true, if_false, Function.comp_apply, unproxy_none (hasProxies_none hp r)]

theorem finJumps_renFin (u : Nat → Nat) (f : Termin) : finJumps (renFin u f) = (finJumps f).map (renJmp u) := by
  cases f <;> rfl

/-- **Entering what `+to-straight` makes, with proxies.**  The program `c`
holds the Gen blocks `blocks` unproxied by `cond` outside the entry `o`;
entering `c'` on the arguments `split` takes out of `s` does what the
unproxied block `o` does in `c` from registers that hold `s` as `ned` asks. -/
theorem toStraightF_entryU [HoonMapKeys Map] {ρ : Nat → Nat} {cond : Map (Nat × List Nat)} {blocks : Map Blob}
    {c : Straight Map} {ned : Need} {o : Nat} {c' : Straight Map} (h : toStraightF cond blocks ned o = some c')
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true)
    (hdb : DownRk ρ blocks) (hd : DownRk ρ c.blocks)
    (hag : ∀ k, k ≠ o → HoonMap.get c.blocks k = (HoonMap.get blocks k).map (unproxyBlob cond)) :
    c'.need = needToOrd ned ∧ ∃ start, HoonMap.get blocks o = some start ∧
      ∀ (lib : Lib) {σ : Type} (O : Oracle σ) (st : σ) (s : Noun) (args : List Noun) (t : Trace) (gul : Noun),
        SkaModel.split c'.need s = some args → ∃ R : Map (Option Noun), HoldsN ned R s ∧
          execEntry lib O st c' args t gul = execBlob lib O c gul st R t (unproxyBlob cond start) [] := by
  rw [toStraightF_run cond blocks o hrun, proxRen_eq] at h
  cases hst : HoonMap.get blocks o with
  | none => rw [hst] at h; cases h
  | some start =>
    rw [hst, Option.bind_some] at h
    obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨rfl, start, rfl, ?_⟩
    intro lib σ O st s args t gul hsp
    have ho1 : 1 ≤ o := (hdb o start hst).1
    generalize hins_def : flattenNeed ned = ins at hrun hnew
    generalize hr0 : ins.headD 0 = r0 at hrun hnew
    have hins : ins = List.range' r0 ins.length := by
      have := (isRun_iff ins r0 0).mp hrun; simpa using this
    obtain ⟨hlen, hholds⟩ := holds_of_split ned r0 s args (regsFrom r0 args (HoonMap.empty : Map (Option Noun)))
      (hins_def ▸ hins) hsp
    rw [hins_def] at hlen
    refine ⟨regsFrom r0 args (HoonMap.empty : Map (Option Noun)), hholds fun i hi => ?_, ?_⟩
    · simp only [SkaModel.read, get_regsFrom, HoonMap.get_empty]
      rw [if_pos (by omega), Nat.add_sub_cancel_left]; cases args[i]? <;> rfl
    have hren := renRel_entry (Map := Map) r0 args
    rw [hlen] at hren
    have hrk := rankDown_start hdb hst
    generalize hbs : HoonMap.put (HoonMap.del blocks o) 0 start = bs at hnew hrk
    -- the map of the unproxied blocks, with the start block at `0`
    generalize hbs' : HoonMap.put (HoonMap.del c.blocks o) 0 (unproxyBlob cond start) = bs'
    have hb : ∀ k, HoonMap.get bs' k = (HoonMap.get bs k).map (renBlob (unproxy cond)) := by
      intro k
      rw [← hbs', ← hbs]
      simp only [HoonMap.get_put, HoonMap.get_del]
      by_cases k0 : k = 0
      · simp [k0, unproxyBlob]
      · by_cases ko : k = o
        · simp [ko, show o ≠ 0 by omega]
        · simp only [k0, ko, if_false, hag k ko]; rfl
    have K := renameBlocks_ren hrk hb hnew
    have hsim : Sim c ⟨needToOrd ned, countArgs (needToOrd ned), new⟩ bs' (renReg r0 ins.length) o ρ := by
      refine ⟨renReg_inj _ _, hd, fun k h0 hk => ?_, ?_, fun k b hb' hk hby => ?_⟩
      · simp [← hbs', HoonMap.get_put, HoonMap.get_del, h0, hk]
      · simp [← hbs', HoonMap.get_put, HoonMap.get_del, show o ≠ 0 by omega]
      · have hk0 : k ≠ 0 := by have := (hd k b hb').1; omega
        have hbs1 : HoonMap.get bs' k = some b := by
          simp [← hbs', HoonMap.get_put, HoonMap.get_del, hk0, hk, hb']
        obtain ⟨kb, hkb, hget⟩ := K k b hbs1
        simp only [keepBlock, hk0, hby, ne_eq, not_false_eq_true, and_false, if_false] at hkb
        obtain ⟨fin', hf, rfl⟩ := Option.map_eq_some_iff.mp hkb
        exact ⟨fin', hf, hget⟩
    have hbs0 : HoonMap.get bs' 0 = some (unproxyBlob cond start) := by simp [← hbs', HoonMap.get_put]
    obtain ⟨kb, hkb, hget⟩ := K 0 _ hbs0
    simp only [keepBlock, ne_eq, not_true_eq_false, false_and, if_false] at hkb
    obtain ⟨fin', hf, rfl⟩ := Option.map_eq_some_iff.mp hkb
    simp only [execEntry, hget, Option.bind_some]
    refine (sim_block hsim lib O gul (ρ o) _ (fun j hj => ?_) fin' hf st _ _ t [] hren).symm
    simp only [unproxyBlob, renBlob, finJumps_renFin, List.mem_map] at hj
    obtain ⟨j0, hj0, rfl⟩ := hj
    exact (hdb o start hst).2 j0 hj0

end Comp
end SkaModel
end Formalization
