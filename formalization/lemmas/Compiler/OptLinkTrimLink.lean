import lemmas.Compiler.OptLinkTrimGate
import lemmas.Compiler.OptLinkOpt

/-!
# `+trim-trace-hints` linked: the whole gate

* `get_hoonMap`: the pairs of the noun of a `TreapMap mugF` are its keys as
  atoms with their values' nouns.
* `get_trimRun`: the model's `trimRun` maps each block by `dropB`.
* `tr_gate`: **where `trimTraceHints` returns `bt`, the gate of
  `+trim-trace-hints` on the nouns of the blocks, of `topo` and of `rev`
  returns the noun of `bt`**: the outer trap (`tr_otrap`), `opened`
  (`tr_opened`), the `+run:by` (`run_by_P` with `tr_rngate`), and the map it
  returns is the noun of `bt` by `isMap_ext`.
* `trimLink`: `TrimLink P` for every `P` whose `trim` is `trimTraceHints`
  (with `noLti_trim`: the pass keeps the terminators).
* `oo_gate_trim`, `opt_gate_trim`: `oo_gate` and `opt_gate` with `TrimLink`
  discharged.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The pairs of the noun of a treap -/

theorem tr_key_atom {ν : Type} (g : ν → Noun) : ∀ (t : Tr ν) (kn w : Noun), Get (t.toNoun g) kn w → ∃ o, kn = A o
  | .nil, kn, w, h => absurd h Get_atom
  | .node k v l r, kn, w, h => by
    simp only [Tr.toNoun] at h
    rcases Get_node.1 h with ⟨e, -⟩ | h | h
    · exact ⟨k, e⟩
    · exact tr_key_atom g l kn w h
    · exact tr_key_atom g r kn w h

/-- The pairs of the noun of a treap: its keys as atoms with the nouns of
their values. -/
theorem get_hoonMap {ν : Type} (g : ν → Noun) (m : TreapMap mugF ν) (kn w : Noun) :
    Get (HoonMap.toNoun g m) kn w ↔ ∃ o x, kn = A o ∧ HoonMap.get m o = some x ∧ w = g x := by
  have hm := isMap_hoonMap g m
  constructor
  · intro h
    obtain ⟨o, rfl⟩ := tr_key_atom g m.1 kn w (by rw [hoonMap_toNoun] at h; exact h)
    have hs := getF_some hm h
    rw [getF_hoonMap] at hs
    cases e : HoonMap.get m o with
    | none => rw [e] at hs; simp [unitNoun] at hs
    | some x =>
      rw [e] at hs
      simp only [unitNoun, Option.some.injEq, Noun.cell.injEq, true_and] at hs
      exact ⟨o, x, rfl, e, hs.symm⟩
  · rintro ⟨o, x, rfl, hx, rfl⟩
    have hs := getF_hoonMap g m o
    rw [hx] at hs
    by_cases hv : ∃ v, Get (HoonMap.toNoun g m) (A o) v
    · obtain ⟨v, hv⟩ := hv
      have h2 := getF_some hm hv
      rw [hs] at h2
      simp only [unitNoun, Option.some.injEq, Noun.cell.injEq, true_and] at h2
      rw [h2]; exact hv
    · have h2 := getF_none hm (fun v h => hv ⟨v, h⟩)
      rw [hs] at h2
      simp [unitNoun] at h2

/-! ## The model's `+run:by` -/

theorem get_trimRun_gen (bl : TreapMap mugF Blob) (uns : Opt.Uns) (opened : List Opt.TKey) (o : Nat)
    (F : TreapMap mugF Blob → Nat → TreapMap mugF Blob)
    (hF : ∀ acc o' b, HoonMap.get bl o' = some b → F acc o' = HoonMap.put acc o' (dropB uns opened b)) :
    ∀ (L : List Nat) (acc : TreapMap mugF Blob), (∀ o ∈ L, (HoonMap.get bl o).isSome) →
    HoonMap.get (L.foldl F acc) o = if o ∈ L then (HoonMap.get bl o).map (dropB uns opened) else HoonMap.get acc o := by
  intro L
  induction L with
  | nil => intro acc _; simp
  | cons o' L ih =>
    intro acc hL
    simp only [List.foldl_cons]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hL o' (by simp))
    rw [ih _ (fun x hx => hL x (by simp [hx])), hF acc o' b hb, HoonMap.get_put]
    by_cases h1 : o ∈ L
    · simp [h1]
    · by_cases h2 : o = o'
      · subst h2; simp [h1, hb]
      · simp [h1, h2]

/-- The model's `+run:by` maps each block by `dropB`. -/
theorem get_trimRun (bl : TreapMap mugF Blob) (uns : Opt.Uns) (opened : List Opt.TKey) (o : Nat) :
    HoonMap.get (Opt.trimRun bl uns opened) o = (HoonMap.get bl o).map (dropB uns opened) := by
  unfold Opt.trimRun
  rw [get_trimRun_gen bl uns opened o _ (fun acc o' b hb => by simp only [hb]; rfl) _ bl
    (fun x hx => (Opt.MapKeys.mem_keys bl x).1 hx)]
  by_cases h : o ∈ Opt.MapKeys.keys bl
  · rw [if_pos h]
  · rw [if_neg h]
    have : HoonMap.get bl o = none := by
      cases e : HoonMap.get bl o with
      | none => rfl
      | some b => exact absurd ((Opt.MapKeys.mem_keys bl o).2 (by simp [e])) h
    rw [this]; rfl

/-- The pass keeps every terminator, so it keeps `NoLti`. -/
theorem noLti_trim {bl bt : TreapMap mugF Blob} {topo : List Nat} {rev : TreapMap mugF (List Nat)}
    (h : Opt.trimTraceHints bl topo rev = some bt) (hl : NoLti bl) : NoLti bt := by
  unfold Opt.trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  intro o b' hb'
  rw [get_trimRun] at hb'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
  exact hl o b hb

/-! ## The gate -/

/-- **`+trim-trace-hints`**: where `trimTraceHints` returns `bt`, the gate on
the nouns of the blocks, of `topo` and of `rev` returns the noun of `bt`. -/
theorem tr_gate (bl : TreapMap mugF Blob) (topo : List Nat) (rev : TreapMap mugF (List Nat))
    (bt : TreapMap mugF Blob) (h : Opt.trimTraceHints bl topo rev = some bt) :
    nock (C trBody (C (C (HoonMap.toNoun Blob.toNoun bl) (C (listNoun A topo) (jarN rev))) optC)) trBody
      = some (HoonMap.toNoun Blob.toNoun bt) := by
  unfold Opt.trimTraceHints at h
  obtain ⟨uns, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  have hU := tr_otrap bl rev (trG (HoonMap.toNoun Blob.toNoun bl) (listNoun A topo) (jarN rev)) topo
    HoonMap.empty (fun _ => false) (A 0) (A 0) uns unsRel_nil outRel_nil hw
  obtain ⟨U, hU1, hU⟩ := hU
  obtain ⟨OPD, hO1, hO⟩ := tr_opened bl U (trG (HoonMap.toNoun Blob.toNoun bl) (listNoun A topo) (jarN rev))
    (listNoun A topo) (jarN rev)
  obtain ⟨OUT, hR1, hRm, hRg⟩ := run_by_P (mug := mugF) layer2 trRnGate trRnBunt
    (C OPD (trS2 U (trG (HoonMap.toNoun Blob.toNoun bl) (listNoun A topo) (jarN rev))
      (HoonMap.toNoun Blob.toNoun bl) (listNoun A topo) (jarN rev)))
    (fun x => ∃ b, x = Blob.toNoun b)
    (fun x => Blob.toNoun (dropB uns (Opt.trimOpened bl) (OptDec.blobDec x)))
    (by
      rintro x ⟨b, rfl⟩
      rw [OptDec.blobDec_toNoun]
      exact tr_rngate b U OPD uns _ hU hO _ _ _ _)
    (isMap_hoonMap Blob.toNoun bl)
    (fun k v hv => by
      obtain ⟨o, x, -, -, rfl⟩ := (get_hoonMap Blob.toNoun bl k v).1 hv
      exact ⟨x, rfl⟩)
  have hEq : OUT = HoonMap.toNoun Blob.toNoun (Opt.trimRun bl uns (Opt.trimOpened bl)) := by
    refine isMap_ext hRm (isMap_hoonMap _ _) (fun k w => ?_)
    rw [hRg, get_hoonMap]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨o, b, rfl, hb, rfl⟩ := (get_hoonMap Blob.toNoun bl k v).1 hv
      refine ⟨o, dropB uns (Opt.trimOpened bl) b, rfl, ?_, ?_⟩
      · rw [get_trimRun, hb]; rfl
      · rw [OptDec.blobDec_toNoun]
    · rintro ⟨o, x, rfl, hx, rfl⟩
      rw [get_trimRun] at hx
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hx
      refine ⟨Blob.toNoun b, (get_hoonMap Blob.toNoun bl _ _).2 ⟨o, b, rfl, hb, rfl⟩, ?_⟩
      rw [OptDec.blobDec_toNoun]
  rw [← hEq]
  have hL := optC_layer2
  unfold trOT trG at hU1
  unfold trS2 trG at hO1 hR1
  conv => lhs; arg 2; unfold trBody
  generalize optC = OC at hL hU1 hO1 hR1
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hU1 hO1 hR1 ⊢
  simp [nock_exec, trRBunt, hU1, hL, by.arm_at, by_arm, by.rep.arm_at, rep_arm, hO1, by.run.arm_at, by_run_arm,
    hR1]

/-- **`TrimLink` holds** for every `P` whose `trim` is `trimTraceHints`. -/
theorem trimLink (P : Opt.Passes (TreapMap mugF))
    (hP : ∀ bl topo rev, P.trim bl topo rev = Opt.trimTraceHints bl topo rev) : TrimLink P := by
  intro bl topo rev bt hl h
  rw [hP] at h
  exact ⟨noLti_trim h hl, by rw [trimBody_eq]; exact tr_gate bl topo rev bt h⟩

/-- **`+optimize-once`** with the model's `+trim-trace-hints`: only `+alias`
is a hypothesis. -/
theorem oo_gate_trim (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P)
    (hP : ∀ bl topo rev, P.trim bl topo rev = Opt.trimTraceHints bl topo rev) (fuel : Nat)
    (s : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (r : Bool × Straight (TreapMap mugF))
    (h : Opt.optimizeOnce fuel P s = some r) :
    nock (C ooBody (C s.toNoun optC)) ooBody = some (C (flag r.1) r.2.toNoun) :=
  oo_gate P hA (trimLink P hP) fuel s hl r h

/-- **`+optimize`** with the model's `+trim-trace-hints`: `+alias` and
`+switch-chains` are the hypotheses. -/
theorem opt_gate_trim (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P)
    (hP : ∀ bl topo rev, P.trim bl topo rev = Opt.trimTraceHints bl topo rev) (hS : SwitchLink P)
    (fuel : Nat) (s s' : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (h : Opt.optimizeF fuel P s = some s') :
    nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun :=
  opt_gate P hA (trimLink P hP) hS fuel s s' hl h

end Compiler
end Formalization
