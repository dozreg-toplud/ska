import lemmas.Compiler.CompInlinedL5

/-!
# `InlCoh` on the model: the cache of `+inlined` across `%full` and `%jets` (track Q)

`InlCoh` (`CompInlinedL3.lean`) asks that every entry `b ↦ v` of
`inl.cache` is `inlinedM` of `b` at some fuel.  Here the clause on the
model's maps (`InlCohM`: `inl` a `FinMap Bell Nomm`) and what the two pokes
that touch the table or `hot` do to it:

* `inlWalk_congr`, **`inlinedM_congr`**: `inlinedM code calls hot single f b`
  reads `code`, `calls c c`, `hot c`, `single c` only at the bells `c` the
  walk can enter from `b` (a predicate `P` that holds of `b` and passes from
  a bell to the info bells of its nomm);
* **`inlinedM_addsTo`** (`%full`): the table grows (`AddsTo T nc T'`); from
  an old key of a closed table the walk enters only info bells, which are
  old keys (`CodeClosed`), whose nomm `AddsTo.old` keeps; so `inlinedM` of
  an old key is the same on the grown table when `calls`, `hot`, `single`
  are the same on old keys;
* `callsOf_addsTo`: the table's `calls` (`CallsOf`) is the same on old keys;
* `singleScc_addsTo`: `SingleScc` on the grown table from `SingleScc` on the
  old one (old SCCs are kept, `inScc_old`) and the new keys;
* **`inlCohM_addsTo`**: `%full` keeps `InlCohM` (no new entry: the
  `+inlined` calls of the poke itself are track K's);
* `inlCoh_of_M`: `InlCohM` gives `InlCoh` on the cache noun with `inl`'s
  noun at its fourth place; `nmOf_realOf`: `nmOf T` is `realOf T`, the code
  of `InlPill`;
* `%jets` (`desk/lib/nock-compilation.hoon`, `++  poke`, `%jets`: `inl.cache`
  loses the bells of `hot-stale`): `JetsStale T hot hot' stale` says that a
  bell that reaches (`Reach`, track P) a bell whose `hot` changed is stale;
  **`inlCohM_jets`**: deleting the stale entries keeps `InlCohM` with the new
  `hot` (the table, `calls` and `single` are not changed by `%jets`).
  What the pill must give for `JetsStale` (open): `hot c` is "the ring
  `call.cole c` has a driver"; `hot-stale` starts from the bells `back.cole`
  lists under a ring whose driver changed (`hot-diff`) and the newly rung
  bells with a driver, then closes under callers (`reverse-bell-graph` of
  `calls`).  `ColeCoh` (`PokeLinkGood5.lean`: `call.cole c = r` iff `c` is in
  `back.cole r`) turns "the ring of `c` changed its driver" into "`c` is in
  `back.cole` of a ring of `hot-diff`", so with `ColeCoh` every bell whose
  `hot` changed is in the start set, and every caller of it is in `stale`.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel SkaModel.Glue SkaModel.Ana SkaModel.Bake SkaModel.PokeM

set_option linter.unusedVariables false

/-! ## The walk reads the bells it can enter only -/

/-- **The walk is congruent** in `calls c c`, `hot c`, `single c`, `go c`
at the info bells `c` of the nomm. -/
theorem inlWalk_congr {calls calls' : Bell → Bell → Bool} {hot hot' single single' : Bell → Bool}
    {go go' : Bell → Option Nomm} :
    ∀ nm : Nomm, (∀ c ∈ nommInfos nm, calls c c = calls' c c ∧ hot c = hot' c ∧ single c = single' c ∧
      go c = go' c) → inlWalk calls hot single go nm = inlWalk calls' hot' single' go' nm := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro h
    have ep := ihp fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep, eq]
  | n0 a => intro _; rfl
  | n1 k => intro _; rfl
  | n2 p q info ihp ihq =>
    intro h
    have ep := ihp fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    cases info with
    | none => simp only [inlWalk, ep, eq]
    | some ck =>
      obtain ⟨c, k⟩ := ck
      obtain ⟨h1, h2, h3, h4⟩ := h c (by simp [nommInfos])
      have hok : inlOK calls hot single c k q = inlOK calls' hot' single' c k q := by
        simp only [inlOK, h1, h2, h3]
      simp only [inlWalk, ep, eq, hok, h4]
  | n3 p ih =>
    intro h
    have ep := ih fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep]
  | n4 p ih =>
    intro h
    have ep := ih fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep]
  | n5 p q ihp ihq =>
    intro h
    have ep := ihp fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep, eq]
  | n6 p q r ihp ihq ihr =>
    intro h
    have ep := ihp fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    have er := ihr fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep, eq, er]
  | n7 p q ihp ihq =>
    intro h
    have ep := ihp fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep, eq]
  | n10 x v q ihv ihq =>
    intro h
    have ev := ihv fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ev, eq]
  | n11s t q body ih =>
    intro h
    have eq := ih fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, eq]
  | n11d t x q body ihh ihq =>
    intro h
    have eh := ihh fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, eh, eq]
  | n12 p q ihp ihq =>
    intro h
    have ep := ihp fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep, eq]
  | mean p x q body k ihp ihq =>
    intro h
    have ep := ihp fun c hc => h c (by simp [nommInfos, hc])
    have eq := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp only [inlWalk, ep, eq]

/-- **`inlinedM` reads only the bells its walk can enter**: on a predicate
`P` of `b` that passes from a bell with a nomm to the info bells of the
nomm, two models that agree on `P` (the nomm, `calls c c`, `hot`, `single`)
give the same result at every fuel. -/
theorem inlinedM_congr {code code' : Bell → Option Nomm} {calls calls' : Bell → Bell → Bool}
    {hot hot' single single' : Bell → Bool} (P : Bell → Prop)
    (hP : ∀ c nm, P c → code c = some nm → ∀ c' ∈ nommInfos nm, P c')
    (hcode : ∀ c, P c → code c = code' c) (hcalls : ∀ c, P c → calls c c = calls' c c)
    (hhot : ∀ c, P c → hot c = hot' c) (hsing : ∀ c, P c → single c = single' c) :
    ∀ f b, P b → inlinedM code calls hot single f b = inlinedM code' calls' hot' single' f b := by
  intro f
  induction f with
  | zero => intro b _; rfl
  | succ n ih =>
    intro b hb
    simp only [inlinedM]
    rw [← hcode b hb]
    cases e : code b with
    | none => rfl
    | some nm =>
      simp only [Option.bind_some]
      exact inlWalk_congr nm fun c hc => ⟨hcalls c (hP b nm hb e c hc), hhot c (hP b nm hb e c hc),
        hsing c (hP b nm hb e c hc), ih c (hP b nm hb e c hc)⟩

/-! ## `%full`: the table grows -/

section Full

variable {T nc T' : FinMap Bell (VarEntry FinMap)}

/-- **`inlinedM` of an old key is the same on the grown table**, when
`calls c c`, `hot`, `single` are the same on old keys. -/
theorem inlinedM_addsTo (hA : AddsTo T nc T') (hC : CodeClosed T)
    {calls calls' : Bell → Bell → Bool} {hot hot' single single' : Bell → Bool}
    (hcalls : ∀ c, (∃ e, FinMap.get T c = some e) → calls c c = calls' c c)
    (hhot : ∀ c, (∃ e, FinMap.get T c = some e) → hot c = hot' c)
    (hsing : ∀ c, (∃ e, FinMap.get T c = some e) → single c = single' c)
    {b : Bell} (hb : ∃ e, FinMap.get T b = some e) (f : Nat) :
    inlinedM (nmOf T) calls hot single f b = inlinedM (nmOf T') calls' hot' single' f b := by
  refine inlinedM_congr (fun c => ∃ e, FinMap.get T c = some e) (fun c nm hc hn c' hc' => ?_)
    (fun c hc => ?_) hcalls hhot hsing f b hb
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hn
    exact (hC c e he).2 c' hc'
  · obtain ⟨e, he⟩ := hc
    simp [nmOf, he, hA.old c e he]

/-- **The table's `calls` is the same on old keys** (`CallsOf` before and
after the growth). -/
theorem callsOf_addsTo (hA : AddsTo T nc T') {calls calls' : Bell → Bell → Bool} (hc : CallsOf T calls)
    (hc' : CallsOf T' calls') : ∀ c, (∃ e, FinMap.get T c = some e) → calls c c = calls' c c := by
  rintro c ⟨e, he⟩
  exact Bool.eq_iff_iff.2 ((hc c e he c).trans (hc' c e (hA.old c e he) c).symm)

/-- **`SingleScc` on the grown table**: an old key keeps its SCC
(`inScc_old`), so `single` may stay as it was there; a new key needs its own
witness. -/
theorem singleScc_addsTo (hA : AddsTo T nc T') (hC : CodeClosed T) {single single' : Bell → Bool}
    (hs : SingleScc T single) (hold : ∀ c, (∃ e, FinMap.get T c = some e) → single' c = single c)
    (hnew : ∀ c, single' c = true → FinMap.get T c = none → (∃ e, FinMap.get T' c = some e) →
      ∀ d, InScc T' c d → d = c) :
    SingleScc T' single' := by
  intro c hc hk d hd
  cases e : FinMap.get T c with
  | none => exact hnew c hc e hk d hd
  | some ec =>
    rw [hold c ⟨ec, e⟩] at hc
    exact hs c hc ⟨ec, e⟩ d ((inScc_old hA hC (by rw [e]; simp) d).1 hd)

end Full

/-! ## The clause on the model's maps -/

/-- **The coherence of `inl.cache` on the model**: every entry `b ↦ m` is
`inlinedM` of `b` on the table at some fuel. -/
def InlCohM (T : FinMap Bell (VarEntry FinMap)) (inl : FinMap Bell Nomm) (calls : Bell → Bell → Bool)
    (hot single : Bell → Bool) : Prop :=
  ∀ b m, FinMap.get inl b = some m → ∃ f, inlinedM (nmOf T) calls hot single f b = some m

/-- **`%full` keeps `InlCohM`**: the table grows, every entry is an old
key, `calls c c`, `hot`, `single` are the same on old keys. -/
theorem inlCohM_addsTo {T nc T' : FinMap Bell (VarEntry FinMap)} (hA : AddsTo T nc T') (hC : CodeClosed T)
    {inl : FinMap Bell Nomm} {calls calls' : Bell → Bell → Bool} {hot hot' single single' : Bell → Bool}
    (hcalls : ∀ c, (∃ e, FinMap.get T c = some e) → calls c c = calls' c c)
    (hhot : ∀ c, (∃ e, FinMap.get T c = some e) → hot c = hot' c)
    (hsing : ∀ c, (∃ e, FinMap.get T c = some e) → single c = single' c)
    (hk : ∀ b m, FinMap.get inl b = some m → ∃ e, FinMap.get T b = some e)
    (h : InlCohM T inl calls hot single) : InlCohM T' inl calls' hot' single' := by
  intro b m hb
  obtain ⟨f, hf⟩ := h b m hb
  exact ⟨f, by rw [← inlinedM_addsTo hA hC hcalls hhot hsing (hk b m hb) f]; exact hf⟩

/-- `nmOf T` is the code `InlPill` reads (`realOf`). -/
theorem nmOf_realOf (T : FinMap Bell (VarEntry FinMap)) : nmOf T = realOf T := rfl

/-- **`InlCoh` from `InlCohM`**, on a cache noun whose fourth place is the
noun of `inl`. -/
theorem inlCoh_of_M {T : FinMap Bell (VarEntry FinMap)} {inl : FinMap Bell Nomm} {calls : Bell → Bell → Bool}
    {hot single : Bell → Bool} {Q : Noun → Prop} {C1 C2 C3 SURE : Noun} (hQ : Q C3)
    (h : InlCohM T inl calls hot single) :
    InlCoh (nmOf T) calls hot single Q (cacheN C1 C2 C3 (inl.toNoun Nomm.toNoun) SURE) := by
  refine ⟨C1, C2, C3, _, SURE, rfl, hQ, FinMap.isMap_toNoun _ _, fun b v hv => ?_⟩
  have hg := FinMap.getF_toNoun Nomm.toNoun inl b
  change getF mugF (TKey.enc b) _ = _ at hv
  rw [hg] at hv
  cases e : FinMap.get inl b with
  | none => rw [e] at hv; simp [unitNoun] at hv
  | some m =>
    rw [e] at hv
    simp only [unitNoun, Option.some.injEq, Noun.cell.injEq] at hv
    obtain ⟨f, hf⟩ := h b m e
    exact ⟨f, m, hf, hv.2.symm⟩

/-! ## `%jets`: the stale entries go -/

/-- **The stale set of `%jets` covers the changes of `hot`**: a bell that
reaches a bell whose `hot` changed is stale.  (Open on the pill: `hot-stale`
with `ColeCoh`, see the header.) -/
def JetsStale (T : FinMap Bell (VarEntry FinMap)) (hot hot' : Bell → Bool) (stale : Bell → Prop) : Prop :=
  ∀ b c, Reach T b c → hot c ≠ hot' c → stale b

/-- **`%jets` keeps `InlCohM`**: `inl'` is `inl` without stale entries, on
the same table, `calls` and `single`, with the new `hot`. -/
theorem inlCohM_jets {T : FinMap Bell (VarEntry FinMap)} (hC : CodeClosed T) (hI : InfoCalls T)
    {inl inl' : FinMap Bell Nomm} {calls : Bell → Bell → Bool} {hot hot' single : Bell → Bool}
    {stale : Bell → Prop} (hS : JetsStale T hot hot' stale)
    (hdel : ∀ b m, FinMap.get inl' b = some m → FinMap.get inl b = some m ∧ ¬ stale b)
    (h : InlCohM T inl calls hot single) : InlCohM T inl' calls hot' single := by
  intro b m hb
  obtain ⟨h1, h2⟩ := hdel b m hb
  obtain ⟨f, hf⟩ := h b m h1
  refine ⟨f, ?_⟩
  rw [← hf]
  refine (inlinedM_congr (fun c => Reach T b c) (fun c nm hc hn c' hc' => ?_) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun c hc => ?_) (fun _ _ => rfl) f b (Reach.refl b)).symm
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hn
    obtain ⟨e', he'⟩ := (hC c e he).2 c' hc'
    exact hc.trans (Reach.step ⟨e, he, hI c e he c' hc', e', he'⟩ (Reach.refl c'))
  · exact Classical.byContradiction fun hne => h2 (hS b c hc hne)

end Compiler
end Formalization
