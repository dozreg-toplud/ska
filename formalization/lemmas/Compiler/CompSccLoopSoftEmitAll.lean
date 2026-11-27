import lemmas.Compiler.CompSccLoopSoftEmitAxs
import lemmas.Compiler.CompSccLoopSoftEmitTrap
import lemmas.Compiler.CompSccLoopSoftEmitOps

/-! # `+soft-emit` without tries in the pill (README Gaps 21.17)

**`se_emit`**: on a soft call whose requirements all have a need `%none` or `%this` (the case
of the 6 soft compiles of the corpus), `(~(soft-emit comp gen) [o s])` is the model
`softEmitT s` on every state: the pushes `seAxs` (`se_axs`), `seCut` (`se_cut`), `seOps`,
`seTries`, `seHed` (`se_ops`, `se_tries`, `se_hed`), then the `?>` and `+emir` (`se_end`), or
the crash of the `?>` on a head block of another shape (`se_bad`).  **`se_emit_hE`** is the
hypothesis `hE` of `sd_tree` for the soft maps whose calls all have such requirements. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- A requirement of a soft call `+soft-emit` handles without tries. -/
def ReqTN (req : List (Nat × Need)) : Prop := ∀ p ∈ req, p.2 = Need.none ∨ ∃ r, p.2 = Need.this r

/-- On such requirements, the `tops` of `softCuts` are all `%this`. -/
theorem softCuts_tops (axs : List (Nat × Nat)) :
    ∀ (req : List (Nat × Need)) (acc c : List Pole × List (Nat × Nat × Need)), ReqTN req →
      (∀ t ∈ acc.2, ∃ r, t.2.2 = Need.this r) → softCuts axs req acc = some c →
      ∀ t ∈ c.2, ∃ r, t.2.2 = Need.this r
  | [], acc, c, _, ha, h => by
    simp only [softCuts, Option.some.injEq] at h
    subst h; exact ha
  | (src, ned) :: rest, acc, c, hr, ha, h => by
    simp only [softCuts] at h
    cases hc : softCutT src ned axs with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨o', t'⟩ := p
      simp only [hc, Option.bind_some] at h
      refine softCuts_tops axs rest _ c (fun p hp => hr p (List.mem_cons_of_mem _ hp)) ?_ h
      intro t ht
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · rcases hr (src, ned) (List.mem_cons_self ..) with e | ⟨r, e⟩
        · simp only at e; subst e; simp [softCutT] at hc; obtain ⟨-, rfl⟩ := hc; simp at ht
        · simp only at e; subst e
          simp only [softCutT] at hc
          cases hl : axs.lookup r with
          | none =>
            simp only [hl] at hc
            split at hc
            · cases hc
            · simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨-, rfl⟩ := hc; simp at ht
          | some q =>
            simp only [hl, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨-, rfl⟩ := hc
            simp only [List.mem_singleton] at ht
            subst ht; exact ⟨r, rfl⟩
      · exact ha t ht

theorem softTries_nil (tops : List (Nat × Nat × Need)) (h : ∀ t ∈ tops, ∃ r, t.2.2 = Need.this r) :
    softTries tops = [] := by
  unfold softTries
  rw [List.filter_eq_nil_iff]
  intro t ht
  obtain ⟨r, e⟩ := h t ht
  obtain ⟨q, r', n⟩ := t
  simp only at e
  subst e
  simp

/-- `?=(~ req.s)` on a soft call with requirements: `|`. -/
theorem se_t0 (ctx : Noun) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (hr : s.req ≠ []) : nock (seS0 g x ctx o s) seT0 = some (A 1) := by
  obtain ⟨⟨src, n⟩, rest, e⟩ : ∃ p rest, s.req = p :: rest := by
    cases h : s.req with
    | nil => exact absurd h hr
    | cons p rest => exact ⟨p, rest, rfl⟩
  simp only [seS0, compCore]
  generalize comp.door = Dr
  generalize genNoun g x = GN
  simp [nock_exec, seT0, Compiler.SoftCall.toNoun, e, eqCode]

/-- `seBat` with the formula after `seHed` left open. -/
def seBatOf (REST : Noun) : Noun :=
  (C (A 6) (C seT0 (C seNil (C (A 8) (C seAxs (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C seCut (C (A 7) (C seGenP (C (A 7) (C sePin (C (A 8) (C seOps (C (A 8) (C seTries (C (A 8) (C seHed REST)))))))))))))))))))

theorem seBat_eq : seBat = seBatOf (C (A 6) (C seHedT (C (C (A 6) (C seTriesT (C seEmir seTryPath)))
    (C (A 0) (A 0))))) := rfl

/-- **The pushes of `seBat`** on a soft call with requirements: `seAxs` gives a map `M` of
`softAxes`, then `seCut`, `seOps`, `seTries` (`~`), `seHed`, on to the subject of the `?>`. -/
theorem se_pre (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat)
    (s : SoftCall) (hreq : ReqTN s.req) (hr : s.req ≠ []) :
    ∃ M, ∀ REST, nock (seS0 g x ctx o s) (seBatOf REST) =
      (softCuts (softAxes s.ned 1 []) s.req ([], [])).bind fun c =>
        (HoonMap.get g.blocks s.head).bind fun hd => nock (C hd.toNoun (C (A 0)
          (C (listNoun Pole.toNoun (c.1 ++ softMoves c.2)) (seS4 (seCutN c) M g x ctx o s)))) REST := by
  have hT0 := se_t0 ctx g x o s hr
  obtain ⟨M, hAx, hM⟩ := se_axs ctx hc g x o s
  have hC := se_cut ctx hc g x o s M _ hM hreq
  refine ⟨M, fun REST => ?_⟩
  unfold seBatOf
  cases hcut : softCuts (softAxes s.ned 1 []) s.req ([], []) with
  | none =>
    rw [hcut] at hC
    simp only [Option.map_none] at hC
    simp only [Option.bind_none]
    simp only [seS0, seS1, compCore] at hT0 hAx hC ⊢
    generalize comp.door = Dr at hT0 hAx hC ⊢
    generalize genNoun g x = GN at hT0 hAx hC ⊢
    generalize Compiler.SoftCall.toNoun s = SN at hT0 hAx hC ⊢
    simp [nock_exec, hT0, hAx, hC]
  | some c =>
    obtain ⟨ops, tops⟩ := c
    rw [hcut] at hC
    simp only [Option.map_some] at hC
    have htops := softCuts_tops _ s.req ([], []) (ops, tops) hreq (by simp) hcut
    have hO := se_ops ctx hc g x o s M ops tops
    have hT := se_tries ctx hc g x o s M (listNoun Pole.toNoun (ops ++ softMoves tops)) ops tops htops
    have hH := se_hed ctx hc g x o s (seCutN (ops, tops)) M (listNoun Pole.toNoun (ops ++ softMoves tops))
    simp only [Option.bind_some]
    cases hg : HoonMap.get g.blocks s.head with
    | none =>
      rw [hg] at hH
      simp only [Option.map_none] at hH
      simp only [Option.bind_none]
      simp only [seS0, seS1, seS4, compCore] at hT0 hAx hC hO hT hH ⊢
      generalize comp.door = Dr at hT0 hAx hC hO hT hH ⊢
      generalize genNoun g x = GN at hT0 hAx hC hO hT hH ⊢
      generalize Compiler.SoftCall.toNoun s = SN at hT0 hAx hC hO hT hH ⊢
      simp [nock_exec, hT0, hAx, hC, hO, hT, hH, seGenP, sePin]
    | some hd =>
      rw [hg] at hH
      simp only [Option.map_some] at hH
      simp only [Option.bind_some]
      simp only [seS0, seS1, seS4, compCore] at hT0 hAx hC hO hT hH ⊢
      generalize comp.door = Dr at hT0 hAx hC hO hT hH ⊢
      generalize genNoun g x = GN at hT0 hAx hC hO hT hH ⊢
      generalize Compiler.SoftCall.toNoun s = SN at hT0 hAx hC hO hT hH ⊢
      simp [nock_exec, hT0, hAx, hC, hO, hT, hH, seGenP, sePin]

/-- **`+soft-emit` without tries**: on a soft call whose requirements are all `%none` or
`%this`, the pill's gate is the model `softEmitT` on every state. -/
theorem se_emit (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat)
    (s : SoftCall) (hreq : ReqTN s.req) :
    nock (compCore g x ctx) (seCall (C (A o) (Compiler.SoftCall.toNoun s)))
      = (softEmitT s g).map fun p => genNoun p.2 x := by
  by_cases hr : s.req = []
  · rw [se_nil g x ctx o s hr]; simp [softEmitT, hr]
  obtain ⟨M, hP⟩ := se_pre ctx hc g x o s hreq hr
  rw [se_slam]
  conv => { lhs; arg 2; rw [seBat_eq] }
  rw [hP]
  simp only [softEmitT, hr, if_false]
  cases hcut : softCuts (softAxes s.ned 1 []) s.req ([], []) with
  | none => rfl
  | some c =>
    obtain ⟨ops, tops⟩ := c
    have htops := softCuts_tops _ s.req ([], []) (ops, tops) hreq (by simp) hcut
    have hS := softTries_nil tops htops
    simp only [Option.bind_some, hS, ne_eq, not_true_eq_false, if_false]
    cases hg : HoonMap.get g.blocks s.head with
    | none => rfl
    | some hd =>
      simp only [Option.bind_some]
      by_cases hs : hd.par = [] ∧ hd.body = [] ∧ ∃ t, hd.fin = Termin.hop t ∧ t.args = []
      · obtain ⟨hp, hb, t, hf, ht⟩ := hs
        rw [se_end g x ctx hc o s hd (ops ++ softMoves tops) (seCutN (ops, tops)) M hp hb t hf ht]
        simp [hp, hb, hf, ht]
      · rw [se_bad hd hs]
        by_cases h1 : hd.par = [] ∧ hd.body = []
        · simp only [h1, and_self, if_true]
          cases hf : hd.fin with
          | hop t =>
            have : t.args ≠ [] := fun e => hs ⟨h1.1, h1.2, t, hf, e⟩
            simp [this]
          | _ => rfl
        · simp only [h1, if_false, Option.map_none]

/-- **`hE` of `sd_tree`** for a soft map whose calls all have requirements `%none` / `%this`:
`F g e` is `softEmitT` of the call the noun `e = [o s]` is. -/
theorem se_emit_hE (ctx : Noun) (hc : CompIn ctx) (x : GenRest) (L : List (Nat × SoftCall))
    (hL : tapList x.soft = L.map fun p => C (A p.1) (Compiler.SoftCall.toNoun p.2))
    (hreq : ∀ p ∈ L, ReqTN p.2.req)
    (F : Gen (TreapMap mugF) → Noun → Option (Gen (TreapMap mugF)))
    (hF : ∀ g p, p ∈ L → F g (C (A p.1) (Compiler.SoftCall.toNoun p.2)) = (softEmitT p.2 g).map (·.2)) :
    ∀ g e, e ∈ tapList x.soft → nock (compCore g x ctx) (seCall e) = (F g e).map (genNoun · x) := by
  intro g e he
  rw [hL] at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  rw [se_emit ctx hc g x p.1 p.2 (hreq p hp), hF g p hp]
  cases softEmitT p.2 g <;> rfl

end Compiler
end Formalization
