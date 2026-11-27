import lemmas.Compiler.PokeLinkGood4
import lemmas.Ska.KnowMeets
import lemmas.Ska.PokeBake

/-!
# `LoopTotal`: the model's SCC loop returns (track P, README Gaps 23)

`efGo` (`+eval-finalized`'s trap) is `none` only at a `%10` of axis `0`
(`+have`'s assert, `+darn:so`) or at an info bell without flags.

* The first never happens on a table of `+ska-poke`: `+fol-loop` turns
  `[10 [0 d] r]` into `[0 0]` (its case `?:  =(0 a.fol)`, the model's
  `Shape.op10`), and the nomms of the table satisfy `Annot` (`InvB.codeOK`,
  kept by `skaPokeB_sound` with no hypothesis), whose case `n10` asks
  `axis ≠ 0`: `annot_noAx0`.  On the real compiler (`tools/hoon/ten0dump.hoon`)
  the nomm of `[10 [0 [0 1]] [0 1]]` is `[%0 0]` with flags `[| |]`.
* The second never happens on a `TarjanSpec` list: an info bell is a callee
  (`InfoCalls`), a key (`CodeClosed`), so old (flags from `F`, `FlagTot`) or
  new in an SCC at or before the current one (callees first).

**`sccLoop_some`**, **`loopTotal_of`** (the leaf `LoopTotal` of
`loopLinkAt_flagsOfT` as a theorem), **`loopTotal_poke`** (at `+ska-poke`'s
tables, from `InvB` of the new `long`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

/-- **A nomm that satisfies `Annot` has no `%10` at axis `0`.** -/
theorem annot_noAx0 {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {f : Noun} {n : Nomm}
    (h : Annot lib code P f n) : NoAx0 n := by
  induction h <;> simp_all [NoAx0]

/-- `+have` with its assert returns at every axis but `0`. -/
theorem haveO_some (s : Sock) {a : Nat} (h : a ≠ 0) : haveO s a = some (haveAx s a) := by
  simp [haveO, h]

/-- `+pull:so` returns at every axis but `0`. -/
theorem pull_some (s : Sock) {a : Nat} (h : a ≠ 0) : ∃ t, So.pull s a = some t := by
  unfold So.pull
  cases s <;> simp [h]

/-- `?&` of two values that return. -/
theorem andS_some {a b : Option Bool} (ha : ∃ x, a = some x) (hb : ∃ y, b = some y) : ∃ z, andS a b = some z := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  cases x <;> simp [andS]

/-- **`+eval-finalized`'s trap returns** on a nomm with no `%10` at axis `0`
whose info bells all have flags. -/
theorem efGo_some (ft : FlagTab) :
    ∀ (n : Nomm) (s : Sock), NoAx0 n → (∀ c ∈ nommInfos n, ∃ p, ft c = some p) → ∃ r, efGo ft s n = some r := by
  intro n
  induction n with
  | cons p q ihp ihq =>
    intro s hn hi
    obtain ⟨rp, hp⟩ := ihp s hn.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨rq, hq⟩ := ihq s hn.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    simp [efGo, hp, hq]
  | n0 p =>
    intro s _ _
    by_cases h : p = 0
    · simp [efGo, h]
    · obtain ⟨t, ht⟩ := pull_some s h
      simp [efGo, h, ht, haveO_some s h]
  | n1 p => intro s _ _; exact ⟨_, rfl⟩
  | n2 p q info ihp ihq =>
    intro s hn hi
    obtain ⟨⟨s1, p1, p2⟩, hp⟩ := ihp s hn.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨⟨s2, q1, q2⟩, hq⟩ := ihq s hn.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    cases info with
    | none => cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> simp [efGo, hp, hq, andS]
    | some i =>
      obtain ⟨⟨x1, x2⟩, hx⟩ := hi i.1 (by simp [nommInfos])
      cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> cases x1 <;> cases x2 <;> simp [efGo, hp, hq, andS, hx]
  | n3 p ihp =>
    intro s hn hi
    obtain ⟨rp, hp⟩ := ihp s hn (fun c hc => hi c (by simp [nommInfos, hc]))
    simp [efGo, hp]
  | n4 p _ => intro s _ _; exact ⟨_, rfl⟩
  | n5 p q ihp ihq =>
    intro s hn hi
    obtain ⟨⟨s1, p1, p2⟩, hp⟩ := ihp s hn.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨⟨s2, q1, q2⟩, hq⟩ := ihq s hn.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> simp [efGo, hp, hq, andS]
  | n6 p q r _ ihq ihr =>
    intro s hn hi
    obtain ⟨rq, hq⟩ := ihq s hn.2.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨rr, hr⟩ := ihr s hn.2.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    simp [efGo, hq, hr]
  | n7 p q ihp ihq =>
    intro s hn hi
    obtain ⟨rp, hp⟩ := ihp s hn.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨rq, hq⟩ := ihq rp.1 hn.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    simp [efGo, hp, hq]
  | n10 a v q ihv ihq =>
    intro s hn hi
    obtain ⟨rv, hv⟩ := ihv s hn.2.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨rq, hq⟩ := ihq s hn.2.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨d, hd⟩ := darn_some rq.1 rv.1 hn.1
    simp [efGo, hv, hq, haveO_some _ hn.1, hd]
  | n11s tag q body ihq =>
    intro s hn hi
    obtain ⟨rq, hq⟩ := ihq s hn (fun c hc => hi c (by simp [nommInfos, hc]))
    simp [efGo, hq]
  | n11d tag hh q body ihh ihq =>
    intro s hn hi
    obtain ⟨rh, hh'⟩ := ihh s hn.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨rq, hq⟩ := ihq s hn.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    simp [efGo, hh', hq]
  | n12 p q _ _ => intro s _ _; exact ⟨_, rfl⟩
  | mean p b q body k ihp ihq =>
    intro s hn hi
    obtain ⟨rp, hp⟩ := ihp s hn.1 (fun c hc => hi c (by simp [nommInfos, hc]))
    obtain ⟨rq, hq⟩ := ihq s hn.2 (fun c hc => hi c (by simp [nommInfos, hc]))
    simp [efGo, hp, hq]

/-- The fold of one SCC returns, and keeps flags on `P`, when each member
evaluates on every table with flags on `P`. -/
theorem efFold_some (nm : Bell → Option Nomm) (P : Bell → Prop) :
    ∀ (l : List Bell) (f : FlagTab), (∀ c, P c → ∃ p, f c = some p) →
      (∀ b ∈ l, ∀ f' : FlagTab, (∀ c, P c → ∃ p, f' c = some p) → ∃ pt, evalFin nm f' b = some pt) →
      ∃ f'', l.foldl (efStep nm) (some f) = some f'' ∧ ∀ c, P c → ∃ p, f'' c = some p
  | [], f, hf, _ => ⟨f, rfl, hf⟩
  | b :: l, f, hf, hl => by
    obtain ⟨pt, hpt⟩ := hl b List.mem_cons_self f hf
    have e : (b :: l).foldl (efStep nm) (some f) =
        l.foldl (efStep nm) (some fun c => if c = b then some pt else f c) := by
      simp [efStep, hpt]
    rw [e]
    refine efFold_some nm P l _ (fun c hc => ?_) (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb'))
    by_cases h : c = b
    · exact ⟨pt, by simp [h]⟩
    · simp only [h, if_false]; exact hf c hc

section Total

variable {T nc T' : FinMap Bell (VarEntry FinMap)}

/-- **The model's SCC loop returns** on a `TarjanSpec` list of the new
bells, from flags on every old key, when the new table is closed, has
`InfoCalls` and no `%10` at axis `0`. -/
theorem sccLoop_some (hA : AddsTo T nc T') (hC' : CodeClosed T') (hI' : InfoCalls T')
    (hN : ∀ b e, FinMap.get T' b = some e → NoAx0 e.nomm) {L : List (List Bell)} (hL : TarjanSpecP nc L) :
    ∀ (rest D : List (List Bell)) (ft : FlagTab), L = D ++ rest →
      (∀ c, FinMap.get T c ≠ none → ∃ p, ft c = some p) →
      (∀ c ∈ D.flatten, ∃ p, ft c = some p) →
      ∃ G, sccLoop (nmOf T') ft rest = some G := by
  intro rest
  induction rest with
  | nil => intro D ft _ _ _; exact ⟨ft, rfl⟩
  | cons S rest ih =>
    intro D ft hLe h1 h2
    have hSL : S ∈ L := by rw [hLe]; simp
    have hSnd : ∀ b ∈ S, b ∈ L.flatten := fun b hb => List.mem_flatten.2 ⟨S, hSL, hb⟩
    -- the bells that have flags while `S` runs
    let P : Bell → Prop := fun c => FinMap.get T c ≠ none ∨ c ∈ D.flatten ∨ c ∈ S
    have hpw : ∀ S' ∈ rest, ∀ b ∈ S, ∀ c ∈ S', ¬ Edge nc b c := by
      have hp := hL.2.2.2
      rw [hLe, List.pairwise_append] at hp
      exact (List.pairwise_cons.1 hp.2.1).1
    have hmem : ∀ b ∈ S, ∀ f' : FlagTab, (∀ c, P c → ∃ p, f' c = some p) →
        ∃ pt, evalFin (nmOf T') f' b = some pt := by
      intro b hb f' hf'
      obtain ⟨-, e0, he0⟩ := listed_new hA hL (hSnd b hb)
      have hbT := (hA.new _ _ he0).2
      unfold evalFin
      have hnm : nmOf T' b = some e0.nomm := by simp [nmOf, hbT]
      rw [hnm]
      simp only [Option.bind_some]
      have hinf : ∀ c ∈ nommInfos e0.nomm, ∃ p, f' c = some p := by
        intro c hc
        apply hf'
        have hcall := hI' b e0 hbT c hc
        obtain ⟨ec, hec⟩ := (hC' b e0 hbT).2 c hc
        rcases hA.cov c ec hec with hco | hcn
        · exact Or.inl (by rw [hco]; simp)
        · have hcl : c ∈ L.flatten := (hL.2.2.1 c).2 ⟨ec, hcn⟩
          obtain ⟨S', hS', hcS'⟩ := List.mem_flatten.1 hcl
          rw [hLe] at hS'
          rcases List.mem_append.1 hS' with hD | hR
          · exact Or.inr (Or.inl (List.mem_flatten.2 ⟨S', hD, hcS'⟩))
          · rcases List.mem_cons.1 hR with rfl | hR'
            · exact Or.inr (Or.inr hcS')
            · exact absurd ⟨e0, he0, hcall, ec, hcn⟩ (hpw S' hR' b hb c hcS')
      obtain ⟨r, hr⟩ := efGo_some f' e0.nomm b.less (hN b e0 hbT) hinf
      exact ⟨_, by rw [hr]; rfl⟩
    have hft1 : ∀ c, P c → ∃ p, (fun c => if c ∈ S then some (false, false) else ft c : FlagTab) c = some p := by
      intro c hc
      by_cases hcS : c ∈ S
      · simp [hcS]
      · simp only [hcS, if_false]
        rcases hc with h | h | h
        · exact h1 c h
        · exact h2 c h
        · exact absurd h hcS
    obtain ⟨ft', hft', hP'⟩ := efFold_some (nmOf T') P S _ hft1 hmem
    have hstep : sccStep (nmOf T') ft S = some ft' := by rw [sccStep_eq]; exact hft'
    have hD' : ∀ c ∈ (D ++ [S]).flatten, ∃ p, ft' c = some p := by
      intro c hc
      simp only [List.flatten_append, List.mem_append, List.flatten_cons, List.flatten_nil, List.append_nil] at hc
      rcases hc with hc | hc
      · exact hP' c (Or.inr (Or.inl hc))
      · exact hP' c (Or.inr (Or.inr hc))
    obtain ⟨G, hG⟩ := ih (D ++ [S]) ft' (by rw [hLe]; simp) (fun c hc => hP' c (Or.inl hc)) hD'
    exact ⟨G, by simp only [sccLoop, hstep, Option.bind_some]; exact hG⟩

end Total

/-- **`LoopTotal` as a theorem**: on a `TarjanSpec` list, from flags at
every old key, when the new table is closed, has `InfoCalls` and no `%10`
at axis `0`. -/
theorem loopTotal_of {code nc : FinMap Bell (VarEntry FinMap)} {F : FlagTab}
    (hA : AddsTo code nc (addCode code nc)) (hC' : CodeClosed (addCode code nc)) (hI' : InfoCalls (addCode code nc))
    (hN : ∀ b e, FinMap.get (addCode code nc) b = some e → NoAx0 e.nomm) (hFt : FlagTot code F) :
    LoopTotal code nc F := by
  intro L hL
  refine sccLoop_some hA hC' hI' hN (tarjanSpecP_of hL) L [] F (by simp) (fun c hc => ?_) (by simp)
  cases h : FinMap.get code c with
  | none => exact absurd h hc
  | some e => exact hFt c e h

/-- **The table of a `long` with `InvB` has no `%10` at axis `0`.** -/
theorem invB_noAx0 {lib : Lib} {L : LongB FinMap} (h : InvB lib L) :
    ∀ b e, FinMap.get L.code b = some e → NoAx0 e.nomm := by
  intro b e hb
  have hr : realOf L.code b = some e.nomm := by simp [realOf, tget_fin, hb]
  exact annot_noAx0 (h.codeOK b e.nomm hr)

/-- **`LoopTotal` at `+ska-poke`'s tables**: the new table is `L'.code` of a
`long` with `InvB` (`skaPokeB_sound`). -/
theorem loopTotal_poke {code : FinMap Bell (VarEntry FinMap)} {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)} {F : FlagTab}
    (hc : CodeClosed code) (hv : VarsKeys E.vars code) (hi : InfoCalls code) (hbg : bakeGraph E n = some bg)
    (hFt : FlagTot code F) {lib : Lib} {L' : LongB FinMap} (hI : InvB lib L')
    (hL' : L'.code = addCode code (newCode code bg.1)) :
    LoopTotal code (newCode code bg.1) F :=
  loopTotal_of (addsTo_addCode code bg.1) (addCode_closed hc hv hbg).1 (infoCalls_addCode hi hbg)
    (fun b e hb => invB_noAx0 hI b e (by rw [hL']; exact hb)) hFt

end Compiler
end Formalization
