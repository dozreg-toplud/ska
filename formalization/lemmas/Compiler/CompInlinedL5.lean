import lemmas.Compiler.CompInlinedL3
import lemmas.Compiler.PokeLinkFlags

/-!
# `inlinedM` returns: the fuel bound for `InlPill` (track Q)

`InlPill` (`Glue/InlineAnnot.lean`) goes from the pill to the model: when
the pill's `+inlined` returns, `inlinedM` returns at some fuel.  The pill
half `inl_pill_gate` (`CompInlinedL4.lean`) holds whenever the model
returns, so what is missing is that the model returns.  It does, at the fuel
`r b + 1`, for any rank `r` that goes down along the calls the walk enters:

* `inlWalk_some`: the walk returns on a nomm when `go` returns on each info
  bell of the nomm that passes the three bell tests of `inlOK` (not `hot`,
  `single`, not calling itself).  The memo key and `+safe-fol-fol` tests can
  only make the walk enter fewer callees, so they are not needed.
* `inlinedM_rank`: if every such info bell `c` of the nomm of a key `b` is a
  key with `r c < r b`, then `inlinedM … f b` returns for every `f > r b`, so
  at `r b + 1`.
* `inlRank T L b`: the index in a callees-first list `L` of SCCs of `T`
  (`TarjanSpecP`, track P) of the component holding `b`.  `inlRank_ok`: on a
  closed table (`CodeClosed`) whose info bells are among the calls
  (`InfoCalls`), with `calls` the table's and `single c` implying that `c`
  is alone in its SCC (`SingleScc`), `inlRank T L` is such a rank: an info
  bell `c` of `b` is an `Edge`, so its component is not later than `b`'s;
  the same component would make `c` and `b` one SCC, so `c = b` by
  `single c`, and then `c` calls itself, which `inlOK` rejects.
* `inlinedM_returns`: the two together: every key `b` of such a table
  returns at the fuel `inlRank T L b + 1`.

What the pill gives for `single`: `SccQ` says the singleton test of
`+scc-of` is `single`; `SingleScc` holds when the SCC `+scc-of` answers is
the true SCC of `c` in `T` (the cache `sccs` correct, the miss path's
`+tarjan` correct).  The fuel bound is then a statement on the model alone.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel SkaModel.Glue SkaModel.Ana SkaModel.Bake

set_option linter.unusedVariables false

/-! ## The walk returns when the callees it enters return -/

/-- **The walk returns** on `nm` when `go` returns on every info bell of
`nm` that is not hot, single and does not call itself. -/
theorem inlWalk_some {calls : Bell → Bell → Bool} {hot single : Bell → Bool} {go : Bell → Option Nomm} :
    ∀ nm : Nomm, (∀ c ∈ nommInfos nm, hot c = false → single c = true → calls c c = false →
      ∃ m, go c = some m) → ∃ m, inlWalk calls hot single go nm = some m := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihp fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd]
  | n0 a => intro _; exact ⟨_, rfl⟩
  | n1 k => intro _; exact ⟨_, rfl⟩
  | n2 p q info ihp ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihp fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    cases info with
    | none => simp [inlWalk, ha, hd]
    | some ck =>
      obtain ⟨c, k⟩ := ck
      cases hok : inlOK calls hot single c k q with
      | false => simp [inlWalk, ha, hd, hok]
      | true =>
        have hok' := hok
        simp only [inlOK, Bool.and_eq_true, Bool.not_eq_true'] at hok'
        obtain ⟨⟨⟨⟨-, -⟩, hh⟩, hs⟩, hc⟩ := hok'
        obtain ⟨m, hm⟩ := h c (by simp [nommInfos]) hh hs hc
        simp [inlWalk, ha, hd, hok, hm]
  | n3 p ih =>
    intro h
    obtain ⟨a, ha⟩ := ih fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha]
  | n4 p ih =>
    intro h
    obtain ⟨a, ha⟩ := ih fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha]
  | n5 p q ihp ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihp fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd]
  | n6 p q r ihp ihq ihr =>
    intro h
    obtain ⟨a, ha⟩ := ihp fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨e, he⟩ := ihr fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd, he]
  | n7 p q ihp ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihp fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd]
  | n10 x v q ihv ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihv fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd]
  | n11s t q body ih =>
    intro h
    obtain ⟨a, ha⟩ := ih fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha]
  | n11d t x q body ihh ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihh fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd]
  | n12 p q ihp ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihp fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd]
  | mean p x q body k ihp ihq =>
    intro h
    obtain ⟨a, ha⟩ := ihp fun c hc => h c (by simp [nommInfos, hc])
    obtain ⟨d, hd⟩ := ihq fun c hc => h c (by simp [nommInfos, hc])
    simp [inlWalk, ha, hd]

/-! ## A rank down the entered calls bounds the fuel -/

/-- **A rank for `inlinedM`**: every info bell `c` of the nomm of a key `b`
that passes the bell tests of `inlOK` is a key, of smaller rank. -/
def InlRankOK (code : Bell → Option Nomm) (calls : Bell → Bell → Bool) (hot single : Bell → Bool)
    (r : Bell → Nat) : Prop :=
  ∀ b nm, code b = some nm → ∀ c ∈ nommInfos nm, hot c = false → single c = true → calls c c = false →
    (∃ m, code c = some m) ∧ r c < r b

/-- **The fuel bound**: under a rank, `inlinedM` returns on every key `b` at
every fuel above `r b` (so at `r b + 1`). -/
theorem inlinedM_rank {code : Bell → Option Nomm} {calls : Bell → Bell → Bool} {hot single : Bell → Bool}
    {r : Bell → Nat} (hr : InlRankOK code calls hot single r) :
    ∀ f b nm, code b = some nm → r b < f → ∃ m, inlinedM code calls hot single f b = some m := by
  intro f
  induction f with
  | zero => intro b nm _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro b nm hb hf
    have hw := inlWalk_some (calls := calls) (hot := hot) (single := single)
      (go := inlinedM code calls hot single n) nm fun c hc hh hs hcc => by
        obtain ⟨⟨m, hm⟩, hlt⟩ := hr b nm hb c hc hh hs hcc
        exact ih c m hm (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hf))
    obtain ⟨m, hm⟩ := hw
    exact ⟨m, by simp only [inlinedM, hb, Option.bind_some, hm]⟩

/-! ## The rank from a callees-first list of the SCCs -/

open SkaModel.Ana

/-- `single c` only of a bell alone in its SCC of `T`. -/
def SingleScc (T : FinMap Bell (VarEntry FinMap)) (single : Bell → Bool) : Prop :=
  ∀ c, single c = true → (∃ e, FinMap.get T c = some e) → ∀ d, InScc T c d → d = c

/-- `calls` is the table's: on a key `c`, `calls c d` iff `d ∈ calls` of
`c`'s entry. -/
def CallsOf (T : FinMap Bell (VarEntry FinMap)) (calls : Bell → Bell → Bool) : Prop :=
  ∀ c e, FinMap.get T c = some e → ∀ d, calls c d = true ↔ FinMap.get e.calls d = some ()

/-- **The rank**: the index in `L` of the component that holds `b`. -/
def inlRank (L : List (List Bell)) (b : Bell) : Nat := L.findIdx fun S => decide (b ∈ S)

theorem inlRank_mem {L : List (List Bell)} {b : Bell} (h : b ∈ L.flatten) :
    ∃ hl : inlRank L b < L.length, b ∈ L[inlRank L b] := by
  obtain ⟨S, hS, hbS⟩ := List.mem_flatten.1 h
  have hex : ∃ x ∈ L, (fun S => decide (b ∈ S)) x = true := ⟨S, hS, by simp [hbS]⟩
  have hl := List.findIdx_lt_length_of_exists hex
  refine ⟨hl, ?_⟩
  have := List.findIdx_getElem (w := hl)
  have h2 : b ∈ L[L.findIdx fun S => decide (b ∈ S)] := by simpa using this
  exact h2

/-- **`inlRank` is a rank** on a closed table whose info bells are calls,
for a callees-first list of its SCCs. -/
theorem inlRank_ok {T : FinMap Bell (VarEntry FinMap)} {L : List (List Bell)} {calls : Bell → Bell → Bool}
    {hot single : Bell → Bool} (hC : CodeClosed T) (hI : InfoCalls T) (hL : TarjanSpecP T L)
    (hc : CallsOf T calls) (hs : SingleScc T single) :
    InlRankOK (nmOf T) calls hot single (inlRank L) := by
  intro b nm hb c hci hh hsc hcc
  simp only [nmOf, Option.map_eq_some_iff] at hb
  obtain ⟨e, he, rfl⟩ := hb
  obtain ⟨e', he'⟩ := (hC b e he).2 c hci
  refine ⟨⟨e'.nomm, by simp [nmOf, he']⟩, ?_⟩
  have hedge : Edge T b c := ⟨e, he, hI b e he c hci, e', he'⟩
  obtain ⟨hli, hbi⟩ := inlRank_mem ((hL.2.2.1 b).2 ⟨e, he⟩)
  obtain ⟨hlj, hcj⟩ := inlRank_mem ((hL.2.2.1 c).2 ⟨e', he'⟩)
  rcases Nat.lt_trichotomy (inlRank L c) (inlRank L b) with hlt | heq | hgt
  · exact hlt
  · exfalso
    -- one component: `c` and `b` are one SCC, so `c = b`, which calls itself
    have hmem := hL.1 _ (List.getElem_mem hli)
    obtain ⟨x, -, hx⟩ := hmem
    have hb' : InScc T x b := mem_sccOrd.1 (hx ▸ hbi)
    have hc' : InScc T x c := mem_sccOrd.1 (hx ▸ (by simpa [heq] using hcj))
    have hcb : InScc T c b := ⟨hb'.1, hc'.2.2.trans hb'.2.1, hb'.2.2.trans hc'.2.1⟩
    have := hs c hsc ⟨e', he'⟩ b hcb
    subst this
    have : calls b b = true := (hc b e he b).2 (hI b e he b hci)
    rw [this] at hcc; cases hcc
  · exfalso
    have hp := List.pairwise_iff_getElem.1 hL.2.2.2 (inlRank L b) (inlRank L c) hli hlj hgt
    exact hp b hbi c hcj hedge

/-- **`inlinedM` returns on every key** of a closed table, at the fuel
`inlRank T L b + 1`, for a callees-first list `L` of its SCCs. -/
theorem inlinedM_returns {T : FinMap Bell (VarEntry FinMap)} {L : List (List Bell)} {calls : Bell → Bell → Bool}
    {hot single : Bell → Bool} (hC : CodeClosed T) (hI : InfoCalls T) (hL : TarjanSpecP T L)
    (hc : CallsOf T calls) (hs : SingleScc T single) :
    ∀ b e, FinMap.get T b = some e → ∃ m, inlinedM (nmOf T) calls hot single (inlRank L b + 1) b = some m := by
  intro b e he
  exact inlinedM_rank (inlRank_ok (hot := hot) hC hI hL hc hs) _ b e.nomm (by simp [nmOf, he]) (Nat.lt_succ_self _)

end Compiler
end Formalization
