import lemmas.Ska.CompSixNext
import lemmas.Ska.CompCond

/-!
# `%6` under a fork-free `%next`: no proxy register

`+proxy` is the only arm that writes `cond`, and `+sect` rewrites the
entries of `cond` that the branches made.  On a goal `%next` without forks
the case `%6` takes `sixNextSimple`, and when its branches and its test make
no proxy, `+sect` has nothing to thread: `made-0` and `made-1` are
`~(dif by c) c`, which has no keys (`keys_difM_self`), so the threading puts
every block back as it was and leaves `cond` (`sect_cond`).  `+fork-sure` and
`+copy-lazy` never write `cond` (`kc_forkSure`, `kc_copyL`).

`sixNextSimple_cond`: when the runs of the branches on fork-free `%next`
goals and the run of the test on `%pick` goals keep `cond`, and the
branches' needs have so few lazy blocks that `+lazy-shut` does not fire,
the case `%6` keeps `cond`.  So on this fragment `toStraightF` takes its
renaming path, as `runL_cond_frag6` gives it for `%done` and `%pick`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `~(dif by c) c` -/

theorem get_foldl_del {ν : Type} : ∀ (l : List Nat) (a : Map ν) (k : Nat),
    HoonMap.get (l.foldl HoonMap.del a) k = if k ∈ l then Option.none else HoonMap.get a k
  | [], a, k => by simp
  | x :: l, a, k => by
    rw [List.foldl_cons, get_foldl_del l, HoonMap.get_del]
    by_cases h1 : k ∈ l <;> by_cases h2 : k = x <;> simp [h1, h2]

/-- **`~(dif by c) c` has no keys.** -/
theorem keys_difM_self {ν : Type} (m : Map ν) : HoonMapKeys.keys (difM m m) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro k hk
  rw [HoonMapKeys.mem_keys, difM, get_foldl_del] at hk
  split at hk
  · simp at hk
  · rename_i h; exact h ((HoonMapKeys.mem_keys m k).mpr hk)

/-! ## `+sect` without new proxies -/

theorem kc_jabBlock (o : Nat) (f : Blob → Option Blob) : KC (jabBlock o f : CM Map Unit) := by
  constructor
  intro g x g' h
  unfold jabBlock at h
  obtain ⟨b, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b', _, e⟩ := Option.map_eq_some_iff.mp h
  cases e; rfl

/-- **The threading of `+sect` keeps `cond`** when the branches made no
proxy: both `made` maps are empty. -/
theorem sectThread_self {rid o0 o1 : Nat} {c : Map (Nat × List Nat)} {g g' : Gen Map} {u : Unit}
    (hc : g.cond = c) (h : sectThread rid o0 o1 c c g = some (u, g')) : g'.cond = g.cond := by
  subst hc
  unfold sectThread at h
  simp only [keys_difM_self, List.foldlM_nil] at h
  obtain ⟨b0, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b1, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · split at h
    · cases h
    · obtain ⟨bt, _, h⟩ := Option.bind_eq_some_iff.mp h
      refine (?_ : KC _).keep _ _ _ h
      exact KC.bind' (KC.pure' _) fun _ => KC.bind' (KC.pure' _) fun _ =>
        KC.bind' (kc_jabBlock _ _) fun _ => KC.bind' (kc_jabBlock _ _) fun _ => kc_jabBlock _ _
  · cases h

/-- The end of `+sect`: the two checks of the arguments and the result. -/
theorem sect_tail {α : Type} {a b : Prop} [Decidable a] [Decidable b] {v : α} {g g' : Gen Map} {x : α}
    (h : (if a then (fun _ => Option.none : CM Map α) else if b then (fun _ => Option.none : CM Map α)
      else (pure v : CM Map α)) g = some (x, g')) : x = v ∧ g' = g := by
  revert h; split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩

/-- **`+sect` taken apart**: two blocks emitted and tagged, the threading
when not dropping, and the fork of the branches' needs at the two blocks. -/
theorem sect_apart {nex0 nex1 : NextL S} {o0 o1 : Nat} {rb : List Nat} {cb cw : Map (Nat × List Nat)}
    {g g' : Gen Map} {lz : Lazy S} {yes nuh : Nat}
    (h : sect nex0 nex1 o0 o1 rb cb cw g = some ((lz, yes, nuh), g')) :
    ∃ rid g4, (∃ rest, rb = rid :: rest) ∧ g4.cond = g.cond ∧
      lz = mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [] ∧
      (g4.drop = true → g' = g4) ∧
      (g4.drop = false → sectThread rid o0 o1 cb cw g4 = some ((), g')) := by
  unfold sect at h
  split at h
  · cases h
  · rename_i rid rest
    obtain ⟨_, g1, h1, h⟩ := bind_some h
    obtain ⟨_, g2, h2, h⟩ := bind_some h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    obtain ⟨_, g4, h4, h⟩ := bind_some h
    obtain ⟨g5, g5', h5, h⟩ := bind_some h
    simp only [get, Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    have c4 : g4.cond = g.cond := by
      rw [(KC.setTag' _ _).keep _ _ _ h4, (KC.setTag' _ _).keep _ _ _ h3, (KC.emit' _).keep _ _ _ h2,
        (KC.emit' _).keep _ _ _ h1]
    dsimp only at h
    refine ⟨rid, g4, ⟨rest, rfl⟩, c4, ?_⟩
    by_cases hd : g4.drop = true
    · rw [if_pos hd] at h
      obtain ⟨e, rfl⟩ := sect_tail h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨rfl, fun _ => rfl, fun h' => by rw [hd] at h'; cases h'⟩
    · rw [if_neg hd] at h
      obtain ⟨u, g6, h6, h⟩ := bind_some h
      obtain ⟨e, rfl⟩ := sect_tail h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨rfl, fun h' => absurd h' hd, fun _ => h6⟩

/-- **`+sect` keeps `cond`** when `cond` did not change since before the
branches. -/
theorem sect_cond {nex0 nex1 : NextL S} {o0 o1 : Nat} {rb : List Nat} {c : Map (Nat × List Nat)}
    {g g' : Gen Map} {x : Lazy S × Nat × Nat} (hc : g.cond = c)
    (h : sect nex0 nex1 o0 o1 rb c c g = some (x, g')) : g'.cond = g.cond := by
  obtain ⟨lz, yes, nuh⟩ := x
  obtain ⟨rid, g4, _, c4, _, hdrop, hthr⟩ := sect_apart h
  cases hd : g4.drop
  · rw [sectThread_self (c4.trans hc) (hthr hd), c4]
  · rw [hdrop hd, c4]

/-- **The fork `+sect` returns** is that of the branches' needs, at the two
blocks it emits. -/
theorem sect_lazy {nex0 nex1 : NextL S} {o0 o1 : Nat} {rb : List Nat} {cb cw : Map (Nat × List Nat)}
    {g g' : Gen Map} {lz : Lazy S} {yes nuh : Nat}
    (h : sect nex0 nex1 o0 o1 rb cb cw g = some ((lz, yes, nuh), g')) :
    lz = mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [] :=
  (sect_apart h).choose_spec.choose_spec.2.2.1

/-! ## `+fork-sure` and `+copy` -/

theorem kc_forkNeedGo : ∀ (ned : Need), KC (forkNeedGo ned : CM Map (Need × Need))
  | Need.none => by simp only [forkNeedGo]; exact KC.pure' _
  | Need.this _ => by simp only [forkNeedGo]; kc
  | Need.pair p q => by
    simp only [forkNeedGo]
    refine KC.bind' (kc_forkNeedGo p) fun a => ?_
    rcases a with ⟨h0, h1⟩
    exact KC.bind' (kc_forkNeedGo q) fun b => by rcases b with ⟨t0, t1⟩; exact KC.pure' _
  | Need.both _ p q => by
    simp only [forkNeedGo]
    refine KC.bind' KC.re' fun _ => KC.bind' KC.re' fun _ => KC.bind' (kc_forkNeedGo p) fun a => ?_
    rcases a with ⟨h0, h1⟩
    exact KC.bind' (kc_forkNeedGo q) fun b => by rcases b with ⟨t0, t1⟩; exact KC.pure' _

theorem kc_forkNeed (ned : Need) (o o0 o1 : Nat) : KC (forkNeed ned o o0 o1 : CM Map (Need × Need)) := by
  unfold forkNeed
  refine KC.bind' (kc_forkNeedGo ned) fun a => ?_
  rcases a with ⟨n0, n1⟩
  kc

theorem kc_forkSure (sur : Sure S) (o o0 o1 : Nat) : KC (forkSure sur o o0 o1 : CM Map (Sure S × Sure S)) := by
  unfold forkSure
  refine KC.bind' (kc_forkNeed _ _ _ _) fun a => ?_
  rcases a with ⟨n0, n1⟩
  exact KC.pure' _

mutual
/-- **`+copy-lazy` keeps `cond`.** -/
theorem kc_copyLazyL (o : Nat) : ∀ (a b : Lazy S), KC (copyLazyL o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine KC.bind' (kc_copyNeed _ _ _) fun a => ?_
    rcases a with ⟨ned, ops⟩
    refine KC.bind' (KC.addOps' _ _) fun _ => KC.bind' ?_ fun _ => KC.bind' ?_ fun _ => KC.pure' _
    · split
      · exact KC.pure' _
      · split
        · exact KC.pure' _
        · exact KC.bind' (kc_mergeForks _ f1) fun _ => KC.pure' _
    · split
      · exact KC.pure' _
      · split
        · exact KC.pure' _
        · exact KC.bind' (kc_mergeBonds _ b1) fun _ => KC.pure' _

theorem kc_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    KC (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact KC.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine KC.bind' ?_ fun _ => KC.bind' (kc_mergeForks idx rest) fun _ => KC.pure' _
    split
    · exact KC.pure' _
    · split
      · exact KC.bind' (kc_copyLazyL oy y _) fun _ => KC.bind' (kc_copyLazyL on n _) fun _ => KC.pure' _
      · exact KC.fail

theorem kc_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    KC (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact KC.pure' _
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine KC.bind' ?_ fun _ => KC.bind' (kc_mergeBonds idx rest) fun _ => KC.pure' _
    split
    · exact KC.pure' _
    · exact KC.bind' (kc_copyLazyL ob l _) fun _ => KC.pure' _
end

theorem kc_copyL (first : NextL S) (second : Lazy S) : KC (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  exact KC.bind' (KC.emit' _) fun _ => KC.bind' (kc_copyLazyL _ _ _) fun _ => KC.pure' _

/-! ## The case `%6` -/

/-- **`%6` under a fork-free `%next` keeps `cond`**, when the test is pure,
the runs of the branches on fork-free `%next` goals and of the test on
`%pick` goals keep it, and the branches return needs with at most `N` lazy
blocks each, where `2 * N + 3 ≤ lazyMax` (so `+lazy-shut` does not fire). -/
theorem sixNextSimple_cond {rp rq rr : CGoalL S → List Nat → CM Map (NextL S)} {p : Nomm}
    (hp : p.pure = true) {N : Nat} (hN : 2 * N + 3 ≤ lazyMax)
    (hrp : ∀ z o region, KC (rp (CGoalL.pick z o) region))
    (hrq : ∀ (s : Sure S) th region g x g', rq (CGoalL.next (ofSure s) th) region g = some (x, g') →
      g'.cond = g.cond ∧ (entries x.laz).length ≤ N)
    (hrr : ∀ (s : Sure S) th region g x g', rr (CGoalL.next (ofSure s) th) region g = some (x, g') →
      g'.cond = g.cond ∧ (entries x.laz).length ≤ N)
    {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (h : sixNextSimple rp rq rr p laz th region g0 = some (nex, g9)) : g9.cond = g0.cond := by
  obtain ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hp h
  have cF : gF.cond = g0.cond := by have := (kc_forkSure _ _ _ _).keep _ _ _ hF; exact this
  obtain ⟨cR, nR⟩ := hrr _ _ _ _ _ _ hR
  obtain ⟨cQ, nQ⟩ := hrq _ _ _ _ _ _ hQ
  have cRF : gR.cond = gF.cond := cR
  have cQF : gQ.cond = gF.cond := cQ.trans cRF
  have cS : gS.cond = gQ.cond := by
    rw [cRF] at hS
    exact sect_cond cQF hS
  have cC : gC.cond = gS.cond := (hrp _ _ _).keep _ _ _ hC
  have hbig : lazyBig lz = false := by
    have e := sect_lazy hS
    rw [e]
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    omega
  have c9 : g9.cond = gC.cond := (kc_copyL _ _).keep _ _ _ (hrest hbig)
  rw [c9, cC, cS, cQF, cF]

end Comp
end SkaModel
end Formalization
