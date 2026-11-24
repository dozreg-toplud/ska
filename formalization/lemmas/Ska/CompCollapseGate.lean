import lemmas.Ska.CompWalkU
import lemmas.Ska.CompMede

/-!
# The gate of `+collapse-lazy-atom`

README Gaps 12.2, the first step of the collapse case.  `collapseGate r o`
puts at each lazy block either nothing (the block wants nothing, or `r`
itself), or `[mov src r']` (the block wants the noun whole in `r'`), or the
ops of `+crash-need` from `src` (the block wants parts of it), where `src` is
`r` at the block `o` and a fresh proxy for `r` elsewhere (`+proxy`).

What the ops do depends on the final `cond`, since the program holds them
unproxied.  So the property of the ops sees the `cond` of the state where
the walk ends: `WalkOKD` is `WalkOKC` (`CompWalkU.lean`) whose property `P`
takes that `cond` as its first argument, and `walkLazy_okD` is the walk for
any relation `C` that keeps the entries of `cond` below the start of each
step (`ProxyFor r` does, by `CondFresh.get_lt`).

* `CollP r cond`: for every renaming `u` that fixes `r` and the registers
  of the block's need and agrees with `unproxy cond` below the end of the
  walk, the renamed ops, from registers where `r` holds an atom `v`, fill the
  block's need for `v` and keep every register outside it, or crash when the
  need does not fit `v`.  The consumer takes `u := unproxy cf` for the final
  `cond` `cf`.
* `collapseGate_ok`: `GateOKD (ProxyFor r) (CollP r) (collapseGate r o)`.
* `walkLazy_okColl`: the walk of `+collapse-lazy-atom` with it.

On the real compiler (`tools/hoon/proxy-dump.hoon`, case `%h`, rerun
2026-11-24) the walk of `[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]` puts
nothing at its own block `0w6` (the need there is `this v3`, `r` itself) and
`[mov proxy v2]` at the lazy block `0w3`, raw `[mov v3 v2]` after unproxying.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## The walk with a property that sees the final `cond` -/

/-- **`WalkOKC` whose property sees the `cond` of the end state.** -/
structure WalkOKD (C : Gen Map → Gen Map → Prop)
    (P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop) (g g' : Gen Map)
    (es : List (Nat × Lazy S)) : Prop where
  bo : g'.bo = g.bo
  drop : g'.drop = g.drop
  le : g.re ≤ g'.re
  cnd : C g g'
  other : ∀ o, o ∉ es.map Prod.fst → HoonMap.get g'.blocks o = HoonMap.get g.blocks o
  at_ : ∀ e ∈ es, ∃ A : List Pole, (∀ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩ →
    HoonMap.get g'.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧ P g'.cond g.re g'.re e.1 e.2.sure A

/-- `P` holds for a wider range of registers and for a `cond` that agrees
below the end of the range. -/
def PMonoD (P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop) : Prop :=
  ∀ (c c' : Map (Nat × List Nat)) lo hi lo' hi' o s A, P c lo hi o s A →
    (∀ k, k < hi → HoonMap.get c' k = HoonMap.get c k) → lo' ≤ lo → hi ≤ hi' → P c' lo' hi' o s A

theorem WalkOKD.nil {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g)
    (P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop) (g : Gen Map) : WalkOKD C P g g [] :=
  ⟨rfl, rfl, Nat.le_refl _, cr g, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

theorem WalkOKD.congr {C : Gen Map → Gen Map → Prop}
    {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} {g g' : Gen Map}
    {es es' : List (Nat × Lazy S)} (h : WalkOKD C P g g' es) (hm : ∀ e, e ∈ es ↔ e ∈ es') : WalkOKD C P g g' es' :=
  ⟨h.bo, h.drop, h.le, h.cnd, fun o ho => h.other o fun hm' => ho (by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm'
      exact List.mem_map.mpr ⟨e, (hm e).mp he, rfl⟩), fun e he => h.at_ e ((hm e).mpr he)⟩

theorem WalkOKD.trans {C : Gen Map → Gen Map → Prop} (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMonoD P) {g g1 g2 : Gen Map}
    {es1 es2 : List (Nat × Lazy S)} (a : WalkOKD C P g g1 es1) (b : WalkOKD C P g1 g2 es2)
    (hd : ∀ x ∈ es1.map Prod.fst, x ∉ es2.map Prod.fst) : WalkOKD C P g g2 (es1 ++ es2) := by
  refine ⟨b.bo.trans a.bo, b.drop.trans a.drop, Nat.le_trans a.le b.le, ct _ _ _ a.cnd b.cnd, fun o ho => ?_,
    fun e he => ?_⟩
  · simp only [List.map_append, List.mem_append, not_or] at ho
    exact (b.other o ho.2).trans (a.other o ho.1)
  · rcases List.mem_append.mp he with h | h
    · obtain ⟨A, hA, hP⟩ := a.at_ e h
      have hn : e.1 ∉ es2.map Prod.fst := hd _ (List.mem_map.mpr ⟨e, h, rfl⟩)
      exact ⟨A, fun B fin hb => (b.other _ hn).trans (hA B fin hb),
        pm _ _ _ _ _ _ _ _ _ hP (cb _ _ b.cnd) (Nat.le_refl _) b.le⟩
    · obtain ⟨A, hA, hP⟩ := b.at_ e h
      have hn : e.1 ∉ es1.map Prod.fst := fun hm => hd _ hm (List.mem_map.mpr ⟨e, h, rfl⟩)
      exact ⟨A, fun B fin hb => hA B fin ((a.other _ hn).trans hb),
        pm _ _ _ _ _ _ _ _ _ hP (fun _ _ => rfl) a.le (Nat.le_refl _)⟩

/-- The gate puts ops at the one block it is given, with `C` between the
states, and its property sees the `cond` it ends with. -/
def GateOKD (C : Gen Map → Gen Map → Prop)
    (P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop)
    (f : Nat → Sure S → CM Map Unit) : Prop :=
  ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map), f o l.sure g = some ((), g') → g.drop = false →
    WalkOKD C P g g' [(o, l)]

mutual
theorem walkLazy_okD {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g)
    (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMonoD P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOKD C P f) : ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map),
    walkLazy f o l g = some ((), g') →
    g.drop = false → (((o, l) :: entries l).map Prod.fst).Nodup → WalkOKD C P g g' ((o, l) :: entries l)
  | o, mk s fk bd, g, g', h, hd, hn => by
    unfold walkLazy at h
    obtain ⟨u, g1, h1, hr⟩ := bind_some h
    have W1 := hf o (mk s fk bd) g g1 h1 hd
    have d1 : g1.drop = false := W1.drop.trans hd
    simp only [entries, List.map_cons, List.map_append, List.nodup_cons, List.mem_append, not_or] at hn ⊢
    split at hr
    · rename_i hfb
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      have h' : some ((), g1) = some ((), g') := hr
      cases h'
      simpa [bondEntries, forkEntries] using W1
    · obtain ⟨u2, g2, h2, h3⟩ := bind_some hr
      have WF := walkForks_okD cr ct cb pm hf fk g1 g2 h2 d1 (List.nodup_append.mp hn.2).2.1
      have WB := walkBonds_okD cr ct cb pm hf bd g2 g' h3 (WF.drop.trans d1) (List.nodup_append.mp hn.2).1
      have W := (W1.trans ct cb pm WF (by
          intro x hx hm; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx; subst hx
          exact hn.1.2 hm)).trans ct cb pm WB (by
          intro x hx hm
          simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
            List.map_append] at hx
          rcases hx with rfl | hx
          · exact hn.1.1 hm
          · exact nodup_disj hn.2 x hm hx)
      exact W.congr fun e => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.append_assoc]
        constructor <;> rintro (h | h | h) <;> simp [h]

theorem walkForks_okD {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g)
    (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMonoD P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOKD C P f) : ∀ (fk : List (ForkE S)) (g g' : Gen Map),
    walkForks f fk g = some ((), g') →
    g.drop = false → ((forkEntries fk).map Prod.fst).Nodup → WalkOKD C P g g' (forkEntries fk)
  | [], g, g', h, _, _ => by
    simp only [walkForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOKD.nil cr P g
  | ((oy, y), (on, n)) :: rest, g, g', h, hd, hn => by
    unfold walkForks at h
    obtain ⟨u1, g1, h1, h⟩ := bind_some h
    obtain ⟨u2, g2, h2, h3⟩ := bind_some h
    simp only [forkEntries, List.map_append] at hn ⊢
    have hn1 := List.nodup_append.mp hn
    have hn2 := List.nodup_append.mp hn1.1
    have Wy := walkLazy_okD cr ct cb pm hf oy y g g1 h1 hd hn2.1
    have Wn := walkLazy_okD cr ct cb pm hf on n g1 g2 h2 (Wy.drop.trans hd) hn2.2.1
    have Wr := walkForks_okD cr ct cb pm hf rest g2 g' h3 (Wn.drop.trans (Wy.drop.trans hd)) hn1.2.1
    refine (Wy.trans ct cb pm Wn (nodup_disj hn1.1)).trans ct cb pm Wr ?_
    simp only [List.map_append]; exact nodup_disj hn

theorem walkBonds_okD {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g)
    (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    (cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)
    {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMonoD P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOKD C P f) : ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map),
    walkBonds f bd g = some ((), g') →
    g.drop = false → ((bondEntries bd).map Prod.fst).Nodup → WalkOKD C P g g' (bondEntries bd)
  | [], g, g', h, _, _ => by
    simp only [walkBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOKD.nil cr P g
  | (o, l) :: rest, g, g', h, hd, hn => by
    unfold walkBonds at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    simp only [bondEntries, List.map_append] at hn ⊢
    have hn1 := List.nodup_append.mp hn
    have Wl := walkLazy_okD cr ct cb pm hf o l g g1 h1 hd hn1.1
    have Wr := walkBonds_okD cr ct cb pm hf rest g1 g' h2 (Wl.drop.trans hd) hn1.2.1
    exact Wl.trans ct cb pm Wr (nodup_disj hn)
end

/-! ## The gate -/

theorem ProxyFor.of_eq {r : Nat} {g g' : Gen Map} (hr : g.re ≤ g'.re) (hc : g'.cond = g.cond) : ProxyFor r g g' :=
  ⟨condFresh_of_eq hr hc, fun k hk => absurd (by rw [hc]) hk⟩

/-- `ProxyFor` keeps the entries of `cond` below the start. -/
theorem ProxyFor.get_lt {r : Nat} {g g' : Gen Map} (h : ProxyFor r g g') {k : Nat} (hk : k < g.re) :
    HoonMap.get g'.cond k = HoonMap.get g.cond k :=
  h.1.get_lt hk

/-- **What the ops of `collapseGate r o` at one block do**, for the `cond`
`cond` of the end of the walk: renamed by any `u` that fixes `r` and the
registers of the block's need and agrees with `unproxy cond` below `hi`, from
registers where `r` holds an atom `v`, they fill the need for `v` and keep
every register outside it, or crash where the need does not fit `v`. -/
def CollP (r : Nat) (cond : Map (Nat × List Nat)) (_lo hi : Nat) (_o : Nat) (sur : Sure S) (ops : List Pole) :
    Prop :=
  ∀ u : Nat → Nat, u r = r → (∀ x, NMem sur.ned x → u x = x) → (∀ x, x < hi → u x = unproxy cond x) →
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map (Option Noun)) (v : Nat), SkaModel.read r R = some (A v) →
    (FitsS sur (A v) → ∃ R', Runs lib O c gul st t (ops.map (renPole u)) R R' ∧ HoldsS sur R' (A v) ∧
      ∀ x, ¬ NMem sur.ned x → SkaModel.read x R' = SkaModel.read x R) ∧
    (¬ FitsS sur (A v) → Crashes lib O c gul st t (ops.map (renPole u)) R)

theorem collP_mono (r : Nat) : PMonoD (CollP (S := S) (Map := Map) r) := by
  intro c c' lo hi lo' hi' o s ops h hc _ hh u hur hus huc
  exact h u hur hus fun x hx => (huc x (Nat.lt_of_lt_of_le hx hh)).trans (by simp only [unproxy, hc x hx])

/-- A need that `+sure-require-look` turns into `this r'` had `r'`: a looked-at
axis other than `1` would make a pair (axis at least `2`) or never fit
(axis `0`). -/
theorem sureOK_this_mem {sur : Sure S} {g0 g1 : Gen Map} {r' : Nat}
    (L : SureOK sur.ned (HoonSet.toList sur.lok) g0 g1 (Need.this r')) : NMem sur.ned r' := by
  have hx : ∀ x ∈ HoonSet.toList sur.lok, x = 1 := by
    intro x hx
    have f := ((L.fits (A 0)).mp trivial).2 x hx
    by_cases h2 : 2 ≤ x
    · rcases L.big ⟨x, hx, h2⟩ with ⟨p, q, e⟩ | ⟨y, p, q, e⟩ <;> cases e
    · have : x = 0 ∨ x = 1 := by omega
      rcases this with rfl | rfl
      · simp [slot?_zero] at f
      · rfl
  rw [← L.same hx]
  rfl

/-- The source of the ops: `r` at the block `o`, a fresh proxy for `r`
elsewhere. -/
theorem collSrc_spec {r o oL src : Nat} {g1 g2 : Gen Map}
    (h : (if oL = o then pure r else proxy r oL : CM Map Nat) g1 = some (src, g2)) (hd : g1.drop = false) :
    ProxyFor r g1 g2 ∧ g2.blocks = g1.blocks ∧ g2.drop = g1.drop ∧ g2.bo = g1.bo ∧ g1.re ≤ g2.re ∧
      (src = r ∨ (src < g2.re ∧ unproxy g2.cond src = r)) := by
  by_cases e : oL = o
  · rw [if_pos e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ProxyFor.refl r g1, rfl, rfl, rfl, Nat.le_refl _, Or.inl rfl⟩
  · rw [if_neg e] at h
    have PF := proxy_proxyFor h
    obtain ⟨e1, e2, e3, e4, -, e6⟩ := proxy_condFresh h
    obtain ⟨tag, -, hu⟩ := e6 hd
    have hbo : g2.bo = g1.bo := by
      unfold proxy at h
      simp only at h
      rw [if_neg (by simp [hd])] at h
      obtain ⟨tag, _, ht⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at ht
      rw [← ht.2]
    exact ⟨PF, e3, e4, hbo, by omega, Or.inr ⟨by omega, hu⟩⟩

/-- The crash case: the need wants parts of the atom. -/
theorem collapseGate_crash {r o oL : Nat} {l : Lazy S} {g g' : Gen Map} {kk : Nat} {ned : Need}
    (L : SureOK l.sure.ned (HoonSet.toList l.sure.lok) g { g with re := kk } ned)
    (hn : ∀ v, ¬ Fits ned (A v)) (hd : g.drop = false)
    (h2 : ((if oL = o then pure r else proxy r oL : CM Map Nat) >>= fun src =>
      crashNeed oL (Sum.inr src) ned) { g with re := kk } = some ((), g')) :
    WalkOKD (ProxyFor r) (CollP (S := S) (Map := Map) r) g g' [(oL, l)] := by
  obtain ⟨src, g2, hs, ha⟩ := bind_some h2
  obtain ⟨PF, hb2, hd2, hbo2, hre2, hsrc⟩ := collSrc_spec hs hd
  simp only [crashNeed] at ha
  obtain ⟨b, hb, rfl⟩ := addOps_spec ha (hd2.trans hd)
  have pf1 : ProxyFor r g { g with re := kk } := ProxyFor.of_eq L.le rfl
  refine ⟨hbo2, hd2, Nat.le_trans L.le hre2, pf1.trans (PF.trans (ProxyFor.of_eq (Nat.le_refl _) rfl)),
    fun o' ho' => ?_, fun e he => ?_⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho'
    rw [HoonMap.get_put, if_neg ho', hb2]
  · simp only [List.mem_singleton] at he
    subst he
    refine ⟨Pole.cel src :: (flattenNeed ned).map (fun x => Pole.imm (A 0) x), fun B fin hb' => ?_, ?_⟩
    · rw [hb2] at hb
      rw [hb] at hb'
      simp only [Option.some.injEq] at hb'
      subst hb'
      simp [HoonMap.get_put]
    · intro u hur _ huc lib σ O c gul st t R v hR
      have us : u src = r := by
        rcases hsrc with e' | ⟨lt, up⟩
        · rw [e']; exact hur
        · rw [huc src lt]; exact up
      refine ⟨fun f => absurd ((fits_sure L _).mpr f) (hn v), fun _ => ?_⟩
      simp only [List.map_cons, renPole, us]
      exact Crashes.append_left (B := List.map (renPole u) _) (crashes_cel hR)

/-- **The gate of `+collapse-lazy-atom`**: it puts ops at the one block it
is given, makes proxies for `r` only, and the ops do what `CollP r` says. -/
theorem collapseGate_ok (r o : Nat) :
    GateOKD (ProxyFor r) (CollP (S := S) (Map := Map) r) (collapseGate (S := S) (Map := Map) r o) := by
  intro oL l g g' h hd
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨kk, e1⟩ := L.gen
  subst e1
  have pf1 : ProxyFor r g { g with re := kk } := ProxyFor.of_eq L.le rfl
  have done0 : (∀ (R : Map (Option Noun)) (v : Nat), SkaModel.read r R = some (A v) → HoldsN ned R (A v)) →
      WalkOKD (ProxyFor r) (CollP (S := S) (Map := Map) r) g { g with re := kk } [(oL, l)] := by
    intro hh
    refine ⟨rfl, rfl, L.le, pf1, fun _ _ => rfl, fun e he => ?_⟩
    simp only [List.mem_singleton] at he
    subst he
    refine ⟨[], fun B fin hb => by simpa using hb, ?_⟩
    intro u _ _ _ lib σ O c gul st t R v hR
    exact ⟨fun _ => ⟨R, Runs.nil R, holdsS_of_sure L (hh R v hR), fun _ _ => rfl⟩,
      fun nf => absurd ((fits_sure L _).mp (fits_of_holds _ (hh R v hR))) nf⟩
  rcases ned with ⟨p, q⟩ | ⟨x, p, q⟩ | r' | _
  · exact collapseGate_crash L (fun v hf => hf) hd h2
  · exact collapseGate_crash L (fun v hf => hf) hd h2
  · simp only at h2
    by_cases e : r = r'
    · rw [if_pos e] at h2
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨-, rfl⟩ := h2
      subst e
      exact done0 fun R v hR => hR
    · rw [if_neg e] at h2
      obtain ⟨src, g2, hs, ha⟩ := bind_some h2
      obtain ⟨PF, hb2, hd2, hbo2, hre2, hsrc⟩ := collSrc_spec hs hd
      obtain ⟨b, hb, rfl⟩ := addOps_spec ha (hd2.trans hd)
      have hr' : NMem l.sure.ned r' := sureOK_this_mem L
      refine ⟨hbo2, hd2, Nat.le_trans L.le hre2, pf1.trans (PF.trans (ProxyFor.of_eq (Nat.le_refl _) rfl)),
        fun o' ho' => ?_, fun e he => ?_⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho'
        rw [HoonMap.get_put, if_neg ho', hb2]
      · simp only [List.mem_singleton] at he
        subst he
        refine ⟨[Pole.mov src r'], fun B fin hb' => ?_, ?_⟩
        · rw [hb2] at hb
          rw [hb] at hb'
          simp only [Option.some.injEq] at hb'
          subst hb'
          simp [HoonMap.get_put]
        · intro u hur hus huc lib σ O c gul st t R v hR
          have us : u src = r := by
            rcases hsrc with e' | ⟨lt, up⟩
            · rw [e']; exact hur
            · rw [huc src lt]; exact up
          have ur : u r' = r' := hus r' hr'
          simp only [List.map_cons, List.map_nil, renPole, us, ur]
          refine ⟨fun _ => ⟨_, runs_mov hR, holdsS_of_sure L (read_store_eq r' _ R),
            fun x hx => read_store_ne (fun e => hx (by rw [e]; exact hr')) _ _⟩,
            fun nf => absurd ((fits_sure L _).mp trivial) nf⟩
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    exact done0 fun _ _ _ => trivial

/-- **The walk of `+collapse-lazy-atom`**: every block of the walk gets ops
that do what `CollP r` says for the `cond` the walk ends with, and `cond`
grew only by proxies for `r`. -/
theorem walkLazy_okColl {r o : Nat} (oL : Nat) (l : Lazy S) (g g' : Gen Map)
    (h : walkLazy (collapseGate r o) oL l g = some ((), g')) (hd : g.drop = false)
    (hn : (((oL, l) :: entries l).map Prod.fst).Nodup) :
    WalkOKD (ProxyFor r) (CollP (S := S) (Map := Map) r) g g' ((oL, l) :: entries l) :=
  walkLazy_okD (ProxyFor.refl r) (fun _ _ _ a b => ProxyFor.trans a b) (fun _ _ h _ hk => ProxyFor.get_lt h hk)
    (collP_mono r) (collapseGate_ok r o) oL l g g' h hd hn

/-- **The ops of the gate, unproxied by the final `cond`, fill the block's
need from the widened input need** `pair ned (this r)` holding `[s0 v]`:
the consumer's form of `CollP`, for a final `cond` `cf` that agrees with the
walk's below its end and has no entry at `r` nor at the registers of the
block's need. -/
theorem collP_fillSem {r : Nat} {cond cf : Map (Nat × List Nat)} {lo hi o : Nat} {sur : Sure S}
    {ops : List Pole} (h : CollP (Map := Map) r cond lo hi o sur ops) (hr : HoonMap.get cf r = Option.none)
    (hs : ∀ x, NMem sur.ned x → HoonMap.get cf x = Option.none)
    (hc : ∀ k, k < hi → HoonMap.get cf k = HoonMap.get cond k)
    (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (ned : Need) (lo' : Nat) (s0 : Noun) (v : Nat) :
    FillSem lib O c gul st t (Need.pair ned (Need.this r)) lo' sur (ops.map (renPole (unproxy cf))) (C s0 (A v))
      (A v) := by
  intro R hR
  obtain ⟨S1, S2⟩ := h (unproxy cf) (by simp [unproxy, hr]) (fun x hx => by simp [unproxy, hs x hx])
    (fun x hx => by simp only [unproxy, hc x hx]) lib σ O c gul st t R v hR.2
  exact ⟨fun f => by
    obtain ⟨R', a, b, k⟩ := S1 f
    exact ⟨R', a, b, fun x _ hn => k x hn⟩, S2⟩

end Comp
end SkaModel
end Formalization
