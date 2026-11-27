import lemmas.Compiler.PokeLinkLoopCut
import lemmas.Compiler.PokeLinkLoop
import lemmas.Compiler.PokeLinkRestNew
import lemmas.Hoon.JabBy
import lemmas.Compiler.TreapSet
import lemmas.Run

/-!
# The SCC loop of `+ska-poke` in the pill (track P, README Gaps 23)

`srLoop` (cut in `PokeLinkLoopCut.lean`) on the loop's subject `lpS q c`
(`q` the noun of `sccs`, `c` that of `code.lon`), against the noun-level
model `accLoop` of this file: the accumulator is a map `FinMap Bell Noun`
(its noun `.toNoun id`, the value of a bell the noun `[nomm pure total]`).

* `jabF_toNoun`: `+jab:by` keeps the canonical treap noun (as `putF_toNoun`
  does for `+put:by`, both from `isMap_ext`).
* `lp_g1`: the gate of `loc1` on `[b acc]` puts `[nomm | |]`, the nomm of
  `b` in `new-code`.
* `lp_g2`: the gate of `loc2` on `[b acc]` writes the flags of
  `+eval-finalized`, from the leaf `EvalFinAt` (the arm `0x57de` of `ana`,
  1,066 cells, against `efGo`).
* `lp_loc1`, `lp_loc2`: the two `~(rep in scc)` folds, in `rap` order.
* `lp_trap`: the trap over `sccs`, against `accLoop`.
* `lp_run`: `srLoop` on `lpS q c`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

/-! ## `+jab:by` and `+rep:in` on the canonical nouns -/

/-- `+jab:by` with a gate that need only work on the value at the key
(`jab_gate_at` of `CompSect.lean`, restated here). -/
theorem jab_gate_at' {mug : Noun → Nat} (c : Noun) (hc : GorIn mug c) (B key fp fs fc : Noun)
    (g : Noun → Noun) (v : Noun) (hg : nock (C fp (C v fc)) fp = some (g v)) :
    ∀ (a out : Noun), getF mug key a = some (C (A 0) v) → jabF mug key g a = some out →
      nock (C by.jab.battery (C (C key (C fp (C fs fc))) (C B (C a c)))) by.jab.battery = some out := by
  intro a
  have hgor := gor_gate (mug := mug) c hc.2
  have hgo := hc.1
  fun_induction jabF mug key g a
  all_goals intro out hv h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals simp [getF, *] at hv
  all_goals first
    | (cases h
       subst hv
       nock_open by.jab.battery
       simp [nock_exec, *]
       done)
    | (nock_open by.jab.battery
       simp_all [nock_exec])

/-- The arm `+jab:by` on a door whose map is a node (`jab_arm_node` of
`OptLinkAlBodyLoc.lean`, restated here). -/
theorem jab_arm_node' (B c p q l r : Noun) :
    nock (C B (C (C (C p q) (C l r)) c)) by.jab.arm
      = some (C by.jab.battery (C (C p (C (C (A 0) (A 15)) (C q (C q q)))) (C B (C (C (C p q) (C l r)) c)))) := by
  nock_open by.jab.arm; simp [nock_exec]

/-- A map noun with a pair in it is a node. -/
theorem node_of_getF {mug : Noun → Nat} {k t v : Noun} (hm : IsMap mug t) (h : getF mug k t = some (C (A 0) v)) :
    ∃ p q l r, t = C (C p q) (C l r) := by
  cases hm with
  | nil => simp [getF] at h
  | node => exact ⟨_, _, _, _, rfl⟩

namespace FinMap

variable {κ ν : Type} [DecidableEq κ] [TKey κ]

/-- **`+jab:by` keeps the canonical noun**: on the noun of `m`, at a key
with value `v`, a gate that maps `f v` to `f w` gives the noun of
`m.put k w`. -/
theorem jabF_toNoun (f : ν → Noun) (m : FinMap κ ν) (k : κ) {v w : ν} (g : Noun → Noun)
    (hv : m.get k = some v) (hg : g (f v) = f w) :
    jabF mugF (TKey.enc k) g (m.toNoun f) = some ((m.put k w).toNoun f) := by
  have hget : Get (m.toNoun f) (TKey.enc k) (f v) := (get_toNoun f m _ _).2 ⟨k, v, hv, rfl, rfl⟩
  obtain ⟨out, hp, hm, hg'⟩ := jabF_spec (TKey.enc k) g (isMap_toNoun f m) hget
  rw [hp, isMap_ext hm (isMap_toNoun f (m.put k w))]
  intro kn vn
  rw [hg', get_toNoun, get_toNoun, hg]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hne, k', v', h1, rfl, rfl⟩)
    · exact ⟨k, w, by simp [put], rfl, rfl⟩
    · refine ⟨k', v', ?_, rfl, rfl⟩
      have : k' ≠ k := fun e => hne (e ▸ rfl)
      simp [put, this, h1]
  · rintro ⟨k', v', h1, rfl, rfl⟩
    by_cases e : k' = k
    · subst e; simp only [put, if_true, Option.some.injEq] at h1; subst h1; exact Or.inl ⟨rfl, rfl⟩
    · simp only [put, e, if_false] at h1
      exact Or.inr ⟨fun h => e (TKey.enc_inj _ _ h), k', v', h1, rfl, rfl⟩

/-- The pre-order of `+rep:in` on the noun of a set lists its `rap`. -/
theorem preorder_setNoun' (m : FinMap κ Unit) :
    preorder m.setNoun = m.rap.map fun e => TKey.enc e.1 := by
  apply map_cell_inj (A 0)
  rw [← preorder_toMap, toMap_setNoun, preorder_toNoun, List.map_map]
  rfl

end FinMap


/-! ## `+rep` with a gate that may crash -/

/-- A fold that may crash. -/
def foldO {σ α : Type} (f : α → σ → Option σ) : List α → σ → Option σ
  | [], s => some s
  | x :: l, s => (f x s).bind (foldO f l)

theorem foldO_append {σ α : Type} (f : α → σ → Option σ) (l1 l2 : List α) (s : σ) :
    foldO f (l1 ++ l2) s = (foldO f l1 s).bind (foldO f l2) := by
  induction l1 generalizing s with
  | nil => rfl
  | cons x l ih =>
    simp only [List.cons_append, foldO]
    cases f x s with
    | none => rfl
    | some t => exact ih t

theorem foldO_map {σ α β : Type} (f : β → σ → Option σ) (g : α → β) (l : List α) (s : σ) :
    foldO f (l.map g) s = foldO (fun x s => f (g x) s) l s := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, foldO]; cases f (g x) s <;> simp [ih]

/-- The loop of `+rep` with a gate that may crash: where the fold returns,
the loop returns its noun. -/
theorem rep_loop_opt {σ : Type} (toN : σ → Noun) (gf : Noun → σ → Option σ) (B ctx bp e bc : Noun) :
    ∀ (a : Noun), Tree a → ∀ (s s' : σ), foldO gf (preorder a) s = some s' →
    (∀ x ∈ preorder a, ∀ s t, gf x s = some t → nock (C bp (C (C x (toN s)) bc)) bp = some (toN t)) →
    nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e (toN s)) bc)) (C B (C a ctx)))))
      by.rep.loop = some (toN s') := by
  intro a ha
  induction ha with
  | nil =>
    intro s s' h _
    simp only [preorder, foldO, Option.some.injEq] at h
    subst h
    nock_open by.rep.loop
    simp [nock_exec]
  | @node n l r _ _ ihl ihr =>
    intro s s' h hf
    simp only [preorder, foldO] at h
    cases h1 : gf n s with
    | none => rw [h1] at h; cases h
    | some t1 =>
      rw [h1, Option.bind_some, foldO_append] at h
      cases h2 : foldO gf (preorder l) t1 with
      | none => rw [h2] at h; cases h
      | some t2 =>
        rw [h2, Option.bind_some] at h
        have hn := hf n (by simp [preorder]) s t1 h1
        have hl := ihl t1 t2 h2 (fun x hx s t => hf x (by simp [preorder, hx]) s t)
        have hr := ihr t2 s' h (fun x hx s t => hf x (by simp [preorder, hx]) s t)
        nock_open by.rep.loop
        simp [nock_exec, hn, hl, hr]

/-- `+rep` with a gate that may crash. -/
theorem rep_gate_opt {σ : Type} (toN : σ → Noun) (gf : Noun → σ → Option σ) (B ctx bp e bc : Noun)
    (a : Noun) (ha : Tree a) (s s' : σ) (h : foldO gf (preorder a) s = some s')
    (hf : ∀ x ∈ preorder a, ∀ s t, gf x s = some t → nock (C bp (C (C x (toN s)) bc)) bp = some (toN t)) :
    nock (C by.rep.battery (C (C bp (C (C e (toN s)) bc)) (C B (C a ctx)))) by.rep.battery = some (toN s') := by
  nock_open by.rep.battery
  simp only [nock_exec, rep_loop_opt toN gf B ctx bp e bc a ha s s' h hf]

/-! ## The noun-level model of the loop -/

/-- The flags of an entry `[nomm pure total]` (loobeans). -/
def decF : Noun → Option (Bool × Bool)
  | Noun.cell _ (Noun.cell (Noun.atom a) (Noun.atom t)) =>
    if a ≤ 1 ∧ t ≤ 1 then some (decide (a = 0), decide (t = 0)) else none
  | _ => none

/-- The flag table `+eval-finalized` reads from an accumulator. -/
noncomputable def accFt (M : FinMap Bell Noun) : FlagTab := fun c => (M.get c).bind decF

/-- The step of `loc1`: `b` put to `[nomm | |]`, the nomm from `new-code`. -/
noncomputable def st1 (nc : FinMap Bell (VarEntry FinMap)) (b : Bell) (M : FinMap Bell Noun) :
    Option (FinMap Bell Noun) :=
  (nc.get b).map fun e => M.put b (C e.nomm.toNoun (C (A 1) (A 1)))

open Classical in
/-- The step of `loc2`: `b`'s entry (with the nomm of `new-code`) gets the
flags of `+eval-finalized` on the accumulator. -/
noncomputable def st2 (nc : FinMap Bell (VarEntry FinMap)) (b : Bell) (M : FinMap Bell Noun) :
    Option (FinMap Bell Noun) :=
  (nc.get b).bind fun e =>
    if ∃ fb, M.get b = some (C e.nomm.toNoun fb) then
      (efGo (accFt M) b.less e.nomm).map fun r => M.put b (C e.nomm.toNoun (flagNoun r.2))
    else none

/-- One SCC: `loc1` then `loc2`, members in the given order. -/
noncomputable def accStep (nc : FinMap Bell (VarEntry FinMap)) (M : FinMap Bell Noun) (L : List Bell) :
    Option (FinMap Bell Noun) :=
  (foldO (st1 nc) L M).bind (foldO (st2 nc) L)

/-- **The loop on the accumulator**, SCC by SCC. -/
noncomputable def accLoop (nc : FinMap Bell (VarEntry FinMap)) (M : FinMap Bell Noun) :
    List (List Bell) → Option (FinMap Bell Noun)
  | [] => some M
  | L :: Ls => (accStep nc M L).bind fun M' => accLoop nc M' Ls

/-- **The leaf on `+eval-finalized`** (arm `0x57de` of `ana`, 1,066 cells):
the call `lpEf` (`(eval-finalized b acc)`: the arm pulled from `ana` at axis
`0x1fffff` of the subject, slammed on `[b acc]` at axes `28`, `29`), on an
accumulator `M` that holds `b` with the nomm `n`, where the model's trap
`efGo` on the flags of `M` returns, returns its flags `[pure total]`. -/
def EvalFinAt : Prop :=
  ∀ (M : FinMap Bell Noun) (b : Bell) (n : Nomm) (fb : Noun) (rr : Sock × Bool × Bool) (G0 Y : Noun),
    M.get b = some (C n.toNoun fb) → efGo (accFt M) b.less n = some rr →
    slot? 0x1fffff (C G0 (C (C (TKey.enc b) (M.toNoun id)) Y)) = some ana →
    nock (C G0 (C (C (TKey.enc b) (M.toNoun id)) Y)) lpEf = some (flagNoun rr.2)

/-! ## The subjects of the loop -/

section Loop

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
  (ncN bakedN vr : Noun)

/-- The subject of `srLoop`: `[sccs [new-code [baked spine]]]` with the
noun `q` of `sccs` and `c` of `code.lon`. -/
noncomputable def lpS (q c : Noun) : Noun :=
  C q (C ncN (C bakedN (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r c vr)))

/-- The trap `scc-loop`: `[lpBat2 [lpBat (lpS q c)]]`. -/
noncomputable def lpC2 (q c : Noun) : Noun :=
  C lpBat2 (C lpBat (lpS root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c))

/-- The noun of `lon` with `code.lon = c`. -/
noncomputable def lpLon (c : Noun) : Noun :=
  C (C r1 (C r2 (C r3 (C r4 jRest)))) (C (memoNoun r.2.2.1) (C c (C callsN (C vr seekN))))

set_option maxHeartbeats 1000000 in
/-- **The gate of `loc1`** on `[b acc]`: `acc` with `b` put to `[nomm | |]`,
the nomm of `b` in `new-code`. -/
theorem lp_g1 (nc : FinMap Bell (VarEntry FinMap)) (b : Bell) (e : VarEntry FinMap) (he : nc.get b = some e)
    (s q c : Noun) (M : FinMap Bell Noun) :
    nock (C lpG1 (C (C (TKey.enc b) (M.toNoun id)) (C s
        (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r (nc.toNoun varEntryNoun) bakedN vr q c))))
      lpG1 = some ((M.put b (C e.nomm.toNoun (C (A 1) (A 1)))).toNoun id) := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hget : getF mugF (TKey.enc b) (nc.toNoun varEntryNoun) = some (C (A 0) (varEntryNoun e)) := by
    rw [FinMap.getF_toNoun, he]; rfl
  have hgot := got_gate layer2 hgc (TKey.enc b) _ _ hget
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (TKey.enc b) (C e.nomm.toNoun (C (A 1) (A 1)))
    (M.toNoun id) _ (FinMap.putF_toNoun id M b _)
  unfold lpG1
  simp [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.got.arm_at, got_arm,
    by.put.arm_at, put_arm, hgot, hput, varEntryNoun]


/-- The bunt of `bell` the gates' samples start from (arm `382` of the tail
of `ana`). -/
def lpBellF : Noun := C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 3)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

noncomputable def lpBell : Noun := (evalFuel 2000 ana lpBellF).getD (A 0)

theorem lp_bell : nock ana lpBellF = some lpBell := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- The gate of `+jab:by` in `lpJab`: `code-entry(pure pure, total total)`. -/
def lpJabG (pt : Noun) : Noun → Noun
  | Noun.cell h _ => C h pt
  | x => x

set_option maxHeartbeats 2000000 in
/-- **The gate of `loc2`** on `[b acc]`: `b`'s entry gets the flags of
`+eval-finalized` (the leaf `EvalFinAt`), by `+jab:by`. -/
theorem lp_g2 (hE : EvalFinAt) (b : Bell) (n : Nomm) (fb : Noun) (rr : Sock × Bool × Bool) (M : FinMap Bell Noun)
    (hb : M.get b = some (C n.toNoun fb)) (he : efGo (accFt M) b.less n = some rr) (l1 s q c : Noun) :
    nock (C lpG2 (C (C (TKey.enc b) (M.toNoun id)) (C l1 (C s
        (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c))))) lpG2 =
      some ((M.put b (C n.toNoun (flagNoun rr.2))).toNoun id) := by
  have hef := hE M b n fb rr lpG2 (C l1 (C s
      (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c))) hb he
    (by simp [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, nock_exec])
  have hget : getF mugF (TKey.enc b) (M.toNoun id) = some (C (A 0) (C n.toNoun fb)) := by
    rw [FinMap.getF_toNoun, hb]; rfl
  have hjF := FinMap.jabF_toNoun id M b (lpJabG (flagNoun rr.2)) hb (w := C n.toNoun (flagNoun rr.2)) rfl
  have hjab := jab_gate_at' layer2 gorIn_morIn_layer2.1 by.battery (TKey.enc b)
    (C (A 10) (C (C (A 3) (C (C (A 0) (A 28)) (C (A 0) (A 29)))) (C (A 0) (A 6))))
    (C (C (A 0) (A 0)) (C (A 0) (A 0)))
    (C (flagNoun rr.2) (C lpG2 (C (C (TKey.enc b) (M.toNoun id)) (C l1 (C s
        (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c))))))
    (lpJabG (flagNoun rr.2)) (C n.toNoun fb) (by simp [nock_exec, lpJabG, flagNoun]) _ _ hget hjF
  simp only [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, flagNoun] at hjab
  obtain ⟨p0, q0, l0, r0, hN⟩ := node_of_getF (FinMap.isMap_toNoun id M) hget
  have hja := jab_arm_node' by.battery layer2 p0 q0 l0 r0
  rw [← hN] at hja
  nock_open lpG2
  rw [nock_op8, hef, Option.bind_some]
  unfold lpJab
  simp [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.jab.arm_at,
    hja, hjab, flagNoun]

end Loop

end Compiler
end Formalization
