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

/-- A step on bells run on the nouns of the set's pre-order. -/
noncomputable def onKey (g : Bell → FinMap Bell Noun → Option (FinMap Bell Noun)) (x : Noun) (M : FinMap Bell Noun) :
    Option (FinMap Bell Noun) :=
  match FinMap.decode? (κ := Bell) x with
  | some b => g b M
  | none => none

theorem foldO_onKey (g : Bell → FinMap Bell Noun → Option (FinMap Bell Noun)) (S : FinMap Bell Unit)
    (M : FinMap Bell Noun) :
    foldO (onKey g) (preorder S.setNoun) M = foldO g (S.rap.map Prod.fst) M := by
  rw [FinMap.preorder_setNoun', foldO_map, foldO_map]
  congr 1
  funext x s
  simp [onKey, FinMap.decode?_enc]

theorem mem_onKey {g : Bell → FinMap Bell Noun → Option (FinMap Bell Noun)} {S : FinMap Bell Unit} {x : Noun}
    (hx : x ∈ preorder S.setNoun) {s t : FinMap Bell Noun} (h : onKey g x s = some t) :
    ∃ b, x = TKey.enc b ∧ g b s = some t := by
  rw [FinMap.preorder_setNoun'] at hx
  obtain ⟨⟨b, u⟩, _, rfl⟩ := List.mem_map.1 hx
  exact ⟨b, rfl, by simpa [onKey, FinMap.decode?_enc] using h⟩

set_option maxHeartbeats 2000000 in
/-- **`loc1`**: `~(rep in scc)` from `code.lon` with the gate of `loc1`. -/
theorem lp_loc1 (nc : FinMap Bell (VarEntry FinMap)) (S : FinMap Bell Unit) (M M1 : FinMap Bell Noun)
    (h : foldO (st1 nc) (S.rap.map Prod.fst) M = some M1) (q : Noun) :
    nock (C S.setNoun (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r (nc.toNoun varEntryNoun)
        bakedN vr q (M.toNoun id))) lpLoc1 = some (M1.toNoun id) := by
  have hf : ∀ x ∈ preorder S.setNoun, ∀ s t, onKey (st1 nc) x s = some t →
      nock (C lpG1 (C (C x (s.toNoun id)) (C S.setNoun (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN
        gr r (nc.toNoun varEntryNoun) bakedN vr q (M.toNoun id))))) lpG1 = some (t.toNoun id) := by
    intro x hx s t ht
    obtain ⟨b, rfl, hb⟩ := mem_onKey hx ht
    simp only [st1] at hb
    cases he : nc.get b with
    | none => rw [he] at hb; cases hb
    | some e =>
      rw [he] at hb
      cases hb
      exact lp_g1 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r bakedN vr nc b e he _ _ _ s
  have hr := rep_gate_opt (fun M : FinMap Bell Noun => M.toNoun id) (onKey (st1 nc)) in.battery layer2 lpG1
    lpBell _ S.setNoun (Tree.of_isSet (FinMap.isSet_setNoun S)) M M1 (by rw [foldO_onKey]; exact h) hf
  have hb := lp_bell
  unfold lpBellF at hb
  simp [nock_exec] at hb
  simp only [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0] at hr
  unfold lpLoc1 lpDoor1 lpBunt1
  simp [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2, in.arm_at, in_arm, in.rep.arm_at, rep_arm,
    hb, hr]

set_option maxHeartbeats 2000000 in
/-- **`loc2`**: `~(rep in scc)` from `loc1` with the gate of `loc2`. -/
theorem lp_loc2 (hE : EvalFinAt) (nc : FinMap Bell (VarEntry FinMap)) (S : FinMap Bell Unit) (M1 M2 : FinMap Bell Noun)
    (h : foldO (st2 nc) (S.rap.map Prod.fst) M1 = some M2) (q c : Noun) :
    nock (C (M1.toNoun id) (C S.setNoun (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN
        bakedN vr q c))) lpLoc2 = some (M2.toNoun id) := by
  have hf : ∀ x ∈ preorder S.setNoun, ∀ s t, onKey (st2 nc) x s = some t →
      nock (C lpG2 (C (C x (s.toNoun id)) (C (M1.toNoun id) (C S.setNoun (lpC2 root r1 r2 r3 r4 jRest codeN callsN
        varsN seekN hotN gr r ncN bakedN vr q c))))) lpG2 = some (t.toNoun id) := by
    intro x hx s t ht
    obtain ⟨b, rfl, hb⟩ := mem_onKey hx ht
    simp only [st2] at hb
    cases he : nc.get b with
    | none => rw [he] at hb; cases hb
    | some e =>
      rw [he, Option.bind_some] at hb
      by_cases hx : ∃ fb, s.get b = some (C e.nomm.toNoun fb)
      · rw [if_pos hx] at hb
        obtain ⟨fb, hfb⟩ := hx
        cases hg : efGo (accFt s) b.less e.nomm with
        | none => rw [hg] at hb; cases hb
        | some rr =>
          rw [hg] at hb
          cases hb
          exact lp_g2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr hE b e.nomm fb rr s
            hfb hg _ _ _ _
      · rw [if_neg hx] at hb; cases hb
  have hr := rep_gate_opt (fun M : FinMap Bell Noun => M.toNoun id) (onKey (st2 nc)) in.battery layer2 lpG2
    lpBell _ S.setNoun (Tree.of_isSet (FinMap.isSet_setNoun S)) M1 M2 (by rw [foldO_onKey]; exact h) hf
  have hb := lp_bell
  unfold lpBellF at hb
  simp [nock_exec] at hb
  simp only [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0] at hr
  unfold lpLoc2 lpDoor2 lpBunt2
  simp [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2, in.arm_at, in_arm, in.rep.arm_at, rep_arm,
    hb, hr]

set_option maxHeartbeats 2000000 in
/-- **The branch of a nonempty `sccs`**: `scc` pushed, `loc1`, `loc2`, then
`code.lon` written and the trap run on `t.sccs`. -/
theorem lp_no (s q' c l1 l2 : Noun)
    (h1 : nock (C s (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr (C s q') c))
      lpLoc1 = some l1)
    (h2 : nock (C l1 (C s (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr (C s q') c)))
      lpLoc2 = some l2) :
    nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr (C s q') c) lpNo =
      nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q' l2) lpBat2 := by
  have hs : nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr (C s q') c)
      (C (A 0) (A 28)) = some s := by
    simp [lpC2, lpS, nock_exec]
  nock_open lpNo
  rw [nock_op8, hs, Option.bind_some, nock_op8, h1, Option.bind_some, nock_op8, h2, Option.bind_some]
  unfold lpTail
  simp [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, nock_exec]

set_option maxHeartbeats 1000000 in
/-- The trap on a nonempty `sccs` takes the branch `lpNo`. -/
theorem lp_cons (s q' c : Noun) :
    nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr (C s q') c) lpBat2 =
      nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr (C s q') c) lpNo := by
  have e : lpBat2 = C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14))))
      (C (C (A 0) (A 0x7fffa)) lpNo)))) := rfl
  conv => lhs; arg 2; rw [e]
  simp [lpC2, lpS, nock_exec]

set_option maxHeartbeats 1000000 in
/-- The trap on an empty `sccs` returns `lon`. -/
theorem lp_nil (c : Noun) :
    nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr (A 0) c) lpBat2 =
      some (lpLon r1 r2 r3 r4 jRest callsN seekN r vr c) := by
  have e : lpBat2 = C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14))))
      (C (C (A 0) (A 0x7fffa)) lpNo)))) := rfl
  conv => lhs; arg 2; rw [e]
  simp [lpC2, lpS, srSp, srS3x, srS0, spAfter, spT0, lpLon, nock_exec]

/-- **The trap `scc-loop`** against `accLoop`: on the noun of a list of SCC
sets and the noun of an accumulator `M`, where the model's loop returns
`M'`, the trap returns `lon` with `code.lon` the noun of `M'`. -/
theorem lp_trap (hE : EvalFinAt) (nc : FinMap Bell (VarEntry FinMap)) :
    ∀ (Ls : List (FinMap Bell Unit)) (M M' : FinMap Bell Noun),
    accLoop nc M (Ls.map fun S => S.rap.map Prod.fst) = some M' →
    nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r (nc.toNoun varEntryNoun) bakedN vr
        (listNoun FinMap.setNoun Ls) (M.toNoun id)) lpBat2 =
      some (lpLon r1 r2 r3 r4 jRest callsN seekN r vr (M'.toNoun id))
  | [], M, M', h => by
    simp only [List.map_nil, accLoop, Option.some.injEq] at h
    subst h
    exact lp_nil root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r _ bakedN vr _
  | S :: Ls, M, M', h => by
    simp only [List.map_cons, accLoop, accStep] at h
    cases h1 : foldO (st1 nc) (S.rap.map Prod.fst) M with
    | none => rw [h1] at h; cases h
    | some M1 =>
      rw [h1, Option.bind_some] at h
      cases h2 : foldO (st2 nc) (S.rap.map Prod.fst) M1 with
      | none => rw [h2] at h; cases h
      | some M2 =>
        rw [h2, Option.bind_some] at h
        simp only [listNoun]
        rw [lp_cons, lp_no root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r _ bakedN vr _ _ _ _ _
          (lp_loc1 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r bakedN vr nc S M M1 h1 _)
          (lp_loc2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r _ bakedN vr hE nc S M1 M2 h2 _ _)]
        exact lp_trap hE nc Ls M2 M' h

set_option maxHeartbeats 2000000 in
/-- **`srLoop`** on the loop's subject: where the trap returns `lon` with
code `c'`, the loop writes it back. -/
theorem lp_run (q c c' : Noun)
    (h : nock (lpC2 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c) lpBat2 =
      some (lpLon r1 r2 r3 r4 jRest callsN seekN r vr c')) :
    nock (lpS root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c) srLoop =
      some (lpS root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c') := by
  have hb : nock (C lpBat (lpS root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r ncN bakedN vr q c)) lpBat =
      some (lpLon r1 r2 r3 r4 jRest callsN seekN r vr c') := by
    nock_open lpBat
    simp only [nock_exec]
    exact h
  rw [srLoop_cut]
  unfold lpTop lpF
  simp only [lpS, srSp, srS3x, srS0, spAfter, spT0, lpLon] at hb ⊢
  simp [nock_exec, hb]

end Loop

/-! ## `accLoop` against the model's loop `sccLoop` -/

section Model

variable {T nc T' : FinMap Bell (VarEntry FinMap)}

theorem get_put' {ν : Type} (m : FinMap Bell ν) (k c : Bell) (v : ν) :
    FinMap.get (m.put k v) c = if c = k then some v else FinMap.get m c := by
  simp [FinMap.put, FinMap.get]

/-- **The accumulator against the model**: the keys `K` hold their nomm in
`T'` and the flags `ft`; the others are absent, with no flags. -/
def AccInv (T' : FinMap Bell (VarEntry FinMap)) (K : Bell → Prop) (M : FinMap Bell Noun) (ft : FlagTab) : Prop :=
  ∀ c, (K c → ∃ e p, FinMap.get T' c = some e ∧ ft c = some p ∧ FinMap.get M c = some (C e.nomm.toNoun (flagNoun p))) ∧
    (¬ K c → FinMap.get M c = none ∧ ft c = none)

theorem accInv_congr {K K' : Bell → Prop} {M : FinMap Bell Noun} {ft ft' : FlagTab} (hK : ∀ c, K c ↔ K' c)
    (hf : ∀ c, ft c = ft' c) (h : AccInv T' K M ft) : AccInv T' K' M ft' := by
  intro c
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨e, p, h1, h2, h3⟩ := (h c).1 ((hK c).2 hk); exact ⟨e, p, h1, (hf c) ▸ h2, h3⟩
  · obtain ⟨h1, h2⟩ := (h c).2 (fun h' => hk ((hK c).1 h')); exact ⟨h1, (hf c) ▸ h2⟩

theorem decF_flag (n : Noun) (p : Bool × Bool) : decF (C n (flagNoun p)) = some p := by
  obtain ⟨a, b⟩ := p; cases a <;> cases b <;> rfl

theorem accFt_of {K : Bell → Prop} {M : FinMap Bell Noun} {ft : FlagTab} (h : AccInv T' K M ft) : accFt M = ft := by
  funext c
  unfold accFt
  by_cases hk : K c
  · obtain ⟨e, p, -, hp, hm⟩ := (h c).1 hk; rw [hm, hp]; simp [decF_flag]
  · obtain ⟨hm, hf⟩ := (h c).2 hk; rw [hm, hf]; rfl

open Classical in
theorem st1_fold (hA : AddsTo T nc T') : ∀ (L : List Bell) (K : Bell → Prop) (M : FinMap Bell Noun) (ft : FlagTab),
    L.Nodup → (∀ b ∈ L, ¬ K b ∧ ∃ e, FinMap.get nc b = some e) → AccInv T' K M ft →
    ∃ M1, foldO (st1 nc) L M = some M1 ∧
      AccInv T' (fun c => K c ∨ c ∈ L) M1 (fun c => if c ∈ L then some (false, false) else ft c)
  | [], K, M, ft, _, _, h => ⟨M, rfl, accInv_congr (fun c => by simp) (fun c => by simp) h⟩
  | x :: L, K, M, ft, hd, hL, h => by
    obtain ⟨hxK, e, he⟩ := hL x List.mem_cons_self
    have hT' := (hA.new x e he).2
    have h1 : AccInv T' (fun c => K c ∨ c = x) (M.put x (C e.nomm.toNoun (C (A 1) (A 1))))
        (fun c => if c = x then some (false, false) else ft c) := by
      intro c
      refine ⟨fun hk => ?_, fun hk => ?_⟩
      · by_cases hc : c = x
        · subst hc; exact ⟨e, (false, false), hT', by simp, by rw [get_put']; simp; rfl⟩
        · obtain ⟨e', p, h1, h2, h3⟩ := (h c).1 (hk.resolve_right hc)
          exact ⟨e', p, h1, by simp [hc, h2], by rw [get_put', if_neg hc]; exact h3⟩
      · have hc : c ≠ x := fun e => hk (Or.inr e)
        obtain ⟨h1, h2⟩ := (h c).2 (fun h' => hk (Or.inl h'))
        exact ⟨by rw [get_put', if_neg hc]; exact h1, by simp [hc, h2]⟩
    have hd' := List.nodup_cons.1 hd
    obtain ⟨M1, hf, hinv⟩ := st1_fold hA L (fun c => K c ∨ c = x) _ _ hd'.2
      (fun b hb => ⟨fun h' => h'.elim (hL b (List.mem_cons_of_mem _ hb)).1 (fun e => hd'.1 (e ▸ hb)),
        (hL b (List.mem_cons_of_mem _ hb)).2⟩) h1
    refine ⟨M1, ?_, accInv_congr (fun c => ?_) (fun c => ?_) hinv⟩
    · simp only [foldO, st1, he, Option.map_some, Option.bind_some]; exact hf
    · simp only [List.mem_cons, or_assoc]
    · by_cases h1 : c ∈ L
      · simp [h1]
      · by_cases h2 : c = x
        · subst h2; simp [h1]
        · simp [h1, h2]

theorem foldl_none {α β : Type} (f : β → α → Option β) (L : List α) :
    L.foldl (fun acc b => acc.bind fun g => f g b) none = none := by
  induction L with
  | nil => rfl
  | cons x L ih => exact ih

theorem st2_fold (hA : AddsTo T nc T') : ∀ (L : List Bell) (K : Bell → Prop) (M : FinMap Bell Noun) (f G : FlagTab),
    (∀ b ∈ L, K b ∧ ∃ e, FinMap.get nc b = some e) → AccInv T' K M f →
    L.foldl (fun acc b => acc.bind fun f => (evalFin (nmOf T') f b).map fun pt =>
      fun c => if c = b then some pt else f c) (some f) = some G →
    ∃ M2, foldO (st2 nc) L M = some M2 ∧ AccInv T' K M2 G
  | [], K, M, f, G, _, h, hG => by
    simp only [List.foldl_nil, Option.some.injEq] at hG
    subst hG; exact ⟨M, rfl, h⟩
  | x :: L, K, M, f, G, hL, h, hG => by
    obtain ⟨hxK, e, he⟩ := hL x List.mem_cons_self
    have hT' := (hA.new x e he).2
    obtain ⟨e', p, h1, h2, h3⟩ := (h x).1 hxK
    rw [hT', Option.some.injEq] at h1
    subst h1
    simp only [List.foldl_cons, Option.bind_some] at hG
    unfold evalFin at hG
    simp only [nmOf, hT', Option.map_some, Option.bind_some] at hG
    cases hr : efGo f x.less e.nomm with
    | none => rw [hr] at hG; simp only [Option.map_none] at hG; rw [foldl_none] at hG; cases hG
    | some rr =>
      rw [hr] at hG
      simp only [Option.map_some, Option.map_some] at hG
      have h1 : AccInv T' K (M.put x (C e.nomm.toNoun (flagNoun rr.2)))
          (fun c => if c = x then some rr.2 else f c) := by
        intro c
        refine ⟨fun hk => ?_, fun hk => ?_⟩
        · by_cases hc : c = x
          · subst hc; exact ⟨e, rr.2, hT', by simp, by rw [get_put']; simp⟩
          · obtain ⟨e', p, h1, h2, h3⟩ := (h c).1 hk
            exact ⟨e', p, h1, by simp [hc, h2], by rw [get_put', if_neg hc]; exact h3⟩
        · have hc : c ≠ x := fun e => hk (e ▸ hxK)
          obtain ⟨h1, h2⟩ := (h c).2 hk
          exact ⟨by rw [get_put', if_neg hc]; exact h1, by simp [hc, h2]⟩
      obtain ⟨M2, hf, hinv⟩ := st2_fold hA L K _ _ G (fun b hb => hL b (List.mem_cons_of_mem _ hb)) h1 hG
      refine ⟨M2, ?_, hinv⟩
      have hex : ∃ fb, FinMap.get M x = some (C e.nomm.toNoun fb) := ⟨_, h3⟩
      simp only [foldO, st2, he, Option.bind_some, if_pos hex, accFt_of h, hr, Option.map_some]
      exact hf

open Classical in
/-- **`accLoop` is the model's loop** on accumulators that agree with it. -/
theorem acc_loop (hA : AddsTo T nc T') : ∀ (Ls : List (List Bell)) (K : Bell → Prop) (M : FinMap Bell Noun) (ft G : FlagTab),
    Ls.flatten.Nodup → (∀ b ∈ Ls.flatten, ¬ K b ∧ ∃ e, FinMap.get nc b = some e) → AccInv T' K M ft →
    sccLoop (nmOf T') ft Ls = some G →
    ∃ M', accLoop nc M Ls = some M' ∧ AccInv T' (fun c => K c ∨ c ∈ Ls.flatten) M' G
  | [], K, M, ft, G, _, _, h, hG => by
    simp only [sccLoop, Option.some.injEq] at hG
    subst hG
    exact ⟨M, rfl, accInv_congr (fun c => by simp) (fun _ => rfl) h⟩
  | L :: Ls, K, M, ft, G, hd, hL, h, hG => by
    simp only [List.flatten_cons] at hd hL
    have hd1 := (List.nodup_append.1 hd).1
    have hd2 := (List.nodup_append.1 hd).2.1
    have hdis := (List.nodup_append.1 hd).2.2
    simp only [sccLoop] at hG
    cases hs : sccStep (nmOf T') ft L with
    | none => rw [hs] at hG; cases hG
    | some ft' =>
      rw [hs, Option.bind_some] at hG
      obtain ⟨M1, hf1, hi1⟩ := st1_fold hA L K M ft hd1
        (fun b hb => hL b (List.mem_append_left _ hb)) h
      obtain ⟨M2, hf2, hi2⟩ := st2_fold hA L (fun c => K c ∨ c ∈ L) M1 _ ft'
        (fun b hb => ⟨Or.inr hb, (hL b (List.mem_append_left _ hb)).2⟩) hi1 hs
      obtain ⟨M', hf', hi'⟩ := acc_loop hA Ls (fun c => K c ∨ c ∈ L) M2 ft' G hd2
        (fun b hb => ⟨fun h' => h'.elim (hL b (List.mem_append_right _ hb)).1
          (fun h'' => hdis b h'' b hb rfl), (hL b (List.mem_append_right _ hb)).2⟩) hi2 hG
      refine ⟨M', ?_, accInv_congr (fun c => ?_) (fun _ => rfl) hi'⟩
      · simp only [accLoop, accStep, hf1, Option.bind_some, hf2]; exact hf'
      · simp only [List.flatten_cons, List.mem_append, or_assoc]

end Model

/-- The accumulator of the old table: `code.lon` as a map of nouns. -/
noncomputable def accOf (F : FlagTab) (T : FinMap Bell (VarEntry FinMap)) : FinMap Bell Noun :=
  FinMap.mapK (fun b e => C e.nomm.toNoun (tabFlags F T b)) T

/-- **The model's loop on the accumulators**: from the old table with total
flags `F`, over a `TarjanSpec` list, where `sccLoop` returns `G`, `accLoop`
returns the accumulator of the new table with `G`, and `G` is total on it. -/
theorem acc_final {code nc : FinMap Bell (VarEntry FinMap)} (hA : AddsTo code nc (addCode code nc))
    {L : List (List Bell)} (hL : TarjanSpec nc L) {F G : FlagTab}
    (hF0 : ∀ c, FinMap.get code c = none → F c = none)
    (hFt : ∀ c e, FinMap.get code c = some e → ∃ p, F c = some p)
    (hG : sccLoop (nmOf (addCode code nc)) F L = some G) :
    accLoop nc (accOf F code) L = some (accOf G (addCode code nc)) ∧
      ∀ c e, FinMap.get (addCode code nc) c = some e → ∃ p, G c = some p := by
  obtain ⟨-, hnd, hcov, -⟩ := hL
  have h0 : AccInv (addCode code nc) (fun c => ∃ e, FinMap.get code c = some e) (accOf F code) F := by
    intro c
    refine ⟨fun ⟨e, he⟩ => ?_, fun hk => ?_⟩
    · obtain ⟨p, hp⟩ := hFt c e he
      refine ⟨e, p, hA.old c e he, hp, ?_⟩
      show (FinMap.get code c).map _ = _
      rw [he]; simp [tabFlags, hp]
    · have hn : FinMap.get code c = none := by
        cases h : FinMap.get code c with
        | none => rfl
        | some e => exact absurd ⟨e, h⟩ hk
      refine ⟨?_, hF0 c hn⟩
      show (FinMap.get code c).map _ = _
      rw [hn]; rfl
  obtain ⟨M', hM', hinv⟩ := acc_loop hA L _ (accOf F code) F G hnd
    (fun b hb => by
      obtain ⟨e, he⟩ := (hcov b).1 hb
      exact ⟨fun ⟨e', he'⟩ => (by rw [(hA.new b e he).1] at he'; cases he'), e, he⟩) h0 hG
  have hK : ∀ c, ((∃ e, FinMap.get code c = some e) ∨ c ∈ L.flatten) ↔ ∃ e, FinMap.get (addCode code nc) c = some e := by
    intro c
    constructor
    · rintro (⟨e, he⟩ | hc)
      · exact ⟨e, hA.old c e he⟩
      · obtain ⟨e, he⟩ := (hcov c).1 hc; exact ⟨e, (hA.new c e he).2⟩
    · rintro ⟨e, he⟩
      rcases hA.cov c e he with h | h
      · exact Or.inl ⟨e, h⟩
      · exact Or.inr ((hcov c).2 ⟨e, h⟩)
  refine ⟨?_, fun c e he => ?_⟩
  · rw [hM']
    congr 1
    apply Subtype.ext
    funext c
    show FinMap.get M' c = (FinMap.get (addCode code nc) c).map _
    by_cases hk : (∃ e, FinMap.get code c = some e) ∨ c ∈ L.flatten
    · obtain ⟨e, p, h1, h2, h3⟩ := (hinv c).1 hk
      rw [h3, h1]; simp [tabFlags, h2]
    · have hn : FinMap.get (addCode code nc) c = none := by
        cases h : FinMap.get (addCode code nc) c with
        | none => rfl
        | some e => exact absurd ((hK c).2 ⟨e, h⟩) hk
      rw [(hinv c).2 hk |>.1, hn]; rfl
  · obtain ⟨e', p, -, h2, -⟩ := (hinv c).1 ((hK c).2 ⟨e, he⟩)
    exact ⟨p, h2⟩

section Top

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- **`LoopRunAt` restated true** (`LoopRunAt` of `PokeLinkLoop.lean` is
false whenever `nc` is not empty: at `Ls = []` the model returns `F` and the
pill leaves `code.lon` unchanged, not the noun of `addCode code nc`): the
list is `TarjanSpec`, `code.lon` is the old table with the flags `F`, `F`
total on the old keys. -/
def LoopRunAtT (code nc baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) (F : FlagTab) : Prop :=
  ∀ (Ls : List (FinMap Bell Unit)) (G : FlagTab),
    TarjanSpec nc (Ls.map fun S => (FinMap.rap S).map Prod.fst) →
    sccLoop (nmOf (addCode code nc)) F (Ls.map fun S => (FinMap.rap S).map Prod.fst) = some G →
    nock (C (listNoun FinMap.setNoun Ls) (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
        (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r (codeNoun (tabFlags F) code) vr)))) srLoop =
      some (C (listNoun FinMap.setNoun Ls) (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
        (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r
          (codeNoun (tabFlags G) (addCode code nc)) vr))))

/-- **`LoopRunAtT` from the leaf `EvalFinAt`**: the SCC loop of the pill is
the model's, on every old table with flags total on its keys. -/
theorem loopRunAtT (hE : EvalFinAt) {code nc : FinMap Bell (VarEntry FinMap)} (baked : FinMap Bell (VarEntry FinMap))
    (vr : Noun) (hA : AddsTo code nc (addCode code nc)) {F : FlagTab}
    (hF0 : ∀ c, FinMap.get code c = none → F c = none)
    (hFt : ∀ c e, FinMap.get code c = some e → ∃ p, F c = some p) :
    LoopRunAtT root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r code nc baked vr F := by
  intro Ls G hL hG
  have hacc := (acc_final hA hL hF0 hFt hG).1
  have ht := lp_trap root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r (baked.toNoun varEntryNoun) vr hE nc
    Ls _ _ hacc
  exact lp_run root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r _ _ vr _ _ _ ht

end Top

/-- **`LoopLinkAt` at `flagsOf` from `+tarjan` and `+eval-finalized`**
(`loopLinkAt_flagsOf` with `LoopRunAt` discharged): on a closed old table
with `InfoCalls` and a solution `F` total on its keys, from the leaves
`SccsLeafAt` (track Q), `EvalFinAt` and `LoopTotal`. -/
theorem loopLinkAt_flagsOfT (hE : EvalFinAt) (root : Ident) (r1 r2 r3 r4 jRest callsN varsN seekN hotN : Noun)
    (gr : Callgraph FinMap × Noun)
    (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
    {code : FinMap Bell (VarEntry FinMap)} {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)} {F : FlagTab} (vr : Noun)
    (hc : CodeClosed code) (hv : VarsKeys E.vars code) (hi : InfoCalls code) (hbg : bakeGraph E n = some bg)
    (hF : FlagSol code F) (hFt : ∀ c e, FinMap.get code c = some e → ∃ p, F c = some p)
    (hS : SccsLeafAt root r1 r2 r3 r4 jRest (codeNoun flagsOf code) callsN varsN seekN hotN gr r
      (newCode code bg.1) bg.1 vr)
    (hT : LoopTotal code (newCode code bg.1) F) :
    LoopLinkAt root r1 r2 r3 r4 jRest (codeNoun flagsOf code) callsN varsN seekN hotN gr r
      flagsOf code (newCode code bg.1) bg.1 vr := by
  obtain ⟨q, hq, Ls, rfl, hspec⟩ := hS
  obtain ⟨G, hG⟩ := hT _ hspec
  refine ⟨_, hq, ?_⟩
  have hfl := (flagsOf_poke hc hv hi hbg hspec hF hG).1
  have e : codeNoun (tabFlags G) (addCode code (newCode code bg.1)) =
      codeNoun flagsOf (addCode code (newCode code bg.1)) :=
    codeNoun_congr fun b _ => (hfl b).symm
  have hl := loopRunAtT root r1 r2 r3 r4 jRest (codeNoun flagsOf code) callsN varsN seekN hotN gr r hE bg.1 vr
    (addsTo_addCode code bg.1) hF.1 hFt Ls G hspec hG
  rw [e, ← codeNoun_flagsOf hc hi hF] at hl
  exact hl

end Compiler
end Formalization
