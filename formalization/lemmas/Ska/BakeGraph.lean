import lemmas.Ska.KnowSound
import lemmas.Ska.Analysis

/-!
# `+bake-graph`: the worklist and its fixed point

A model of `+bake-graph` (`nock-compilation.hoon`), arm by arm: `+pick`
(`pick`), one evaluation of the worklist (`bakeStep`, with the `roll` of the
sites `newStep` and the `roll` of the touched callees `touchStep`), the
worklist (`bakeLoop`, with fuel: `none` is a crash or too little fuel), the
final pass (`finalStep`, with the `res` of the final pass `bakeRes`), and
`bakeGraph`.  Maps and sets are the treaps of `Analysis.lean`; `~(rep in ..)`
and `~(rep by ..)` visit in `rap` order, `~(tap in ..)` and `~(val by ..)` in
`tap` order, and `~(key by ..)`, `~(uni in ..)` and `~(gas in ..)` are folds
of `put` (a treap is its contents, `Treap.ext`).

`bakeLoop_sound`: when the worklist ends, every site `[b k]` of every
function `c` of the bakes, as `+know` lists it under `c`'s bake, that `+pick`
does not send to an existing variant, has a bake for `b` that every subject
fitting both `less.b` and `k` fits (`Fits`).  So the `res` of the final pass
sends every subject of a site to a variant whose bell it fits
(`bakeRes_fits`).
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

variable {M : Type → Type → Type} [Treap M]

/-- The parameters of `+bake-graph`, and the two flags of `bake-mode` it
reads: `fold` (`!@(off:bake-mode & |)`, for `+know`) and `frozen`. -/
structure BEnv (M : Type → Type → Type) where
  root : Bell
  dat : Bell → Option Datum
  jetted : Bell → Bool
  vars : M Bell (M Bell Unit)
  fold : Bool
  frozen : Bool

/-- The state of the worklist. -/
structure BSt (M : Type → Type → Type) where
  bak : M Bell Sock
  fix : M Bell Unit
  out : M Bell (M Bell Unit)
  inn : M Bell (M Bell (List Sock))
  evals : Nat
  grew : Nat

/-- The gate of the `~(rep in ..)` of `+pick`: the variant that knows the
most among those fit for `k`.  `none` is a crash of `+huge:so`. -/
def pickGate (k : Sock) (acc : Option (Option Bell)) (v : Bell) : Option (Option Bell) :=
  acc.bind fun best => (So.huge v.less k).bind fun hv =>
    if hv then
      match best with
      | none => some (some v)
      | some u => (So.huge u.less v.less).map fun h => if h then some v else some u
    else some best

/-- `+pick`: an existing variant of the code bell `c` fit for a site that
knows `k`, if `k` provides `less.c`. -/
def pick (vars : M Bell (M Bell Unit)) (c : Bell) (k : Sock) : Option (Option Bell) :=
  (So.huge c.less k).bind fun h =>
    if h then ((Treap.rap (Treap.gut vars c Treap.empty)).map Prod.fst).foldl (pickGate k) (some none)
    else some none

/-- `idc`: the `res` of the worklist's `+know`. -/
def idc : Bell → Sock → Option Bell := fun c _ => some c

/-- The gate of the `roll` over the sites: a site that `+pick` sends to no
variant adds what it knows to its callee's list. -/
def newStep (vars : M Bell (M Bell Unit)) (acc : Option (M Bell (List Sock))) (s : Site) :
    Option (M Bell (List Sock)) :=
  acc.bind fun new => (pick vars s.1 s.2).map fun p =>
    match p with
    | some _ => new
    | none => Treap.put new s.1 (s.2 :: Treap.gut new s.1 [])

/-- `~(key by m)`. -/
def keySet {ν : Type} (m : M Bell ν) : M Bell Unit :=
  (Treap.tap m).foldl (fun acc e => Treap.put acc e.1 ()) Treap.empty

/-- `~(uni in a b)`. -/
def uniIn (a b : M Bell Unit) : M Bell Unit :=
  (Treap.tap b).foldl (fun acc e => Treap.put acc e.1 ()) a

/-- `~(gas in s l)`. -/
def gasIn (s : M Bell Unit) (l : List Bell) : M Bell Unit :=
  l.foldl (fun acc c => Treap.put acc c ()) s

/-- What `cur` now tells its callee `c`: `inn` of `c` with `cur`'s list
replaced, or dropped when `cur` no longer calls `c`. -/
def innUpd (new : M Bell (List Sock)) (cur c : Bell) (m : M Bell (List Sock)) : M Bell (List Sock) :=
  match Treap.get new c with
  | none => Treap.del m cur
  | some ks => Treap.put m cur ks

/-- The bake of a callee against its old one, with the count of bakes that
would have grown: `+norm-sock` of the `+purr:so` when the new one is not a
loss. -/
def rebakeG (bake : Sock) (old : Option Sock) (grew : Nat) : Option (Sock × Nat) :=
  match old with
  | none => some (bake, grew)
  | some o => (So.huge bake o).bind fun h =>
      if h then some (bake, grew) else (normSockH (So.purr bake o)).map fun b => (b, grew + 1)

/-- The gate of the `roll` over the touched callees. -/
def touchStep (E : BEnv M) (cur : Bell) (new : M Bell (List Sock))
    (acc : Option (List Bell × BSt M)) (c : Bell) : Option (List Bell × BSt M) :=
  acc.bind fun ⟨changed, st⟩ =>
  let m := innUpd new cur c (Treap.gut st.inn c Treap.empty)
  let st := { st with inn := Treap.put st.inn c m }
  if c = E.root then some (changed, st) else
  let st := { st with fix := if E.jetted c then Treap.put st.fix c () else st.fix }
  let ks := ((Treap.tap m).map Prod.snd).flatten
  (bakeOf (E.frozen || Treap.has st.fix c) c.less ks).bind fun bake =>
  let old := Treap.get st.bak c
  (rebakeG bake old st.grew).bind fun ⟨bake, grew⟩ =>
  let st := { st with grew := grew }
  if some bake = old then some (changed, st) else
  some (c :: changed, { st with bak := Treap.put st.bak c bake })

/-- The sites of `c` under its bake, as the worklist's `+know` lists them. -/
def sitesOf (E : BEnv M) (st : BSt M) (c : Bell) : Option (List Site) :=
  (E.dat c).bind fun d => (Treap.get st.bak c).bind fun s =>
    (know E.fold d.nomm s E.dat idc).map Prod.snd

/-- One evaluation of the worklist: `cur` under its bake, what it tells its
callees, their bakes again, and the callees whose bake changed queued. -/
def bakeStep (E : BEnv M) (cur : Bell) (rest : List Bell) (qs : M Bell Unit) (st : BSt M) :
    Option (List Bell × M Bell Unit × BSt M) :=
  let qs := Treap.del qs cur
  (sitesOf E st cur).bind fun sites =>
  let st := { st with evals := st.evals + 1 }
  (sites.foldl (newStep E.vars) (some Treap.empty)).bind fun new =>
  let newBells := keySet new
  let prev := Treap.gut st.out cur Treap.empty
  let st := { st with out := Treap.put st.out cur newBells }
  let touched := uniIn prev newBells
  ((Treap.tap touched).map Prod.fst |>.foldl (touchStep E cur new) (some ([], st))).map fun ⟨changed, st⟩ =>
  let fresh := changed.filter fun c => !Treap.has qs c
  (rest ++ fresh, gasIn qs fresh, st)

/-- The worklist, with fuel. -/
def bakeLoop (E : BEnv M) : Nat → List Bell → M Bell Unit → BSt M → Option (BSt M)
  | 0, _, _, _ => none
  | _ + 1, [], _, st => some st
  | n + 1, cur :: rest, qs, st => (bakeStep E cur rest qs st).bind fun ⟨q, qs, st⟩ => bakeLoop E n q qs st

/-- The state the worklist starts from: the root's bake is its code
requirement, and it is fixed. -/
def bakeInit (E : BEnv M) : BSt M :=
  ⟨Treap.put Treap.empty E.root E.root.less, Treap.put Treap.empty E.root (), Treap.empty, Treap.empty, 0, 0⟩

/-- The `res` of the final pass: an existing variant `+pick` finds, or the
bake of the callee. -/
def bakeRes (E : BEnv M) (st : BSt M) : Bell → Sock → Option Bell := fun c k =>
  (pick E.vars c k).bind fun p =>
    match p with
    | some v => some v
    | none => (Treap.get st.bak c).map fun s => ⟨s, c.fol⟩

/-- An entry of the variants to compile: the folded nomm, the variants it
calls and the `.seek` of its function. -/
structure VarEntry (M : Type → Type → Type) where
  nomm : Nomm
  calls : M Bell Unit
  seek : Cape

/-- The gate of the final `~(rep by bak.st)`. -/
def finalStep (E : BEnv M) (st : BSt M) (acc : Option (M Bell (VarEntry M) × M Bell (M Bell Unit)))
    (e : Bell × Sock) : Option (M Bell (VarEntry M) × M Bell (M Bell Unit)) :=
  acc.bind fun ⟨out, vars⟩ =>
  (E.dat e.1).bind fun d =>
  (know E.fold d.nomm e.2 E.dat (bakeRes E st)).bind fun ⟨nomm, sites⟩ =>
  let v : Bell := ⟨e.2, e.1.fol⟩
  (sites.mapM fun s => bakeRes E st s.1 s.2).map fun vs =>
  (Treap.put out v ⟨nomm, Treap.silt vs, d.seek⟩,
    Treap.put vars e.1 (Treap.put (Treap.gut vars e.1 Treap.empty) v ()))

/-- `+bake-graph`: the variants to compile and the code bell -> variants
index with them. -/
def bakeGraph (E : BEnv M) (n : Nat) : Option (M Bell (VarEntry M) × M Bell (M Bell Unit)) :=
  (bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E)).bind fun st =>
    (Treap.rap st.bak).foldl (finalStep E st) (some (Treap.empty, E.vars))

/-! ## Maps and sets -/

theorem has_iff {ν : Type} (m : M Bell ν) (k : Bell) : Treap.has m k = true ↔ ∃ v, Treap.get m k = some v := by
  unfold Treap.has
  cases Treap.get m k <;> simp

theorem has_foldl_put {α : Type} (key : α → Bell) :
    ∀ (l : List α) (acc : M Bell Unit) (b : Bell),
      Treap.has (l.foldl (fun acc e => Treap.put acc (key e) ()) acc) b = true ↔
        Treap.has acc b = true ∨ ∃ e ∈ l, key e = b
  | [], acc, b => by simp
  | e :: l, acc, b => by
    simp only [List.foldl_cons]
    rw [has_foldl_put key l]
    simp only [has_iff, Treap.get_put, List.mem_cons]
    constructor
    · rintro (⟨v, hv⟩ | ⟨e', he', rfl⟩)
      · split at hv
        · rename_i h; exact Or.inr ⟨e, Or.inl rfl, h.symm⟩
        · exact Or.inl ⟨v, hv⟩
      · exact Or.inr ⟨e', Or.inr he', rfl⟩
    · rintro (⟨v, hv⟩ | ⟨e', rfl | he', rfl⟩)
      · by_cases h : b = key e
        · exact Or.inl ⟨(), by rw [if_pos h]⟩
        · exact Or.inl ⟨v, by rw [if_neg h]; exact hv⟩
      · exact Or.inl ⟨(), by rw [if_pos rfl]⟩
      · exact Or.inr ⟨e', he', rfl⟩

theorem has_keySet {ν : Type} (m : M Bell ν) (b : Bell) :
    Treap.has (keySet m) b = true ↔ ∃ v, Treap.get m b = some v := by
  unfold keySet
  rw [has_foldl_put]
  simp only [has_iff, Treap.get_empty, reduceCtorEq, exists_false, false_or]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e.2, (Treap.mem_tap _ _ _).mp he⟩
  · rintro ⟨v, hv⟩; exact ⟨(b, v), (Treap.mem_tap _ _ _).mpr hv, rfl⟩

theorem has_uniIn (a b : M Bell Unit) (c : Bell) :
    Treap.has (uniIn a b) c = true ↔ Treap.has a c = true ∨ Treap.has b c = true := by
  unfold uniIn
  rw [has_foldl_put]
  constructor
  · rintro (h | ⟨e, he, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ((has_iff _ _).mpr ⟨e.2, (Treap.mem_tap _ _ _).mp he⟩)
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨v, hv⟩ := (has_iff _ _).mp h
      exact Or.inr ⟨(c, v), (Treap.mem_tap _ _ _).mpr hv, rfl⟩

theorem has_gasIn (s : M Bell Unit) (l : List Bell) (c : Bell) :
    Treap.has (gasIn s l) c = true ↔ Treap.has s c = true ∨ c ∈ l := by
  unfold gasIn
  rw [has_foldl_put (fun c => c)]
  simp

theorem has_del {ν : Type} (m : M Bell ν) (k c : Bell) :
    Treap.has (Treap.del m k) c = true ↔ Treap.has m c = true ∧ c ≠ k := by
  simp only [has_iff, Treap.get_del]
  by_cases h : c = k <;> simp [h]

theorem mem_tap_keys (m : M Bell Unit) (c : Bell) :
    c ∈ (Treap.tap m).map Prod.fst ↔ Treap.has m c = true := by
  rw [has_iff]
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact ⟨e.2, (Treap.mem_tap _ _ _).mp he⟩
  · rintro ⟨v, hv⟩
    exact List.mem_map.mpr ⟨(c, v), (Treap.mem_tap _ _ _).mpr hv, rfl⟩

theorem innUpd_idem (new : M Bell (List Sock)) (cur c : Bell) (m : M Bell (List Sock)) :
    innUpd new cur c (innUpd new cur c m) = innUpd new cur c m := by
  unfold innUpd
  split
  · exact Treap.ext _ _ fun k => by simp only [Treap.get_del]; split <;> rfl
  · exact Treap.ext _ _ fun k => by simp only [Treap.get_put]; split <;> rfl

theorem innUpd_other (new : M Bell (List Sock)) {cur c' : Bell} (c : Bell) (m : M Bell (List Sock))
    (h : c' ≠ cur) : Treap.get (innUpd new cur c m) c' = Treap.get m c' := by
  unfold innUpd
  split
  · rw [Treap.get_del, if_neg h]
  · rw [Treap.get_put, if_neg h]

theorem innUpd_cur (new : M Bell (List Sock)) (cur c : Bell) (m : M Bell (List Sock)) {ks : List Sock}
    (h : Treap.get new c = some ks) : Treap.get (innUpd new cur c m) cur = some ks := by
  unfold innUpd
  rw [h]
  simp only [Treap.get_put, if_true]

/-! ## What a site of `cur` tells its callee -/

theorem newFold_none (vars : M Bell (M Bell Unit)) :
    ∀ (l : List Site), l.foldl (newStep vars) none = none
  | [] => rfl
  | _ :: l => newFold_none vars l

/-- Every site that `+pick` sends to no variant is in the list of its callee
in `new`. -/
theorem newFold_spec (vars : M Bell (M Bell Unit)) :
    ∀ (l : List Site) (acc new : M Bell (List Sock)), l.foldl (newStep vars) (some acc) = some new →
      (∀ b ks, Treap.get acc b = some ks → ∃ ks', Treap.get new b = some ks' ∧ ∀ k ∈ ks, k ∈ ks') ∧
      ∀ b k, (b, k) ∈ l → pick vars b k = some none → ∃ ks, Treap.get new b = some ks ∧ k ∈ ks
  | [], acc, new, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun b ks hb => ⟨ks, hb, fun _ h => h⟩, fun _ _ h => by simp at h⟩
  | s :: l, acc, new, h => by
    simp only [List.foldl_cons] at h
    cases hp : pick vars s.1 s.2 with
    | none =>
      simp only [newStep, Option.bind_some, hp, Option.map_none] at h
      rw [newFold_none] at h; cases h
    | some p =>
      simp only [newStep, Option.bind_some, hp, Option.map_some] at h
      have acc' := newFold_spec vars l _ new h
      refine ⟨fun b ks hb => ?_, fun b k hm hpk => ?_⟩
      · cases p with
        | some _ => exact acc'.1 b ks hb
        | none =>
          by_cases e : b = s.1
          · have hput : Treap.get (Treap.put acc s.1 (s.2 :: Treap.gut acc s.1 [])) b = some (s.2 :: ks) := by
              rw [Treap.get_put, if_pos e, ← e]; simp [Treap.gut, hb]
            obtain ⟨ks', h1, h2⟩ := acc'.1 b (s.2 :: ks) hput
            exact ⟨ks', h1, fun k hk => h2 k (List.mem_cons_of_mem _ hk)⟩
          · exact acc'.1 b ks (by rw [Treap.get_put, if_neg e]; exact hb)
      · rcases List.mem_cons.mp hm with e | hm
        · cases e
          rw [hp] at hpk
          cases hpk
          obtain ⟨ks', h1, h2⟩ := acc'.1 b (k :: Treap.gut acc b []) (by simp [Treap.get_put])
          exact ⟨ks', h1, h2 k List.mem_cons_self⟩
        · exact acc'.2 b k hm hpk


/-! ## Recomputing the bakes of the touched callees -/

/-- A site's subjects fit the bake of its callee. -/
def GoodSite (st : BSt M) (b : Bell) (k : Sock) : Prop :=
  ∃ s, Treap.get st.bak b = some s ∧ ∀ y, Fits b.less y → Fits k y → Fits s y

theorem rebakeG_fits {bake s : Sock} {old : Option Sock} {g g' : Nat} {y : Noun} (hb : Fits bake y)
    (h : rebakeG bake old g = some (s, g')) : Fits s y := by
  unfold rebakeG at h
  split at h
  · cases h; exact hb
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨b, _, h⟩ := h
    split at h
    · cases h; exact hb
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨b', hb', rfl, _⟩ := h
      exact normSockH_fits (purr_fits_left _ _ _ hb) hb'

theorem touchFold_none (E : BEnv M) (cur : Bell) (new : M Bell (List Sock)) :
    ∀ (l : List Bell), l.foldl (touchStep E cur new) none = none
  | [] => rfl
  | _ :: l => touchFold_none E cur new l

theorem gut_eq_of_get {ν μ : Type} {a b : M Bell (M ν μ)} {k : Bell} (h : Treap.get a k = Treap.get b k) (d : M ν μ) :
    Treap.gut a k d = Treap.gut b k d := by
  unfold Treap.gut; rw [h]

/-- One callee, unfolded: its `inn` updated, and when it is not the root its
bake recomputed from it and kept (and queued) when it changed. -/
theorem touchStep_cases {E : BEnv M} {cur : Bell} {new : M Bell (List Sock)} {c : Bell}
    {changed0 changed1 : List Bell} {st0 st1 : BSt M}
    (h : touchStep E cur new (some (changed0, st0)) c = some (changed1, st1)) :
    st1.inn = Treap.put st0.inn c (innUpd new cur c (Treap.gut st0.inn c Treap.empty)) ∧
    ((c = E.root ∧ st1.bak = st0.bak ∧ changed1 = changed0) ∨
     (c ≠ E.root ∧ ∃ fixed bake bake' g g',
        bakeOf fixed c.less (((Treap.tap (innUpd new cur c (Treap.gut st0.inn c Treap.empty))).map Prod.snd).flatten) = some bake ∧
        rebakeG bake (Treap.get st0.bak c) g = some (bake', g') ∧
        ((some bake' = Treap.get st0.bak c ∧ st1.bak = st0.bak ∧ changed1 = changed0) ∨
         (st1.bak = Treap.put st0.bak c bake' ∧ changed1 = c :: changed0)))) := by
  simp only [touchStep, Option.bind_some] at h
  by_cases hc : c = E.root
  · rw [if_pos hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Or.inl ⟨hc, rfl, rfl⟩⟩
  · rw [if_neg hc] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨bake, hbake, ⟨bake', grew'⟩, hre, h⟩ := h
    by_cases hold : some bake' = Treap.get st0.bak c
    · rw [if_pos hold] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inr ⟨hc, _, bake, bake', _, grew', hbake, hre, Or.inl ⟨hold, rfl, rfl⟩⟩⟩
    · rw [if_neg hold] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inr ⟨hc, _, bake, bake', _, grew', hbake, hre, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- One callee: what changes and what its bake keeps. -/
theorem touchStep_spec {E : BEnv M} {cur : Bell} {new : M Bell (List Sock)} {c : Bell}
    {changed0 changed1 : List Bell} {st0 st1 : BSt M}
    (h : touchStep E cur new (some (changed0, st0)) c = some (changed1, st1)) :
    (∀ b, b ≠ c → Treap.get st1.inn b = Treap.get st0.inn b ∧ Treap.get st1.bak b = Treap.get st0.bak b) ∧
    Treap.gut st1.inn c Treap.empty = innUpd new cur c (Treap.gut st0.inn c Treap.empty) ∧
    (c ≠ E.root → ∀ c' ks, Treap.get (Treap.gut st1.inn c Treap.empty) c' = some ks → ∀ k ∈ ks, GoodSite st1 c k) ∧
    (∀ b, Treap.get st1.bak b ≠ Treap.get st0.bak b → b ∈ changed1) ∧
    (∀ b ∈ changed0, b ∈ changed1) ∧
    (c = E.root → Treap.get st1.bak E.root = Treap.get st0.bak E.root) := by
  obtain ⟨hinn, hcase⟩ := touchStep_cases h
  have hgut : Treap.gut st1.inn c Treap.empty = innUpd new cur c (Treap.gut st0.inn c Treap.empty) := by
    rw [hinn]; simp [Treap.gut, Treap.get_put]
  have hinnb : ∀ b, b ≠ c → Treap.get st1.inn b = Treap.get st0.inn b := fun b hb => by
    rw [hinn, Treap.get_put, if_neg hb]
  rcases hcase with ⟨hc, hbak, hch⟩ | ⟨hc, fixed, bake, bake', g, g', hbake, hre, hcase⟩
  · subst hch
    refine ⟨fun b hb => ⟨hinnb b hb, by rw [hbak]⟩, hgut, fun h => absurd hc h,
      fun b hb => absurd (by rw [hbak]) hb, fun b hb => hb, fun _ => by rw [hbak]⟩
  · have hfit : ∀ c' ks, Treap.get (Treap.gut st1.inn c Treap.empty) c' = some ks →
        ∀ k ∈ ks, ∀ y, Fits c.less y → Fits k y → Fits bake' y := by
      intro c' ks hks k hk y hy hky
      rw [hgut] at hks
      refine rebakeG_fits (bakeOf_fits hy hky ?_ hbake) hre
      exact List.mem_flatten.mpr ⟨ks, List.mem_map.mpr ⟨(c', ks), (Treap.mem_tap _ _ _).mpr hks, rfl⟩, hk⟩
    rcases hcase with ⟨hold, hbak, hch⟩ | ⟨hbak, hch⟩
    · subst hch
      refine ⟨fun b hb => ⟨hinnb b hb, by rw [hbak]⟩, hgut, fun _ c' ks hks k hk => ⟨bake', ?_, hfit c' ks hks k hk⟩,
        fun b hb => absurd (by rw [hbak]) hb, fun b hb => hb, fun h => absurd h hc⟩
      rw [hbak, ← hold]
    · subst hch
      refine ⟨fun b hb => ⟨hinnb b hb, by rw [hbak, Treap.get_put, if_neg hb]⟩, hgut,
        fun _ c' ks hks k hk => ⟨bake', by rw [hbak, Treap.get_put, if_pos rfl], hfit c' ks hks k hk⟩,
        fun b hb => ?_, fun b hb => List.mem_cons_of_mem _ hb, fun h => absurd h hc⟩
      by_cases e : b = c
      · subst e; exact List.mem_cons_self
      · rw [hbak, Treap.get_put, if_neg e] at hb; exact absurd rfl hb

theorem goodSite_of_bak {st st' : BSt M} {b : Bell} {k : Sock} (h : Treap.get st'.bak b = Treap.get st.bak b)
    (hg : GoodSite st b k) : GoodSite st' b k := by
  obtain ⟨s, hs, hf⟩ := hg
  exact ⟨s, by rw [h, hs], hf⟩

/-- All the touched callees. -/
theorem touchFold_spec (E : BEnv M) (cur : Bell) (new : M Bell (List Sock)) :
    ∀ (L : List Bell) (changed0 changed' : List Bell) (st0 st' : BSt M),
      L.foldl (touchStep E cur new) (some (changed0, st0)) = some (changed', st') →
      (∀ b, b ∉ L → Treap.get st'.inn b = Treap.get st0.inn b ∧ Treap.get st'.bak b = Treap.get st0.bak b) ∧
      (∀ b ∈ L, Treap.gut st'.inn b Treap.empty = innUpd new cur b (Treap.gut st0.inn b Treap.empty)) ∧
      (∀ b ∈ L, b ≠ E.root → ∀ c ks, Treap.get (Treap.gut st'.inn b Treap.empty) c = some ks →
        ∀ k ∈ ks, GoodSite st' b k) ∧
      (∀ b, Treap.get st'.bak b ≠ Treap.get st0.bak b → b ∈ changed') ∧
      (∀ b ∈ changed0, b ∈ changed') ∧
      Treap.get st'.bak E.root = Treap.get st0.bak E.root
  | [], changed0, changed', st0, st', h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => absurd rfl h, fun _ h => h, rfl⟩
  | c :: L, changed0, changed', st0, st', h => by
    simp only [List.foldl_cons] at h
    cases h1 : touchStep E cur new (some (changed0, st0)) c with
    | none => rw [h1, touchFold_none] at h; cases h
    | some p =>
      obtain ⟨changed1, st1⟩ := p
      rw [h1] at h
      obtain ⟨S1, S2, S3, S4, S5, S6⟩ := touchStep_spec h1
      obtain ⟨F1, F2, F3, F4, F5, F6⟩ := touchFold_spec E cur new L changed1 changed' st1 st' h
      refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb hr c' ks hks k hk => ?_, fun b hb => ?_,
        fun b hb => F5 b (S5 b hb), ?_⟩
      · have hbc : b ≠ c := fun e => hb (e ▸ List.mem_cons_self)
        have hbL : b ∉ L := fun e => hb (List.mem_cons_of_mem _ e)
        exact ⟨(F1 b hbL).1.trans (S1 b hbc).1, (F1 b hbL).2.trans (S1 b hbc).2⟩
      · by_cases hbL : b ∈ L
        · rw [F2 b hbL]
          by_cases e : b = c
          · subst e; rw [S2, innUpd_idem]
          · rw [gut_eq_of_get (S1 b e).1]
        · have e : b = c := by
            rcases List.mem_cons.mp hb with e | e
            · exact e
            · exact absurd e hbL
          subst e
          rw [gut_eq_of_get (F1 b hbL).1, S2]
      · by_cases hbL : b ∈ L
        · exact F3 b hbL hr c' ks hks k hk
        · have e : b = c := by
            rcases List.mem_cons.mp hb with e | e
            · exact e
            · exact absurd e hbL
          subst e
          rw [gut_eq_of_get (F1 b hbL).1] at hks
          exact goodSite_of_bak (F1 b hbL).2 (S3 hr c' ks hks k hk)
      · by_cases e : Treap.get st'.bak b = Treap.get st1.bak b
        · exact F5 b (S4 b (by rwa [e] at hb))
        · exact F4 b e
      · by_cases e : c = E.root
        · rw [F6, S6 e]
        · rw [F6, (S1 E.root (fun h => e h.symm)).2]

/-! ## The worklist's invariant -/

/-- The invariant of the worklist: the root keeps its code requirement, every
queued function is on the list, every site that a callee's `inn` records
fits the callee's bake, and every function that is not queued has the sites
of its current bake recorded in the `inn` of their callees. -/
structure LoopInv (E : BEnv M) (q : List Bell) (qs : M Bell Unit) (st : BSt M) : Prop where
  root : Treap.get st.bak E.root = some E.root.less
  queued : ∀ c, Treap.has qs c = true → c ∈ q
  inn : ∀ b, b ≠ E.root → ∀ c ks, Treap.get (Treap.gut st.inn b Treap.empty) c = some ks →
    ∀ k ∈ ks, GoodSite st b k
  sites : ∀ c, Treap.has qs c = false → ∀ sites, sitesOf E st c = some sites →
    ∀ b k, (b, k) ∈ sites → pick E.vars b k = some none →
      b = E.root ∨ ∃ ks, Treap.get (Treap.gut st.inn b Treap.empty) c = some ks ∧ k ∈ ks

theorem sitesOf_eq {E : BEnv M} {st st' : BSt M} {c : Bell} (h : Treap.get st'.bak c = Treap.get st.bak c) :
    sitesOf E st' c = sitesOf E st c := by
  unfold sitesOf; rw [h]

theorem loopInv_init (E : BEnv M) : LoopInv E [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) where
  root := by simp [bakeInit, Treap.get_put]
  queued := fun c h => by
    rw [has_iff] at h
    obtain ⟨_, h⟩ := h
    simp only [Treap.get_put, Treap.get_empty] at h
    split at h
    · rename_i e; exact e ▸ List.mem_singleton_self _
    · cases h
  inn := fun b _ c ks h => by simp [bakeInit, Treap.gut, Treap.get_empty] at h
  sites := fun c hq sites h => by
    have hc : c ≠ E.root := fun e => by subst e; simp [Treap.has, Treap.get_put] at hq
    simp [sitesOf, bakeInit, Treap.get_put, Treap.get_empty, hc] at h

theorem not_mem_of_has {qs : M Bell Unit} {fresh : List Bell} {c : Bell}
    (h : Treap.has (gasIn qs fresh) c = false) : Treap.has qs c = false ∧ c ∉ fresh := by
  constructor
  · cases hh : Treap.has qs c
    · rfl
    · exact absurd ((has_gasIn qs fresh c).mpr (Or.inl hh)) (by simp [h])
  · intro hm
    exact absurd ((has_gasIn qs fresh c).mpr (Or.inr hm)) (by simp [h])

/-- **One evaluation keeps the invariant.** -/
theorem bakeStep_inv {E : BEnv M} {cur : Bell} {rest q' : List Bell} {qs qs' : M Bell Unit} {st st' : BSt M}
    (hI : LoopInv E (cur :: rest) qs st) (h : bakeStep E cur rest qs st = some (q', qs', st')) :
    LoopInv E q' qs' st' := by
  simp only [bakeStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨sites, hsites, new, hnew, ⟨changed, st3⟩, hfold, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨F1, F2, F3, F4, -, F6⟩ := touchFold_spec E cur new _ [] changed _ st3 hfold
  have hN := (newFold_spec E.vars sites Treap.empty new hnew).2
  -- the touched callees are those `cur` calls now or called before
  have hL : ∀ b ks, Treap.get new b = some ks →
      b ∈ (Treap.tap (uniIn (Treap.gut st.out cur Treap.empty) (keySet new))).map Prod.fst := by
    intro b ks hb
    rw [mem_tap_keys, has_uniIn]
    exact Or.inr ((has_keySet new b).mpr ⟨ks, hb⟩)
  refine ⟨?_, fun c hc => ?_, fun b hb c ks hks k hk => ?_, fun c hq sites' hs' b k hm hp => ?_⟩
  · rw [F6]; exact hI.root
  · rcases (has_gasIn _ _ c).mp hc with hc | hc
    · obtain ⟨hc, hne⟩ := (has_del qs cur c).mp hc
      rcases List.mem_cons.mp (hI.queued c hc) with e | e
      · exact absurd e hne
      · exact List.mem_append_left _ e
    · exact List.mem_append_right _ hc
  · by_cases hbL : b ∈ (Treap.tap (uniIn (Treap.gut st.out cur Treap.empty) (keySet new))).map Prod.fst
    · exact F3 b hbL hb c ks hks k hk
    · rw [gut_eq_of_get (F1 b hbL).1] at hks
      exact goodSite_of_bak (F1 b hbL).2 (hI.inn b hb c ks hks k hk)
  · obtain ⟨hq1, hq2⟩ := not_mem_of_has hq
    have hbak : Treap.get st3.bak c = Treap.get st.bak c := by
      by_cases hne : Treap.get st3.bak c = Treap.get st.bak c
      · exact hne
      · exact absurd (List.mem_filter.mpr ⟨F4 c hne, by simp [hq1]⟩) hq2
    rw [sitesOf_eq hbak] at hs'
    have hinnEq : ∀ c', c' ≠ cur → Treap.get (Treap.gut st3.inn b Treap.empty) c' =
        Treap.get (Treap.gut st.inn b Treap.empty) c' := by
      intro c' hc'
      by_cases hbL : b ∈ (Treap.tap (uniIn (Treap.gut st.out cur Treap.empty) (keySet new))).map Prod.fst
      · rw [F2 b hbL, innUpd_other new b _ hc']
      · rw [gut_eq_of_get (F1 b hbL).1]
    by_cases e : c = cur
    · subst e
      rw [hsites] at hs'
      cases hs'
      obtain ⟨ks, hks, hk⟩ := hN b k hm hp
      refine Or.inr ⟨ks, ?_, hk⟩
      rw [F2 b (hL b ks hks)]
      exact innUpd_cur new c b _ hks
    · have hq0 : Treap.has qs c = false := by
        cases hh : Treap.has qs c
        · rfl
        · exact absurd ((has_del qs cur c).mpr ⟨hh, e⟩) (by simp [hq1])
      rcases hI.sites c hq0 sites' hs' b k hm hp with hr | ⟨ks, hks, hk⟩
      · exact Or.inl hr
      · exact Or.inr ⟨ks, by rw [hinnEq c e]; exact hks, hk⟩

theorem bakeLoop_inv (E : BEnv M) :
    ∀ (n : Nat) (q : List Bell) (qs : M Bell Unit) (st st' : BSt M), LoopInv E q qs st →
      bakeLoop E n q qs st = some st' → ∃ qs', LoopInv E [] qs' st'
  | 0, _, _, _, _, _, h => by simp [bakeLoop] at h
  | n + 1, [], qs, st, st', hI, h => by
    simp only [bakeLoop, Option.some.injEq] at h
    subst h; exact ⟨qs, hI⟩
  | n + 1, cur :: rest, qs, st, st', hI, h => by
    simp only [bakeLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨q', qs', st1⟩, h1, h2⟩ := h
    exact bakeLoop_inv E n q' qs' st1 st' (bakeStep_inv hI h1) h2

/-- **The fixed point of the worklist**: when it ends, every site of every
function under its bake that `+pick` sends to no existing variant has a bake
for its callee that every subject fitting both the callee's code requirement
and the site's sock fits. -/
theorem bakeLoop_sound {E : BEnv M} {n : Nat} {st : BSt M}
    (h : bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st) :
    ∀ c sites, sitesOf E st c = some sites → ∀ b k, (b, k) ∈ sites → pick E.vars b k = some none →
      GoodSite st b k := by
  obtain ⟨qs, hI⟩ := bakeLoop_inv E n _ _ _ st (loopInv_init E) h
  intro c sites hs b k hm hp
  have hq : Treap.has qs c = false := by
    cases hh : Treap.has qs c
    · rfl
    · exact absurd (hI.queued c hh) (List.not_mem_nil)
  rcases hI.sites c hq sites hs b k hm hp with hr | ⟨ks, hks, hk⟩
  · subst hr
    exact ⟨_, hI.root, fun y hy _ => hy⟩
  · by_cases hr : b = E.root
    · subst hr; exact ⟨_, hI.root, fun y hy _ => hy⟩
    · exact hI.inn b hr c ks hks k hk

/-! ## The final pass lists the sites the worklist saw -/

/-- A nomm with the bells of its calls blanked: what `+know`'s folds look at. -/
def eraseN : Nomm → Nomm
  | Nomm.cons p q => Nomm.cons (eraseN p) (eraseN q)
  | Nomm.n0 p => Nomm.n0 p
  | Nomm.n1 p => Nomm.n1 p
  | Nomm.n2 p q info => Nomm.n2 (eraseN p) (eraseN q) (info.map fun i => (⟨Sock.void, A 0⟩, i.2))
  | Nomm.n3 p => Nomm.n3 (eraseN p)
  | Nomm.n4 p => Nomm.n4 (eraseN p)
  | Nomm.n5 p q => Nomm.n5 (eraseN p) (eraseN q)
  | Nomm.n6 p q r => Nomm.n6 (eraseN p) (eraseN q) (eraseN r)
  | Nomm.n7 p q => Nomm.n7 (eraseN p) (eraseN q)
  | Nomm.n10 a v q => Nomm.n10 a (eraseN v) (eraseN q)
  | Nomm.n11s tag q body => Nomm.n11s tag (eraseN q) body
  | Nomm.n11d tag h q body => Nomm.n11d tag (eraseN h) (eraseN q) body
  | Nomm.n12 p q => Nomm.n12 (eraseN p) (eraseN q)
  | Nomm.mean p _ q body k => Nomm.mean (eraseN p) ⟨Sock.void, A 0⟩ (eraseN q) body k

theorem lit_erase {a b : Nomm} (h : (eraseN a) = (eraseN b)) : lit a = lit b := by
  cases a <;> cases b <;> simp_all [eraseN, lit]

theorem safeNomm_eraseN : ∀ a : Nomm, safeNomm (eraseN a) = safeNomm a := by
  intro a
  induction a with
  | cons p q ih1 ih2 => simp only [eraseN, safeNomm, ih1, ih2]
  | n11s t q b ih => simp only [eraseN, safeNomm, ih]
  | n11d t h q b ih1 ih2 => simp only [eraseN, safeNomm, ih1, ih2]
  | mean p b q body k ih1 ih2 => simp only [eraseN, safeNomm, ih1, ih2]
  | _ => rfl

theorem safeNomm_erase {a b : Nomm} (h : eraseN a = eraseN b) : safeNomm a = safeNomm b := by
  rw [← safeNomm_eraseN a, h, safeNomm_eraseN]

theorem lit_eraseN (a : Nomm) : lit (eraseN a) = lit a := by cases a <;> rfl

/-- `knowGo` with a `res` that succeeds, and with `idc`: the same products
and sites, and nomms that differ only in the bells of their calls. -/
def SameRun (r r' : (Nomm × Anno) × List Site) : Prop :=
  eraseN r'.1.1 = eraseN r.1.1 ∧ r'.1.2 = r.1.2 ∧ r'.2 = r.2

theorem knowGo_idc (fold : Bool) (dat : Bell → Option Datum) (res : Bell → Sock → Option Bell) :
    ∀ (nm : Nomm) (sub : Anno) (st : List Site) (r : (Nomm × Anno) × List Site),
      knowGo fold dat res nm sub st = some r →
      ∃ r', knowGo fold dat idc nm sub st = some r' ∧ SameRun r r' := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r1, hr1, h⟩ := h
    obtain ⟨l', hl', el, pl, sl⟩ := ihp sub st l hl
    obtain ⟨r1', hr1', er, pr, sr⟩ := ihq sub l.2 r1 hr1
    rw [← sl] at hr1'
    simp only [knowGo, hl', Option.bind_some, hr1']
    have e1 : lit l'.1.1 = lit l.1.1 := by rw [← lit_eraseN, el, lit_eraseN]
    have e2 : lit r1'.1.1 = lit r1.1.1 := by rw [← lit_eraseN, er, lit_eraseN]
    rw [e1, e2]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sr⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, el, er], by simp only [pl, pr], sr⟩
  | n0 p =>
    intro sub st r h
    exact ⟨r, by rw [← h]; rfl, rfl, rfl, rfl⟩
  | n1 p =>
    intro sub st r h
    exact ⟨r, by rw [← h]; rfl, rfl, rfl, rfl⟩
  | n2 p q info ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, f, hf, h⟩ := h
    obtain ⟨s', hs', es, ps, ss⟩ := ihp sub st s hs
    obtain ⟨f', hf', ef, pf, sf⟩ := ihq sub s.2 f hf
    rw [← ss] at hf'
    simp only [knowGo, hs', Option.bind_some, hf']
    cases info with
    | none =>
      simp only [Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, by simp only [eraseN, es, ef, Option.map_none], rfl, sf⟩
    | some i =>
      obtain ⟨b, mk⟩ := i
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, _, rfl⟩ := h
      simp only [idc, Option.map_some]
      exact ⟨_, rfl, by simp only [eraseN, es, ef, Option.map_some], by simp only [ps], by simp only [ps, sf]⟩
  | n3 p ih =>
    intro sub st r h
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ih sub st a ha
    simp only [knowGo, ha', Option.map_some]
    rw [pa, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sa⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea], rfl, sa⟩
  | n4 p ih =>
    intro sub st r h
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ih sub st a ha
    simp only [knowGo, ha', Option.map_some]
    rw [pa, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sa⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea], rfl, sa⟩
  | n5 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    rw [pa, pb, safeNomm_erase ea, safeNomm_erase eb]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sb⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea, eb], rfl, sb⟩
  | n6 p q r0 ihp ihq ihr =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha
    simp only [knowGo, ha', Option.bind_some]
    rw [pa, safeNomm_erase ea, sa]
    split at h
    · exact ihq sub a.2 r h
    · exact ihr sub a.2 r h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, c, hc, rfl⟩ := h
      obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb
      obtain ⟨c', hc', ec, pc, sc⟩ := ihr sub b.2 c hc
      rw [← sb] at hc'
      simp only [hb', Option.bind_some, hc', Option.map_some]
      exact ⟨_, rfl, by simp only [eraseN, ea, eb, ec], by simp only [pb, pc], sc⟩
  | n7 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq a.1.2 a.2 b hb
    rw [← sa, ← pa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    have e2 : lit b'.1.1 = lit b.1.1 := by rw [← lit_eraseN, eb, lit_eraseN]
    rw [e2, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, eb, rfl, sb⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea, eb], pb, sb⟩
  | n10 ax v q ihv ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ihv sub st a ha
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb']
    have e1 : lit a'.1.1 = lit a.1.1 := by rw [← lit_eraseN, ea, lit_eraseN]
    have e2 : lit b'.1.1 = lit b.1.1 := by rw [← lit_eraseN, eb, lit_eraseN]
    rw [e1, e2, pa, pb]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sb⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s', hs', rfl⟩ := h
      simp only [hs', Option.map_some]
      exact ⟨_, rfl, by simp only [eraseN, ea, eb], rfl, sb⟩
  | n11s tag q body ih =>
    intro sub st r h
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ih sub st a ha
    simp only [knowGo, ha', Option.map_some]
    have e1 : lit a'.1.1 = lit a.1.1 := by rw [← lit_eraseN, ea, lit_eraseN]
    rw [e1]
    split at h
    · cases h; exact ⟨_, rfl, ea, rfl, sa⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea], pa, sa⟩
  | n11d tag hh q body ihh ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ihh sub st a ha
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    have e2 : lit b'.1.1 = lit b.1.1 := by rw [← lit_eraseN, eb, lit_eraseN]
    rw [e2, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, eb, rfl, sb⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea, eb], pb, sb⟩
  | n12 p q ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    exact ⟨_, rfl, by simp only [eraseN, ea, eb], rfl, sb⟩
  | mean p b q body k ihp ihq =>
    intro sub st r h
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, v, hv, c, hc, rfl⟩ := h
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha
    obtain ⟨c', hc', ec, pc, sc⟩ := ihq sub ((b, a.1.2.sock) :: a.2) c hc
    rw [← sa, ← pa] at hc'
    simp only [knowGo, ha', Option.bind_some, idc, hc', Option.map_some]
    exact ⟨_, rfl, by simp only [eraseN, ea, ec], pc, sc⟩

/-! ## The `res` of the final pass -/

theorem pickFold_spec (k : Sock) (L : List Bell) :
    ∀ (l : List Bell), (∀ v ∈ l, v ∈ L) → ∀ acc : Option (Option Bell),
      (∀ u, acc = some (some u) → u ∈ L ∧ So.huge u.less k = some true) →
      ∀ u, l.foldl (pickGate k) acc = some (some u) → u ∈ L ∧ So.huge u.less k = some true
  | [], _, acc, hacc, u, h => hacc u h
  | v :: l, hl, acc, hacc, u, h => by
    simp only [List.foldl_cons] at h
    refine pickFold_spec k L l (fun w hw => hl w (List.mem_cons_of_mem _ hw)) _ ?_ u h
    intro w hw
    simp only [pickGate, Option.bind_eq_some_iff] at hw
    obtain ⟨best, rfl, hv, hhv, hw⟩ := hw
    split at hw
    · rename_i htrue
      subst htrue
      split at hw
      · cases hw; exact ⟨hl _ List.mem_cons_self, hhv⟩
      · rename_i u' 
        simp only [Option.map_eq_some_iff] at hw
        obtain ⟨b, _, hb⟩ := hw
        split at hb
        · cases hb; exact ⟨hl _ List.mem_cons_self, hhv⟩
        · cases hb; exact hacc w rfl
    · cases hw; exact hacc w rfl

/-- **What `+pick` finds**: a variant of the code bell that the site's sock
provides. -/
theorem pick_spec {vars : M Bell (M Bell Unit)} {c : Bell} {k : Sock} {v : Bell}
    (h : pick vars c k = some (some v)) :
    Treap.has (Treap.gut vars c Treap.empty) v = true ∧ So.huge v.less k = some true := by
  simp only [pick, Option.bind_eq_some_iff] at h
  obtain ⟨hc, _, h⟩ := h
  split at h
  · obtain ⟨hm, hh⟩ := pickFold_spec k _ _ (fun w hw => hw) (some none) (fun u hu => by cases hu) v h
    refine ⟨?_, hh⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact (has_iff _ _).mpr ⟨e.2, (Treap.mem_rap _ _ _).mp he⟩
  · cases h

/-- **The `res` of the final pass is sound** on the sites of a variant: it
names a variant with the callee's formula, in the table `code'`, whose bell
every subject of the site fits.  It assumes of the variants of earlier pokes
(`vars`) that they have their code bell's formula and are in `code'`, and of
`code'` that it has the variants of this poke. -/
theorem bakeRes_ok {E : BEnv M} {n : Nat} {st : BSt M} {code' : Bell → Option Nomm}
    (hloop : bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st)
    (hvars : ∀ c v, Treap.has (Treap.gut E.vars c Treap.empty) v = true → v.fol = c.fol ∧ ∃ nb, code' v = some nb)
    (hcode : ∀ c s, Treap.get st.bak c = some s → ∃ nb, code' ⟨s, c.fol⟩ = some nb)
    {t : Bell} {s : Sock} {d : Datum} {nomm : Nomm} {sites : List Site}
    (hd : E.dat t = some d) (hs : Treap.get st.bak t = some s)
    (hk : know E.fold d.nomm s E.dat (bakeRes E st) = some (nomm, sites)) :
    ResOK code' (bakeRes E st) sites := by
  intro b k v hm hv
  -- the worklist saw these sites
  simp only [know, Option.map_eq_some_iff] at hk
  obtain ⟨r, hr, e⟩ := hk
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  obtain ⟨r', hr', -, -, hsr⟩ := knowGo_idc E.fold E.dat (bakeRes E st) d.nomm ⟨s, A 1⟩ [] r hr
  have hsites : sitesOf E st t = some r.2 := by
    simp only [sitesOf, hd, Option.bind_some, hs, know, hr', Option.map_some, hsr]
  simp only [bakeRes, Option.bind_eq_some_iff] at hv
  obtain ⟨p, hp, hv⟩ := hv
  cases p with
  | some u =>
    cases hv
    obtain ⟨hu, hh⟩ := pick_spec hp
    obtain ⟨hf, hc⟩ := hvars b v hu
    exact ⟨hf, hc, fun y _ hy => pick_fits hh hy⟩
  | none =>
    simp only [Option.map_eq_some_iff] at hv
    obtain ⟨sb, hsb, rfl⟩ := hv
    obtain ⟨s', hs', hfit⟩ := bakeLoop_sound hloop t r.2 hsites b k hm hp
    rw [hsb] at hs'
    cases hs'
    exact ⟨rfl, hcode b sb hsb, fun y hy hk => hfit y hy hk⟩

/-- **A variant of the final pass stands for its code bell's formula** on
every subject that fits both the code requirement and the bake, given a
sound table `code` for the code bells' nomms, sound datum products, and the
assumptions of `bakeRes_ok` on the variants' table `code'`. -/
theorem variant_annot {lib : Lib} {code code' : Bell → Option Nomm} {E : BEnv M} {n : Nat} {st : BSt M}
    (hc : CodeOK lib code) (hdat : DatOK lib E.dat)
    (hloop : bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st)
    (hvars : ∀ c v, Treap.has (Treap.gut E.vars c Treap.empty) v = true → v.fol = c.fol ∧ ∃ nb, code' v = some nb)
    (hcode : ∀ c s, Treap.get st.bak c = some s → ∃ nb, code' ⟨s, c.fol⟩ = some nb)
    {t : Bell} {s : Sock} {d : Datum} {nomm : Nomm} {sites : List Site}
    (hd : E.dat t = some d) (hs : Treap.get st.bak t = some s) (hA : Annot lib code (Fits t.less) t.fol d.nomm)
    (hk : know E.fold d.nomm s E.dat (bakeRes E st) = some (nomm, sites)) :
    Annot lib code' (fun x => Fits t.less x ∧ Fits s x) t.fol nomm :=
  know_annot hc hdat hA hk (bakeRes_ok hloop hvars hcode hd hs hk)

end Bake

end SkaModel
end Formalization
