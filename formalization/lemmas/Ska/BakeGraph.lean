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
  let st := if E.jetted c then { st with fix := Treap.put st.fix c () } else st
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


end Bake

end SkaModel
end Formalization
