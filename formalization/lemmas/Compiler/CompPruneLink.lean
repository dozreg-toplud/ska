import lemmas.Compiler.CompWalkGen
import lemmas.Compiler.CompClaLink
import lemmas.Hoon.ListsMore

/-!
# `+lazy-empty` and `+lazy-prune` of the door of `+comp`

Neither arm carries a `%fast` hint; the generator names neither.  Their
Nock is written here and tied to the pill by kernel facts on `comp.door`:
`+lazy-empty` is door arm `54` (core axis `86`, the axis `+lazy-prune`
calls it by), `+lazy-prune` door arm `874364` (core axis `0x15577c`, the
axis `+split` and `+into` call it by).  Each arm is `[8 [1 bunt] [1 bat]
0 1]`: it builds the gate `[bat [bunt door-core]]`.

`+lazy-empty` (`le_gate`): `?&` of four tests in order, the need is
`[%none ~]`, the looks are `~` or `[1 ~ ~]` (`cs_small_cases`), the
forks are `~`, the bonds are `~`.  The model `Lazy.lazyEmpty` is the
same conjunction: no departure.

`+lazy-prune` (`comp_lazy_prune`): `[sure.l (skip fork.l ..) (skip bond.l
..)]` with `+skip` of layer 2; the fork gate says yes when both needs of
the fork are empty (`+lazy-empty` of the yes need first, then of the no
need, short-circuited), the bond gate when the bond's need is.  The model
`Lazy.lazyPrune` filters the same entries in the same order: no
departure.  It reads of the context only layer 2 (`CompIn`) and nothing
of the state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-! ## The Nock -/

/-- The battery of `+lazy-empty`. -/
def leBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 24))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 48)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 49)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 25)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 25))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 50)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 51))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 102)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 103)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 27)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- The bunt of `need-lazy`, `[[[%none ~] ~] ~ ~]`. -/
def lzBunt : Noun := C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))

/-- The arm `+lazy-empty`. -/
def leArm : Noun := C (A 8) (C (C (A 1) lzBunt) (C (C (A 1) leBat) (C (A 0) (A 1))))

/-- The battery of `+lazy-prune`. -/
def lpBat : Noun :=
  (C (C (A 0) (A 12)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))

/-- The gate of the `+skip` over the forks: `&((lazy-empty laz.y.e)
(lazy-empty laz.n.e))`. -/
def lpGF : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- The gate of the `+skip` over the bonds: `(lazy-empty laz.e)`. -/
def lpGB : Noun :=
  (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))

/-- The arm `+lazy-prune`. -/
def lpArm : Noun := C (A 8) (C (C (A 1) lzBunt) (C (C (A 1) lpBat) (C (A 0) (A 1))))

/-- `+lazy-empty` is door arm `54`. -/
theorem comp_le_at : slot? 54 comp.door = some leArm := by kernel_rfl

/-- `+lazy-prune` is door arm `874364`. -/
theorem comp_lp_at : slot? 874364 comp.door = some lpArm := by kernel_rfl

/-! ## `+lazy-empty` -/

/-- The tests of the forks and bonds of `+lazy-empty`. -/
theorem le_lists (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) :
    (fk = [] ∧ listN (fk.map forkE) = A 0 ∨ fk ≠ [] ∧ eqCode (A 0) (listN (fk.map forkE)) = A 1) ∧
    (bd = [] ∧ listN (bd.map bondE) = A 0 ∨ bd ≠ [] ∧ eqCode (A 0) (listN (bd.map bondE)) = A 1) := by
  constructor
  · by_cases h : fk = []
    · left; subst h; exact ⟨rfl, rfl⟩
    · right; exact ⟨h, wl_eq_nil _ (by simpa using h)⟩
  · by_cases h : bd = []
    · left; subst h; exact ⟨rfl, rfl⟩
    · right; exact ⟨h, wl_eq_nil _ (by simpa using h)⟩

/-- **`+lazy-empty`** is `Lazy.lazyEmpty`, on every lazy need and context. -/
theorem le_gate (laz : Lazy CSet) (D : Noun) :
    nock (C leBat (C laz.toNoun D)) leBat = some (loob (Lazy.lazyEmpty laz)) := by
  obtain ⟨⟨ned, lok⟩, fk, bd⟩ := laz
  rw [lazy_toNoun_mk]
  obtain ⟨hf, hb⟩ := le_lists fk bd
  nock_open leBat
  cases ned with
  | pair p q =>
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    simp [nock_exec, Sure.toNoun, Need.toNoun, hp, Lazy.lazyEmpty, loob, eqCode]
  | this r => simp [nock_exec, Sure.toNoun, Need.toNoun, Lazy.lazyEmpty, loob, eqCode_atom, Tag.this]
  | both r h t => simp [nock_exec, Sure.toNoun, Need.toNoun, Lazy.lazyEmpty, loob, eqCode_atom, Tag.both]
  | none =>
    rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
    · rcases hf with ⟨hf0, hf⟩ | ⟨hf0, hf⟩ <;> rcases hb with ⟨hb0, hb⟩ | ⟨hb0, hb⟩ <;>
        simp [nock_exec, Sure.toNoun, Need.toNoun, Tag.none, hl, hsm, Lazy.lazyEmpty, loob, hf, hb,
          hf0, hb0, List.isEmpty_iff]
    · rcases hf with ⟨hf0, hf⟩ | ⟨hf0, hf⟩ <;> rcases hb with ⟨hb0, hb⟩ | ⟨hb0, hb⟩ <;>
        simp [nock_exec, Sure.toNoun, Need.toNoun, Tag.none, hl, hsm, Lazy.lazyEmpty, loob, hf, hb,
          hf0, hb0, List.isEmpty_iff]
    · rcases n with k | ⟨n1, n2⟩
      · by_cases hk : k = 1
        · subst hk
          rcases l with l | ⟨l1, l2⟩
          · by_cases hl0 : l = 0
            · subst hl0
              rcases r with r | ⟨r1, r2⟩
              · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                simp [nock_exec, Sure.toNoun, Need.toNoun, hl, Lazy.lazyEmpty, hsm, loob,
                  eqCode_atom, Tag.none, Ne.symm hr0]
              · simp [nock_exec, Sure.toNoun, Need.toNoun, hl, Lazy.lazyEmpty, hsm, loob,
                  eqCode_atom, eqCode, Tag.none]
            · simp [nock_exec, Sure.toNoun, Need.toNoun, hl, Lazy.lazyEmpty, hsm, loob,
                eqCode_atom, Tag.none, Ne.symm hl0]
          · simp [nock_exec, Sure.toNoun, Need.toNoun, hl, Lazy.lazyEmpty, hsm, loob,
              eqCode_atom, eqCode, Tag.none]
        · simp [nock_exec, Sure.toNoun, Need.toNoun, hl, Lazy.lazyEmpty, hsm, loob,
            eqCode_atom, Tag.none, Ne.symm hk]
      · simp [nock_exec, Sure.toNoun, Need.toNoun, hl, Lazy.lazyEmpty, hsm, loob,
          eqCode_atom, eqCode, Tag.none]

/-! ## `+skip` over a list of encoded entries -/

@[nock_exec] theorem lp_skip_arm (d : Noun) :
    nock d skip.arm = some (C skip.battery (C (C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))) d)) := by
  nock_open skip.arm; simp only [nock_exec]

/-- `+skip` over the nouns `E a` of a list, with a gate that says `p a` on
each: the nouns of the entries on which it says no, in order. -/
theorem skip_gate_map {α : Type} (E : α → Noun) (c bp bs bc : Noun) (p : α → Bool) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (loob (p a))) :
    nock (C skip.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) skip.battery
      = some (listN ((l.filter fun a => !p a).map E)) := by
  classical
  let p' : Noun → Bool := fun x => match l.find? (fun a => decide (E a = x)) with
    | some a => p a
    | none => false
  have hp : ∀ a ∈ l, p' (E a) = p a := by
    intro a ha
    have hfa := hf a ha
    cases e : l.find? (fun b => decide (E b = E a)) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 e a ha
      simp at this
    | some b =>
      have hb := List.mem_of_find?_eq_some e
      have hbe : E b = E a := by simpa using List.find?_some e
      have hfb := hf b hb
      rw [hbe, hfa] at hfb
      have : p a = p b := by
        cases h1 : p a <;> cases h2 : p b <;> simp_all [loob]
      simp only [p', e, this]
  rw [skip_gate c bp bs bc p' (l.map E) (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    rw [hp a ha]; exact hf a ha)]
  congr 2
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro a ha
  simp [Function.comp_def, hp a ha]

/-! ## `+lazy-prune` -/

/-- The gate of `+lazy-empty`, built from the door core. -/
theorem comp_le_arm (d : Noun) : nock d leArm = some (C leBat (C lzBunt d)) := by
  unfold leArm; simp only [nock_exec]

/-- **`+lazy-prune`** is `Lazy.lazyPrune`, on every lazy need, in every door
core whose context has layer 2 (`CompIn`). -/
theorem comp_lazy_prune (hc : CompIn ctx) (laz : Lazy CSet) (G : Noun) :
    nock (C lpBat (C laz.toNoun (C comp.door (C G ctx)))) lpBat = some (Lazy.lazyPrune laz).toNoun := by
  obtain ⟨s, fk, bd⟩ := laz
  have hle := comp_le_at
  have hF := skip_gate_map forkE layer2 lpGF (C (C (A 0) lzBunt) (C (A 0) lzBunt))
    (C lpBat (C (Lazy.mk s fk bd).toNoun (C comp.door (C G ctx))))
    (fun e : Lazy.ForkE CSet => Lazy.lazyEmpty e.1.2 && Lazy.lazyEmpty e.2.2)
    fk (fun e _ => by
      obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
      have hy := le_gate y (C comp.door (C G ctx))
      have hn := le_gate n (C comp.door (C G ctx))
      unfold lpGF
      generalize comp.door = Dr at hle hy hn ⊢
      cases hey : Lazy.lazyEmpty y <;> cases hen : Lazy.lazyEmpty n <;>
        simp [nock_exec, forkE, hle, comp_le_arm, hy, hn, hey, hen, loob])
  have hB := skip_gate_map bondE layer2 lpGB (C (A 0) lzBunt)
    (C lpBat (C (Lazy.mk s fk bd).toNoun (C comp.door (C G ctx))))
    (fun e : Nat × Lazy CSet => Lazy.lazyEmpty e.2)
    bd (fun e _ => by
      obtain ⟨ob, l⟩ := e
      have hl := le_gate l (C comp.door (C G ctx))
      unfold lpGB
      generalize comp.door = Dr at hle hl ⊢
      simp [nock_exec, bondE, hle, comp_le_arm, hl])
  simp only [lazy_toNoun_mk] at hF hB ⊢
  unfold lzBunt lpGF at hF
  unfold lzBunt lpGB at hB
  nock_open lpBat
  simp [nock_exec, hc, skip.arm_at, hF, hB, Lazy.lazyPrune, lazy_toNoun_mk, lzBunt]

end Compiler
end Formalization
