import lemmas.Compiler.CompSccLoopParts
import lemmas.Compiler.CompSccLoopGate
import lemmas.Hoon.MapFolds
import lemmas.Hoon.UniBy
import lemmas.Ska.SccLoop

/-! # The nouns of the loop of `+compile-scc-in` and the model state (README Gaps 21.11)

The relation `StN` between a model state of `Ska/SccLoop.lean` (bells are nouns, `B = Noun`) and
the nouns the trap of the sweeps carries:

* `st = [any tick ran chg]`: `any` a loobean, `tick` an atom, `ran` and `chg` treaps of bells to
  ticks under `mugF` that hold the model's `ran`, `chg` (`TickMap`, for every key);
* `map-local` and `cache` (the `ML`, `CA` of the trap core `LoopP.core`): any relation `R` of
  the model's `ml` and `sure` to them, a parameter.  What is assumed of it is exactly what the
  member gate hypothesis `MemGate` says: a member run on nouns that `R` relates to the model's
  `ml`, `sure` returns the model's `chg` and nouns that `R` relates to the model's new `ml`,
  `sure`.  The cache threads (each run's product cache is the next run's input); `R` may carry
  any invariant of it (for the reading of Gaps 21.10: the cache extends the one the loop started
  with, with fresh entries only outside the SCC).

The ghost fields of `St` (`rd`, `tr`, `sw`) have no noun. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.SccLoop

/-- The fixed nouns of the loop: `done`, `kids`, the sample of `+compile-scc-in` with the cache it
was called with (`CA0`, which `member` and `final` keep in their context), `top`, `may` and
`order`. -/
structure LoopP where
  DN : Noun
  KIDS : Noun
  SCC : Noun
  LONG : Noun
  JH : Noun
  CA0 : Noun
  TOP : Noun
  MAY : Noun
  ORD : Noun

namespace LoopP

/-- The context of `member` and `final`. -/
def ctx (p : LoopP) : Noun := csiCtx p.DN p.KIDS p.SCC p.LONG p.JH p.CA0

/-- The gate `member`. -/
def mg (p : LoopP) : Noun := C memBody (C memBunt p.ctx)

/-- The subject of `final`. -/
def sm (p : LoopP) : Noun := csiSM p.DN p.KIDS p.SCC p.LONG p.JH p.CA0

/-- The gate `final`. -/
def fg (p : LoopP) : Noun := C fBody (C fBunt p.sm)

/-- The subject of `csiFix`, with `map-local` `ML` (axis 62) and `cache` `CA` (axis 2039). -/
def subj (p : LoopP) (ML CA : Noun) : Noun :=
  C p.fg (C p.mg (C p.DN (C p.KIDS (C ML (C csiBody (C (csiSam p.SCC p.LONG p.JH CA) compK))))))

/-- The trap core of the sweeps: `counter`, `st`, then `[top may order subject]`; `map-local` at
axis 4094, `cache` at axis `0x1fff7`. -/
def core (p : LoopP) (CNT ST ML CA : Noun) : Noun :=
  csfCore CNT ST (C p.TOP (C p.MAY (C p.ORD (p.subj ML CA))))

end LoopP

/-- A tick of `ran` or `chg` as `+get:by` gives it. -/
def tickOpt : Option Nat → Noun
  | none => A 0
  | some t => C (A 0) (A t)

/-- A treap of bells to ticks that holds `f` (at every key). -/
def TickMap (f : Noun → Option Nat) (M : Noun) : Prop :=
  IsMap mugF M ∧ ∀ k v, Get M k v ↔ ∃ t, f k = some t ∧ v = A t

variable {N : Type} [DecidableEq N]

/-- **`StN`**: the noun `st = [any tick ran chg]` of a model state. -/
def StN (st : St Noun N) (ST : Noun) : Prop :=
  ∃ RAN CHG, ST = C (loob st.any) (C (A st.tick) (C RAN CHG)) ∧ TickMap st.ran RAN ∧
    TickMap st.chg CHG

/-- **The member gate, as the one hypothesis about `+run`** (the shape of `hm` of
`csi_final_one`, for every member, `keep` and state): on the sample `[b MODE keep ML TOP CA]`,
with `R` relating the state's `ml`, `sure` to `ML`, `CA`, the gate returns `[chg ray cache]`
with `chg` the model's (`member c top b mode keep st`), and `R` relates the model's new `ml`,
`sure` to `ray`, `cache`. -/
def MemGate (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (ctx : Noun) (top : Noun → N) (TOP : Noun) (mode : Mode) (MODE : Noun) : Prop :=
  ∀ (st : St Noun N) (keep : Bool) (b ML CA : Noun), b ∈ c.scc → R st.ml st.sure ML CA →
    ∃ ML' CA', nock (C memBody (C (memSam b MODE (loob keep) ML TOP CA) ctx)) memBody
        = some (C (loob (member c top b mode keep st).1) (C ML' CA')) ∧
      R (member c top b mode keep st).2.ml (member c top b mode keep st).2.sure ML' CA'

/-- `kids` holds `c.kids` at the members: `(~(get ju kids) b)` is a set whose members are the
kids of `b`. -/
def KidsN (c : Cfg Noun N) (KIDS : Noun) : Prop :=
  ∀ b ∈ c.scc, ∃ out, getF mugF b KIDS = some out ∧ Tree (unUnit out) ∧
    ∀ k, k ∈ preorder (unUnit out) ↔ k ∈ c.kids b

/-- `scc` is a set whose `+tap` is `c.scc` (so `~(wyt in scc)` is its length). -/
def SccN (c : Cfg Noun N) (SCC : Noun) : Prop :=
  Tree SCC ∧ tapList SCC = c.scc ∧ (preorder SCC).length = c.scc.length

/-- The print of `csfRec`, `(print-comp 0 |.(leaf+"[fixpoint-compilation {(scow %ud counter)}]"))`,
returns a gate that gives back its sample.  In the pill `print-comp` is the `+slog` version
(`comp-verb` is set), so this runs `+scow` on `counter`: a statement about the pill alone. -/
def PrintId (p : LoopP) : Prop :=
  ∀ (k : Nat) (ST ML CA RES : Noun), ∃ BAT SAM CTX,
    nock (C RES (p.core (A k) ST ML CA)) csfRecPrint = some (C BAT (C SAM CTX)) ∧
      ∀ x, nock (C BAT (C x CTX)) BAT = some x

/-! ## The empty state -/

theorem tickMap_empty : TickMap (fun _ => none) (A 0) :=
  ⟨IsMap.nil, fun k v => by simp [get_nil]⟩

theorem stN_st0 (st : St Noun N) (h0 : st.any = false) (ht : st.tick = 0)
    (hr : st.ran = fun _ => none) (hc : st.chg = fun _ => none) : StN st csfSt0 :=
  ⟨A 0, A 0, by simp [csfSt0, csfOrdBunt, h0, ht, loob], hr ▸ tickMap_empty, hc ▸ tickMap_empty⟩

/-- `+get:by` on a `TickMap`. -/
theorem tickMap_get {f : Noun → Option Nat} {M : Noun} (h : TickMap f M) (k : Noun) :
    getF mugF k M = some (tickOpt (f k)) := by
  rcases e : f k with _ | t
  · exact getF_none h.1 (fun v hv => by obtain ⟨t, ht, _⟩ := (h.2 k v).1 hv; simp [e] at ht)
  · exact getF_some h.1 ((h.2 k (A t)).2 ⟨t, e, rfl⟩)

/-- `+put:by` on a `TickMap`. -/
theorem tickMap_put {f : Noun → Option Nat} {M : Noun} (h : TickMap f M) (k : Noun) (t : Nat) :
    ∃ M', putF mugF k (A t) M = some M' ∧ TickMap (upd f k (some t)) M' := by
  obtain ⟨out, hput, hmap, hget⟩ := putF_spec mugF M k (A t) h.1
  refine ⟨out, hput, hmap, fun k' v' => ?_⟩
  rw [hget, h.2]
  by_cases e : k' = k
  · subst e; simp [upd, eq_comm]
  · simp [upd, e]

end Compiler
end Formalization
