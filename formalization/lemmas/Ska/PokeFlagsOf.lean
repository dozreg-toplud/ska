import lemmas.Ska.PokeFlags
import lemmas.Ska.PokeEnc

/-!
# `flagsOf`: the flags of a table, as the SCC loop leaves them

P1 (README Gaps 23): `enc` takes the flags as `fl : Flags`; the pill writes
those of the SCC loop of `+ska-poke` (`sccLoop`, `PokeFlags.lean`, checked
on 53 pokes by `PokeFlagsCheck.lean`: from no flags, over the SCCs of the
WHOLE table callees first, the loop gives every key the flags the compiler
wrote, also after `%jets` and `%fast`).  The flags are then a function of
the table, characterised here without an order of the SCCs:

* `Edge T b c`: `b` calls `c` in `calls` and both are keys (the graph
  `+tarjan` sees); `Reach T` its reflexive-transitive closure;
* `sccSet T b`: the SCC of a key `b` (the keys `c` with `b` and `c`
  reaching each other), a set, whose `rap` order is the order of
  `~(rep in scc)`;
* `FlagSol T F`: `F` is a solution of the loop on `T`: on each key `b`,
  `F b` is `evalFin` of `b` on the table where the members of `b`'s SCC
  before `b` (in `rap` order) have their `F`, `b` and the later members
  `[| |]`, every other key its `F`; `F` is `none` off the keys;
* `flagsOf : Flags`, the flags noun of a solution (`Classical.epsilon`);
* `TarjanSpec nc L` (the leaf on `+tarjan` the loop needs, README Gaps 23):
  `L` lists each SCC of the new code `nc` once, as its `rap` order, and no
  member of an earlier SCC calls a member of a later one (callees first).

*Open* (in order): `FlagSol` has exactly one solution on a closed table
(induction on `Reach` through the SCCs, members in `rap` order); `sccLoop`
over a `TarjanSpec` list from the old table's solution gives the new
table's (each SCC's step reads only earlier SCCs and its own members); then
`LoopLinkAt` at `fl = flagsOf` from the pill's loop (`srSccs` against
`TarjanSpec`, `srLoop` against `sccLoop`).
-/

namespace Formalization
namespace Compiler

open Nock SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF

/-- The nomms of a table. -/
noncomputable def nmOf (T : FinMap Bell (VarEntry FinMap)) : Bell → Option Nomm :=
  fun b => (FinMap.get T b).map (·.nomm)

/-- **The graph of `+tarjan`**: `b` calls `c`, both keys. -/
def Edge (T : FinMap Bell (VarEntry FinMap)) (b c : Bell) : Prop :=
  ∃ e, FinMap.get T b = some e ∧ FinMap.get e.calls c = some () ∧ ∃ e', FinMap.get T c = some e'

inductive Reach (T : FinMap Bell (VarEntry FinMap)) : Bell → Bell → Prop
  | refl (b : Bell) : Reach T b b
  | step {a b c : Bell} : Edge T a b → Reach T b c → Reach T a c

/-- The keys of `b`'s SCC. -/
def InScc (T : FinMap Bell (VarEntry FinMap)) (b c : Bell) : Prop :=
  (∃ e, FinMap.get T c = some e) ∧ Reach T b c ∧ Reach T c b

open Classical in
/-- **The SCC of `b`**, as a set. -/
noncomputable def sccSet (T : FinMap Bell (VarEntry FinMap)) (b : Bell) : FinMap Bell Unit :=
  ⟨fun c => if InScc T b c then some () else none, by
    obtain ⟨l, hl⟩ := T.2
    refine ⟨l, fun k hk => hl k ?_⟩
    by_cases h : InScc T b k
    · obtain ⟨⟨e, he⟩, -⟩ := h
      intro h0
      have : FinMap.get T k = none := h0
      rw [this] at he; cases he
    · simp [h] at hk⟩

/-- The members of `b`'s SCC in the order of `~(rep in scc)`. -/
noncomputable def sccOrd (T : FinMap Bell (VarEntry FinMap)) (b : Bell) : List Bell :=
  (FinMap.rap (sccSet T b)).map Prod.fst

open Classical in
/-- The flag table `b`'s evaluation reads: the members of its SCC before it
with `F`, it and the later ones `[| |]`, the other bells `F`. -/
noncomputable def ftAt (T : FinMap Bell (VarEntry FinMap)) (F : FlagTab) (b : Bell) : FlagTab := fun c =>
  let ord := sccOrd T b
  if c ∈ ord then (if ord.idxOf c < ord.idxOf b then F c else some (false, false)) else F c

/-- **A solution of the SCC loop on `T`.** -/
def FlagSol (T : FinMap Bell (VarEntry FinMap)) (F : FlagTab) : Prop :=
  (∀ b, FinMap.get T b = none → F b = none) ∧
    ∀ b e, FinMap.get T b = some e → F b = evalFin (nmOf T) (ftAt T F b) b

/-- **`flagsOf`**: the flags noun of a solution of the loop (any flag table
when there is none). -/
noncomputable def flagsOf : Flags := fun T b =>
  match Classical.epsilon (FlagSol T) b with
  | some p => flagNoun p
  | none => A 0

/-- **`flagsOf` is the flags of THE solution** when the loop has exactly
one on `T` (uniqueness is the first open item). -/
theorem flagsOf_eq {T : FinMap Bell (VarEntry FinMap)} {F : FlagTab} (hF : FlagSol T F)
    (hu : ∀ G, FlagSol T G → G = F) (b : Bell) :
    flagsOf T b = match F b with
      | some p => flagNoun p
      | none => A 0 := by
  have h := hu _ (Classical.epsilon_spec (p := FlagSol T) ⟨F, hF⟩)
  unfold flagsOf
  rw [h]

/-- **The leaf on `+tarjan`**: `L` lists each SCC of `nc` once, in `rap`
order, callees first. -/
def TarjanSpec (nc : FinMap Bell (VarEntry FinMap)) (L : List (List Bell)) : Prop :=
  (∀ S ∈ L, ∃ b, (∃ e, FinMap.get nc b = some e) ∧ S = sccOrd nc b) ∧
    L.flatten.Nodup ∧ (∀ b, b ∈ L.flatten ↔ ∃ e, FinMap.get nc b = some e) ∧
    ∀ i j, i < j → ∀ (hi : i < L.length) (hj : j < L.length), ∀ b ∈ L[i], ∀ c ∈ L[j], ¬ Edge nc b c

/-- `TarjanSpec` on the noun the pill's push 8 makes: the list of the SCC
sets. -/
def TarjanSpecN (nc : FinMap Bell (VarEntry FinMap)) (q : Noun) : Prop :=
  ∃ L : List (FinMap Bell Unit), q = listNoun FinMap.setNoun L ∧
    TarjanSpec nc (L.map fun S => (FinMap.rap S).map Prod.fst)

end Compiler
end Formalization
