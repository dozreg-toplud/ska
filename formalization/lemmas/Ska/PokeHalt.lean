import lemmas.Ska.PokeAna

/-!
# When `+poke` answers `%full`: the loops that must end

`FullAnswers` (`Contract.lean`, `Gap.halting` of `lemmas/Assembly.lean`)
asks that `+poke` answer every `%full` poke from a state that satisfies its
invariant.  For the model of `+poke` with the analysis arm `anaArm`
(`PokeAna.lean`), `fullAnswers_of` reduces it to named hypotheses, one per
loop, each stated on the fuel the model gives that loop:

* `AnaEnds`: `+ska-callgraph` and `+prune-callgraph` end within the fuel of
  the analysis, and the root identity has a datum in the pruned graph;
* `BakeEnds`: the worklist of `+bake-graph` ends within its fuel;
* `FinalEnds`: the final pass of `+bake-graph` (`+know` under every bake,
  `+pick` and `+huge:so` for every site) does not crash;
* `RootAnswers`: the reference compiler gives the root bell a form, when the
  root is not a jetted arm with a hot driver (then `CompHyp.answers` makes
  `+compiled-mono` return);

besides the soundness hypotheses (`CompHyp`, `PokeSites`), which give the
invariant of the state the compile step starts from.

What is proved of the loops here: the worklist does not depend on extra
fuel (`bakeLoop_mono`), so `BakeEnds` holds of any fuel function at least
as large as one that works; and a bake only loses knowledge (`rebakeG_grows`:
every noun of the old bake fits the new one; `bakeLoop_grows`: a callee's
bake at the end admits every noun its bake admitted at any earlier point).
-/

namespace Formalization
namespace SkaModel

open Nock Ana Bake

namespace Bake

variable {M : Type → Type → Type} [Treap M]

/-- **More fuel does not change what the worklist gives.** -/
theorem bakeLoop_mono (E : BEnv M) : ∀ (n k : Nat) (q : List Bell) (qs : M Bell Unit) (st st' : BSt M),
    bakeLoop E n q qs st = some st' → bakeLoop E (n + k) q qs st = some st'
  | 0, _, _, _, _, _, h => by simp [bakeLoop] at h
  | n + 1, k, [], qs, st, st', h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simpa [bakeLoop] using h
  | n + 1, k, cur :: rest, qs, st, st', h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [bakeLoop, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨p, h1, h2⟩ := h
    exact ⟨p, h1, bakeLoop_mono E n k _ _ _ _ h2⟩

/-- **A rebake loses knowledge**: every noun of the old bake fits the new
one. -/
theorem rebakeG_grows {bake s o : Sock} {g g' : Nat} (h : rebakeG bake (some o) g = some (s, g')) : Sub o s := by
  unfold rebakeG at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨hv, hh, h⟩ := h
  intro x hx
  split at h
  · rename_i hy
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    subst hy
    exact huge_sound hh hx
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨s', hs', rfl, -⟩ := h
    exact normSockH_fits (purr_fits_right _ _ _ hx) hs'

/-- The relation of two states of the worklist: every callee with a bake in
the first has one in the second that admits every noun of the first. -/
def Grows (st st' : BSt M) : Prop :=
  ∀ c o, Treap.get st.bak c = some o → ∃ o', Treap.get st'.bak c = some o' ∧ Sub o o'

theorem Grows.refl (st : BSt M) : Grows st st := fun _ o h => ⟨o, h, Sub.refl o⟩

theorem Grows.trans {a b c : BSt M} (h1 : Grows a b) (h2 : Grows b c) : Grows a c := by
  intro x o h
  obtain ⟨o1, h1', s1⟩ := h1 x o h
  obtain ⟨o2, h2', s2⟩ := h2 x o1 h1'
  exact ⟨o2, h2', s1.trans s2⟩

theorem touchStep_grows {E : BEnv M} {cur : Bell} {new : M Bell (List Sock)} {c : Bell}
    {ch ch' : List Bell} {st st' : BSt M} (h : touchStep E cur new (some (ch, st)) c = some (ch', st')) :
    Grows st st' := by
  intro x o hx
  obtain ⟨_, hcase⟩ := touchStep_cases h
  rcases hcase with ⟨_, hbak, _⟩ | ⟨_, fixed, bake, bake', g, g', _, hre, hcase⟩
  · exact ⟨o, by rw [hbak]; exact hx, Sub.refl o⟩
  · rcases hcase with ⟨_, hbak, _⟩ | ⟨hbak, _⟩
    · exact ⟨o, by rw [hbak]; exact hx, Sub.refl o⟩
    · rw [hbak, Treap.get_put]
      split
      · rename_i e
        subst e
        rw [hx] at hre
        exact ⟨bake', rfl, rebakeG_grows hre⟩
      · exact ⟨o, hx, Sub.refl o⟩

theorem touchFold_grows (E : BEnv M) (cur : Bell) (new : M Bell (List Sock)) :
    ∀ (l : List Bell) (ch0 ch1 : List Bell) (st0 st1 : BSt M),
      l.foldl (touchStep E cur new) (some (ch0, st0)) = some (ch1, st1) → Grows st0 st1
  | [], _, _, _, _, h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Grows.refl _
  | c :: l, ch0, ch1, st0, st1, h => by
    simp only [List.foldl_cons] at h
    cases h1 : touchStep E cur new (some (ch0, st0)) c with
    | none => rw [h1, touchFold_none] at h; cases h
    | some p =>
      obtain ⟨chm, stm⟩ := p
      rw [h1] at h
      exact (touchStep_grows h1).trans (touchFold_grows E cur new l chm ch1 stm st1 h)

theorem bakeStep_grows {E : BEnv M} {cur : Bell} {rest q' : List Bell} {qs qs' : M Bell Unit} {st st' : BSt M}
    (h : bakeStep E cur rest qs st = some (q', qs', st')) : Grows st st' := by
  simp only [bakeStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨sites, _, new, _, ⟨changed, st3⟩, hfold, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, -, rfl⟩ := he
  have hg := touchFold_grows E cur new _ [] changed _ _ hfold
  exact fun c o h => hg c o h

/-- **Bakes only lose knowledge**: a callee's bake at the end of the
worklist admits every noun its bake admitted at the start of any run of the
worklist. -/
theorem bakeLoop_grows (E : BEnv M) : ∀ (n : Nat) (q : List Bell) (qs : M Bell Unit) (st st' : BSt M),
    bakeLoop E n q qs st = some st' → Grows st st'
  | 0, _, _, _, _, h => by simp [bakeLoop] at h
  | n + 1, [], _, st, st', h => by
    simp only [bakeLoop, Option.some.injEq] at h
    subst h
    exact Grows.refl _
  | n + 1, cur :: rest, qs, st, st', h => by
    simp only [bakeLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨q', qs', st2⟩, h1, h2⟩ := h
    exact (bakeStep_grows h1).trans (bakeLoop_grows E n q' qs' st2 st' h2)

end Bake

namespace PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR R : Type}

/-- **The analysis ends** within its fuel on every poke from a state that
satisfies `InvB`: `+ska-callgraph` and `+prune-callgraph` return, and the
root identity has a datum in the pruned graph. -/
def AnaEnds (lib : Lib) (env : Env R) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j, InvB lib L →
    ∃ r, skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some r

/-- **The worklist of `+bake-graph` ends** within its fuel, on every poke
from a state that satisfies `InvB`. -/
def BakeEnds (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (bf : BEnv M → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    ∃ st, bakeLoop (anaEnv jet fold frozen s f L j hot dats memo' rd reg')
      (bf (anaEnv jet fold frozen s f L j hot dats memo' rd reg'))
      [(anaEnv jet fold frozen s f L j hot dats memo' rd reg').root]
      (Treap.put Treap.empty (anaEnv jet fold frozen s f L j hot dats memo' rd reg').root ())
      (bakeInit (anaEnv jet fold frozen s f L j hot dats memo' rd reg')) = some st

/-- **The final pass of `+bake-graph` does not crash** on the state the
worklist ends with: every bake has a datum, `+know` returns under it, and
`+pick` and `+huge:so` return for every site. -/
def FinalEnds (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    ∀ n st, bakeLoop (anaEnv jet fold frozen s f L j hot dats memo' rd reg') n
      [(anaEnv jet fold frozen s f L j hot dats memo' rd reg').root]
      (Treap.put Treap.empty (anaEnv jet fold frozen s f L j hot dats memo' rd reg').root ())
      (bakeInit (anaEnv jet fold frozen s f L j hot dats memo' rd reg')) = some st →
    ∃ out, (Treap.rap st.bak).foldl (finalStep (anaEnv jet fold frozen s f L j hot dats memo' rd reg') st)
      (some (Treap.empty, (anaEnv jet fold frozen s f L j hot dats memo' rd reg').vars)) = some out

/-- **The compiler has a form for the root bell** of every `%full` poke from
a state that satisfies the invariant, unless the root is a jetted arm with a
hot driver. -/
def RootAnswers (lib : Lib) (A : Arms M Map J H CR) (ref : Ref M Map J H) : Prop :=
  ∀ (st : CSt M Map J H CR) s f r, InvS lib ref st → A.skaPoke s f st.long st.jets st.hot = some r →
    A.jetRoot r.2.2.1 st.hot r.1 = none → ∃ x, ref r.2.1 r.2.2.1 st.hot r.1 true = some x

/-- **The analysis arm returns** when its three loops end. -/
theorem anaArm_some {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R}
    (jetsOf : J → R → J) (newOf : R → Noun)
    (ha : AnaEnds lib env fuel regOf) (hb : BakeEnds lib env jet fold frozen fuel bf regOf)
    (hf : FinalEnds lib env jet fold frozen fuel regOf) {s f : Noun} {L : LongB M} {j : J} (hot : H)
    (hI : InvB lib L) : ∃ r, anaArm env jet fold frozen fuel bf regOf jetsOf newOf s f L j hot = some r := by
  obtain ⟨⟨pr, dats, memo', rd, reg'⟩, h1⟩ := ha s f L j hI
  obtain ⟨stb, h2⟩ := hb s f L j hot pr dats memo' rd reg' hI h1
  obtain ⟨out, h3⟩ := hf s f L j hot pr dats memo' rd reg' hI h1 _ stb h2
  simp only [anaEnv] at h2 h3
  simp only [anaArm, skaPokeB, h1, Option.bind_some, bakeGraph, h2, h3, Option.map_some]
  exact ⟨_, rfl⟩

/-- **`+poke` answers every `%full` poke** from a state that satisfies its
invariant, given that the loops end and the root bell has a form. -/
theorem fullAnswers_of (A : Arms M Map J H CR) {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun}
    (hC : CompHyp A lib ref) (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf)
    (hs : PokeSites lib env jet fold frozen fuel regOf)
    (ha : AnaEnds lib env fuel regOf) (hb : BakeEnds lib env jet fold frozen fuel bf regOf)
    (hf : FinalEnds lib env jet fold frozen fuel regOf) (hr : RootAnswers lib A ref) :
    FullAnswers (pokeS A) (InvS lib ref) := by
  intro st s f1 f2 hI
  obtain ⟨r, hk⟩ := anaArm_some jetsOf newOf ha hb hf st.hot hI.1 (s := s) (f := C f1 f2) (j := st.jets)
  rw [← hA] at hk
  have hAna := anaHyp_of_meet A hA hs
  obtain ⟨hB, -, -⟩ := hAna.ana s (C f1 f2) st.long st.jets st.hot r hk hI.1
  have hok1 : CacheOK ref r.2.1 r.2.2.1 st.hot st.cache :=
    ⟨fun b x hx => hC.stable s (C f1 f2) _ _ _ r b true x hk hI.1 (hI.2.1 b x hx),
     fun b x hx => hC.stable s (C f1 f2) _ _ _ r b false x hk hI.1 (hI.2.2 b x hx)⟩
  have hI1 : InvS lib ref ({ st with long := r.2.1, jets := r.2.2.1 } : CSt M Map J H CR) := ⟨hB, hok1⟩
  simp only [pokeS, hk, Option.bind_some]
  split
  · exact ⟨_, rfl⟩
  · rename_i hj
    obtain ⟨x, hx⟩ := hr st s (C f1 f2) r hI hk hj
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hC.answers _ r.1 true x hI1 hx)
    exact ⟨_, by rw [hp]; rfl⟩

end PokeM

end SkaModel
end Formalization
