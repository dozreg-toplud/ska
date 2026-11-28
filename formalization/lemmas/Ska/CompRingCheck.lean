import lemmas.Ska.CompRingRunEq
import lemmas.Ska.CompCall

/-!
# The direct call through a ring against the real compiler (generated)

Written by `tools/gen/ringcheck.py` from the output of `tools/hoon/ringdump.hoon` (track K,
README Gaps 19 (h), 2026-11-28); do not edit by hand.

The core `[[ma [mb mc]] 1 2 0]` is registered by `%fast` (`/mm`) before any compile, so its arms
get the rings `[/mm 4]`, `[/mm 10]`, `[/mm 11]` at the analysis that first sees them; `ma =
[6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [0 3]]` recurs on the tail of its payload, `mb = [4 [9
4 [0 1]]]`, `mc = [[9 4 [0 1]] [9 10 [0 1]]]`.  The roots, each `[7 [0 1] X]` on the core:
`rt` a tail call of `ma`, `rn` under `%4`, `rc` / `rk` in the head / tail of a cons, `rp` as the
test of a `%6`, `rb` in a branch of a `%6`, `rm` a tail call of `mb`, `rx` a tail call of `mc`.

For each root, `ringMono` (`finishLUCMR` on the dumped nomm) against the raw blocks of
`+compiled-mono`, `ringNary` (`finishLFCR` on the dumped INLINED nomm, the dumped need and cape,
nothing baked) against those of `+compiled-nary`, and for every callee (`ma`, `mb`, `mc`) its
n-ary code against `nary.cache`.  The environment: each callee's dumped need and its ring, `sure`
`[%none ~]`, impure, not hinted, `sof` false.  The blocks are compared as nouns: the dump's `[k
blob]` against `C (A k) blob.toNoun` of the model, so the ring nouns are the dump's.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

/-- The cape of a noun (`&` is `0`, `|` is `1`). -/
def capeN : Noun → Cape
  | Noun.atom 1 => Cape.no
  | Noun.cell h t => Cape.cell (capeN h) (capeN t)
  | _ => Cape.yes

/-- The bell of a noun `[[cape data] fol]`. -/
def bellN : Noun → Bell
  | Noun.cell (Noun.cell c d) f => ⟨Sock.mk (capeN c) d, f⟩
  | Noun.cell _ f => ⟨Sock.void, f⟩
  | Noun.atom _ => ⟨Sock.void, A 0⟩

/-- The `need-ordered` of a noun. -/
def needOrdN : Noun → NeedOrd
  | Noun.cell (Noun.atom t) r =>
      if t = Tag.this then NeedOrd.this else if t = Tag.none then NeedOrd.none
      else match r with
        | Noun.cell h q => NeedOrd.both (needOrdN h) (needOrdN q)
        | _ => NeedOrd.none
  | Noun.cell p q => NeedOrd.pair (needOrdN p) (needOrdN q)
  | Noun.atom _ => NeedOrd.none

/-- The environment of the dump: the callees' needs and rings (by the noun of the bell). -/
def envRing (cs : List (Noun × Noun × Noun)) : CallEnv :=
  ⟨fun b => (cs.find? (fun c => c.1 == b.toNoun)).map fun c => needOrdN c.2.1,
   fun _ => NeedOrd.none, fun _ => false, fun b => (cs.find? (fun c => c.1 == b.toNoun)).map fun c => c.2.2,
   fun _ => some false, fun _ _ _ _ _ => false⟩

/-- The need, the argument count and the present blocks `[k blob]` below `n`, as nouns. -/
def strOut (c : Straight FM) (n : Nat) : Noun × Nat × List Noun :=
  (c.need.toNoun, c.nargs, (List.range n).filterMap fun k => (c.blocks.f k).map fun bl => C (A k) bl.toNoun)

def ringMono (env : CallEnv) (nm : Nomm) (n : Nat) : Option (Noun × Nat × List Noun) :=
  (finishLUCMR (S := LS) (Map := FM) env nm).map fun c => strOut c n

def ringNary (env : CallEnv) (nm : Nomm) (ord : Noun) (less : Noun) (n : Nat) : Option (Noun × Nat × List Noun) :=
  (finishLFCR (S := LS) (Map := FM) env nm (needOrdN ord) (capeN (match less with | Noun.cell c _ => c | _ => A 0))
    (fun ned => (ned, []))).map fun c => strOut c n

/-- The environment of `rt`. -/
def env_rt : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4)))]

/-- The nomm of `rt`. -/
def nomm_rt : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))))

/-- The inlined nomm of `rt` (`inl.cache`). -/
def inl_rt : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))))

/- `rt`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rt nomm_rt 6 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 6712682) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 1) (A 0)) (C (C (A 28013) (A 0)) (A 4)))))))),
    (C (A 2) (C (A 0) (C (A 0) (C (A 6714218) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (A 2) (C (C (A 28013) (A 0)) (A 4)))))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 3) (A 1))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 4) (C (A 0) (C (C (C (A 6579560) (C (A 2) (A 4))) (C (C (A 7102836) (C (A 2) (A 3))) (A 0))) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (A 0) (C (A 0) (C (A 7433315) (C (A 2) (C (C (A 0) (A 4)) (C (A 0) (A 2))))))))])

/- `rt`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rt inl_rt (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 2 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 1))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 6712682) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 1) (A 0)) (C (C (A 28013) (A 0)) (A 4))))))))])

/- `rt`, the n-ary code of its callee 0 (`nary.cache`, from its `inl.cache` nomm). -/
#guard ringNary env_rt (Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n7 (Nomm.n10 3 (Nomm.n0 7) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n0 3)) (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 9 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 8)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (A 0) (C (A 6712682) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 2) (A 0)) (C (C (A 28013) (A 0)) (A 4)))))))),
    (C (A 6) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 4))) (C (C (A 7103843) (A 4)) (C (C (A 7102836) (C (A 4) (A 5))) (C (C (A 7761773) (C (A 5) (A 2))) (A 0))))) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 7) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 1))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 8) (C (A 0) (C (A 0) (C (A 7433315) (C (A 3) (C (C (A 0) (A 6)) (C (A 0) (A 7))))))))])

/-- The environment of `rn`. -/
def env_rn : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4)))]

/-- The nomm of `rn`. -/
def nomm_rn : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n4 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none))))))

/-- The inlined nomm of `rn` (`inl.cache`). -/
def inl_rn : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n4 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none))))))

/- `rn`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rn nomm_rn 9 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 6))) (A 0)) (C (A 7368552) (C (A 0) (A 8)))))),
    (C (A 1) (C (A 0) (C (C (C (A 6516329) (C (A 2) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7761773) (C (A 4) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (C (A 5) (A 0)) (C (C (C (A 7761773) (C (A 5) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 4) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 3) (A 0)) (C (A 7) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 7)) (A 0)) (A 3)))))),
    (C (A 5) (C (A 0) (C (C (C (A 6714211) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (A 6) (C (A 8) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 8)) (A 0)) (A 3)))))),
    (C (A 6) (C (A 0) (C (C (C (A 7761773) (C (A 9) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 4)))))),
    (C (A 7) (C (A 0) (C (C (C (A 6579560) (C (A 6) (A 10))) (C (C (A 7102836) (C (A 6) (A 9))) (A 0))) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 8) (C (A 0) (C (A 0) (C (A 7433315) (C (A 6) (C (C (A 0) (A 7)) (C (A 0) (A 5))))))))])

/- `rn`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rn inl_rn (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 4 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 1) (C (A 0) (C (C (C (A 6516329) (C (A 2) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7761773) (C (A 4) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 3) (A 0)) (C (A 4) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 2))))))])

/-- The environment of `rc`. -/
def env_rc : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4)))]

/-- The nomm of `rc`. -/
def nomm_rc : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.cons (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n0 1)))

/-- The inlined nomm of `rc` (`inl.cache`). -/
def inl_rc : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.cons (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n0 1)))

/- `rc`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rc nomm_rc 11 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 7))) (A 0)) (C (A 7368552) (C (A 0) (A 10)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7237475) (C (A 2) (C (A 3) (A 1)))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 4) (C (A 0) (C (C (C (A 7761773) (C (A 5) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (C (A 6) (A 0)) (C (C (C (A 7761773) (C (A 6) (A 5))) (A 0)) (C (A 7368552) (C (A 0) (A 4)))))),
    (C (A 6) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 4) (A 0)) (C (A 8) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 8)) (A 0)) (A 5)))))),
    (C (A 7) (C (A 0) (C (C (C (A 6714211) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (A 7) (C (A 9) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 9)) (A 0)) (A 5)))))),
    (C (A 8) (C (A 0) (C (C (C (A 7761773) (C (A 10) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 9) (C (A 0) (C (C (C (A 6579560) (C (A 7) (A 11))) (C (C (A 7102836) (C (A 7) (A 10))) (A 0))) (C (A 7368552) (C (A 0) (A 8)))))),
    (C (A 10) (C (A 0) (C (A 0) (C (A 7433315) (C (A 7) (C (C (A 0) (A 9)) (C (A 0) (A 7))))))))])

/- `rc`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rc inl_rc (C (A 1752461154) (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0)))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 6 ==
  some ((C (A 1752461154) (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0)))), 2,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 1) (A 5))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 7237476) (A 2))))),
    (C (A 2) (C (A 0) (C (C (C (A 7237475) (C (A 3) (C (A 4) (A 2)))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 4) (C (A 0) (C (C (C (A 7761773) (C (A 6) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 5) (A 0)) (C (A 6) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 4))))))])

/-- The environment of `rk`. -/
def env_rk : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4)))]

/-- The nomm of `rk`. -/
def nomm_rk : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none))))))

/-- The inlined nomm of `rk` (`inl.cache`). -/
def inl_rk : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none))))))

/- `rk`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rk nomm_rk 11 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 7))) (A 0)) (C (A 7368552) (C (A 0) (A 10)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7237475) (C (A 2) (C (A 3) (A 1)))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 4) (C (A 0) (C (C (C (A 7761773) (C (A 5) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (C (A 6) (A 0)) (C (C (C (A 7761773) (C (A 6) (A 5))) (A 0)) (C (A 7368552) (C (A 0) (A 4)))))),
    (C (A 6) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 4) (A 0)) (C (A 8) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 8)) (A 0)) (A 5)))))),
    (C (A 7) (C (A 0) (C (C (C (A 6714211) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (A 7) (C (A 9) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 9)) (A 0)) (A 5)))))),
    (C (A 8) (C (A 0) (C (C (C (A 7761773) (C (A 10) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 9) (C (A 0) (C (C (C (A 6579560) (C (A 7) (A 11))) (C (C (A 7102836) (C (A 7) (A 10))) (A 0))) (C (A 7368552) (C (A 0) (A 8)))))),
    (C (A 10) (C (A 0) (C (A 0) (C (A 7433315) (C (A 7) (C (C (A 0) (A 9)) (C (A 0) (A 7))))))))])

/- `rk`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rk inl_rk (C (A 1752461154) (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0)))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 6 ==
  some ((C (A 1752461154) (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0)))), 2,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 1) (A 5))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 7237476) (A 2))))),
    (C (A 2) (C (A 0) (C (C (C (A 7237475) (C (A 3) (C (A 4) (A 2)))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 4) (C (A 0) (C (C (C (A 7761773) (C (A 6) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 5) (A 0)) (C (A 6) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 4))))))])

/-- The environment of `rp`. -/
def env_rp : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4)))]

/-- The nomm of `rp`. -/
def nomm_rp : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n6 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n1 (A 7)) (Nomm.n1 (A 8))))

/-- The inlined nomm of `rp` (`inl.cache`). -/
def inl_rp : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n6 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n1 (A 7)) (Nomm.n1 (A 8))))

/- `rp`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rp nomm_rp 13 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 7))) (A 0)) (C (A 7368552) (C (A 0) (A 12)))))),
    (C (A 1) (C (A 0) (C (C (C (A 7171433) (C (A 8) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7171433) (C (A 7) (A 2))) (A 0)) (C (A 7237476) (A 2))))),
    (C (A 5) (C (A 0) (C (A 0) (C (A 7238242) (C (A 4) (C (C (A 0) (A 2)) (C (A 0) (A 1)))))))),
    (C (A 6) (C (A 0) (C (C (C (A 7761773) (C (A 5) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 7) (C (C (A 6) (A 0)) (C (C (C (A 7761773) (C (A 6) (A 5))) (A 0)) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 8) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 3) (A 0)) (C (A 8) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 8)) (A 0)) (A 7)))))),
    (C (A 9) (C (A 0) (C (C (C (A 6714211) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (A 7) (C (A 9) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (C (C (A 0) (A 9)) (A 0)) (A 7)))))),
    (C (A 10) (C (A 0) (C (C (C (A 7761773) (C (A 10) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 8)))))),
    (C (A 11) (C (A 0) (C (C (C (A 6579560) (C (A 7) (A 11))) (C (C (A 7102836) (C (A 7) (A 10))) (A 0))) (C (A 7368552) (C (A 0) (A 10)))))),
    (C (A 12) (C (A 0) (C (A 0) (C (A 7433315) (C (A 7) (C (C (A 0) (A 11)) (C (A 0) (A 9))))))))])

/- `rp`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rp inl_rp (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 8 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 7)))))),
    (C (A 1) (C (A 0) (C (C (C (A 7171433) (C (A 8) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7171433) (C (A 7) (A 2))) (A 0)) (C (A 7237476) (A 2))))),
    (C (A 5) (C (A 0) (C (A 0) (C (A 7238242) (C (A 4) (C (C (A 0) (A 2)) (C (A 0) (A 1)))))))),
    (C (A 6) (C (A 0) (C (C (C (A 7761773) (C (A 5) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 7) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 3) (A 0)) (C (A 5) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 6))))))])

/-- The environment of `rb`. -/
def env_rb : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4)))]

/-- The nomm of `rb`. -/
def nomm_rb : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n1 (A 0))))

/-- The inlined nomm of `rb` (`inl.cache`). -/
def inl_rb : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n1 (A 0))))

/- `rb`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rb nomm_rb 11 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 7))) (C (C (A 7103843) (A 7)) (C (C (A 7102836) (C (A 7) (A 8))) (C (C (A 7761773) (C (A 8) (A 6))) (A 0))))) (C (A 7368552) (C (A 0) (A 10)))))),
    (C (A 1) (C (A 0) (C (C (C (A 7171433) (C (A 0) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (A 0) (C (A 6712682) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 2) (A 0)) (C (C (A 28013) (A 0)) (A 4)))))))),
    (C (A 3) (C (A 0) (C (A 0) (C (A 6714218) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (A 3) (C (C (A 28013) (A 0)) (A 4)))))))),
    (C (A 4) (C (A 0) (C (C (C (A 7761773) (C (A 4) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 5) (C (A 0) (C (C (C (A 6579560) (C (A 3) (A 5))) (C (C (A 7102836) (C (A 3) (A 4))) (A 0))) (C (A 7368552) (C (A 0) (A 4)))))),
    (C (A 6) (C (A 0) (C (A 0) (C (A 7433315) (C (A 3) (C (C (A 0) (A 5)) (C (A 0) (A 3)))))))),
    (C (A 8) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 10) (C (A 0) (C (A 0) (C (A 7433315) (C (A 6) (C (C (A 0) (A 8)) (C (A 0) (A 1))))))))])

/- `rb`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rb inl_rb (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 7 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 1) (C (A 0) (C (C (C (A 7171433) (C (A 0) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (A 0) (C (A 6712682) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 2) (A 0)) (C (C (A 28013) (A 0)) (A 4)))))))),
    (C (A 4) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 6) (C (A 0) (C (A 0) (C (A 7433315) (C (A 3) (C (C (A 0) (A 4)) (C (A 0) (A 1))))))))])

/-- The environment of `rm`. -/
def env_rm : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 10))),
    ((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4)))]

/-- The nomm of `rm`. -/
def nomm_rm : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1)))))), Option.none)))))

/-- The inlined nomm of `rm` (`inl.cache`). -/
def inl_rm : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n4 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none))))))))

/- `rm`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rm nomm_rm 6 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 6712682) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (C (A 28013) (A 0)) (A 10)))))))),
    (C (A 2) (C (A 0) (C (A 0) (C (A 6714218) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (A 2) (C (C (A 28013) (A 0)) (A 10)))))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 3) (A 1))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 4) (C (A 0) (C (C (C (A 6579560) (C (A 2) (A 4))) (C (C (A 7102836) (C (A 2) (A 3))) (A 0))) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (A 0) (C (A 0) (C (A 7433315) (C (A 2) (C (C (A 0) (A 4)) (C (A 0) (A 2))))))))])

/- `rm`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rm inl_rm (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (C (A 0) (A 1))) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (C (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1))))) (A 0))) (A 0))) 4 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 1) (C (A 0) (C (C (C (A 6516329) (C (A 2) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7761773) (C (A 4) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 3) (A 0)) (C (A 4) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 2))))))])

/- `rm`, the n-ary code of its callee 0 (`nary.cache`, from its `inl.cache` nomm). -/
#guard ringNary env_rm (Nomm.n4 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none))))) (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) 4 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 1) (C (A 0) (C (C (C (A 6516329) (C (A 2) (A 1))) (A 0)) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7761773) (C (A 4) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 3) (A 0)) (C (A 4) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 2))))))])

/-- The environment of `rx`. -/
def env_rx : CallEnv := envRing [((C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 4))),
    ((C (C (C (C (A 0) (C (A 0) (A 1))) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (C (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1))))) (A 0))) (A 0))) (C (C (A 9) (C (A 4) (C (A 0) (A 1)))) (C (A 9) (C (A 10) (C (A 0) (A 1)))))), (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), (C (C (A 28013) (A 0)) (A 11)))]

/-- The nomm of `rx`. -/
def nomm_rx : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (C (A 9) (C (A 4) (C (A 0) (A 1)))) (C (A 9) (C (A 10) (C (A 0) (A 1)))))) (some (bellN (C (C (C (C (A 0) (C (A 0) (A 1))) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (C (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1))))) (A 0))) (A 0))) (C (C (A 9) (C (A 4) (C (A 0) (A 1)))) (C (A 9) (C (A 10) (C (A 0) (A 1)))))), Option.none)))))

/-- The inlined nomm of `rx` (`inl.cache`). -/
def inl_rx : Nomm := (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.cons (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n4 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))))))))))

/- `rx`, the whole-subject code (`+compiled-mono`). -/
#guard ringMono env_rx nomm_rx 6 ==
  some ((C (A 1936287860) (A 0)), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 6712682) (C (C (C (C (C (A 0) (C (A 0) (A 1))) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (C (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1))))) (A 0))) (A 0))) (C (C (A 9) (C (A 4) (C (A 0) (A 1)))) (C (A 9) (C (A 10) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (C (A 28013) (A 0)) (A 11)))))))),
    (C (A 2) (C (A 0) (C (A 0) (C (A 6714218) (C (C (C (C (C (A 0) (C (A 0) (A 1))) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (C (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1))))) (A 0))) (A 0))) (C (C (A 9) (C (A 4) (C (A 0) (A 1)))) (C (A 9) (C (A 10) (C (A 0) (A 1)))))) (C (A 2) (C (C (A 28013) (A 0)) (A 11)))))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 3) (A 1))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 4) (C (A 0) (C (C (C (A 6579560) (C (A 2) (A 4))) (C (C (A 7102836) (C (A 2) (A 3))) (A 0))) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (A 0) (C (A 0) (C (A 7433315) (C (A 2) (C (C (A 0) (A 4)) (C (A 0) (A 2))))))))])

/- `rx`, the n-ary code (`+compiled-nary`). -/
#guard ringNary env_rx inl_rx (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (C (A 0) (A 0))) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (C (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1))))) (C (C (A 9) (C (A 4) (C (A 0) (A 1)))) (C (A 9) (C (A 10) (C (A 0) (A 1))))))) (A 0))) 11 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 7))) (A 0)) (C (A 7368552) (C (A 0) (A 10)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7237475) (C (A 2) (C (A 3) (A 1)))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 8) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 4) (C (A 0) (C (C (C (A 6516329) (C (A 4) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (A 0) (C (C (C (A 7761773) (C (A 6) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 4)))))),
    (C (A 6) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 5) (A 0)) (C (A 6) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 8) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 5))) (A 0)) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 10) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 7) (A 0)) (C (A 8) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 8))))))])

/- `rx`, the n-ary code of its callee 1 (`nary.cache`, from its `inl.cache` nomm). -/
#guard ringNary env_rx (Nomm.cons (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))) (Nomm.n7 (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n4 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (some (bellN (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))), Option.none)))))))) (C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))) (C (C (C (A 0) (C (A 0) (A 1))) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (C (C (A 4) (C (A 9) (C (A 4) (C (A 0) (A 1))))) (A 0))) (A 0))) 11 ==
  some ((C (C (A 1701736302) (A 0)) (C (A 1936287860) (A 0))), 1,
    [(C (A 0) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 7))) (A 0)) (C (A 7368552) (C (A 0) (A 10)))))),
    (C (A 1) (C (A 0) (C (A 0) (C (A 7237476) (A 1))))),
    (C (A 2) (C (A 0) (C (C (C (A 7237475) (C (A 2) (C (A 3) (A 1)))) (A 0)) (C (A 7368552) (C (A 0) (A 1)))))),
    (C (A 3) (C (A 0) (C (C (C (A 7761773) (C (A 8) (A 2))) (A 0)) (C (A 7368552) (C (A 0) (A 2)))))),
    (C (A 4) (C (A 0) (C (C (C (A 6516329) (C (A 4) (A 3))) (A 0)) (C (A 7368552) (C (A 0) (A 3)))))),
    (C (A 5) (C (A 0) (C (C (C (A 7761773) (C (A 6) (A 4))) (A 0)) (C (A 7368552) (C (A 0) (A 4)))))),
    (C (A 6) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 5) (A 0)) (C (A 6) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 5)))))),
    (C (A 8) (C (A 0) (C (C (C (A 7761773) (C (A 0) (A 5))) (A 0)) (C (A 7368552) (C (A 0) (A 6)))))),
    (C (A 10) (C (A 0) (C (C (C (A 6709603) (C (C (C (C (C (A 0) (A 1)) (A 1)) (C (C (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))) (A 0)) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 3))) (C (C (A 9) (C (A 4) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3)))))) (C (C (A 7) (A 0)) (C (A 8) (C (C (A 28013) (A 0)) (A 4)))))) (A 0)) (C (A 7368552) (C (A 0) (A 8))))))])

end Comp
end SkaModel
end Formalization
