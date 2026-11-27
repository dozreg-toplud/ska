import lemmas.Compiler.CompSccLoopSt
import lemmas.Ska.SccLoopDfs
import lemmas.Hoon.TapIn
import lemmas.Hoon.DifIn
import lemmas.Hoon.Lists

/-! # The DFS postorder of `+compile-scc-in` in the pill (README Gaps 21.11, item 1)

`csfOrder` (the bunt of `[vis out]`, `stk`, `roots = ~(tap in scc)`, the trap `csfOrdTrap`)
against the model `dfsOrder` of `Ska/SccLoopDfs.lean`, on the kids lists `kidsL KIDS`
(`~(tap in (~(get ju kids) b))`).

* The trap core `ordCore ROOTS STK VIS OUT S0` (`roots` at axis 6, `stk` at 14, `vis` at 60,
  `out` at 61, the subject of `csiFix` at 31).
* One lemma per branch of the trap: `ord_end` (`(flop out)`), `ord_root_skip`, `ord_root_push`,
  `ord_pop`, `ord_kid_skip`, `ord_kid_push`.
* `ord_trap`: wherever `dfsF` returns, the trap returns the same list (induction on the fuel).
* `csf_order`: `csfOrder` returns `(listN (dfsOrder (kidsL KIDS) (tapList SCC)))`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The kids of `b` as the DFS lists them: `~(tap in (~(get ju kids) b))`. -/
def kidsL (KIDS b : Noun) : List Noun := ((getF mugF b KIDS).map fun out => tapList (unUnit out)).getD []

/-- The noun of the DFS stack: a list of `[b kids]`. -/
def stkN (stk : List (Noun × List Noun)) : Noun := listN (stk.map fun f => C f.1 (listN f.2))

/-- The trap core of the DFS. -/
def ordCore (ROOTS STK VIS OUT S0 : Noun) : Noun := C csfOrdTrap (C ROOTS (C STK (C (C VIS OUT) S0)))

theorem tapF_tree {X : Noun} (h : Tree X) : tapF X (A 0) = some (listN (tapList X)) := by
  have := tapF_list h []
  simpa [listN, appendN] using this

/-! ## The branches of the trap -/

/-- `?~  roots  (flop out)`. -/
theorem ord_end (p : LoopP) (CA VIS : Noun) (out : List Noun) :
    nock (ordCore (A 0) (A 0) VIS (listN out) (p.subj (A 0) CA)) csfOrdTrap
      = some (listN out.reverse) := by
  have hL := compK_layer2
  have hf := flop_gate layer2 homoIn_layer2 out
  conv => { lhs; arg 2; unfold csfOrdTrap }
  unfold ordCore LoopP.subj csiSam
  generalize compK = KC at hL ⊢
  simp [nock_exec, hL, flop.arm_at, flop_arm, hf]

/-- A root already visited: `$(roots t.roots)`. -/
theorem ord_root_skip (p : LoopP) (CA r ROOTS VIS OUT : Noun) (hs : IsSet mugF VIS) (hr : Has VIS r) :
    nock (ordCore (C r ROOTS) (A 0) VIS OUT (p.subj (A 0) CA)) csfOrdTrap
      = nock (ordCore ROOTS (A 0) VIS OUT (p.subj (A 0) CA)) csfOrdTrap := by
  have hL := compK_layer2
  obtain ⟨t, ht, hiff⟩ := hasInF_spec mugF VIS r hs
  have ht' : t = true := hiff.2 hr
  subst ht'
  have hh := has_in_gate layer2 gorIn_morIn_layer2.1 r VIS true ht
  conv => { lhs; arg 2; unfold csfOrdTrap }
  unfold ordCore LoopP.subj csiSam
  generalize compK = KC at hL ⊢
  simp [nock_exec, hL, in.arm_at, in_arm, in.has.arm_at, has_in_arm, hh]

/-- A new root: `vis` with it, `stk` the one frame `[r ~(tap in (~(get ju kids) r))]`. -/
theorem ord_root_push (p : LoopP) (CA r ROOTS VIS OUT VIS' X : Noun) (hs : IsSet mugF VIS)
    (hr : ¬ Has VIS r) (hput : putInF mugF r VIS = some VIS') (hX : getF mugF r p.KIDS = some X)
    (hT : Tree (unUnit X)) :
    nock (ordCore (C r ROOTS) (A 0) VIS OUT (p.subj (A 0) CA)) csfOrdTrap
      = nock (ordCore ROOTS (C (C r (listN (tapList (unUnit X)))) (A 0)) VIS' OUT (p.subj (A 0) CA))
          csfOrdTrap := by
  have hL := compK_layer2
  obtain ⟨t, ht, hiff⟩ := hasInF_spec mugF VIS r hs
  have ht' : t = false := by
    cases t
    · rfl
    · exact absurd (hiff.1 rfl) hr
  subst ht'
  have hh := has_in_gate layer2 gorIn_morIn_layer2.1 r VIS false ht
  have hp := put_in_gate layer2 gorIn_morIn_layer2 r VIS VIS' hput
  have hju := ju_get_gate layer2 juIn_layer2 ju.battery r p.KIDS X hX
  have htap := tapF_tree hT
  conv => { lhs; arg 2; unfold csfOrdTrap }
  unfold ordCore LoopP.subj csiSam
  generalize compK = KC at hL ⊢
  simp [nock_exec, hL, in.arm_at, in_arm, in.has.arm_at, has_in_arm, hh, in.put.arm_at, put_in_arm,
    hp, in.tap.arm_at, tap_arm, tap_loop, htap, ju.arm_at, ju_arm, ju.get.arm_at, ju_get_arm, hju]

/-- A frame with no kid left: `$(stk t.stk, out [b.i.stk out])`. -/
theorem ord_pop (p : LoopP) (CA b STK ROOTS VIS OUT : Noun) :
    nock (ordCore ROOTS (C (C b (A 0)) STK) VIS OUT (p.subj (A 0) CA)) csfOrdTrap
      = nock (ordCore ROOTS STK VIS (C b OUT) (p.subj (A 0) CA)) csfOrdTrap := by
  conv => { lhs; arg 2; unfold csfOrdTrap }
  unfold ordCore LoopP.subj csiSam
  simp [nock_exec]

/-- A kid already visited: `$(stk stk1)`. -/
theorem ord_kid_skip (p : LoopP) (CA b k KS STK ROOTS VIS OUT : Noun) (hs : IsSet mugF VIS)
    (hk : Has VIS k) :
    nock (ordCore ROOTS (C (C b (C k KS)) STK) VIS OUT (p.subj (A 0) CA)) csfOrdTrap
      = nock (ordCore ROOTS (C (C b KS) STK) VIS OUT (p.subj (A 0) CA)) csfOrdTrap := by
  have hL := compK_layer2
  obtain ⟨t, ht, hiff⟩ := hasInF_spec mugF VIS k hs
  have ht' : t = true := hiff.2 hk
  subst ht'
  have hh := has_in_gate layer2 gorIn_morIn_layer2.1 k VIS true ht
  conv => { lhs; arg 2; unfold csfOrdTrap }
  unfold ordCore LoopP.subj csiSam
  generalize compK = KC at hL ⊢
  simp [nock_exec, hL, in.arm_at, in_arm, in.has.arm_at, has_in_arm, hh]

/-- A new kid: `vis` with it, its frame pushed on `stk1`. -/
theorem ord_kid_push (p : LoopP) (CA b k KS STK ROOTS VIS OUT VIS' X : Noun) (hs : IsSet mugF VIS)
    (hk : ¬ Has VIS k) (hput : putInF mugF k VIS = some VIS') (hX : getF mugF k p.KIDS = some X)
    (hT : Tree (unUnit X)) :
    nock (ordCore ROOTS (C (C b (C k KS)) STK) VIS OUT (p.subj (A 0) CA)) csfOrdTrap
      = nock (ordCore ROOTS (C (C k (listN (tapList (unUnit X)))) (C (C b KS) STK)) VIS' OUT
          (p.subj (A 0) CA)) csfOrdTrap := by
  have hL := compK_layer2
  obtain ⟨t, ht, hiff⟩ := hasInF_spec mugF VIS k hs
  have ht' : t = false := by
    cases t
    · rfl
    · exact absurd (hiff.1 rfl) hk
  subst ht'
  have hh := has_in_gate layer2 gorIn_morIn_layer2.1 k VIS false ht
  have hp := put_in_gate layer2 gorIn_morIn_layer2 k VIS VIS' hput
  have hju := ju_get_gate layer2 juIn_layer2 ju.battery k p.KIDS X hX
  have htap := tapF_tree hT
  conv => { lhs; arg 2; unfold csfOrdTrap }
  unfold ordCore LoopP.subj csiSam
  generalize compK = KC at hL ⊢
  simp [nock_exec, hL, in.arm_at, in_arm, in.has.arm_at, has_in_arm, hh, in.put.arm_at, put_in_arm,
    hp, in.tap.arm_at, tap_arm, tap_loop, htap, ju.arm_at, ju_arm, ju.get.arm_at, ju_get_arm, hju]

/-! ## The trap against `dfsF` -/

theorem kidsL_of {KIDS b X : Noun} (h : getF mugF b KIDS = some X) : kidsL KIDS b = tapList (unUnit X) := by
  simp [kidsL, h]

theorem stkN_cons (b : Noun) (ks : List Noun) (stk : List (Noun × List Noun)) :
    stkN ((b, ks) :: stk) = C (C b (listN ks)) (stkN stk) := rfl

/-- **The trap against `dfsF`**: wherever `dfsF (kidsL KIDS) n vis out stk roots` returns `l`, the
trap on the nouns of `[roots stk vis out]` returns `(listN l)`, when the roots left and the kids on
the stack are members (`DfsInv`), each member has a kids set in `KIDS` (`hk`) and the kids of a
member are members (`hin`). -/
theorem ord_trap (p : LoopP) (CA : Noun) (U : List Noun)
    (hk : ∀ b ∈ U, ∃ out, getF mugF b p.KIDS = some out ∧ Tree (unUnit out))
    (hin : ∀ b ∈ U, ∀ k ∈ kidsL p.KIDS b, k ∈ U) :
    ∀ (n : Nat) (vis out : List Noun) (stk : List (Noun × List Noun)) (roots l : List Noun),
      dfsF (kidsL p.KIDS) n vis out stk roots = some l → DfsInv U stk roots →
      ∀ VIS, IsSet mugF VIS → (∀ x, Has VIS x ↔ x ∈ vis) →
      nock (ordCore (listN roots) (stkN stk) VIS (listN out) (p.subj (A 0) CA)) csfOrdTrap
        = some (listN l) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; simp [dfsF] at h
  | succ n ih =>
    intro vis out stk roots l h hi VIS hs hv
    match stk, roots with
    | [], [] =>
      simp only [dfsF, Option.some.injEq] at h; subst h
      exact ord_end p CA VIS out
    | [], r :: rs =>
      have hr : r ∈ U := hi.1 r (List.mem_cons_self ..)
      have hrs : ∀ x ∈ rs, x ∈ U := fun x hx => hi.1 x (List.mem_cons_of_mem _ hx)
      simp only [dfsF] at h
      split at h
      · next hm =>
        have e := ord_root_skip p CA r (listN rs) VIS (listN out) hs ((hv r).2 hm)
        simp only [listN, appendN, stkN, List.map_nil] at e ⊢
        rw [e]
        exact ih _ _ _ _ _ h ⟨hrs, by simp⟩ VIS hs hv
      · next hm =>
        obtain ⟨X, hX, hT⟩ := hk r hr
        obtain ⟨VIS', hput, hs', hv'⟩ := putInF_spec mugF VIS r hs
        have e := ord_root_push p CA r (listN rs) VIS (listN out) VIS' X hs (fun h => hm ((hv r).1 h))
          hput hX hT
        have hih := ih _ _ _ _ _ h ⟨hrs, by
          intro f hf k hk'; simp at hf; subst hf; exact hin r hr k hk'⟩ VIS' hs' (by
          intro x; rw [hv' x, hv x]; simp)
        rw [kidsL_of hX] at hih
        simp only [listN, appendN, stkN, List.map_nil, List.map_cons] at e hih ⊢
        rw [e]; exact hih
    | (b, []) :: stk, roots =>
      simp only [dfsF] at h
      have e := ord_pop p CA b (stkN stk) (listN roots) VIS (listN out)
      have hih := ih _ _ _ _ _ h ⟨hi.1, fun f hf => hi.2 f (List.mem_cons_of_mem _ hf)⟩ VIS hs hv
      rw [stkN_cons]
      simp only [listN, appendN] at e hih ⊢
      rw [e]; exact hih
    | (b, k :: ks) :: stk, roots =>
      have hk0 : k ∈ U := hi.2 (b, k :: ks) (List.mem_cons_self ..) k (List.mem_cons_self ..)
      have hks : ∀ x ∈ ks, x ∈ U :=
        fun x hx => hi.2 (b, k :: ks) (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx)
      have hst : ∀ f ∈ stk, ∀ x ∈ f.2, x ∈ U := fun f hf => hi.2 f (List.mem_cons_of_mem _ hf)
      simp only [dfsF] at h
      split at h
      · next hm =>
        have e := ord_kid_skip p CA b k (listN ks) (stkN stk) (listN roots) VIS (listN out) hs
          ((hv k).2 hm)
        have hih := ih _ _ _ _ _ h ⟨hi.1, by
          intro f hf; rcases List.mem_cons.1 hf with rfl | hf
          · exact hks
          · exact hst f hf⟩ VIS hs hv
        rw [stkN_cons]
        rw [stkN_cons] at hih
        simp only [listN, appendN] at e hih ⊢
        rw [e]; exact hih
      · next hm =>
        obtain ⟨X, hX, hT⟩ := hk k hk0
        obtain ⟨VIS', hput, hs', hv'⟩ := putInF_spec mugF VIS k hs
        have e := ord_kid_push p CA b k (listN ks) (stkN stk) (listN roots) VIS (listN out) VIS' X hs
          (fun h => hm ((hv k).1 h)) hput hX hT
        have hih := ih _ _ _ _ _ h ⟨hi.1, by
          intro f hf; rcases List.mem_cons.1 hf with rfl | hf
          · exact hin k hk0
          · rcases List.mem_cons.1 hf with rfl | hf
            · exact hks
            · exact hst f hf⟩ VIS' hs' (by intro x; rw [hv' x, hv x]; simp)
        rw [kidsL_of hX, stkN_cons, stkN_cons] at hih
        rw [stkN_cons]
        simp only [listN, appendN] at e hih ⊢
        rw [e]; exact hih

/-- **`csfOrder` against `dfsOrder`**: on the subject of `csiFix`, with `scc` a set, a kids set
in `KIDS` at each member, and the kids of a member members, the DFS returns the list of
`dfsOrder (kidsL KIDS) ~(tap in scc)`. -/
theorem csf_order (p : LoopP) (CA : Noun) (hscc : IsSet mugF p.SCC)
    (hk : ∀ b ∈ tapList p.SCC, ∃ out, getF mugF b p.KIDS = some out ∧ Tree (unUnit out))
    (hin : ∀ b ∈ tapList p.SCC, ∀ k ∈ kidsL p.KIDS b, k ∈ tapList p.SCC) :
    nock (p.subj (A 0) CA) csfOrder = some (listN (dfsOrder (kidsL p.KIDS) (tapList p.SCC))) := by
  have ht := ord_trap p CA (tapList p.SCC) hk hin _ [] [] [] (tapList p.SCC) _
    (dfsF_total (kidsL p.KIDS) (tapList p.SCC) hin) ⟨fun r hr => hr, by simp⟩ (A 0) isSet_nil
    (fun x => by simp [not_has_atom])
  have hL := compK_layer2
  have htap := tapF_tree (Tree.of_isSet hscc)
  simp only [stkN, List.map_nil, listN, appendN] at ht
  unfold ordCore at ht
  unfold csfOrder
  unfold LoopP.subj csiSam at ht ⊢
  generalize compK = KC at hL ht ⊢
  simp [nock_exec, hL, csfOrdRoots, csfOrdBunt, in.arm_at, in_arm, in.tap.arm_at, tap_arm, tap_loop, htap]
  exact ht

end Compiler
end Formalization
