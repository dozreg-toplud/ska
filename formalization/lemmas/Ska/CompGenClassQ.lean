import lemmas.Ska.CompGenClassP
import lemmas.Ska.CompGenClassM

/-!
# The widened class with hops up: `NextGXU`, the fragment `GenFrag6`, the induction

README Gaps 12.39, item 12 (g).  `NextGX` (`CompGenClassP.lean`) cannot
close its own `[7 p q]` and cons: the second part's `PremG` asks `UpBelow`
of the state after the first part, and the top's `RunOKGD` asks `GrowU`;
`NextGCS` got both from `GrowU` (`guq.up H.up`, `closedS_n7`), and `GrowG`
drops `GrowU.new`'s hops-up half (`JumpsU` of the new blocks).  `NextGXU`
puts it back as its own clause `JNewG` (checked: `CompGenClassCheckX.lean`,
clauses `jnew`, `upEnd`).  From it, with `Clear` and the re-pointings'
targets, the state after a run is `UpBelow` and `Clear` again
(`upBelow_growG`, `clear_growG`), and under a goal with no entry the run
grows as `GrowU` (`growU_of_growG`).

`GenFrag6`: `GenFrag` with `[6 c a b]`, the test `%6`-free (`GenFrag`: it
runs under `%pick`, whose class is `PickD`), the branches any.  The closures
in `NextGXU` are exact `Prop`s (`ClosedXN3` ... `ClosedXN6`); `[0 a]` and
`[1 k]` are proved (`closedX_n0`, `closedX_n1`, from `NextGCS`);
`nextGXU_all_of` is the one induction from the others.  The top:
`contract_genFrag6_of` (a cons or `[0 a]` at the root, `%done` into
`[don re]`), the contract from the closures.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The hops-up clause -/

/-- **`GrowU.new`'s hops-up half**: every block that is new in `g1`
meets `JumpsU`. -/
def JNewG (g0 g1 : Gen Map) : Prop :=
  ∀ k b', HoonMap.get g1.blocks k = some b' → HoonMap.get g0.blocks k = Option.none →
    JumpsU g1.blocks g1.bo k b'.fin

theorem GrowU.jnew {g0 g1 : Gen Map} (h : GrowU g0 g1) : JNewG g0 g1 := fun k b' hb h0 => by
  rcases h.new k b' hb with ⟨b, hb0, _, _⟩ | ⟨_, _, hj⟩
  · rw [h0] at hb0; cases hb0
  · exact hj

/-- **The state after a run is `Clear`.** -/
theorem clear_growG {L : Lazy S} {g0 g1 : Gen Map} (hc : Clear g0) (G : GrowG L g0 g1) (hbo : g0.bo ≤ g1.bo) :
    Clear g1 := fun k hk => by
  cases e : HoonMap.get g1.blocks k with
  | none => rfl
  | some b' =>
    exfalso
    rcases G.new k b' e with ⟨b, hb, _⟩ | ⟨_, u⟩
    · rw [hc k (by omega)] at hb; cases hb
    · omega

/-- **The state after a run is `UpBelow`**: an old block keeps its
terminator or is re-pointed (a hop to a new label), a new one hops up only
below the end (`JumpsU`). -/
theorem upBelow_growG {L : Lazy S} {g0 g1 : Gen Map} (hu : UpBelow g0) (hc : Clear g0) (G : GrowG L g0 g1)
    (J : JNewG g0 g1) (hbo : g0.bo ≤ g1.bo) : UpBelow g1 := by
  intro u t hup
  obtain ⟨b', j, hb', hf, ht, hlt⟩ := hup
  cases e0 : HoonMap.get g0.blocks u with
  | none =>
    have hj := (J u b' hb' e0) j (by rw [hf]; simp [finJumps])
    rcases hj.2 with ⟨h1, _⟩ | ⟨_, _, h3, _⟩
    · omega
    · omega
  | some b =>
    have hu0 : u < g0.bo := Classical.byContradiction fun hn => by rw [hc u (by omega)] at e0; cases e0
    obtain ⟨b'', hb'', _, hfin⟩ := G.keep u b hu0 e0
    rw [hb'] at hb''
    cases hb''
    rcases hfin with hfin | ⟨_, B, fin, F, o1, o2, F2, h0, h1, l1, u1, _⟩
    · have := hu u t ⟨b, j, e0, hfin ▸ hf, ht, hlt⟩
      omega
    · rw [hb'] at h1
      cases h1
      simp only [Termin.hop.injEq] at hf
      subst hf
      simp at ht
      omega

/-- **Under a goal with no entry, `GrowG` and `JNewG` are `GrowU`.** -/
theorem growU_of_growG {L : Lazy S} {g0 g1 : Gen Map} (hL : entries L = []) (hc : Clear g0) (G : GrowG L g0 g1)
    (J : JNewG g0 g1) (hbo : g0.bo ≤ g1.bo) (hd : g1.drop = g0.drop) : GrowU g0 g1 where
  bo := hbo
  drop := hd
  keep := fun k b hk hb => by
    obtain ⟨b', h1, h2, h3⟩ := G.keep k b hk hb
    refine ⟨b', h1, h2, ?_⟩
    rcases h3 with h3 | ⟨hm, _⟩
    · exact h3
    · rw [hL] at hm; cases hm
  new := fun k b' hb => by
    cases e0 : HoonMap.get g0.blocks k with
    | none =>
      rcases G.new k b' hb with ⟨b, h0, _⟩ | ⟨l, u⟩
      · rw [e0] at h0; cases h0
      · exact Or.inr ⟨l, u, J k b' hb e0⟩
    | some b =>
      have hk : k < g0.bo := Classical.byContradiction fun hn => by rw [hc k (by omega)] at e0; cases e0
      obtain ⟨b'', h1, h2, h3⟩ := G.keep k b hk e0
      rw [hb] at h1
      cases h1
      rcases h3 with h3 | ⟨hm, _⟩
      · exact Or.inl ⟨b, (by first | rfl | exact e0), h2, h3⟩
      · rw [hL] at hm; cases hm

/-! ## The class -/

/-- **The widened class with hops up, `NextGXU`**: `NextGX` and `JNewG`. -/
abbrev NextGXU (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {L : Lazy S} {th : Jmp} {nex : NextL S},
    PremG (Map := Map) L th g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ∃ (Q : Wit) (x : Bool), RunOKGen lib N P f L th Q x g0 g1 nex ∧ GrowG L g0 g1 ∧ JNewG g0 g1 ∧
      ResG (Map := Map) L g0 g1 nex.laz ∧ FrontsSGX (Map := Map) Q x g0 g1 L nex

theorem NextGXU.toGX {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : NextGXU (S := S) (Map := Map) lib N env P f nm) : NextGX (S := S) (Map := Map) lib N env P f nm :=
  fun H hr => let ⟨Q, x, R, g, _, r, fs⟩ := h H hr; ⟨Q, x, R, g, r, fs⟩

/-- `NextGCS` is the case `x = false`, no re-pointing. -/
theorem NextGCS.toGXU {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : NextGCS (S := S) (Map := Map) lib N env P f nm) : NextGXU (S := S) (Map := Map) lib N env P f nm :=
  fun H hr =>
    let ⟨Q, R, g, _, r, fs⟩ := h H hr
    ⟨Q, false, R, g.toG, g.jnew, r, fun a ha => Or.inl (fs a ha)⟩

/-- **The state after a run of the class meets `PremG`'s state fields.** -/
theorem NextGXU.state {L : Lazy S} {th : Jmp} {g0 g1 : Gen Map} (H : PremG (Map := Map) L th g0)
    (G : GrowG L g0 g1) (J : JNewG g0 g1) (hbo : g0.bo ≤ g1.bo) : UpBelow g1 ∧ Clear g1 :=
  ⟨upBelow_growG H.up H.clr G J hbo, clear_growG H.clr G hbo⟩

/-! ## The fragment -/

/-- **The fragment with `%6`**: `GenFrag` with `[6 c a b]`, the test
`%6`-free, the branches any. -/
inductive GenFrag6 : Noun → Nomm → Prop
  | n0 {a : Nat} : 2 ≤ a → GenFrag6 (slot a) (Nomm.n0 a)
  | n1 (k : Noun) : GenFrag6 (quote k) (Nomm.n1 k)
  | n3 {f : Noun} {p : Nomm} : GenFrag6 f p → GenFrag6 (C (A 3) f) (Nomm.n3 p)
  | n4 {f : Noun} {p : Nomm} : GenFrag6 f p → GenFrag6 (C (A 4) f) (Nomm.n4 p)
  | n5 {fp fq : Noun} {p q : Nomm} : GenFrag6 fp p → GenFrag6 fq q → GenFrag6 (n3 (A 5) fp fq) (Nomm.n5 p q)
  | cons {fp fq : Noun} {p q : Nomm} : GenFrag6 fp p → GenFrag6 fq q → GenFrag6 (C fp fq) (Nomm.cons p q)
  | n7 {fb fc : Noun} {p q : Nomm} : GenFrag6 fb p → GenFrag6 fc q → GenFrag6 (n3 (A 7) fb fc) (Nomm.n7 p q)
  | n6 {fc fa fb : Noun} {c a b : Nomm} : GenFrag fc c → GenFrag6 fa a → GenFrag6 fb b →
      GenFrag6 (n4 (A 6) fc fa fb) (Nomm.n6 c a b)

theorem GenFrag.to6 {f : Noun} {nm : Nomm} (h : GenFrag f nm) : GenFrag6 f nm := by
  induction h with
  | n0 ha => exact GenFrag6.n0 ha
  | n1 k => exact GenFrag6.n1 k
  | n3 _ ih => exact GenFrag6.n3 ih
  | n4 _ ih => exact GenFrag6.n4 ih
  | n5 _ _ ihp ihq => exact GenFrag6.n5 ihp ihq
  | cons _ _ ihp ihq => exact GenFrag6.cons ihp ihq
  | n7 _ _ ihp ihq => exact GenFrag6.n7 ihp ihq

theorem genFrag6_pure {f : Noun} {nm : Nomm} (h : GenFrag6 f nm) : nm.pure = true := by
  induction h with
  | n0 _ => rfl
  | n1 _ => rfl
  | n3 _ ih => simp [Nomm.pure, ih]
  | n4 _ ih => simp [Nomm.pure, ih]
  | n5 _ _ ihp ihq => simp [Nomm.pure, ihp, ihq]
  | cons _ _ ihp ihq => simp [Nomm.pure, ihp, ihq]
  | n7 _ _ ihp ihq => simp [Nomm.pure, ihp, ihq]
  | n6 hc _ _ iha ihb => simp [Nomm.pure, genFrag_pure hc, iha, ihb]

/-! ## The closures in `NextGXU` -/

section Ifaces
variable (S Map)

def ClosedXN3 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {f : Noun} {p : Nomm}, GenFrag6 f p → (∀ P, NextGXU (S := S) (Map := Map) lib N env P f p) →
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (C (A 3) f) (Nomm.n3 p)

def ClosedXN4 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {f : Noun} {p : Nomm}, GenFrag6 f p → (∀ P, NextGXU (S := S) (Map := Map) lib N env P f p) →
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (C (A 4) f) (Nomm.n4 p)

def ClosedXN5 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fp fq : Noun} {p q : Nomm}, GenFrag6 fp p → GenFrag6 fq q →
    (∀ P, NextGXU (S := S) (Map := Map) lib N env P fp p) → (∀ P, NextGXU (S := S) (Map := Map) lib N env P fq q) →
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (n3 (A 5) fp fq) (Nomm.n5 p q)

def ClosedXCons (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fp fq : Noun} {p q : Nomm}, GenFrag6 fp p → GenFrag6 fq q →
    (∀ P, NextGXU (S := S) (Map := Map) lib N env P fp p) → (∀ P, NextGXU (S := S) (Map := Map) lib N env P fq q) →
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (C fp fq) (Nomm.cons p q)

def ClosedXN7 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fb fc : Noun} {p q : Nomm}, GenFrag6 fb p → GenFrag6 fc q →
    (∀ P, NextGXU (S := S) (Map := Map) lib N env P fb p) → (∀ P, NextGXU (S := S) (Map := Map) lib N env P fc q) →
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q)

/-- `%6` under `%next`: the test `%6`-free (`GenFrag`, so `PickD` by
`pickD_of_uok`), the branches in the class. -/
def ClosedXN6 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fc fa fb : Noun} {c a b : Nomm}, GenFrag fc c → GenFrag6 fa a → GenFrag6 fb b →
    (∀ P, NextGXU (S := S) (Map := Map) lib N env P fa a) → (∀ P, NextGXU (S := S) (Map := Map) lib N env P fb b) →
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b)

end Ifaces

/-- **`[0 a]` in `NextGXU`.** -/
theorem closedX_n0 (lib : Lib) (N : Needs) (env : CallEnv) {a : Nat} (ha : 2 ≤ a) :
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (slot a) (Nomm.n0 a) :=
  fun P => NextGCS.toGXU (closedS_n0 lib N env ha P)

/-- **`[1 k]` in `NextGXU`.** -/
theorem closedX_n1 (lib : Lib) (N : Needs) (env : CallEnv) (k : Noun) :
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P (quote k) (Nomm.n1 k) :=
  fun P => NextGCS.toGXU (closedS_n1 lib N env k P)

/-- **The one induction in `NextGXU`, from the closures.** -/
theorem nextGXU_all_of {lib : Lib} {N : Needs} {env : CallEnv}
    (h3 : ClosedXN3 S Map lib N env) (h4 : ClosedXN4 S Map lib N env) (h5 : ClosedXN5 S Map lib N env)
    (hc : ClosedXCons S Map lib N env) (h7 : ClosedXN7 S Map lib N env) (h6 : ClosedXN6 S Map lib N env)
    {f : Noun} {nm : Nomm} (hf : GenFrag6 f nm) :
    ∀ P, NextGXU (S := S) (Map := Map) lib N env P f nm := by
  induction hf with
  | n0 ha => exact closedX_n0 lib N env ha
  | n1 k => exact closedX_n1 lib N env k
  | n3 hp ih => exact h3 hp ih
  | n4 hp ih => exact h4 hp ih
  | n5 hp hq ihp ihq => exact h5 hp hq ihp ihq
  | cons hp hq ihp ihq => exact hc hp hq ihp ihq
  | n7 hp hq ihp ihq => exact h7 hp hq ihp ihq
  | n6 hc' ha hb iha ihb => exact h6 hc' ha hb iha ihb

/-! ## The top -/

/-- **A cons or `[0 a]` under `%done`**, from `NextGXU` at the goal into
`[don re]` (`cm2_done_of_next` for the widened class: the goal has no
entry, so the run grows as `GrowU`). -/
theorem doneGS_of_nextGXU {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax))
    (H : NextGXU (S := S) (Map := Map) lib N env P f nm) : DoneGS S Map lib N env P f nm := by
  intro sup region g0 g2 nex b0 d0 hu hcl hcb hr
  rw [runLC_done_next env sup hs region g0] at hr
  have PG := cm2_premDon (S := S) b0 d0 hu hcl hcb
  obtain ⟨Q, x, R, gg, J, Res, FS⟩ := H PG hr
  have GU := growU_of_growG (entries_ofSure _) PG.clr gg J R.bo R.drop
  exact ⟨runOKGD_done_of_gen hu hcb d0 R GU, Res.lu, Res.cl, Res.ecl, Res.sa⟩

/-- **THE UNARY CONTRACT ON `GenFrag6` at a cons or `[0 a]` root, from the
closures**: the whole-subject code that `+comp`'s model makes has the need
`this` and meets both halves of the contract for its formula, at every
subject. -/
theorem contract_genFrag6_of (lib : Lib) (env : CallEnv) (N : Needs)
    (h3 : ClosedXN3 S Map lib N env) (h4 : ClosedXN4 S Map lib N env) (h5 : ClosedXN5 S Map lib N env)
    (hc : ClosedXCons S Map lib N env) (h7 : ClosedXN7 S Map lib N env) (h6 : ClosedXN6 S Map lib N env)
    {f : Noun} {nm : Nomm} (hf : GenFrag6 f nm)
    (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ ax, 2 ≤ ax ∧ nm = Nomm.n0 ax))
    {c : Straight Map} (h : finishLUC (S := S) (Map := Map) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  have hs' : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨
      (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax) := by
    rcases hs with hs | ⟨ax, hax, e⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inr ⟨ax, by omega, e⟩)
  have H := finishLUC_contractGD (P := fun _ => True) lib N
    (fun hr => (doneGS_of_nextGXU (S := S) (Map := Map) hs'
      (nextGXU_all_of h3 h4 h5 hc h7 h6 hf (fun _ => True)) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) h
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
