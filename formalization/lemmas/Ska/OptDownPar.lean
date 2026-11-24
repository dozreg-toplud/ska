import lemmas.Ska.OptTopoOK
import lemmas.Ska.OptMiddleBlocks
import lemmas.Ska.OptHopsBlocks

/-!
# `DownPar`: no jump passes a parameter of a block below its target

`DownPar bl`: no argument register of a jump is a parameter of a block
reachable from the jump's target (`RFrom`, reflexive).  Its case of the
target itself is `PassOK` (`downPar_passOK`).  It is the invariant that gives
`PassOK` of the result of `+remove-empty-middle`: a hop redirected past a
chain of empty blocks passes registers that the first jump or a hop of the
chain passed, and the new target lies below all of them.

On `+comp` output a parameter is defined only by the jumps into its block,
so a jump that moves it before reaching that block moves a register that is
not there yet.  Checked on the real compiler (`tools/hoon/optcheck.hoon`,
135 cases, 2026-11-24): `DownPar` holds on the raw code, after every pass of
every round of `+optimize` (194 rounds, 2229 checks) and on the output.

All three structural passes keep it: `rub_downPar` (old jumps, or a hop that
passes nothing), `hops_downPar` (a merged block ends as the last block of its
chain), `mid_downPar` (`rewriteJump_safe`, `rewriteHop_safe`: the arguments of
a redirected jump come from the first jump or from a hop of the chain, and the
new target lies below both).  Each keeps the parameters and makes no new
paths (every new jump is a path of the code before: `RFrom`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- Reachability from a label, reflexive. -/
inductive RFrom (bl : Map Blob) : Nat → Nat → Prop
  | refl (x : Nat) : RFrom bl x x
  | step {x z : Nat} {b : Blob} {j : Jmp} : HoonMap.get bl x = some b → j ∈ getJmps b.fin → RFrom bl j.there z →
      RFrom bl x z

theorem RFrom.trans {bl : Map Blob} {x y z : Nat} (h : RFrom bl x y) (h' : RFrom bl y z) : RFrom bl x z := by
  induction h with
  | refl => exact h'
  | step hb hj _ ih => exact RFrom.step hb hj (ih h')

theorem RFrom.one {bl : Map Blob} {x : Nat} {b : Blob} {j : Jmp} (hb : HoonMap.get bl x = some b)
    (hj : j ∈ getJmps b.fin) : RFrom bl x j.there :=
  RFrom.step hb hj (RFrom.refl _)

/-- No argument of `J` is a parameter of a block reachable from its target. -/
def Safe (bl : Map Blob) (J : Jmp) : Prop :=
  ∀ r, some r ∈ J.args → ∀ z bz, RFrom bl J.there z → HoonMap.get bl z = some bz → r ∉ bz.par

/-- **No jump passes a parameter of a block below its target.** -/
def DownPar (bl : Map Blob) : Prop :=
  ∀ y b j, HoonMap.get bl y = some b → j ∈ getJmps b.fin → Safe bl j

theorem downPar_passOK {bl : Map Blob} (h : DownPar bl) : PassOK bl :=
  fun o b j b2 hb hj hb2 r hr => h o b j hb hj r hr j.there b2 (RFrom.refl _) hb2

/-- What a pass must show to keep `DownPar`: every new jump is a path of the
code before and is safe there, and every block keeps its parameters. -/
theorem downPar_of {bl bl' : Map Blob}
    (hpar : ∀ z bz', HoonMap.get bl' z = some bz' → ∃ bz, HoonMap.get bl z = some bz ∧ bz'.par = bz.par)
    (hj : ∀ y b' j', HoonMap.get bl' y = some b' → j' ∈ getJmps b'.fin → RFrom bl y j'.there ∧ Safe bl j') :
    DownPar bl' := by
  have hsub : ∀ x z, RFrom bl' x z → RFrom bl x z := by
    intro x z h
    induction h with
    | refl => exact RFrom.refl _
    | step hb hj' _ ih => exact (hj _ _ _ hb hj').1.trans ih
  intro y b' j' hb' hj' r hr z bz' hz hbz'
  obtain ⟨bz, hbz, e⟩ := hpar z bz' hbz'
  rw [e]
  exact (hj y b' j' hb' hj').2 r hr z bz (hsub _ _ hz) hbz

/-! ## `+remove-useless-branching` -/

section
variable [MapKeys Map]

theorem rub_downPar {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hd : DownPar bl) : DownPar bl' := by
  have H := rub_blocks h
  refine downPar_of (bl := bl) (fun z bz' hz => ?_) (fun y b' j' hb' hj' => ?_)
  · obtain ⟨bz, e, hbz, -, rfl⟩ := H.back hz
    exact ⟨bz, hbz, rfl⟩
  · obtain ⟨b, e, hb, he, rfl⟩ := H.back hb'
    simp only [rubBlob] at hj'
    rcases rubFin_cases he with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
    · exact ⟨RFrom.one hb hj', hd y b j' hb hj'⟩
    · rw [h2] at hj'
      simp only [getJmps, List.mem_singleton] at hj'
      subst hj'
      have hz : z ∈ getJmps b.fin := by
        rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;> simp [hf, getJmps]
      exact ⟨RFrom.one (j := z) hb hz, fun r hr => by simp at hr⟩

end

/-! ## `+remove-hops` -/

/-- The end of a merged chain is the end of a block down the chain. -/
theorem mtail_rfrom {bl : Map Blob} {rev : Map (List Nat)} {o : Nat} {b : Blob} {T : List Pole} {F : Termin}
    (h : MTail bl rev o b T F) (hb : HoonMap.get bl o = some b) :
    ∃ e be, HoonMap.get bl e = some be ∧ F = be.fin ∧ RFrom bl o e := by
  induction h with
  | stop => exact ⟨_, _, hb, rfl, RFrom.refl _⟩
  | @link o b t b1 ops T F hf _ hb1 _ _ ih =>
    obtain ⟨e, be, hbe, hF, hr⟩ := ih hb1
    exact ⟨e, be, hbe, hF, RFrom.step hb (by simp [hf, getJmps]) hr⟩

theorem hops_downPar {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (hn : topo.Nodup) (h0 : topo.head? = some 0) (h : removeHops fuel bl rev topo = some (ch, bl'))
    (hd : DownPar bl) : DownPar bl' := by
  have H := hops_blocks hn h0 h
  refine downPar_of (bl := bl) (fun z bz' hz => ?_) (fun y b' j' hb' hj' => ?_)
  · obtain ⟨bz, T, F, hbz, -, rfl⟩ := H.back z bz' hz
    exact ⟨bz, hbz, rfl⟩
  · obtain ⟨b, T, F, hb, hmt, rfl⟩ := H.back y b' hb'
    obtain ⟨e, be, hbe, hF, hr⟩ := mtail_rfrom hmt hb
    simp only [merge] at hj'
    rw [hF] at hj'
    exact ⟨hr.trans (RFrom.one hbe hj'), hd e be j' hbe hj'⟩

/-! ## `+remove-empty-middle` -/

theorem mkSub_mem : ∀ (P : List Nat) (V : List (Option Nat)) (s0 s : Nat → Option (Option Nat)),
    mkSub P V s0 = some s → ∀ q v, s q = some v → v ∈ V ∨ s0 q = some v
  | [], [], s0, s, h, q, v, hv => by
    simp only [mkSub, Option.some.injEq] at h; subst h; exact Or.inr hv
  | [], _ :: _, _, _, h, _, _, _ => by simp [mkSub] at h
  | _ :: _, [], _, _, h, _, _, _ => by simp [mkSub] at h
  | p :: ps, a :: as, s0, s, h, q, v, hv => by
    simp only [mkSub] at h
    rcases mkSub_mem ps as _ s h q v hv with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · by_cases e : q = p
      · simp only [e, if_true, Option.some.injEq] at h1
        subst h1; exact Or.inl List.mem_cons_self
      · simp only [e, if_false] at h1
        exact Or.inr h1

theorem passArg_some {s : Nat → Option (Option Nat)} {a : Option Nat} {r : Nat} (h : passArg s a = some r) :
    ∃ a0, a = some a0 ∧ (s a0 = some (some r) ∨ (s a0 = none ∧ r = a0)) := by
  cases a with
  | none => simp [passArg] at h
  | some a0 =>
    refine ⟨a0, rfl, ?_⟩
    simp only [passArg] at h
    cases e : s a0 with
    | none => rw [e] at h; simp only [Option.getD_none, Option.some.injEq] at h; exact Or.inr ⟨rfl, h.symm⟩
    | some v => rw [e] at h; simp only [Option.getD_some] at h; subst h; exact Or.inl rfl

theorem rewriteJump_safe {bl : Map Blob} (hd : DownPar bl) :
    ∀ (n : Nat) (j j' : Jmp), Safe bl j → rewriteJump bl n j = some j' → Safe bl j' ∧ RFrom bl j.there j'.there
  | 0, _, _, _, h => by simp [rewriteJump] at h
  | n + 1, j, j', hs, h => by
    simp only [rewriteJump] at h
    split at h
    · cases h; exact ⟨hs, RFrom.refl _⟩
    · obtain ⟨nex, hn, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · cases h
      · split at h
        · cases h; exact ⟨hs, RFrom.refl _⟩
        · split at h
          · rename_i t ht
            split at h
            · cases h; exact ⟨hs, RFrom.refl _⟩
            · have htj : t ∈ getJmps nex.fin := by simp [getJmps, ht]
              obtain ⟨h1, h2⟩ := rewriteJump_safe hd n t j' (hd _ nex t hn htj) h
              exact ⟨h1, (RFrom.one hn htj).trans h2⟩
          · cases h; exact ⟨hs, RFrom.refl _⟩

theorem rewriteHop_safe {bl : Map Blob} {rd : Nat → List Nat} (hd : DownPar bl) :
    ∀ (n : Nat) (j j' : Jmp), Safe bl j → rewriteHop bl rd n j = some j' → Safe bl j' ∧ RFrom bl j.there j'.there
  | 0, _, _, _, h => by simp [rewriteHop] at h
  | n + 1, j, j', hs, h => by
    simp only [rewriteHop] at h
    obtain ⟨nex, hn, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; exact ⟨hs, RFrom.refl _⟩
    · split at h
      · rename_i t ht
        split at h
        · cases h; exact ⟨hs, RFrom.refl _⟩
        · obtain ⟨s, hsub, h⟩ := Option.bind_eq_some_iff.mp h
          have htj : t ∈ getJmps nex.fin := by simp [getJmps, ht]
          have hst := hd _ nex t hn htj
          have hs1 : Safe bl ⟨t.args.map (passArg s), t.there⟩ := by
            intro r hr z bz hz hbz
            simp only [List.mem_map] at hr
            obtain ⟨a, ha, hpa⟩ := hr
            obtain ⟨a0, rfl, h1 | ⟨-, e⟩⟩ := passArg_some hpa
            · rcases mkSub_mem _ _ _ s hsub a0 _ h1 with h2 | h2
              · exact hs r h2 z bz ((RFrom.one hn htj).trans hz) hbz
              · cases h2
            · rw [e]; exact hst a0 ha z bz hz hbz
          obtain ⟨h1, h2⟩ := rewriteHop_safe hd n _ j' hs1 h
          exact ⟨h1, (RFrom.one hn htj).trans h2⟩
      · cases h; exact ⟨hs, RFrom.refl _⟩

theorem middleFin_safe {bl : Map Blob} {rd : Nat → List Nat} {fuel : Nat} (hd : DownPar bl) {f f' : Termin}
    (hf : ∀ j ∈ getJmps f, Safe bl j) (h : middleFin bl rd fuel f = some f') :
    ∀ j' ∈ getJmps f', ∃ j ∈ getJmps f, Safe bl j' ∧ RFrom bl j.there j'.there := by
  intro j' hj'
  cases f with
  | hop t =>
    simp only [middleFin, Option.map_eq_some_iff] at h
    obtain ⟨t', ht', rfl⟩ := h
    simp only [getJmps, List.mem_singleton] at hj'
    subst hj'
    have htm : t ∈ getJmps (Termin.hop t) := by simp [getJmps]
    exact ⟨t, htm, rewriteHop_safe hd _ _ _ (hf t htm) ht'⟩
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj'
    have hzm : z ∈ getJmps (Termin.clq 0 z o) := by simp [getJmps]
    have hom : o ∈ getJmps (Termin.clq 0 z o) := by simp [getJmps]
    rcases hj' with rfl | rfl
    · exact ⟨z, by simp [getJmps], rewriteJump_safe hd _ _ _ (hf z (by simp [getJmps])) hz⟩
    · exact ⟨o, by simp [getJmps], rewriteJump_safe hd _ _ _ (hf o (by simp [getJmps])) ho⟩
  | _ =>
    simp only [middleFin, Option.some.injEq] at h
    subst h
    exact ⟨j', hj', hf j' hj', RFrom.refl _⟩

section
variable [MapKeys Map]

/-- **`+remove-empty-middle` keeps `DownPar`.** -/
theorem mid_downPar {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (hd : DownPar bl) : DownPar bl' := by
  have H := mid_blocks h
  have back : ∀ k b', HoonMap.get bl' k = some b' → ∃ b f', HoonMap.get bl k = some b ∧
      middleFin bl (readersOf bl) fuel b.fin = some f' ∧ b' = { b with fin := f' } := by
    intro k b' hb'
    cases e : HoonMap.get bl k with
    | none => rw [(H k).1 e] at hb'; cases hb'
    | some b =>
      obtain ⟨f', hf', e'⟩ := (H k).2 b e
      rw [e'] at hb'; cases hb'
      exact ⟨b, f', rfl, hf', rfl⟩
  refine downPar_of (bl := bl) (fun z bz' hz => ?_) (fun y b' j' hb' hj' => ?_)
  · obtain ⟨bz, f', hbz, -, rfl⟩ := back z bz' hz
    exact ⟨bz, hbz, rfl⟩
  · obtain ⟨b, f', hb, hf', rfl⟩ := back y b' hb'
    obtain ⟨j, hj, hs, hr⟩ := middleFin_safe hd (fun j hj => hd y b j hb hj) hf' j' hj'
    exact ⟨(RFrom.one hb hj).trans hr, hs⟩

/-- **`PassOK` of the result of `+remove-empty-middle`**, from `DownPar` of
its input. -/
theorem mid_passOK_of {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (hd : DownPar bl) : PassOK bl' :=
  downPar_passOK (mid_downPar h hd)

end

end Opt
end SkaModel
end Formalization
