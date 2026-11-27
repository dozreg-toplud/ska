import lemmas.Ska.CompHintFrame

/-!
# Spots around calls and in sequence (README Gaps 24.16)

* `copyL_noBond`: `+copy` of two lazies with no fork and no bond has none.
* `noBondH_n2_none`: **`NoBondH` of the indirect call** `[2 p q]`, the
  subject `p` not hinted (else `+past` parks the formula's need in a bond).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `+copy` of two lazies with no fork and no bond has no fork and no bond. -/
theorem copyL_noBond {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (hf : first.laz.fork = []) (hb : first.laz.bond = []) (hf2 : second.fork = []) (hb2 : second.bond = [])
    (h : copyL first second g = some (nex, g')) : nex.laz.fork = [] ∧ nex.laz.bond = [] := by
  unfold copyL at h
  obtain ⟨oc, ge, he, h⟩ := bind_some h
  obtain ⟨laz, gf, hc, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rcases first with ⟨⟨s1, f1, b1⟩, th1⟩
  simp only [fork_mk, bond_mk] at hf hb
  subst hf hb
  simp only [copyLazyL, hf2, hb2, List.isEmpty_nil, if_true] at hc
  obtain ⟨⟨ned, ops⟩, g2, -, hc⟩ := bind_some hc
  obtain ⟨u, g3, -, hc⟩ := bind_some hc
  simp only [pure_apply, Option.bind_some, bind_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨rfl, rfl⟩

section NoBond
variable {snd : Nomm → NeedOrd → Bool} {env : CallEnv}

/-- **`NoBondH` of the indirect call**: the parts with `NoBondH`, the
subject not hinted (`+past` of the formula's need over it is the need). -/
theorem noBondH_n2_none {p q : Nomm} (hp : NoBondH (S := S) (Map := Map) snd env p)
    (hq : NoBondH (S := S) (Map := Map) snd env q) (hh : hinted env.cod p ≠ some true) :
    NoBondH (S := S) (Map := Map) snd env (Nomm.n2 p q Option.none) := by
  intro sup sur th region g0 g1 nex hr
  obtain ⟨nex0, ga, out, pro, gb, o, gc, nexF, gd, nexF', ge, nexS, gf, -, -, -, hF, hP, hS, hC⟩ :=
    runLCH_n2_none hr
  obtain ⟨fF, bF⟩ := hq hF
  have eP : nexF' = nexF := by
    unfold pastL at hP
    split at hP
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hP
      exact hP.1.symm
    · cases eh : hinted env.cod p with
      | none => simp [eh] at hP
      | some b =>
        cases b with
        | true => exact absurd eh hh
        | false =>
          simp only [eh, pure_apply, Option.some.injEq, Prod.mk.injEq] at hP
          exact hP.1.symm
  subst eP
  obtain ⟨fS, bS⟩ := hp hS
  exact copyL_noBond fS bS fF bF hC

end NoBond

end Comp
end SkaModel
end Formalization
