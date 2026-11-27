import lemmas.Compiler.CompSccOfHeightS

/-!
# The poke's `env` iterated over the heights (README Gaps 19 (g), step 3)

The configuration of an SCC `S` reads the needs of the callees outside `S` through an `env`; those
callees are lower, so the poke's `env` is built height by height:

* `envIt base SC0 ht cfg rk m`: `base` at `m = 0`; at `m + 1`, the bells of height `m` read
  `envP` of the configurations `cfg (envIt m)` (the model's compile of their SCC, whose outside
  needs come from the lower heights), all other bells keep `envIt m`.
* `envLim`: each bell `b` reads `envIt (ht b + 1)`.
* `envIt_low`: below `m`, `envIt m` is `envLim` (what `SccLoopDataS` asks of `r.env := envIt m`).
* **`envLim_agree`**: the agreement clause of the loop at height `m` (members read the model's
  final need and sure need of `cfg (envIt m) S`), for `envLim`.
* `envFrom_envIt`, `envFrom_envLim`: the code table facts carry over.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The `env` of the heights below `m`.** -/
noncomputable def envIt (base : CallEnv) (SC0 : Noun) (ht : Noun → Nat) (cfg : CallEnv → Noun → Cfg Noun NeedOrd)
    (rk : ∀ e S, Ranked (cfg e S)) : Nat → CallEnv
  | 0 => base
  | m + 1 =>
    { envIt base SC0 ht cfg rk m with
      need := fun b => if ht b.toNoun = m then
          (envP (envIt base SC0 ht cfg rk m) SC0 (cfg (envIt base SC0 ht cfg rk m)) (rk (envIt base SC0 ht cfg rk m))).need b
        else (envIt base SC0 ht cfg rk m).need b
      sure := fun b => if ht b.toNoun = m then
          (envP (envIt base SC0 ht cfg rk m) SC0 (cfg (envIt base SC0 ht cfg rk m)) (rk (envIt base SC0 ht cfg rk m))).sure b
        else (envIt base SC0 ht cfg rk m).sure b }

/-- **The poke's `env`**: each bell reads the iterate just above its height. -/
noncomputable def envLim (base : CallEnv) (SC0 : Noun) (ht : Noun → Nat) (cfg : CallEnv → Noun → Cfg Noun NeedOrd)
    (rk : ∀ e S, Ranked (cfg e S)) : CallEnv :=
  { base with
    need := fun b => (envIt base SC0 ht cfg rk (ht b.toNoun + 1)).need b
    sure := fun b => (envIt base SC0 ht cfg rk (ht b.toNoun + 1)).sure b }

theorem envIt_fields (base : CallEnv) (SC0 : Noun) (ht : Noun → Nat) (cfg : CallEnv → Noun → Cfg Noun NeedOrd)
    (rk : ∀ e S, Ranked (cfg e S)) : ∀ m, (envIt base SC0 ht cfg rk m).pure = base.pure ∧
      (envIt base SC0 ht cfg rk m).ring = base.ring ∧ (envIt base SC0 ht cfg rk m).cod = base.cod ∧
      (envIt base SC0 ht cfg rk m).sof = base.sof
  | 0 => ⟨rfl, rfl, rfl, rfl⟩
  | m + 1 => envIt_fields base SC0 ht cfg rk m

theorem envFrom_envIt {base : CallEnv} {SC0 : Noun} {ht : Noun → Nat} {cfg : CallEnv → Noun → Cfg Noun NeedOrd}
    {rk : ∀ e S, Ranked (cfg e S)} {CODE COLE : Noun} (he : EnvFrom base CODE COLE) (m : Nat) :
    EnvFrom (envIt base SC0 ht cfg rk m) CODE COLE := by
  obtain ⟨hp, hr, hc, -⟩ := envIt_fields base SC0 ht cfg rk m
  exact ⟨fun b => by rw [hc]; exact he.cod b, fun b c h => by rw [hp]; exact he.pure b c h,
    fun b h => by rw [hr]; exact he.ring b h⟩

theorem envFrom_envLim {base : CallEnv} {SC0 : Noun} {ht : Noun → Nat} {cfg : CallEnv → Noun → Cfg Noun NeedOrd}
    {rk : ∀ e S, Ranked (cfg e S)} {CODE COLE : Noun} (he : EnvFrom base CODE COLE) :
    EnvFrom (envLim base SC0 ht cfg rk) CODE COLE :=
  ⟨he.cod, he.pure, he.ring⟩

/-- **Below `m`, the iterate is the limit.** -/
theorem envIt_low (base : CallEnv) (SC0 : Noun) (ht : Noun → Nat) (cfg : CallEnv → Noun → Cfg Noun NeedOrd)
    (rk : ∀ e S, Ranked (cfg e S)) : ∀ (m : Nat) (b : Bell), ht b.toNoun < m →
      (envIt base SC0 ht cfg rk m).need b = (envLim base SC0 ht cfg rk).need b ∧
      (envIt base SC0 ht cfg rk m).sure b = (envLim base SC0 ht cfg rk).sure b
  | 0, b, h => absurd h (Nat.not_lt_zero _)
  | m + 1, b, h => by
    by_cases e : ht b.toNoun = m
    · subst e; exact ⟨rfl, rfl⟩
    · have h' : ht b.toNoun < m := by omega
      obtain ⟨h1, h2⟩ := envIt_low base SC0 ht cfg rk m b h'
      refine ⟨?_, ?_⟩
      · show (if ht b.toNoun = m then _ else (envIt base SC0 ht cfg rk m).need b) = _
        rw [if_neg e]; exact h1
      · show (if ht b.toNoun = m then _ else (envIt base SC0 ht cfg rk m).sure b) = _
        rw [if_neg e]; exact h2

/-- **The agreement clause of the loop at height `m`, for `envLim`**: the members of `S` (whose
`sccs` entry is `S`, all of height `m`) read the model's final need and sure need of the
configuration `cfg (envIt m) S` (whose outside needs are the lower heights'). -/
theorem envLim_agree (base : CallEnv) (SC0 : Noun) (ht : Noun → Nat) (cfg : CallEnv → Noun → Cfg Noun NeedOrd)
    (rk : ∀ e S, Ranked (cfg e S)) (m : Nat) (S : Noun)
    (hmem : ∀ b' : Bell, b'.toNoun ∈ (cfg (envIt base SC0 ht cfg rk m) S).scc →
      getF mugF b'.toNoun SC0 = some (C (A 0) S) ∧ ht b'.toNoun = m)
    (s : St Noun NeedOrd)
    (hs : compileSccIn (cfg (envIt base SC0 ht cfg rk m) S) false
      (fuelR (cfg (envIt base SC0 ht cfg rk m) S) (rk (envIt base SC0 ht cfg rk m) S)) St.empty = some s)
    (b' : Bell) (hb : b'.toNoun ∈ (cfg (envIt base SC0 ht cfg rk m) S).scc) :
    (envLim base SC0 ht cfg rk).need b' = s.ml b'.toNoun ∧
      ∀ v, s.sure b'.toNoun = some v → (envLim base SC0 ht cfg rk).sure b' = v := by
  obtain ⟨-, hm⟩ := hmem b' hb
  have ha := envP_agree (envIt base SC0 ht cfg rk m) SC0 S (cfg (envIt base SC0 ht cfg rk m))
    (rk (envIt base SC0 ht cfg rk m)) (fun b h => (hmem b h).1) s hs b' hb
  have e1 : (envLim base SC0 ht cfg rk).need b' =
      (envP (envIt base SC0 ht cfg rk m) SC0 (cfg (envIt base SC0 ht cfg rk m)) (rk (envIt base SC0 ht cfg rk m))).need b' := by
    show (envIt base SC0 ht cfg rk (ht b'.toNoun + 1)).need b' = _
    rw [hm]; show (if ht b'.toNoun = m then _ else _) = _; rw [if_pos hm]
  have e2 : (envLim base SC0 ht cfg rk).sure b' =
      (envP (envIt base SC0 ht cfg rk m) SC0 (cfg (envIt base SC0 ht cfg rk m)) (rk (envIt base SC0 ht cfg rk m))).sure b' := by
    show (envIt base SC0 ht cfg rk (ht b'.toNoun + 1)).sure b' = _
    rw [hm]; show (if ht b'.toNoun = m then _ else _) = _; rw [if_pos hm]
  exact ⟨e1.trans ha.1, fun v hv => e2.trans (ha.2 v hv)⟩

end Compiler
end Formalization
