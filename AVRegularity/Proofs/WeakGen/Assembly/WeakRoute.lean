-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.InhFacts

/-! **Weak entry: the route by passages.** The construction and its
certificates are built by one induction over the passages, from the root at `M + J_w` down to `M`.
At the passage from the level `i`, everything is read from the incoming stage `stage i` of a partial
construction (`WeakStageAt`) and its weak certificate:
* `WeakPassageLiftsStatement`: lift families of every reserve for the
  sources of the passage, from the incoming stage holomorphically generated with no export
  (local existence: cut off the smooth data near each admissible offset, `cycle_lift_exists`,
  window uniqueness to patch). An all-cap production
  `IndependentWeakStageFluxProduction` of the incoming stage would live on the
  independent parameter box of the producer, far larger than the holomorphy carrier, so no
  certificate supplies it, and the passages only need its lifts;
* `WeakPassageExistsStatement` (for one passage): the weak passage out of
  the incoming stage exists, with its tags;
* `WeakPassageCert1Statement`: the passage keeps the weak certificate
  (`weakPassageCert_of_ingredients`, from `weakLevelComplexContext` and the weak ledger).
`weakConstruction_exists` proves the construction exists, for every instance of the plan, by the
induction: the certificate of the incoming stage gives its holomorphic generation, hence the next
passage; the passage gives the certificate of the next stage. There is no all-cap statement and no
cycle. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen

variable {plan : WeakCoefficientPlan}

/-- **The incoming stage of a passage**: a partial construction down to the level `i > M`. -/
structure WeakStageAt (plan : WeakCoefficientPlan) where
  inst : WeakCoefficientInstance plan
  i : ℕ
  hi : inst.M < i
  hiJ : i ≤ inst.M + inst.physical.Jw
  stage : ℕ → GenStage inst.D ScalarH inst.Dm inst.physical.bw inst.j₀
  pc : IsPartialWeakConstruction inst i stage

/-- **The lifts of one passage** (local existence at every reserve). -/
def WeakPassageLiftsStatement (plan : WeakCoefficientPlan) : Prop :=
  ∀ (y : WeakStageAt plan), WeakHolGen (y.stage y.i) → ∀ R : ℕ,
    ∃ Cc : ∀ s : WeakSource (y.stage y.i), ℤ → RealChain → ℕ → ℕ →
        LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ),
      ∀ s : WeakSource (y.stage y.i), s.IsLiftFamily R R y.inst.physical.Nw
        (y.inst.D.eps ((y.stage y.i).level - 1)) (Cc s)

/-- **One weak passage exists** out of an incoming stage holomorphically generated with no
export. -/
def WeakPassageExistsStatement (plan : WeakCoefficientPlan) : Prop :=
  ∀ (y : WeakStageAt plan), WeakHolGen (y.stage y.i) →
    ∃ G' : GenStage y.inst.D ScalarH y.inst.Dm y.inst.physical.bw y.inst.j₀,
      IsWeakPassage y.inst.D y.inst.P y.inst.menu (y.inst.D.termRW y.inst.physical.σw y.inst.M)
          (1 + (y.inst.M + y.inst.physical.Jw - y.i) * y.inst.menu.N) (y.stage y.i) G' ∧
        G'.HasTags y.inst.P

/-- A root stage has every weak certificate. -/
theorem weakCertified_of_isWeakRoot {x : WeakCoefficientInstance plan} {r : ℕ}
    {G : GenStage x.D ScalarH x.Dm x.physical.bw x.j₀} (h : IsWeakRoot (x.M + x.physical.Jw) r G)
    (C mres : ℝ) (L : ℕ) : WeakCertified C mres L G :=
  fun v u γ => ((h.2.2.1 v u).false γ).elim

/-- Extending a partial construction by one passage. -/
theorem IsPartialWeakConstruction.extend {x : WeakCoefficientInstance plan} {i : ℕ}
    {stage : ℕ → GenStage x.D ScalarH x.Dm x.physical.bw x.j₀}
    (h : IsPartialWeakConstruction x i stage) (hi : x.M < i) (hiJ : i ≤ x.M + x.physical.Jw)
    {G' : GenStage x.D ScalarH x.Dm x.physical.bw x.j₀}
    (hp : IsWeakPassage x.D x.P x.menu (x.D.termRW x.physical.σw x.M)
      (1 + (x.M + x.physical.Jw - i) * x.menu.N) (stage i) G') (ht : G'.HasTags x.P) :
    IsPartialWeakConstruction x (i - 1) (Function.update stage (i - 1) G') := by
  refine ⟨?_, fun i' hi' hi'J => ?_⟩
  · rw [Function.update_of_ne (by omega)]
    exact h.1
  · rcases Nat.lt_or_ge i i' with hlt | hge
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.2 i' hlt hi'J
    · obtain rfl : i' = i := by omega
      rw [Function.update_of_ne (by omega), Function.update_self]
      exact ⟨hp, ht⟩

/-- **The construction exists**, by the induction over the passages: the passage existence and the one-passage
certificate, from the root. -/
theorem weakConstruction_exists (hplan : WeakComplexContextPlanOK plan) {Kc : WeakConstFn}
    (hex : WeakPassageExistsStatement plan) (hcert : WeakPassageCert1Statement plan Kc)
    (x : WeakCoefficientInstance plan) :
    ∃ stage : ℕ → GenStage x.D ScalarH x.Dm x.physical.bw x.j₀,
      IsWeakConstruction x.D x.P x.menu x.M x.physical.Jw (x.D.termRW x.physical.σw x.M) 0 stage := by
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.hΛ]; have := case_Lambda_ge x; omega
  have hJ := x.physical.Jw_pos
  have hthr := hplan.2 x.request x.j₀
  have hlarge := x.level_large
  -- the descent from the root
  have main : ∀ k ≤ x.physical.Jw, ∃ stage : ℕ → GenStage x.D ScalarH x.Dm x.physical.bw x.j₀,
      IsPartialWeakConstruction x (x.M + x.physical.Jw - k) stage ∧ ∃ C : ℝ, 0 ≤ C ∧
        WeakCertified C (weakReserve x (x.M + x.physical.Jw - k))
          (weakWeight x (x.M + x.physical.Jw - k)) (stage (x.M + x.physical.Jw - k)) := by
    intro k hk
    induction k with
    | zero =>
      let G0 := WeakEntryProofs.weakRootStage x.D x.Dm x.physical.bw x.j₀ (x.M + x.physical.Jw) 0 (by omega)
        (by omega) (Construction.Stream.ocTau_pos hΛ1)
      have hr : IsWeakRoot (x.M + x.physical.Jw) 0 G0 :=
        WeakEntryProofs.weakRootStage_isWeakRoot _ _ _ _ _ _ _ _ _
      refine ⟨fun _ => G0, ⟨hr, fun i' hi' hi'J => absurd hi'J (by omega)⟩, 1, zero_le_one, ?_⟩
      exact weakCertified_of_isWeakRoot hr _ _ _
    | succ k ih =>
      obtain ⟨stage, hpc, C, hC, hW⟩ := ih (by omega)
      set i := x.M + x.physical.Jw - k with hidef
      have hi : x.M < i := by omega
      have hiJ : i ≤ x.M + x.physical.Jw := by omega
      obtain ⟨G', hp, ht⟩ := hex ⟨x, i, hi, hiJ, stage, hpc⟩ hW.weakHolGen
      have hpc' := hpc.extend hi hiJ hp ht
      have hW' : WeakCertified C (weakReserve x i) (weakWeight x i)
          (Function.update stage (i - 1) G' i) := by
        rw [Function.update_of_ne (by omega)]
        exact hW
      obtain ⟨hK, hW''⟩ := hcert ⟨x, i, hi, hiJ, Function.update stage (i - 1) G', hpc'⟩ C hC hW'
      rw [show x.M + x.physical.Jw - (k + 1) = i - 1 by omega]
      exact ⟨Function.update stage (i - 1) G', hpc', _, hK, hW''⟩
  obtain ⟨stage, hpc, -⟩ := main x.physical.Jw le_rfl
  rw [Nat.add_sub_cancel] at hpc
  exact ⟨stage, rfl, hpc.1, fun i hi hiJ => hpc.2 i hi hiJ⟩

end AVRegularity.Providers.WeakGen
