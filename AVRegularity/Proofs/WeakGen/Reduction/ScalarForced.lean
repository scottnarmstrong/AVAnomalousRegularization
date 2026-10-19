-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
public import AVRegularity.EntryWeakAssembly.Assembly.WeakComparisonDescending
import AVRegularity.CycleComparison.Error.WeakSolution
public import AVRegularity.EntryWeakAssembly.QuietScalarEvolution
import AVRegularity.Applications.TorusEnergy.StreamComparison
public import AVRegularity.Applications.TorusEnergy.StreamFacts
public import AVRegularity.Applications.Limits.Equi
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **One passage of the weak reduction, solved at large reserves**.

The stage `i - 1` of a weak construction is solved on a window from any datum at the reserves
`K_v = K_w + m + (J_w R_w - rank v)(J_w N_w - 1)` (`weakReductionReserve`, any order offset `m`;
independent of `D_m`): the coupling of an edge lowers the rank, so every edge is admissible
(`weakStage_edge_admissible`), the system is triangular, and the coefficients of every order
come from `weakEntry_physCoeff_allOrder`. At the offset `m + D_m - 2`, the coupled solution
truncated to `K_w + m` is the regularized system of the stage at width zero, with input lifts the
truncations of `w` (`weakReduction_regSolution_of_coupled`).

The reserves depend only on the component, so the trace of a solution of stage `i` at the next
quiet time is a datum of the right reserves for stage `i - 1`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **A coupled solution of a stage at large reserves is its regularized system at width zero**
(`kernel_of_coupled` at the instance path of `GenStage.IsRegSolution`). -/
theorem regSolution_of_coupled (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀) {ν t₀ t₁ : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {D' k : ℕ} {K : CompIn G.comps → ℕ}
    {A : ∀ v u, (d : admissibleOrders K D' v u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => hr u.1.root) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => hr v.1.root)}
    (hD : D' ≤ Dm) (hkK : ∀ v, k ≤ K v) (hlift : ∀ v, k + Dm - 1 ≤ K v + 1)
    (hA : ∀ v u d s y, A v u d s y = ∑ γ : G.fam.Γ v u, G.physCoeff v u γ d.1 s y)
    (hP : ∀ v u (γ : G.fam.Γ v u) n, n ∈ Finset.Icc 2 Dm → n ∉ admissibleOrders K D' v u →
      ∀ s y, G.physCoeff v u γ n s y = 0)
    (hS : ∀ v u γ s, G.sysS P seedK freshK φ₀ hφ₀ v u γ s = ContinuousLinearMap.id ℝ _)
    {f : ∀ v : CompIn G.comps, TorusHk (K v) (hr v.1.root)}
    {u : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
    {w : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)}
    (hc : IsCoupledWeakSolutionTorus ν t₀ t₁ bv D' K A f (fun _ _ => 0) (fun _ _ => 0) u w) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ (fun v => truncateTorusHk (hkK v) (f v))
      (fun _ _ => 0) (fun _ _ => 0) (fun v t => truncateTorusHk (hkK v) (u v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ (hkK v)) (w v t))
      (fun _ u' _ t => truncateTorusHk (hlift u') (w u' t)) :=
  kernel_of_coupled (P := fun v u γ n => G.physCoeff v u γ n) hD hkK hlift hA hP hS hc

end Stage

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The reserve of a component in the reduction at the order offset `m`: `K_w + m` plus the
descending reserve. It does not depend on `D_m`. The reduction proper is read at the offset
`D_m - 2` (the kernel lifts have order `K_w + D_m - 1`); the offset `m + D_m - 2` gives the
reduction at the order `K_w + m` (shared higher-order lemma). -/
def weakReductionReserve (R : WeakPassageRequest A) (m : ℕ) (c : Comp) : ℕ :=
  R.Kw + m + weakComparisonReserve R c

theorem weakReductionReserve_le (R : WeakPassageRequest A) (m : ℕ) (c : Comp) :
    weakReductionReserve R m c ≤ R.Kw + m + A.Jw * A.Rw * (A.Jw * A.Nw - 1) :=
  Nat.add_le_add_left (weak_comparison_reserve_le R c) _

theorem weakReductionReserve_kw (R : WeakPassageRequest A) (m : ℕ) (c : Comp) :
    R.Kw + m ≤ weakReductionReserve R m c :=
  Nat.le_add_right _ _

/-! ### The raw data of a weak construction -/

/-- **The raw data of a weak construction**: an `OCData`, a stage family with
`IsWeakConstruction`, the streams and the band chain at the terminal level `M`. It is what both
the entry data (`WeakEntryData`, `WeakEntryStages`) and a passage instance
(`WeakPassageInstance`) carry. The reduction is proved over it. -/
structure WeakRawSetting (R : WeakPassageRequest A) where
  D : OCData
  alpha : D.α = B.α
  q_eq : D.q = B.q
  base_eq : D.Λ = A.Λ
  profile_eq : D.ζ = B.ζ
  base128 : 128 ≤ A.Λ
  streams : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ
  M : ℕ
  band : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ
  terminal : D.term = M
  Dm : ℕ
  order_ge : 1 + A.Jw * A.Nw ≤ Dm
  j₀ : ℕ
  P : ProvParams
  stage : ℕ → GenStage D ScalarH Dm A.bw j₀
  construction : IsWeakConstruction D P
    (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw (D.termRW A.σw M) 0 stage

namespace WeakRawSetting

variable (S : WeakRawSetting R)

theorem lambda_pos : 1 ≤ S.D.Λ := by
  have := S.base128
  rw [S.base_eq]; omega

theorem eps_pos (j : ℕ) : 0 < S.D.eps j := Construction.Stream.ocEpsilon_pos S.lambda_pos

theorem band' : IsOCBandChain S.D.α S.D.q S.D.Λ S.D.ζ S.D.term S.D.κ := by
  rw [S.alpha, S.q_eq, S.base_eq, S.profile_eq, S.terminal]; exact S.band

theorem profile : IsFastProfile S.D.ζ := by rw [S.profile_eq]; exact B.hζ

theorem kappa_pos : 0 < S.D.κ S.M := by
  have := weakData_kap_pos S.D S.lambda_pos S.profile S.band' S.D.term
  rwa [weakData_kap_terminal S.D S.D.term le_rfl, S.terminal] at this

theorem kap_eq (j : ℕ) (hj : S.M ≤ j) : S.D.kap j = S.D.κ S.M := by
  rw [weakData_kap_terminal S.D j (by rw [S.terminal]; exact hj), S.terminal]

theorem two_le_Dm : 2 ≤ S.Dm := by
  have h1 := Nat.mul_le_mul A.Jw_pos A.Nw_pos
  have := S.order_ge
  omega

theorem level_eq (i : ℕ) (hMi : S.M ≤ i) (hi : i ≤ S.M + A.Jw) : (S.stage i).level = i :=
  EntryWeakProofs.weakConstruction_level S.P _ S.M A.Jw 0 _ S.stage S.construction i hMi hi

/-- **All-order regularity of the physical coefficients** of the passage stages: jointly
measurable on every window, `C^n` and periodic at every time, with finite seminorms of every
order at every radius `ρ ≤ ε_{i-1}`. -/
def CoeffRegular : Prop :=
  ∀ i, S.M ≤ i → i < S.M + A.Jw → ∀ (v u : CompIn (S.stage i).comps)
    (γ : (S.stage i).fam.Γ v u) (n d : ℕ) (a b : ℝ),
    Measurable (fun z : Set.Icc a b × Vec 2 => (S.stage i).physCoeff v u γ d z.1 z.2) ∧
      (∀ t, ContDiff ℝ (n : ℕ) ((S.stage i).physCoeff v u γ d t)) ∧
      (∀ t, AVenhance.IsZ2Periodic ((S.stage i).physCoeff v u γ d t)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ S.D.eps (i - 1) →
        coefficientSeminorm ρ n a b ((S.stage i).physCoeff v u γ d) ≠ ⊤

end WeakRawSetting

/-! ### One passage over the raw data -/

/-- The coefficient of the reduction system: the sum of the physical coefficients of an edge. -/
def weakStageCoeff (S : WeakRawSetting R) (m i : ℕ) (v u : CompIn (S.stage i).comps)
    (d : admissibleOrders (fun v : CompIn (S.stage i).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) v u) (t : ℝ) (y : Vec 2) :=
  ∑ γ : (S.stage i).fam.Γ v u, (S.stage i).physCoeff v u γ d.1 t y

/-- Every edge of a stage is admissible at its orders `2 ≤ d ≤ 1 + J_w N_w`. -/
theorem weakStage_edge_admissible (S : WeakRawSetting R) (m i : ℕ)
    (hMi : S.M ≤ i) (hit : i ≤ S.M + A.Jw) (v u : CompIn (S.stage i).comps)
    (γ : (S.stage i).fam.Γ v u) (d : ℕ) (hd : 2 ≤ d) (hdmax : d ≤ 1 + A.Jw * A.Nw) :
    d ∈ admissibleOrders (fun v : CompIn (S.stage i).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) v u := by
  obtain ⟨hr, he⟩ := EntryWeakProofs.weakConstruction_rank_bounds S.P _ S.M A.Jw 0 _ S.stage
    S.construction i hMi hit
  have hruv := he v u γ
  have hrv : weakComponentRank v.1 ≤ A.Jw * A.Rw :=
    (hr v.1 v.2).trans (Nat.mul_le_mul_right A.Rw (by omega))
  have hrem : A.Jw * A.Rw - weakComponentRank v.1 + 1 ≤
      A.Jw * A.Rw - weakComponentRank u.1 := by omega
  have hmul := Nat.mul_le_mul_right (A.Jw * A.Nw - 1) hrem
  rw [Nat.add_mul, Nat.one_mul] at hmul
  have hprod : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hd, hdmax⟩, ?_⟩
  dsimp only [weakReductionReserve, weakComparisonReserve]
  omega

/-- The physical coefficients vanish at the non-admissible orders of the reduction reserves. -/
theorem weakStage_physCoeff_nonadmissible (S : WeakRawSetting R)
    (m i : ℕ) (hMi : S.M ≤ i) (hit : i < S.M + A.Jw) (v u : CompIn (S.stage i).comps)
    (γ : (S.stage i).fam.Γ v u) (n : ℕ) (hn : n ∈ Finset.Icc 2 S.Dm)
    (hna : n ∉ admissibleOrders (fun v : CompIn (S.stage i).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) v u) (s : ℝ) (y : Vec 2) :
    (S.stage i).physCoeff v u γ n s y = 0 := by
  have ho := EntryWeakProofs.weakConstruction_output_maxOrder_bound S.P _ S.M A.Jw _ 0 S.stage
    S.construction i hMi hit v u γ
  by_cases hle : n ≤ ((S.stage i).fam.identity v u γ).maxOrder
  · exact absurd (weakStage_edge_admissible S m i hMi hit.le v u γ n (Finset.mem_Icc.1 hn).1
      (hle.trans ho)) hna
  · exact constituentPhysical_zero_above_max (S.stage i).fam _ _ _ (S.stage i).actual v u γ n
      (not_le.mp hle) s y

/-- The reduction coefficients vanish unless they lower the rank. -/
theorem weakStageCoeff_triangular (S : WeakRawSetting R) (m i : ℕ)
    (hMi : S.M ≤ i) (hit : i ≤ S.M + A.Jw) (v u : CompIn (S.stage i).comps)
    (hvu : ¬ weakComponentRank u.1 < weakComponentRank v.1)
    (d : admissibleOrders (fun v : CompIn (S.stage i).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) v u) :
    weakStageCoeff S m i v u d = 0 := by
  funext t y
  exact Finset.sum_eq_zero fun γ _ => absurd ((EntryWeakProofs.weakConstruction_rank_bounds S.P _
    S.M A.Jw 0 _ S.stage S.construction i hMi hit).2 v u γ) hvu

/-- **The reduction coefficients satisfy the coefficient hypotheses of `coupled_energy_torus`** at
the reduction reserves, at every radius `ρ ≤ ε_{i-1}`. -/
theorem weakStageCoeff_gate (S : WeakRawSetting R) (hreg : S.CoeffRegular)
    (m i : ℕ) (hMi : S.M ≤ i) (hit : i < S.M + A.Jw) (a b ρ : ℝ)
    (hρ : 0 < ρ) (hρe : ρ ≤ S.D.eps (i - 1)) (v u : CompIn (S.stage i).comps)
    (d : admissibleOrders (fun v : CompIn (S.stage i).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) v u) :
    Measurable (fun p : Set.Icc a b × Vec 2 => weakStageCoeff S m i v u d p.1 p.2) ∧
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (weakReductionReserve R m v.1 : ℕ)
      (weakStageCoeff S m i v u d t)) ∧
    (∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (weakStageCoeff S m i v u d t)) ∧
    coefficientSeminorm ρ (weakReductionReserve R m v.1) a b
      (weakStageCoeff S m i v u d) ≠ ⊤ := by
  have hreg := fun γ => hreg i hMi hit v u γ (weakReductionReserve R m v.1) d.1 a b
  refine ⟨Finset.measurable_sum _ fun γ _ => (hreg γ).1,
    fun t _ => ContDiff.sum fun γ _ => (hreg γ).2.1 t,
    fun t _ n y => Finset.sum_congr rfl fun γ _ => (hreg γ).2.2.1 t n y, ?_⟩
  refine ne_top_of_le_ne_top ?_ (CycleComparison.Error.coefficientSeminorm_finset_sum_le
    Finset.univ ρ hρ.le (weakReductionReserve R m v.1) a b
    (fun γ => (S.stage i).physCoeff v u γ d.1) (fun γ _ t _ => (hreg γ).2.1 t))
  exact ENNReal.sum_ne_top.2 fun γ _ => (hreg γ).2.2.2 ρ hρ hρe

/-- **The coupled system of one passage has a solution** from every datum at the reduction
reserves. -/
theorem weakStage_coupled_exists (S : WeakRawSetting R) (hM2 : 2 ≤ S.M)
    (hreg : S.CoeffRegular) (m i : ℕ) (hMi : S.M < i) (hi : i ≤ S.M + A.Jw) (t₀ t₁ : ℝ)
    (ht : t₀ ≤ t₁)
    (f : ∀ v : CompIn (S.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)) :
    ∃ (u : ∀ v : CompIn (S.stage (i - 1)).comps, ℝ →
        TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root))
      (w : ∀ v : CompIn (S.stage (i - 1)).comps, ℝ →
        TorusHk (weakReductionReserve R m v.1 + 1) (ScalarH v.1.root)),
      IsCoupledWeakSolutionTorus (S.D.kap (S.stage (i - 1)).level) t₀ t₁
        (streamVel (S.D.Φ (S.stage (i - 1)).level)) (1 + A.Jw * A.Nw)
        (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
        (weakStageCoeff S m (i - 1)) f (fun _ _ => 0) (fun _ _ => 0) u w := by
  have hM1 : S.M ≤ i - 1 := by omega
  have hit : i - 1 < S.M + A.Jw := by omega
  have hlevel : (S.stage (i - 1)).level = i - 1 := S.level_eq (i - 1) hM1 hit.le
  have hΛ1 := S.lambda_pos
  have hν : 0 < S.D.kap (S.stage (i - 1)).level :=
    EntryWeakProofs.weakData_kap_pos S.D hΛ1 S.profile S.band' _
  have hm1 : 1 ≤ (S.stage (i - 1)).level := by rw [hlevel]; omega
  obtain ⟨ρ₀, hρ₀, hdrift⟩ := stream_torusDriftData B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
    B.ζ B.hζ A.Λ S.base128 S.D.Φ S.streams (S.stage (i - 1)).level hm1 hν t₀ t₁
    (R.Kw + m + A.Jw * A.Rw * (A.Jw * A.Nw - 1))
  have hρ : 0 < min ρ₀ (S.D.eps (i - 1 - 1)) :=
    lt_min hρ₀ (Construction.Stream.ocEpsilon_pos hΛ1)
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have hgate := weakStageCoeff_gate S hreg m (i - 1) hM1 hit t₀ t₁ _ hρ (min_le_right _ _)
  exact triangular_coupled_exists_from (hdrift _ hρ (min_le_left _ _)) ht hρ hν
    (by omega : 2 ≤ 1 + A.Jw * A.Nw)
    (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
    (fun v => weakReductionReserve_le R m v.1) (weakStageCoeff S m (i - 1))
    (fun v u d => (hgate v u d).1) (fun v u d => (hgate v u d).2.1)
    (fun v u d => (hgate v u d).2.2.1) (fun v u d => (hgate v u d).2.2.2)
    (fun v => weakComponentRank v.1) (weakStageCoeff_triangular S m (i - 1) hM1 hit.le) f

/-! ### The entry data as raw data -/

variable {plan : WeakEntryGluePlan} {C : WeakEntryAllocation R (plan.radius R)}

/-- The raw data of the stages of a weak entry. -/
@[reducible] def weakEntryRawSetting {x : WeakEntryData plan C} (g : WeakEntryStages x) :
    WeakRawSetting R where
  D := x.D
  alpha := x.alpha
  q_eq := x.q_eq
  base_eq := x.base_eq
  profile_eq := x.profile_eq
  base128 := x.base128
  streams := x.streams
  M := x.M
  band := x.band
  terminal := x.terminal
  Dm := x.Dm
  order_ge := x.order_ge
  j₀ := x.j₀
  P := x.P
  stage := g.stage
  construction := g.construction

theorem weakEntryData_two_le_Dm (x : WeakEntryData plan C) : 2 ≤ x.Dm := by
  have h1 : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have := x.order_ge
  omega

/-- The order `K_w + m` lies below the reserves at the offset `m + D_m - 2`. -/
theorem weakReductionReserve_order (x : WeakEntryData plan C) (m : ℕ) (c : Comp) :
    R.Kw + m ≤ weakReductionReserve R (m + x.Dm - 2) c := by
  have := weakEntryData_two_le_Dm x
  unfold weakReductionReserve
  omega

/-- The kernel lifts of order `K_w + m + D_m - 1` lie below the lifts at the offset
`m + D_m - 2`. -/
theorem weakReductionReserve_lift (x : WeakEntryData plan C) (m : ℕ) (c : Comp) :
    R.Kw + m + x.Dm - 1 ≤ weakReductionReserve R (m + x.Dm - 2) c + 1 := by
  have := weakEntryData_two_le_Dm x
  unfold weakReductionReserve
  omega

theorem weakEntryData_M_ge_two (hcommon : WeakEntryCommonOK plan) (x : WeakEntryData plan C) :
    2 ≤ x.M := by
  have hj2 : x.j₀ + 2 ≤ x.M := ((weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan)
    weakBasePlan_complexContext).2 (weakCoeffRequestOne R) x.j₀).trans
      ((hcommon.2 R C x.j₀).trans x.level_ge)
  omega

/-- The stages of a weak entry have physical coefficients of every order
(`weakEntry_physCoeff_allOrder`). -/
theorem weakEntryRawSetting_coeffRegular (hcommon : WeakEntryCommonOK plan)
    {x : WeakEntryData plan C} (g : WeakEntryStages x) : (weakEntryRawSetting g).CoeffRegular :=
  fun i hMi hit v u γ n d a b => weakEntry_physCoeff_allOrder hcommon g i hMi hit v u γ n d a b

/-- The coefficient of the reduction system of a weak entry. -/
abbrev weakReductionCoeff {x : WeakEntryData plan C} (g : WeakEntryStages x) (m i : ℕ) :=
  weakStageCoeff (weakEntryRawSetting g) m i

/-- **The truncated coupled solution of one passage is the regularized system of the stage** at
width zero, at order `K_w + m` from the offset `m + D_m - 2`, with input lifts the truncations
of `w`. -/
theorem weakReduction_regSolution_of_coupled {x : WeakEntryData plan C} (g : WeakEntryStages x)
    (m i : ℕ) (hMi : x.M < i) (hi : i ≤ x.M + A.Jw) {t₀ t₁ : ℝ}
    {f : ∀ v : CompIn (g.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R (m + x.Dm - 2) v.1) (ScalarH v.1.root)}
    {u : ∀ v : CompIn (g.stage (i - 1)).comps, ℝ →
      TorusHk (weakReductionReserve R (m + x.Dm - 2) v.1) (ScalarH v.1.root)}
    {w : ∀ v : CompIn (g.stage (i - 1)).comps, ℝ →
      TorusHk (weakReductionReserve R (m + x.Dm - 2) v.1 + 1) (ScalarH v.1.root)}
    (hc : IsCoupledWeakSolutionTorus (x.D.kap (g.stage (i - 1)).level) t₀ t₁
      (streamVel (x.D.Φ (g.stage (i - 1)).level)) (1 + A.Jw * A.Nw)
      (fun v : CompIn (g.stage (i - 1)).comps => weakReductionReserve R (m + x.Dm - 2) v.1)
      (weakReductionCoeff g (m + x.Dm - 2) (i - 1)) f (fun _ _ => 0) (fun _ _ => 0) u w) :
    (g.stage (i - 1)).IsRegSolution x.P (fun _ => isoPairedKernel 0 R.nW)
      (fun _ => isoPairedKernel 0 R.nW) A.φ₀ A.hφ₀ (x.D.kap (g.stage (i - 1)).level)
      (streamVel (x.D.Φ (g.stage (i - 1)).level)) (R.Kw + m) t₀ t₁
      (fun v => truncateTorusHk (weakReductionReserve_order x m v.1) (f v)) (fun _ _ => 0)
      (fun _ _ => 0) (fun v t => truncateTorusHk (weakReductionReserve_order x m v.1) (u v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ (weakReductionReserve_order x m v.1)) (w v t))
      (fun _ u' _ t => truncateTorusHk (weakReductionReserve_lift x m u'.1) (w u' t)) :=
  regSolution_of_coupled x.P _ _ A.φ₀ A.hφ₀ (g.stage (i - 1)) (by have := x.order_ge; omega)
    (fun v => weakReductionReserve_order x m v.1) (fun v => weakReductionReserve_lift x m v.1)
    (fun _ _ _ _ _ => rfl)
    (weakStage_physCoeff_nonadmissible (weakEntryRawSetting g) (m + x.Dm - 2) (i - 1)
      (show x.M ≤ i - 1 by omega) (show i - 1 < x.M + A.Jw by omega))
    (fun v u γ s => sysS_isoPairedKernel_zero x.P R.nW A.hφ₀ A.mass (g.stage (i - 1)) v u γ s) hc
end

/-! **The families of the weak reduction, passage by passage**.

Over the raw data `S : WeakRawSetting R` and a clock `K : WeakRawClock S`:
* `WeakStageFamily`, `WeakStageLift`: families of a stage at the reduction reserves.
* `weakStageTrace`: the trace of a family of stage `i` on the components of stage `i - 1` (its
  value on the old components, zero on the new ones), at the reduction reserves, which depend
  only on the component and the order offset.
* `WeakRawClock`: the passage times `t_i`, the window end `a + T₀`, and a first time `t_root > a`
  of the root at the reserves, with `t_{M+J_w+1} ≤ t_root ≤ t_{M+J_w}`.
* `WeakStagePassage`: stage `i - 1` is solved on `[t_i, a + T₀]` at the reduction reserves from
  the trace of the family of stage `i` at `t_i`.
* `weakStage_families`: from any family on the root stage, the families of all the stages
  `M ≤ i < M + J_w`, solving every passage (downward induction over the passages,
  `weakStage_coupled_exists` at each).

For a weak entry (`WeakEntryStages g`, `WeakEntrySchedule s`) these are `WeakReductionFamily g`,
`WeakReductionLift g`, `weakReductionTrace g`, `WeakReductionPassage s`: the same objects at
`weakEntryRawSetting g` and `weakEntryRawClock s` (root time `t_{M+J_w+1}`). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- A family of a stage at the reduction reserves. -/
abbrev WeakStageFamily (S : WeakRawSetting R) (m i : ℕ) : Type :=
  ∀ v : CompIn (S.stage i).comps, ℝ → TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)

/-- The gradient lifts of a family of a stage at the reduction reserves. -/
abbrev WeakStageLift (S : WeakRawSetting R) (m i : ℕ) : Type :=
  ∀ v : CompIn (S.stage i).comps, ℝ →
    TorusHk (weakReductionReserve R m v.1 + 1) (ScalarH v.1.root)

/-- The trace of a family of stage `i` at time `t` on the components of stage `i - 1`: its value
on the old components, zero on the new ones. -/
def weakStageTrace (S : WeakRawSetting R) (m i : ℕ) (U : WeakStageFamily S m i) (t : ℝ) :
    ∀ v : CompIn (S.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root) :=
  fun v => if hv : v.1 ∈ (S.stage i).comps then U ⟨v.1, hv⟩ t else 0

theorem weakStageTrace_old (S : WeakRawSetting R) (m i : ℕ) (U : WeakStageFamily S m i) (t : ℝ)
    (v : CompIn (S.stage (i - 1)).comps) (hv : v.1 ∈ (S.stage i).comps) :
    weakStageTrace S m i U t v = U ⟨v.1, hv⟩ t := by
  unfold weakStageTrace
  exact dite_eq_left hv

theorem weakStageTrace_new (S : WeakRawSetting R) (m i : ℕ) (U : WeakStageFamily S m i) (t : ℝ)
    (v : CompIn (S.stage (i - 1)).comps) (hv : v.1 ∉ (S.stage i).comps) :
    weakStageTrace S m i U t v = 0 := by
  unfold weakStageTrace
  exact dite_eq_right hv

/-- **The truncated trace is the terminal trace** of the truncated family, at every order below
the reserves. -/
theorem weakStage_terminalTrace (S : WeakRawSetting R) (m i : ℕ) (U : WeakStageFamily S m i)
    (t : ℝ) {k : ℕ} (hk : ∀ c, k ≤ weakReductionReserve R m c) :
    IsTerminalTrace (S.stage i) (S.stage (i - 1))
      (fun v => truncateTorusHk (hk v.1) (U v t))
      (fun v => truncateTorusHk (hk v.1) (weakStageTrace S m i U t v)) :=
  ⟨fun v hv => congrArg (truncateTorusHk (hk v.1)) (weakStageTrace_old S m i U t v hv),
    fun v hv => (congrArg (truncateTorusHk (hk v.1))
      (weakStageTrace_new S m i U t v hv)).trans (map_zero _)⟩

/-- **The clock of a reduction over raw data**: the start `a`, the passage times `t_i`, and a
first time `t_root` of the root at the reserves, strictly after the start and between `t_{M+J_w+1}`
and `t_{M+J_w}`. Every passage time lies in the window `[a, a + T₀]`, and the times decrease
with the level. -/
structure WeakRawClock (S : WeakRawSetting R) where
  a : ℝ
  tq : ℕ → ℝ
  troot : ℝ
  troot_gt : a < troot
  troot_ge : tq (S.M + A.Jw + 1) ≤ troot
  troot_le : troot ≤ tq (S.M + A.Jw)
  tq_le : ∀ i, S.M < i → i ≤ S.M + A.Jw → tq i ≤ a + A.T₀
  tq_step : ∀ i, S.M < i → i ≤ S.M + A.Jw → tq (i + 1) ≤ tq i

/-- **One passage of the families**: stage `i - 1` solved on `[t_i, a + T₀]` at the reduction
reserves from the trace of the family of stage `i` at `t_i`. -/
abbrev WeakStagePassage (S : WeakRawSetting R) (K : WeakRawClock S) (m : ℕ)
    (Uhi : ∀ i, WeakStageFamily S m i) (Whi : ∀ i, WeakStageLift S m i) (i : ℕ) : Prop :=
  IsCoupledWeakSolutionTorus (S.D.kap (S.stage (i - 1)).level) (K.tq i) (K.a + A.T₀)
    (streamVel (S.D.Φ (S.stage (i - 1)).level)) (1 + A.Jw * A.Nw)
    (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
    (weakStageCoeff S m (i - 1)) (weakStageTrace S m i (Uhi i) (K.tq i))
    (fun _ _ => 0) (fun _ _ => 0) (Uhi (i - 1)) (Whi (i - 1))

/-- **The families of the reduction**: from any family on the root stage, families on all the
stages solving every passage. -/
theorem weakStage_families (S : WeakRawSetting R) (hM2 : 2 ≤ S.M) (hreg : S.CoeffRegular)
    (K : WeakRawClock S) (m : ℕ) (Uroot : WeakStageFamily S m (S.M + A.Jw)) :
    ∃ (Uhi : ∀ i, WeakStageFamily S m i) (Whi : ∀ i, WeakStageLift S m i),
      Uhi (S.M + A.Jw) = Uroot ∧
        ∀ i, S.M < i → i ≤ S.M + A.Jw → WeakStagePassage S K m Uhi Whi i := by
  have main : ∀ n, n ≤ A.Jw →
      ∃ (Uhi : ∀ i, WeakStageFamily S m i) (Whi : ∀ i, WeakStageLift S m i),
        Uhi (S.M + A.Jw) = Uroot ∧
          ∀ i, S.M + A.Jw - n < i → i ≤ S.M + A.Jw → WeakStagePassage S K m Uhi Whi i := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨Function.update (fun _ _ _ => 0) (S.M + A.Jw) Uroot, fun _ _ _ => 0,
        Function.update_self _ _ _, fun i hi hi' => absurd hi' (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨Uhi, Whi, hroot, hpass⟩ := ih (by omega)
      obtain ⟨j, hj⟩ : ∃ j, j = S.M + A.Jw - n := ⟨_, rfl⟩
      have hMj : S.M < j := by omega
      have hjJ : j ≤ S.M + A.Jw := by omega
      obtain ⟨u, w, hc⟩ := weakStage_coupled_exists S hM2 hreg m j hMj hjJ (K.tq j)
        (K.a + A.T₀) (K.tq_le j hMj hjJ) (weakStageTrace S m j (Uhi j) (K.tq j))
      refine ⟨Function.update Uhi (j - 1) u, Function.update Whi (j - 1) w, ?_, ?_⟩
      · rw [Function.update_of_ne (show S.M + A.Jw ≠ j - 1 by omega)]
        exact hroot
      · intro i hi hi'
        by_cases hij : i = j
        · subst hij
          unfold WeakStagePassage
          rw [Function.update_of_ne (show i ≠ i - 1 by omega), Function.update_self,
            Function.update_self]
          exact hc
        · have hp := hpass i (by omega) hi'
          unfold WeakStagePassage at hp ⊢
          rw [Function.update_of_ne (show i ≠ j - 1 by omega),
            Function.update_of_ne (show i - 1 ≠ j - 1 by omega),
            Function.update_of_ne (show i - 1 ≠ j - 1 by omega)]
          exact hp
  obtain ⟨Uhi, Whi, hroot, hpass⟩ := main A.Jw le_rfl
  exact ⟨Uhi, Whi, hroot, fun i hi hi' => hpass i (by omega) hi'⟩

/-! ### The weak entry -/

variable {plan : WeakEntryGluePlan} {C : WeakEntryAllocation R (plan.radius R)}

/-- A family of a stage of a weak entry at the reduction reserves. -/
abbrev WeakReductionFamily {x : WeakEntryData plan C} (g : WeakEntryStages x) (m i : ℕ) : Type :=
  WeakStageFamily (weakEntryRawSetting g) m i

/-- The gradient lifts of a family of a stage of a weak entry at the reduction reserves. -/
abbrev WeakReductionLift {x : WeakEntryData plan C} (g : WeakEntryStages x) (m i : ℕ) : Type :=
  WeakStageLift (weakEntryRawSetting g) m i

/-- The trace of a family of stage `i` of a weak entry on the components of stage `i - 1`. -/
abbrev weakReductionTrace {x : WeakEntryData plan C} (g : WeakEntryStages x) (m i : ℕ)
    (U : WeakReductionFamily g m i) (t : ℝ) :
    ∀ v : CompIn (g.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root) :=
  weakStageTrace (weakEntryRawSetting g) m i U t

/-- **Every passage time lies in the window.** -/
theorem weakEntrySchedule_tq_le {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) (i : ℕ) (hMi : x.M < i) (hi : i ≤ x.M + A.Jw) :
    s.tq i ≤ x.a + A.T₀ := by
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact le_trans (by norm_num) x.base128
  have hstep : ∀ n, x.M + 1 + n ≤ x.M + A.Jw → s.tq (x.M + 1 + n) ≤ s.tq (x.M + 1) := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih =>
      intro hn
      have hc := (s.quietMargins (x.M + 1 + n) (by omega) (by omega)).2.1
      have hτ : 0 < ocTauP x.D.α x.D.q x.D.Λ (x.M + 1 + n) := Velocity.Jets.ocTauP_pos hΛ1
      rw [show x.M + 1 + (n + 1) = x.M + 1 + n + 1 by omega]
      linarith [ih (by omega)]
  have h1 := hstep (i - (x.M + 1)) (by omega)
  rw [show x.M + 1 + (i - (x.M + 1)) = i by omega] at h1
  linarith [s.finish, A.τ_small]

/-- The passage times of a schedule decrease with the level. -/
theorem weakEntrySchedule_tq_step {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) (i : ℕ) (hMi : x.M < i) (hi : i ≤ x.M + A.Jw) :
    s.tq (i + 1) ≤ s.tq i := by
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact le_trans (by norm_num) x.base128
  have hτ : 0 < ocTauP x.D.α x.D.q x.D.Λ i := Velocity.Jets.ocTauP_pos hΛ1
  linarith [(s.quietMargins i hMi hi).2.1]

/-- The clock of a schedule of a weak entry; the root time is `t_{M+J_w+1}`. -/
@[reducible] def weakEntryRawClock {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) : WeakRawClock (weakEntryRawSetting g) where
  a := x.a
  tq := s.tq
  troot := s.tq (x.M + A.Jw + 1)
  troot_gt := s.start
  troot_ge := le_rfl
  troot_le := weakEntrySchedule_tq_step s (x.M + A.Jw) (by have := A.Jw_pos; omega) le_rfl
  tq_le := weakEntrySchedule_tq_le s
  tq_step := weakEntrySchedule_tq_step s

/-- **One passage of the families** of a weak entry: stage `i - 1` solved on `[t_i, a + T₀]` at
the reduction reserves from the trace of the family of stage `i` at `t_i`. -/
abbrev WeakReductionPassage {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) (m : ℕ) (Uhi : ∀ i, WeakReductionFamily g m i)
    (Whi : ∀ i, WeakReductionLift g m i) (i : ℕ) : Prop :=
  WeakStagePassage (weakEntryRawSetting g) (weakEntryRawClock s) m Uhi Whi i
end

end AVRegularity.Providers.WeakGen.Reduction
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The weak reduction from scalar smoothing** (`WeakEntryReductionStatement`).

* `WeakScalarSmoothingStatement`: the new analytic content of the reduction. A weak solution of
  the scalar equation with an actual stream drift has, at every time of `[t₀, T]` with `t₀`
  strictly after its start, a representative in `H^k`, for every `k`.
* `weak_entry_reduction_of_smoothing`: the reduction for every glue plan whose floors dominate
  the common coefficient plan (`WeakEntryCommonOK`), from scalar smoothing.
  1. The schedule starts strictly after `a` (`WeakEntrySchedule.start`), so scalar smoothing
     gives the root family at the reduction reserves from `t_{M+J_w+1}` on.
  2. `weakStage_families` solves every passage at the reduction reserves from the trace of
     the previous family.
  3. The reduction is the truncation to `K_w` of the families at the order offset `D_m - 2`:
     `U = trunc u`, `U_w = trunc w`, and the input lifts `U_k = trunc w` at order `K_w + D_m - 1`
     (`weakReduction_regSolution_of_coupled`). The terminal trace is the truncated trace, and the
     quiet margin facts are those of the schedule.
* `weakReduction_coupled_families`: the coupled families at every order offset `m` (reserves
  `K_w + m` plus the descending reserve, independent of `D_m`), for the consistency half.
* `weakReduction_of_coupled`, `weakReduction_exists_at`: the reduction at every order `K_w + m`,
  from the families at the offset `m + D_m - 2` (existence half of the shared higher-order lemma). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

/-- **Scalar smoothing** (the new analytic content of the weak reduction): a weak solution of the
scalar equation with an actual stream drift has, at every time of `[t₀, T]` with `a < t₀`, a
representative in `H^k`, for every `k`. -/
def WeakScalarSmoothingStatement : Prop :=
  ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → ∀ q : ℝ, IsAdmissibleQ α s q →
  ∀ ζ : ℝ → ℝ, IsFastProfile ζ → ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ,
  IsOCStreamSeq α q Λ ζ Φ → ∀ m : ℕ, 1 ≤ m → ∀ κ : ℝ, 0 < κ →
  ∀ (a T : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (Φ m)) κ a T f θ → ∀ t₀ : ℝ, a < t₀ → ∀ k : ℕ,
    ∃ u : ℝ → TorusHk k ℝ, ∀ t ∈ Set.Icc t₀ T,
      (u t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube] θ t

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- **One passage of the families at the offset `m + D_m - 2` is a weak passage solution** after
truncation to `K_w + m`. -/
theorem weakReduction_passageSolution {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) (m : ℕ) (Uhi : ∀ i, WeakReductionFamily g (m + x.Dm - 2) i)
    (Whi : ∀ i, WeakReductionLift g (m + x.Dm - 2) i) (i : ℕ) (hi : x.M < i)
    (hi' : i ≤ x.M + A.Jw) (hp : WeakReductionPassage s (m + x.Dm - 2) Uhi Whi i) :
    IsWeakPassageSolution x.P A.φ₀ A.hφ₀ R.nW (R.Kw + m) (g.stage i) (g.stage (i - 1)) (s.tq i)
      (x.a + A.T₀) (fun v t => truncateTorusHk (weakReductionReserve_order x m v.1) (Uhi i v t))
      (fun v t => truncateTorusHk (weakReductionReserve_order x m v.1) (Uhi (i - 1) v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ (weakReductionReserve_order x m v.1))
        (Whi (i - 1) v t))
      (fun _ u _ t => truncateTorusHk (weakReductionReserve_lift x m u.1) (Whi (i - 1) u t)) := by
  have htr := weakStage_terminalTrace (weakEntryRawSetting g) (m + x.Dm - 2) i (Uhi i) (s.tq i)
    (weakReductionReserve_order x m)
  have hreg := weakReduction_regSolution_of_coupled g m i hi hi' hp
  exact ⟨_, htr, hreg⟩

/-- **The truncated coupled families at the offset `m + D_m - 2` are a weak reduction** at the
order `K_w + m`, once their root component has the value `θ(t)` and every passage is solved. -/
theorem weakReduction_of_coupled {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) (θ : ℝ → Vec 2 → ℝ) (m : ℕ)
    {Uhi : ∀ i, WeakReductionFamily g (m + x.Dm - 2) i}
    {Whi : ∀ i, WeakReductionLift g (m + x.Dm - 2) i}
    (hroot : ∀ (hr : (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps),
      ∀ t ∈ Set.Icc (s.tq (x.M + A.Jw + 1)) (x.a + A.T₀),
        (Uhi (x.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
            (valueIndex2 (weakReductionReserve R (m + x.Dm - 2) (⟨0, []⟩ : Comp))) =ᵐ[
          volume.restrict AVenhance.unitCube] θ t)
    (hpass : ∀ i, x.M < i → i ≤ x.M + A.Jw → WeakReductionPassage s (m + x.Dm - 2) Uhi Whi i) :
    IsWeakReduction x.P A.φ₀ A.hφ₀ R.nW x.M A.Jw (R.Kw + m) 0 x.a (x.a + A.T₀) θ g.stage s.tq
      (fun i v t => truncateTorusHk (weakReductionReserve_order x m v.1) (Uhi i v t))
      (fun i v t => truncateTorusHk (Nat.succ_le_succ (weakReductionReserve_order x m v.1))
        (Whi i v t))
      (fun i _ u _ t => truncateTorusHk (weakReductionReserve_lift x m u.1) (Whi i u t)) := by
  refine ⟨s.start.le, (s.finish.trans (by linarith [A.τ_small])), fun hr t ht => ?_,
    fun i hi hi' => ?_⟩
  · exact (KernelEnergy.truncateTorusHk_toFunction_jet_ae (weakReductionReserve_order x m _)
      (Uhi (x.M + A.Jw) ⟨_, hr⟩ t) (valueIndex2 (R.Kw + m))).trans (hroot hr t ht)
  · obtain ⟨c1, c2, c3, c4, c5⟩ := s.quietMargins i hi hi'
    exact ⟨c1, c2, c3, c4, c5,
      weakReduction_passageSolution s m Uhi Whi i hi hi' (hpass i hi hi')⟩

/-- **The coupled families of the reduction over raw data, at every order offset** `m`: families
at the reduction reserves `K_w + m` plus the descending reserve (independent of `D_m`), whose root
component has the value `θ(t)` from the root time of the clock on, solving every passage. -/
theorem weakStage_coupled_families (S : WeakRawSetting R) (hM2 : 2 ≤ S.M)
    (hreg : S.CoeffRegular) (K : WeakRawClock S) (hsm : WeakScalarSmoothingStatement)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (S.D.Φ (S.M + A.Jw))) (S.D.κ S.M) K.a (K.a + A.T₀) f θ)
    (m : ℕ) :
    ∃ (Uhi : ∀ i, WeakStageFamily S m i) (Whi : ∀ i, WeakStageLift S m i),
      (∀ (hr : (⟨0, []⟩ : Comp) ∈ (S.stage (S.M + A.Jw)).comps),
        ∀ t ∈ Set.Icc K.troot (K.a + A.T₀),
          (Uhi (S.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
              (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
            AVenhance.unitCube] θ t) ∧
        ∀ i, S.M < i → i ≤ S.M + A.Jw → WeakStagePassage S K m Uhi Whi i := by
  have hm : 1 ≤ S.M + A.Jw := by have := A.Jw_pos; omega
  choose Uθ hUθ using fun k => hsm B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ A.Λ
    S.base128 S.D.Φ S.streams (S.M + A.Jw) hm (S.D.κ S.M) S.kappa_pos K.a (K.a + A.T₀) f θ hθ
    K.troot K.troot_gt k
  obtain ⟨Uhi, Whi, hroot, hpass⟩ := weakStage_families S hM2 hreg K m
    (fun v => Uθ (weakReductionReserve R m v.1))
  refine ⟨Uhi, Whi, fun hr t ht => ?_, hpass⟩
  rw [hroot]
  exact hUθ _ t ht

/-- **The coupled families of the reduction of a weak entry at every order offset** `m`
(`weakStage_coupled_families` at the entry data; the root time is `t_{M+J_w+1}`). -/
theorem weakReduction_coupled_families (hcommon : WeakEntryCommonOK plan)
    (hsm : WeakScalarSmoothingStatement) {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (m : ℕ) :
    ∃ (Uhi : ∀ i, WeakReductionFamily g m i) (Whi : ∀ i, WeakReductionLift g m i),
      (∀ (hr : (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps),
        ∀ t ∈ Set.Icc (s.tq (x.M + A.Jw + 1)) (x.a + A.T₀),
          (Uhi (x.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
              (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
            AVenhance.unitCube] θ t) ∧
        ∀ i, x.M < i → i ≤ x.M + A.Jw → WeakReductionPassage s m Uhi Whi i :=
  weakStage_coupled_families (weakEntryRawSetting g) (weakEntryData_M_ge_two hcommon x)
    (weakEntryRawSetting_coeffRegular hcommon g) (weakEntryRawClock s) hsm f θ hθ m

/-- **The weak reduction at every order** `K_w + m` (shared higher-order lemma, existence):
the families at the offset `m + D_m - 2`, truncated to `K_w + m`. -/
theorem weakReduction_exists_at (hcommon : WeakEntryCommonOK plan)
    (hsm : WeakScalarSmoothingStatement) {x : WeakEntryData plan C} (g : WeakEntryStages x)
    (s : WeakEntrySchedule g) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (m : ℕ) :
    ∃ (Ur : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk (R.Kw + m) (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ →
        TorusHk (R.Kw + m + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (g.stage i).fam.Γ v u), ℝ →
        TorusHk (R.Kw + m + x.Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction x.P A.φ₀ A.hφ₀ R.nW x.M A.Jw (R.Kw + m) 0 x.a (x.a + A.T₀) θ g.stage
        s.tq Ur Urw Urk := by
  obtain ⟨Uhi, Whi, hroot, hpass⟩ :=
    weakReduction_coupled_families hcommon hsm s f θ hθ (m + x.Dm - 2)
  exact ⟨_, _, _, weakReduction_of_coupled s θ m hroot hpass⟩

/-- **The weak reduction** from scalar smoothing, for every glue plan dominating the common
coefficient plan (the order offset `0` of `weakReduction_exists_at`). -/
theorem weak_entry_reduction_of_smoothing (plan : WeakEntryGluePlan)
    (hcommon : WeakEntryCommonOK plan) (hsm : WeakScalarSmoothingStatement) :
    WeakEntryReductionStatement plan := by
  intro B A R C x g s f θ hθ
  obtain ⟨Ur, Urw, Urk, h⟩ := weakReduction_exists_at hcommon hsm g s f θ hθ 0
  exact ⟨⟨Ur, Urw, Urk, h⟩⟩
end

/-! **Scalar smoothing from one identification**.

* `WeakScalarTorusIdentificationStatement` (named, the single identification): a weak solution
  `θ` of the scalar equation with an actual stream drift is, on `[t₁, T]` for every `t₁` strictly
  after its start, an order-zero solution of the torus class (`WeakScalarTorusSolution`) from
  `θ(t₁)`, with values `θ(t)` at every `t ∈ [t₁, T]`. It goes from the window weak form to the
  per-time identity.

  The degenerate cases are included:
  - `t₁ = T`: the window is one point; `u ≡ θ(T)`, `w = 0`, and the identity is over an empty
    time interval.
  - `t₁` close to `a`: nothing uniform in `t₁` is claimed.
  - Zero drift: the heat flow from `θ(t₁)`. The proof uses only a smooth, bounded,
    divergence-free, periodic drift.
  - The datum `f` plays no role. `t₁ > a` avoids identifying `θ(a)` with `f`.
* `stream_weakScalarTorusDrift`: the actual stream drift has the drift data of the scalar torus
  class at some radius, on every window and to every finite order. Only existence and uniqueness
  are used, never the constants.
* `weak_scalar_step_up`: one order up inside the torus class. Restart at an almost-every-time
  point where the gradient lift has the next order, solve one order higher, and identify with the
  truncation by uniqueness.
* `weak_scalar_torus_solution_of_identification`: the native scalar torus trajectory of every
  order `k` on `[s, T]`, `s ∈ (a, t₀)`, with values `θ` (the step-up iterated).
* `weak_scalar_smoothing_of_identification`: `WeakScalarSmoothingStatement` from the
  identification.

  The degenerate cases are included:
  - `k = 0`: the identification itself.
  - `t₀ > T`: vacuous.
  - A datum already in `H^k` needs no smoothing, but the statement is the same.
* `weak_entry_reduction_of_identification`: the reduction from the identification. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

/-- **The single identification of scalar smoothing**: on `[t₁, T]`, `a < t₁ ≤ T`, a weak solution
with an actual stream drift is an order-zero solution of the torus class from `θ(t₁)`, with values
`θ(t)` at every time. -/
def WeakScalarTorusIdentificationStatement : Prop :=
  ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → ∀ q : ℝ, IsAdmissibleQ α s q →
  ∀ ζ : ℝ → ℝ, IsFastProfile ζ → ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ,
  IsOCStreamSeq α q Λ ζ Φ → ∀ m : ℕ, 1 ≤ m → ∀ κ : ℝ, 0 < κ →
  ∀ (a T : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (Φ m)) κ a T f θ → ∀ t₁ : ℝ, a < t₁ → t₁ ≤ T →
    ∃ (u : ℝ → TorusHk 0 ℝ) (w : ℝ → TorusHk 1 ℝ),
      WeakScalarTorusSolution κ t₁ T (streamVel (Φ m)) 0 (u t₁) u w ∧
      ∀ t ∈ Set.Icc t₁ T,
        (u t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube] θ t

/-- **The actual stream drift has the scalar torus drift data** on every window, to every finite
order, at some radius. -/
theorem stream_weakScalarTorusDrift (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m) {ν : ℝ} (hν : 0 < ν) (a b : ℝ)
    (Q : ℕ) : ∃ ρ : ℝ, Nonempty (WeakScalarTorusDrift ν ρ a b (streamVel (Φ m)) Q) := by
  obtain ⟨ρ₀, hρ₀, h⟩ := Comparison.stream_torusDriftData α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ
    m hm hν a b Q
  have hd := h ρ₀ hρ₀ le_rfl
  obtain ⟨a', B₀, lam, ha, hB, hlam, hjets, hs1, hs2⟩ := hd.jets
  have hmeas : Measurable (fun p : ℝ × Vec 2 => streamVel (Φ m) p.1 p.2) :=
    (Infra.Construction.smoothPeriodic_streamVel
      (Velocity.streamSeq_admissible hζ hΛ hΦ m)).smooth.continuous.measurable
  exact ⟨ρ₀, ⟨⟨hν, hρ₀, hmeas, hd.bdd, hd.smooth, hd.div, hd.per, a', ha, B₀, hB, lam, hlam,
    hjets, hs1, hs2⟩⟩⟩

/-- A property of almost every time of a window holds at some time of every nonempty open
subinterval. -/
theorem exists_time_of_ae {a b c : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), P t) (hac : a < c) (hcb : c ≤ b) :
    ∃ t ∈ Set.Ioo a c, P t := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioo a c ⊆ Set.Icc a b := fun t ht => ⟨ht.1.le, ht.2.le.trans hcb⟩
  have hfalse : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), False := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h,
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    exact hcon t hmem ht
  have hz := ae_iff.1 hfalse
  simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ,
    Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hz
  linarith

/-- **One order up inside the torus class**: a solution at order `j` on `[s, T]` with values `θ`
gives, at some `s' ∈ (s, t₀)`, a solution at order `j + 1` on `[s', T]` with values `θ`. -/
theorem weak_scalar_step_up {κ s T t₀ : ℝ} {v : ℝ → Vec 2 → Vec 2} {j k : ℕ}
    (hdrift : ∀ a b : ℝ, ∃ ρ : ℝ, Nonempty (WeakScalarTorusDrift κ ρ a b v k))
    (hst₀ : s < t₀) (ht₀ : t₀ ≤ T) (hjk : j + 1 ≤ k) {u : ℝ → TorusHk j ℝ}
    {w : ℝ → TorusHk (j + 1) ℝ} (hsol : WeakScalarTorusSolution κ s T v j (u s) u w)
    {θ : ℝ → Vec 2 → ℝ}
    (hval : ∀ t ∈ Set.Icc s T,
      (u t).toFunction.jet (valueIndex2 j) =ᵐ[volume.restrict AVenhance.unitCube] θ t) :
    ∃ (s' : ℝ) (u' : ℝ → TorusHk (j + 1) ℝ) (w' : ℝ → TorusHk (j + 1 + 1) ℝ),
      s < s' ∧ s' < t₀ ∧ WeakScalarTorusSolution κ s' T v (j + 1) (u' s') u' w' ∧
      ∀ t ∈ Set.Icc s' T,
        (u' t).toFunction.jet (valueIndex2 (j + 1)) =ᵐ[volume.restrict AVenhance.unitCube] θ t := by
  obtain ⟨s', ⟨hss', hs't₀⟩, htr⟩ := exists_time_of_ae (hsol.2.2.1 0) hst₀ ht₀
  have hs'T : s' ≤ T := hs't₀.le.trans ht₀
  obtain ⟨ρ, ⟨hd⟩⟩ := hdrift s' T
  obtain ⟨⟨u', w', hsol'⟩, -⟩ := weak_scalar_torus_exists_unique hjk hd hs'T (w s')
  have hlow := weak_scalar_torus_solution_truncate (Nat.le_succ j) hsol'
  rw [htr] at hlow
  have hres : WeakScalarTorusSolution κ s' T v j (u s') u w :=
    CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_right hss'.le hs'T hsol
  have heq := (weak_scalar_torus_exists_unique (Nat.le_of_succ_le hjk) hd hs'T (u s')).2 _ _ _ _
    hlow hres
  have hu's' : u' s' = w s' := hsol'.2.2.2.1 0
  refine ⟨s', u', w', hss', hs't₀, hu's' ▸ hsol', fun t ht => ?_⟩
  have h1 := KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.le_succ j) (u' t) (valueIndex2 j)
  rw [heq t ht] at h1
  exact h1.symm.trans (hval t ⟨hss'.le.trans ht.1, ht.2⟩)

/-- **The native scalar torus trajectory of every order from the identification**: for every
`k` and `a < t₀ ≤ T` there is `s ∈ (a, t₀)` and an order-`k` solution of the scalar torus class on
`[s, T]` (`WeakScalarTorusSolution`, with its gradient lift) whose values are `θ` at every time. -/
theorem weak_scalar_torus_solution_of_identification (hid : WeakScalarTorusIdentificationStatement)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ)
    (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (hκ : 0 < κ) (a T : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (Φ m)) κ a T f θ) (t₀ : ℝ) (ht₀ : a < t₀) (hT : t₀ ≤ T)
    (k : ℕ) :
    ∃ (s' : ℝ) (u : ℝ → TorusHk k ℝ) (w : ℝ → TorusHk (k + 1) ℝ),
      a < s' ∧ s' < t₀ ∧ WeakScalarTorusSolution κ s' T (streamVel (Φ m)) k (u s') u w ∧
      ∀ t ∈ Set.Icc s' T,
        (u t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube] θ t := by
  have ht₁ : a < (a + t₀) / 2 := by linarith
  have ht₁₀ : (a + t₀) / 2 < t₀ := by linarith
  obtain ⟨u₀, w₀, hsol₀, hval₀⟩ := hid α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm κ hκ a T f
    θ hθ ((a + t₀) / 2) ht₁ (ht₁₀.le.trans hT)
  have hdrift := fun a' b' => stream_weakScalarTorusDrift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ
    hΦ m hm hκ a' b' k
  have main : ∀ j, j ≤ k → ∃ (s' : ℝ) (u : ℝ → TorusHk j ℝ) (w : ℝ → TorusHk (j + 1) ℝ),
      a < s' ∧ s' < t₀ ∧ WeakScalarTorusSolution κ s' T (streamVel (Φ m)) j (u s') u w ∧
      ∀ t ∈ Set.Icc s' T,
        (u t).toFunction.jet (valueIndex2 j) =ᵐ[volume.restrict AVenhance.unitCube] θ t := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨(a + t₀) / 2, u₀, w₀, ht₁, ht₁₀, hsol₀, hval₀⟩
    | succ j ih =>
      intro hj
      obtain ⟨s', u, w, has', hs', hsol, hval⟩ := ih (by omega)
      obtain ⟨s'', u', w', hss, hs'', hsol', hval'⟩ :=
        weak_scalar_step_up hdrift hs' hT hj hsol hval
      exact ⟨s'', u', w', has'.trans hss, hs'', hsol', hval'⟩
  exact main k le_rfl

/-- **Scalar smoothing from the identification.** -/
theorem weak_scalar_smoothing_of_identification (hid : WeakScalarTorusIdentificationStatement) :
    WeakScalarSmoothingStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm κ hκ a T f θ hθ t₀ ht₀ k
  by_cases hT : t₀ ≤ T
  · obtain ⟨s', u, -, -, hs', -, hval⟩ := weak_scalar_torus_solution_of_identification hid α s
      hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm κ hκ a T f θ hθ t₀ ht₀ hT k
    exact ⟨u, fun t ht => hval t ⟨hs'.le.trans ht.1, ht.2⟩⟩
  · exact ⟨fun _ => 0, fun t ht => absurd (ht.1.trans ht.2) hT⟩

/-- **The weak reduction from the identification**, for every glue plan dominating the common
coefficient plan. -/
theorem weak_entry_reduction_of_identification (plan : WeakEntryGluePlan)
    (hcommon : WeakEntryCommonOK plan) (hid : WeakScalarTorusIdentificationStatement) :
    WeakEntryReductionStatement plan :=
  weak_entry_reduction_of_smoothing plan hcommon (weak_scalar_smoothing_of_identification hid)
end

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The scalar identification, step 1**: one weak solution is a forced torus
solution, and its pairing identity in divergence form.

* `streamSeq_isContDrift`: the actual stream drift is a continuous, bounded, periodic,
  divergence-free drift (`IsContDrift`).
* `isTorusForced_of_weakSolutionOnWith`: a weak solution is `IsTorusForced` with flux `κ Dθ` and
  forcing `−b·Dθ` (the single-solution form of `isTorusForced_difference`).
* `weak_pairing_divergence`: for a smooth periodic test `ψ` and `t₁ ≤ σ ≤ τ < t₂`,
  `⟨θ τ, ψ⟩ − ⟨θ σ, ψ⟩ = ∫_σ^τ ∫ (−(b·Dθ) ψ − κ Dθ·∇ψ)`. This is `weak_pairing_increment` with
  both derivatives moved back onto `θ` at almost every time (`periodic_drift_ibp`,
  `periodic_grad_ibp`). -/

open Applications

/-- **The actual stream drift is a continuous drift** in the sense of the window weak form. -/
theorem streamSeq_isContDrift {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    IsContDrift (streamVel (Φ m)) := by
  have hadm := Velocity.streamSeq_admissible hζ hΛ hΦ m
  obtain ⟨hs, hp⟩ := isSmoothStream_of_seq hζ hΛ hΦ m
  obtain ⟨C, hC⟩ := bounded_streamVel_smooth hs hp 0 1
  refine ⟨Velocity.streamSeq_velocity_spatial_periodic hζ hΛ hΦ m,
    finite_velocity_continuous hζ hΛ hΦ m, ⟨max C 0, le_max_right _ _, fun t x => ?_⟩,
    Velocity.streamSeq_velocity_divFree hζ hΛ hΦ m⟩
  have hshift : Φ m t = Φ m (t - ⌊t⌋) := by
    funext y
    have h := hadm.2 ⌊t⌋ 0 (t - ⌊t⌋) y
    have h0 : latticeShift (0 : Fin 2 → ℤ) = (0 : Vec 2) := by
      ext i
      simp [latticeShift]
    rw [h0, add_zero, sub_add_cancel] at h
    exact h
  have hv : streamVel (Φ m) t x = streamVel (Φ m) (t - ⌊t⌋) x := by
    simp [AVenhance.streamVel, hshift]
  rw [hv]
  exact (hC _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩ x).trans (le_max_left _ _)

/-- **A weak solution is a forced torus solution** with flux `κ Dθ` and forcing `−b·Dθ`. -/
theorem isTorusForced_of_weakSolutionOnWith {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hbb : ∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x, ‖b t x‖ ≤ C)
    (hbp : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (b t))
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    IsTorusForced θ Dθ (fun t x => κ • Dθ t x) (fun t x => -vecDot (b t x) (Dθ t x)) t₁ t₂ := by
  obtain ⟨Cb, hCb⟩ := hbb
  have hbpo : ∀ t ∈ Set.Ioo t₁ t₂, IsZ2Periodic (b t) := fun t ht =>
    hbp t (Set.Ioo_subset_Icc_self ht)
  have hIoo : MeasurableSet (Set.Ioo t₁ t₂) := measurableSet_Ioo
  have h' := h
  obtain ⟨hus, -, huL2, huDL2, huH1, -, hucont, -⟩ := h'
  refine ⟨hus, huL2, huDL2, fun i => ?_, ?_, huH1, ?_, ?_, ?_, hucont⟩
  · have := (huDL2 i).const_mul κ
    simpa using this
  · exact (memLp_dot_window (a := t₁) (b := t₂) (m := b) (D := Dθ) hbm
      (fun t ht x => hCb t (Set.Ioo_subset_Icc_self ht) x) huDL2).neg
  · filter_upwards [huH1] with t h1
    intro n x
    simp [h1.2.1 n x]
  · filter_upwards [huH1, ae_restrict_mem hIoo] with t h1 ht
    intro n x
    simp only [hbpo t ht n x, h1.2.1 n x]
  · intro φ hφ
    have hA := (isLocalWeakSolution_of_weakSolutionOnWith hbpo h).2.2.2 φ hφ
    rw [← hA]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring

/-- The transport and diffusion pairing moved back onto an `H¹` slice. -/
theorem incK_eq_divergence {b : Vec 2 → Vec 2} (hbc : Continuous b)
    (hbB : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (hbp : IsZ2Periodic b)
    (hdiv : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b x) (spaceGrad φ x) = 0) (κ : ℝ)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) :
    ∫ x in unitCube, u x * (vecDot (b x) (spaceGrad ψ x) + κ * lapl ψ x) =
      ∫ x in unitCube, (-(vecDot (b x) (Du x) * ψ x) - κ * vecDot (Du x) (spaceGrad ψ x)) := by
  have hdrift := periodic_drift_ibp hbc hbB hbp hdiv hu hψ hψp
  have hgrad (j : Fin 2) := periodic_grad_ibp hu (contDiff_spaceGrad_apply hψ j)
    (fun n x => congrFun (spaceGrad_periodic hψp n x) j) j
  have hψ1 : ContDiff ℝ 1 ψ := contDiff_one_of_top hψ
  have huL := hu.2.2.1
  have hDuL := hu.2.2.2.1
  have hbg : Continuous fun x => vecDot (b x) (spaceGrad ψ x) := by
    unfold vecDot
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hbc).mul (continuous_spaceGrad_apply hψ1 i)
  have ib : Integrable (fun x => u x * vecDot (b x) (spaceGrad ψ x)) (volume.restrict unitCube) :=
    integrable_mul_memL2 huL (memL2_continuous hbg)
  have il (j : Fin 2) : Integrable (fun x => u x * spaceGrad (fun y => spaceGrad ψ y j) x j)
      (volume.restrict unitCube) :=
    integrable_mul_memL2 huL (memL2_continuous
      (continuous_spaceGrad_apply (contDiff_one_of_top (contDiff_spaceGrad_apply hψ j)) j))
  have ig (j : Fin 2) : Integrable (fun x => Du x j * spaceGrad ψ x j) (volume.restrict unitCube) :=
    integrable_mul_memL2 (hDuL j) (memL2_continuous (continuous_spaceGrad_apply hψ1 j))
  have ibd (j : Fin 2) : Integrable (fun x => Du x j * (b x j * ψ x)) (volume.restrict unitCube) :=
    integrable_mul_memL2 (hDuL j) (memL2_continuous
      (((continuous_apply j).comp hbc).mul hψ.continuous))
  have hL : ∫ x in unitCube, u x * (vecDot (b x) (spaceGrad ψ x) + κ * lapl ψ x) =
      (∫ x in unitCube, u x * vecDot (b x) (spaceGrad ψ x)) +
        κ * ∑ j : Fin 2, ∫ x in unitCube, u x * spaceGrad (fun y => spaceGrad ψ y j) x j := by
    rw [← integral_finsetSum _ (fun j _ => il j), ← integral_const_mul,
      ← integral_add ib ((integrable_finsetSum _ (fun j _ => il j)).const_mul κ)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [lapl, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hB : ∫ x in unitCube, vecDot (b x) (Du x) * ψ x =
      ∑ j : Fin 2, ∫ x in unitCube, Du x j * (b x j * ψ x) := by
    rw [← integral_finsetSum _ (fun j _ => ibd j)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [vecDot, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hI1 : Integrable (fun x => ∑ j : Fin 2, Du x j * (b x j * ψ x)) (volume.restrict unitCube) :=
    integrable_finsetSum _ fun j _ => ibd j
  have hI2 : Integrable (fun x => ∑ j : Fin 2, Du x j * spaceGrad ψ x j)
      (volume.restrict unitCube) := integrable_finsetSum _ fun j _ => ig j
  have e : ∀ x, -(vecDot (b x) (Du x) * ψ x) - κ * vecDot (Du x) (spaceGrad ψ x) =
      -(∑ j : Fin 2, Du x j * (b x j * ψ x)) - κ * ∑ j : Fin 2, Du x j * spaceGrad ψ x j := by
    intro x
    simp only [vecDot, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ => show b x j * Du x j * ψ x = Du x j * (b x j * ψ x) by
      ring)]
  have hR : ∫ x in unitCube, (-(vecDot (b x) (Du x) * ψ x) - κ * vecDot (Du x) (spaceGrad ψ x)) =
      -(∑ j : Fin 2, ∫ x in unitCube, Du x j * (b x j * ψ x)) -
        κ * ∑ j : Fin 2, ∫ x in unitCube, Du x j * spaceGrad ψ x j := by
    calc ∫ x in unitCube, (-(vecDot (b x) (Du x) * ψ x) - κ * vecDot (Du x) (spaceGrad ψ x))
        = ∫ x in unitCube, (-(∑ j : Fin 2, Du x j * (b x j * ψ x)) -
            κ * ∑ j : Fin 2, Du x j * spaceGrad ψ x j) :=
          integral_congr_ae (Eventually.of_forall e)
      _ = _ := by
          rw [integral_sub (f := fun x => -(∑ j : Fin 2, Du x j * (b x j * ψ x)))
            (g := fun x => κ * ∑ j : Fin 2, Du x j * spaceGrad ψ x j) hI1.neg (hI2.const_mul κ),
            integral_neg, integral_const_mul, integral_finsetSum _ (fun j _ => ibd j),
            integral_finsetSum _ (fun j _ => ig j)]
  rw [hL, hR, ← hB, hdrift]
  have hl : ∀ j : Fin 2, ∫ x in unitCube, u x * spaceGrad (fun y => spaceGrad ψ y j) x j =
      -∫ x in unitCube, Du x j * spaceGrad ψ x j := fun j => by
    rw [hgrad j, neg_neg]
  simp only [hl, Finset.sum_neg_distrib]
  ring

/-- **The pairing identity in divergence form**: for a smooth periodic test and
`t₁ ≤ σ ≤ τ < t₂`, the increment of `⟨θ, ψ⟩` is the time integral of the transport and diffusion
terms with both derivatives on `θ`. -/
theorem weak_pairing_divergence {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) {σ τ : ℝ} (hσ : t₁ ≤ σ) (hστ : σ ≤ τ)
    (hτ : τ < t₂) :
    pairing θ ψ τ - pairing θ ψ σ = ∫ t in σ..τ, ∫ x in unitCube,
      (-(vecDot (b t x) (Dθ t x) * ψ x) - κ * vecDot (Dθ t x) (spaceGrad ψ x)) := by
  rw [weak_pairing_increment hb h hψ hψp hσ hστ hτ]
  have hH1 := (ae_restrict_iff' measurableSet_Ioo).1 h.2.2.2.2.1
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hH1] with t ht htI
  rw [Set.uIoc_of_le hστ] at htI
  exact incK_eq_divergence (hb.slice_continuous t) ⟨B, hB0, fun x => hB t x⟩ (hb.periodic t)
    (hb.divFree t) κ (ht ⟨hσ.trans_lt htI.1, htI.2.trans_lt hτ⟩) hψ hψp

end AVRegularity.Providers.WeakGen.Reduction
end
end
end
