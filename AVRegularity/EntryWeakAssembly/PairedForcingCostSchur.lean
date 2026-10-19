-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
public import AVRegularity.EntryWeakAssembly.Assembly.WeakQuietCoefficientOfIngredients
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.Analysis.Schur.Finite
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Ledger
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Positive finite path summation, with no loss depending on the component
count. The analytic scalar/source evolution is an explicitly separate leaf. -/

/-- The finite Schur test controls a vector dominated rowwise by a positive matrix. -/
theorem quiet_finite_schur : QuietFiniteSchurStatement := by
  classical
  intro ι _ K x y C hC hK hy hdom hrow hcol
  have hleft : (∑ v, y v ^ 2) ≤ ∑ v, ∑ u, K v u * y v * x u := by
    apply Finset.sum_le_sum
    intro v _
    have h := mul_le_mul_of_nonneg_left (hdom v) (hy v)
    simpa only [pow_two, Finset.mul_sum, mul_left_comm, mul_assoc] using h
  have hs := Analysis.Schur.finiteSchurBilinear Finset.univ Finset.univ K y x C hC
    (fun v _ u _ => hK v u) (fun v _ => hrow v) (fun u _ => hcol u)
  have htotal := hleft.trans hs
  have hySq : 0 ≤ ∑ v, y v ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg (y v)
  have hroot := Real.sqrt_nonneg (∑ v, y v ^ 2)
  by_cases hz : Real.sqrt (∑ v, y v ^ 2) = 0
  · rw [hz]; exact mul_nonneg hC (Real.sqrt_nonneg _)
  · have hp := lt_of_le_of_ne hroot (Ne.symm hz)
    apply le_of_mul_le_mul_left _ hp
    calc
      Real.sqrt (∑ v, y v ^ 2) * Real.sqrt (∑ v, y v ^ 2) = ∑ v, y v ^ 2 :=
        Real.mul_self_sqrt hySq
      _ ≤ C * Real.sqrt (∑ v, y v ^ 2) * Real.sqrt (∑ u, x u ^ 2) := htotal
      _ = Real.sqrt (∑ v, y v ^ 2) * (C * Real.sqrt (∑ u, x u ^ 2)) := by ring

/-- Positive path kernels have both row and column budgets bounded by the same
stored-total polynomial. The existing weakStoredPath_sum_le supplies each power. -/
theorem weak_quiet_path_schur (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) :
    WeakQuietPathSchurStatement plan prices := by
  classical
  intro B A R c i
  let G := c.stage i
  let w := weakStoredEdgeWeight G A.Nw A.Jw A.η₀
  have hw : ∀ e, 0 ≤ w e := weakStoredEdgeWeight_nonneg G A.Nw A.Jw A.η₀
  have hp : ∀ n (π : StagePath G (n + 1)), 0 ≤ pathWeight w π :=
    fun _ π => pathWeight_nonneg w hw π
  have hkernel : ∀ v u, 0 ≤ weakQuietPathKernel prices c i v u := by
    intro v u
    unfold weakQuietPathKernel
    apply add_nonneg
    · split <;> [exact prices.nonneg R 0; exact le_rfl]
    · apply Finset.sum_nonneg
      intro n _
      apply mul_nonneg (prices.nonneg R _)
      apply Finset.sum_nonneg
      intro π _
      split <;> [exact hp n π; exact le_rfl]
  have hcost : 0 ≤ weakQuietPathCost prices c i :=
    add_nonneg (prices.nonneg R 0) (Finset.sum_nonneg fun n _ =>
      mul_nonneg (prices.nonneg R _) (pow_nonneg (weakStoredTotal_nonneg G _ _ _) _))
  refine ⟨hkernel, hcost, ?_, ?_⟩
  · intro v
    have hone : ∀ n, (∑ u, ∑ π : StagePath G (n + 1),
        if (π.step (Fin.last n)).1 = v ∧ (π.step 0).2.1 = u then pathWeight w π else 0) ≤
        weakStoredTotal G A.Nw A.Jw A.η₀ ^ (n + 1) := by
      intro n
      rw [Finset.sum_comm]
      apply le_trans _ (weakStoredPath_sum_le G A.Nw A.Jw A.η₀ (n + 1))
      apply Finset.sum_le_sum
      intro π _
      by_cases ht : (π.step (Fin.last n)).1 = v
      · simp only [ht, true_and]
        simp [w]
      · simp only [ht, false_and, ite_false, Finset.sum_const_zero]
        exact hp n π
    unfold weakQuietPathKernel weakQuietPathCost
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply add_le_add le_rfl
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hone n) (prices.nonneg R _)
  · intro u
    have hone : ∀ n, (∑ v, ∑ π : StagePath G (n + 1),
        if (π.step (Fin.last n)).1 = v ∧ (π.step 0).2.1 = u then pathWeight w π else 0) ≤
        weakStoredTotal G A.Nw A.Jw A.η₀ ^ (n + 1) := by
      intro n
      rw [Finset.sum_comm]
      apply le_trans _ (weakStoredPath_sum_le G A.Nw A.Jw A.η₀ (n + 1))
      apply Finset.sum_le_sum
      intro π _
      by_cases hs : (π.step 0).2.1 = u
      · simp only [hs, and_true]
        simp [w]
      · simp only [hs, and_false, ite_false, Finset.sum_const_zero]
        exact hp n π
    unfold weakQuietPathKernel weakQuietPathCost
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply add_le_add le_rfl
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hone n) (prices.nonneg R _)

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
section
/-! **The kernel price of the paired system at the requested order `K_w`**. The stage invariant
prices the paired kernels only at orders `≤ k_W.K_s`, which the request's field order `K_w` need not
respect, so the price is recomputed at `K_w` and the capped radius `c_K x`, from the same
ingredients as the stage invariant: the uniform physical production at the order `K_w`
(`weakKernelPhysicalData A s_Z K_w`), the identity price (`weak_kernel_identity_price`), the stored
ledger (`weakStoredLedgerData`) and the relabeled Schur bound (`weakRelabel_schur_of_stored`), with
the regularizer constants of the weak paired kernel (`weakPairedRegConstants`).
* `WeakEntryPairedPlanOK`: lower bounds only. The radius is at most `1/2048`, and the level floor
  dominates `weakPairedLevelFloor` (the production and ledger thresholds at `K_w`, the level where
  the price `C ε_M^{χ_w}` is at most `1/8`, and the level where the drift strain at `c_K x` is
  paid: `ε_M^γ ≤ 256/(C_drift + 1)`).
* `weakPaired_schur`: both Schur sums of the paired kernel matrix of `Gw` at `K_w` are at most
  `C ε_M^{χ_w}`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs
open AVRegularity.WeakEntryProofs.Assembly

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- The regularizer constants of the weak paired kernel. -/
theorem exists_weakPairedRegConstants (R : WeakPassageRequest A) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm,
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b c r ((isoPairedKernel r R.nW).op A.φ₀ A.hφ₀) :=
  exists_isoPairedKernel_regularizer_constants A.φ₀
    (Providers.hasCompactSupport_of_unitBall A.support) A.smooth A.hφ₀ R.nW

/-- The chosen regularizer constants. -/
def weakPairedRegConstants (R : WeakPassageRequest A) : ℕ → ℝ :=
  Classical.choose (exists_weakPairedRegConstants R)

theorem weakPairedRegConstants_spec (R : WeakPassageRequest A) :
    (∀ j, 0 ≤ weakPairedRegConstants R j) ∧ ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm,
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b (weakPairedRegConstants R) r
        ((isoPairedKernel r R.nW).op A.φ₀ A.hφ₀) :=
  Classical.choose_spec (exists_weakPairedRegConstants R)

/-- The price constant of one identity at the order `K_w`. -/
def weakPairedPriceConst (R : WeakPassageRequest A) : ℝ :=
  (weakKernelPhysicalData A R.sZ R.Kw).C *
    ∑ d ∈ Finset.Icc 2 (1 + A.Jw * A.Nw), max 0 (weakPairedRegConstants R (d - 2))

theorem weakPairedPriceConst_nonneg (R : WeakPassageRequest A) : 0 ≤ weakPairedPriceConst R :=
  mul_nonneg (weakKernelPhysicalData A R.sZ R.Kw).nonneg
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)

/-- The level floor of the paired solve. -/
def weakPairedLevelFloor (R : WeakPassageRequest A) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    max (max (weakKernelPhysicalData A R.sZ R.Kw).threshold (weakStoredLedgerData A).threshold)
      (max (Classical.choose (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1 hΛ
          (weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 A.η₀_small)
          (c := 1 / (8 * (weakPairedPriceConst R * (weakStoredLedgerData A).C + 1)))
          (by have := weakPairedPriceConst_nonneg R
              have := (weakStoredLedgerData A).positive
              positivity)))
        (Classical.choose (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1 hΛ
          (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).1
          (c := 256 / (Construction.Preservation.Buffer.actualDriftJetConstant + 1))
          (by have := Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
              positivity))))
  else 0

/-- Plan condition of the paired solve (lower bounds only). -/
def WeakEntryPairedPlanOK (plan : WeakEntryGluePlan) : Prop :=
  (∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    plan.radius R ≤ 1 / 2048) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ),
    weakPairedLevelFloor R ≤ plan.levelFloor R C j₀

/-- **What the level floor gives at the terminal level.** -/
theorem weakPairedLevelFloor_spec {plan : WeakEntryGluePlan} (hok : WeakEntryPairedPlanOK plan)
    {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
    (x : WeakEntryData plan C) :
    (weakKernelPhysicalData A R.sZ R.Kw).threshold ≤ x.M ∧
      (weakStoredLedgerData A).threshold ≤ x.M ∧
      ocEpsilon B.q A.Λ x.M ^ weakChi B.α B.q A.η₀ ≤
        1 / (8 * (weakPairedPriceConst R * (weakStoredLedgerData A).C + 1)) ∧
      ocEpsilon B.q A.Λ x.M ^ ocGamma B.α B.q ≤
        256 / (Construction.Preservation.Buffer.actualDriftJetConstant + 1) := by
  have hle := (hok.2 R C x.j₀).trans x.level_ge
  unfold weakPairedLevelFloor at hle
  rw [dite_eq_left x.base128] at hle
  refine ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hle),
    (le_max_right _ _).trans ((le_max_left _ _).trans hle), ?_, ?_⟩
  · exact Classical.choose_spec (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1
      x.base128 (weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 A.η₀_small)
      (c := 1 / (8 * (weakPairedPriceConst R * (weakStoredLedgerData A).C + 1)))
      (by have := weakPairedPriceConst_nonneg R
          have := (weakStoredLedgerData A).positive
          positivity)) x.M
      ((le_max_left _ _).trans ((le_max_right _ _).trans hle))
  · exact Classical.choose_spec (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1
      x.base128 (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).1
      (c := 256 / (Construction.Preservation.Buffer.actualDriftJetConstant + 1))
      (by have := Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
          positivity)) x.M
      ((le_max_right _ _).trans ((le_max_right _ _).trans hle))

/-- **The paired kernel matrix of `Gw` at the order `K_w` and the capped radius has both Schur
sums at most `C ε_M^{χ_w}`.** -/
theorem weakPaired_schur {plan : WeakEntryGluePlan} (hok : WeakEntryPairedPlanOK plan)
    {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
    {x : WeakEntryData plan C} (g : WeakEntryStages x) (law : BirthLaw)
    (hm : law.rootMass = g.rootM)
    (e : ∀ v u, (g.stage x.M).fam.Γ v u ≃ g.Gw.fam.Γ (g.relabel v) (g.relabel u))
    (hB : ∀ v u (γ : (g.stage x.M).fam.Γ v u) d,
      g.Gw.physCoeff (g.relabel v) (g.relabel u) (e v u γ) d = (g.stage x.M).physCoeff v u γ d)
    (a b : ℝ) :
    SchurBound (weakPairedPriceConst R * (weakStoredLedgerData A).C *
        x.D.eps x.M ^ weakChi B.α B.q A.η₀)
      (kernelSchurMatrix (ι := CompIn g.Gw.comps) (h := fun v => ScalarH v.1.root)
        (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (x.D.κ x.M)
        (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) R.Kw x.Dm a b
        (weakPairedRegConstants R) (fun _ _ _ => x.D.termRW A.σw x.M)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun v u γ d => g.Gw.physCoeff v u γ d.1)) := by
  obtain ⟨hVs, hSs, -, -⟩ := weakPairedLevelFloor_spec hok x
  have h128 := x.base128
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans h128
  have hζ : IsFastProfile x.D.ζ := by rw [x.profile_eq]; exact B.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.alpha, x.q_eq, x.base_eq, x.profile_eq, x.terminal]; exact x.band
  have hε : 0 < x.D.eps x.M := Construction.Stream.ocEpsilon_pos hΛ1
  have hε' : 0 < x.D.eps (x.M + 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hε1 : x.D.eps x.M ≤ 1 := by
    simpa only [OCData.eps, x.q_eq, x.base_eq] using
      (Scales.epsilon_basic (m := x.M) B.hq.1 h128).2.1
  have hν : 0 < x.D.κ x.M := CycleReference.bandChain_pos hΛ1 hζ hband (by rw [x.terminal])
  set ρ := x.D.termRStar (plan.radius R) x.M with hρdef
  set r := x.D.termRW A.σw x.M with hrdef
  have hcK := weak_entry_radius_spec (plan.radiusBudget R)
  have hρ : 0 ≤ ρ := mul_nonneg hcK.1.le hε.le
  have hρe : ρ ≤ x.D.eps x.M := mul_le_of_le_one_left hε.le hcK.2.1
  have hr : 0 < r := Real.rpow_pos_of_pos hε _
  have hre : r ≤ x.D.eps x.M := by
    change x.D.eps x.M ^ (1 + A.σw) ≤ _
    rw [Real.rpow_add hε, Real.rpow_one]
    exact mul_le_of_le_one_right hε.le (Real.rpow_le_one hε.le hε1 A.σw_pos.le)
  have hhr : x.D.eps (x.M + 1) ≤ r := by
    simpa only [r, OCData.eps, OCData.termRW, x.q_eq, x.base_eq] using
      (weakStoredLedgerData A).price h128 x.M hSs
  set G := g.stage x.M
  set V := weakKernelPhysicalData A R.sZ R.Kw
  set Cp := weakPairedPriceConst R
  have hC : 0 ≤ Cp := weakPairedPriceConst_nonneg R
  have hprod := V.bound h128 x.D (by rw [x.terminal]; exact hVs) x.alpha x.q_eq x.base_eq
    x.profile_eq x.streams hband x.Dm x.order_ge x.j₀ g.stage x.P x.M R.sX 0 A.η₀ r x.terminal
    g.construction x.M le_rfl (by have := A.Jw_pos; omega)
  have horder := EntryWeakProofs.weakConstruction_output_maxOrder_bound x.P
    ⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, x.M + A.Jw⟩ x.M A.Jw r 0 g.stage g.construction x.M le_rfl
    (by have := A.Jw_pos; omega)
  have htotal := (weakStoredLedgerData A).total h128 x.M hSs x.D x.alpha x.q_eq x.base_eq
    x.terminal x.band x.Dm x.j₀ x.P R.sX R.sZ g.stage g.construction
  have hprice (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      (∑ d : ↥(Finset.Icc 2 x.Dm),
        (coefficientSeminorm ρ R.Kw a b (G.physCoeff v u γ d.1)).toReal *
          weakPairedRegConstants R (d.1 - 2) / (x.D.κ x.M * r ^ (d.1 - 2))) ≤
        Cp * (G.fam.identity v u γ).record.size := by
    apply weak_kernel_identity_price (fun d => G.physCoeff v u γ d) (x.D.κ x.M) V.C
      (G.fam.identity v u γ).record.size (x.D.eps (x.M + 1)) (x.D.eps x.M) r ρ
      (weakPairedRegConstants R) (G.fam.identity v u γ).maxOrder (1 + A.Jw * A.Nw) x.Dm R.Kw a b
      hν V.nonneg (G.fam.identity v u γ).record.size_nonneg hε hε'.le hr hhr hre hρ hρe
      (horder v u γ)
    · intro d hd
      funext t y
      exact CycleJointProofs.constituentPhysical_zero_above_max G.fam
        (x.D.kap G.level) (x.D.eps G.level) (x.D.eps (G.level - 1)) G.actual v u γ d hd t y
    · intro d hd hdn
      exact hprod v u γ d R.Kw hd hdn le_rfl a b
  have hschur := weakRelabel_schur_of_stored A.Nw A.Jw A.η₀ G g.Gw g.relabel Cp hC
    (kernelSchurMatrix (ι := CompIn g.Gw.comps) (h := fun v => ScalarH v.1.root)
      (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (x.D.κ x.M) ρ (g.Gw.mass law) R.Kw
      x.Dm a b (weakPairedRegConstants R) (fun _ _ _ => r)
      (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
      (fun v u γ d => g.Gw.physCoeff v u γ d.1))
  have hpoint (v u : CompIn G.comps) :
      kernelSchurMatrix (ι := CompIn g.Gw.comps) (h := fun v => ScalarH v.1.root)
        (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (x.D.κ x.M) ρ (g.Gw.mass law)
        R.Kw x.Dm a b (weakPairedRegConstants R) (fun _ _ _ => r)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun v u γ d => g.Gw.physCoeff v u γ d.1) (g.relabel v) (g.relabel u) ≤
        Cp * Real.sqrt (weakMass x.D A.Nw A.Jw A.η₀ u.1 / weakMass x.D A.Nw A.Jw A.η₀ v.1) *
          ∑ γ : G.fam.Γ v u, (G.fam.identity v u γ).record.size := by
    unfold kernelSchurMatrix
    rw [weakEncoding_mass A.Nw A.Jw A.η₀ _ _ G g.Gw g.relabel g.encoding law hm u,
      weakEncoding_mass A.Nw A.Jw A.η₀ _ _ G g.Gw g.relabel g.encoding law hm v,
      ← (e v u).sum_comp]
    simp only [ContinuousLinearMap.norm_id, one_mul, hB]
    calc
      _ ≤ Real.sqrt _ * ∑ γ : G.fam.Γ v u, Cp * (G.fam.identity v u γ).record.size :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ _ => hprice v u γ) (Real.sqrt_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hs := hschur hpoint
  have hfinal : Cp * weakStoredTotal G A.Nw A.Jw A.η₀ ≤
      Cp * (weakStoredLedgerData A).C * x.D.eps x.M ^ weakChi B.α B.q A.η₀ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left htotal hC
  exact ⟨fun v => (hs.1 v).trans hfinal, fun u => (hs.2 u).trans hfinal⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! Middle-half quiet margins are trimmed, and the existing availability theorem
makes their entire finer history quiet. Heat-window fitting is eventual. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Providers.QuietAtlas
namespace AVRegularity.WeakEntryProofs.Assembly

/-- The whole backward middle half is trimmed, including its endpoints. This
only asserts pulse vanishing on small neighborhoods, not fast independence. -/
theorem weak_middle_half_trimmed {plan : WeakPassagePlan} {B} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hw : WeakQuietWindow c r i) : weakMiddleHalf c r i ⊆ ocTrimmedQuiet c.D i := by
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  obtain ⟨l, hl⟩ := hw.2.2.2.1
  have hτ := Construction.Stream.ocTau_pos (α := c.D.α) (q := c.D.q) (m := i) hΛ
  have hτP := (CycleReference.pulse_time_scale_relations (α := c.D.α) (q := c.D.q) (m := i) hΛ).1
  intro t ht
  refine mem_ocTrimmedQuietTimes.mpr fun u hu => ?_
  apply CycleJointProofs.renewal_boundary_quiet_margin hΛ c.D.ζ l
  change _ ≤ t ∧ t ≤ _ at ht
  change _ ≤ u ∧ u ≤ _ at hu
  rw [← hl]
  constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]

/-- History on the middle half: every active child's complete, two-sided
availability hull is quiet, uniformly in the finite depth of the construction. -/
theorem weak_middle_half_history (plan : WeakPassagePlan) : WeakMiddleHalfHistoryStatement plan := by
  intro hplan B A R c r i hi _ hw
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  obtain ⟨j, hj, hstart⟩ := (hplan c).1
  have hstart' : IsCarrierStart c.D.α c.D.q c.D.Λ 1 1 1 j := by
    simpa only [c.alpha, c.q_eq, c.base_eq] using hstart
  exact (isHistoryQuiet_ocTrimmedQuiet hΛ (le_refl 1) hstart' (c.M + A.Jw) i
    (by omega)).mono (weak_middle_half_trimmed c r i hw)

private theorem heat_exponent_pos {α q : ℝ} (hα : 0 < α) (hq : 1 < q) :
    0 < ocGamma α q - 3 * ocDelta α q := by
  have hid : ocGamma α q - 3 * ocDelta α q =
      (q - 1) * (5 + (6 * q + 11) * α) / (8 * (q + 1)) := by
    unfold ocGamma ocDelta
    field_simp
    ring
  rw [hid]
  apply div_pos
  · apply mul_pos (sub_pos.mpr hq)
    have hq0 : 0 < q := zero_lt_one.trans hq
    positivity
  · linarith

/-- Both purely geometric plan conditions admit one threshold, independent of
J, Dm, the stage, the clock and every scalar datum. -/
theorem weak_quiet_geometry_threshold (B : WeakCoefficientBase) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (∃ j : ℕ, j ≤ M + 1 ∧ IsCarrierStart B.α B.q Λ 1 1 1 j) ∧
      ∀ ν ∈ ocBand B.α B.q Λ M, ∀ i : ℕ, M < i →
        ocEpsilon B.q Λ (i - 1) ^ 2 / ν ≤ ocTauP B.α B.q Λ i / 2 := by
  obtain ⟨j, hj⟩ := Providers.carrier_start_exists B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
    Λ hΛ 1 1 1 zero_lt_one
  obtain ⟨C, hC, hscale⟩ := EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨N, hN⟩ := Providers.exists_parent_rpow_lt B.hq.1 hΛ
    (heat_exponent_pos B.hα₀ B.hq.1) (show 0 < 1 / (2 * C) by positivity)
  refine ⟨max j N, fun M hM => ⟨⟨j, by omega, hj⟩, ?_⟩⟩
  intro ν hν i hi
  have hP := Velocity.Jets.ocTauP_pos (α := B.α) (q := B.q) (m := i)
    ((by norm_num : 1 ≤ 128).trans hΛ)
  have hE := Construction.Stream.ocEpsilon_pos (q := B.q) (n := M)
    ((by norm_num : 1 ≤ 128).trans hΛ)
  have hνpos : 0 < ν := lt_of_lt_of_le (by
    apply div_pos (Real.rpow_pos_of_pos hE _)
    norm_num) hν.1
  have hs := (hscale Λ hΛ M ν hν i hi).2.2.1
  have hsmall := hN i (by omega)
  have hb : C * ocEpsilon B.q Λ (i - 1) ^ (ocGamma B.α B.q - 3 * ocDelta B.α B.q) ≤ 1 / 2 := by
    apply le_of_lt
    have hh := mul_lt_mul_of_pos_left hsmall hCpos
    convert hh using 1
    field_simp
  have hratio := hs.trans hb
  have hm := (div_le_iff₀ (mul_pos hνpos hP)).mp hratio
  apply (div_le_iff₀ hνpos).mpr
  nlinarith only [hm]

/-- A numerical terminal floor for both quiet margin geometry requirements. -/
def weakQuietGeometryFloor (B : WeakCoefficientBase) (Λ : ℕ) : ℕ :=
  if hΛ : 128 ≤ Λ then Classical.choose (weak_quiet_geometry_threshold B Λ hΛ) else 0

/-- Instantiating the common plan requires only domination of this numerical
floor. In particular no carrier premise is added to the passage statement. -/
theorem weak_quiet_geometry_plan_of_threshold (plan : WeakPassagePlan)
    (hlevel : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) j,
      weakQuietGeometryFloor B A.Λ ≤ plan.levelFloor R j) : WeakQuietGeometryPlanOK plan := by
  intro B A R c
  have h128 := (plan.base_ge B).trans c.base_ge
  have hM : Classical.choose (weak_quiet_geometry_threshold B A.Λ h128) ≤ c.M := by
    have ht := (hlevel R c.j₀).trans c.level_ge
    simpa only [weakQuietGeometryFloor, dite_eq_left h128] using ht
  obtain ⟨hstart, hfit⟩ := Classical.choose_spec (weak_quiet_geometry_threshold B A.Λ h128) c.M hM
  refine ⟨hstart, fun i hi _ => ?_⟩
  have h := hfit (c.D.κ c.M) c.band.1 i hi
  simpa only [OCData.eps, c.q_eq, c.base_eq, c.alpha] using h

/-- The coefficient layer with the pure quiet margin/history geometry discharged. -/
theorem weak_quiet_coefficient_of_parent_jets (plan : WeakPassagePlan)
    (hplan : WeakQuietGeometryPlanOK plan) (hcommon : WeakPassageCommonOK plan)
    (hjets : WeakMiddleHalfJetsStatement plan) :
    WeakQuietCoefficientStatement plan :=
  weak_quiet_coefficient_of_ingredients plan hplan hcommon (weak_middle_half_history plan) hjets

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! **The forcing cost, step 2: the Schur tests of the forcing.**
* `pfc_flux_mass_schur`: the kernel-flux mass bound (`kernelFluxMassSchur`, private
  there), with the gradient energy replaced by an arbitrary nonnegative quantity `X j`: if each
  term of the flux of `A i` has factorial norm at most `√(X j)` times the kernel price, and the
  Schur matrix is bounded by `θ`, then `massNormSq A ≤ (ν θ)² ∑ π_j⁻¹ X_j`.
* `pfc_schur`: the Schur bound `C ε_M^{χ_w}` of the paired kernel matrix of `Gw` at the order
  `K_w`, for an arbitrary sequence of regularizer constants `cc` (the proof of
  `weakPaired_schur`, which fixes `cc` to the regularizer constants of the paired kernel). -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.KernelEnergy
namespace AVRegularity.WeakEntryProofs
open AVRegularity.WeakEntryProofs.Assembly

theorem pfcSchurRootProduct (pii pij z : ℝ) (hpii : 0 < pii) (hpij : 0 < pij) :
    Real.sqrt (pij / pii) * Real.sqrt (pij⁻¹ * z) =
      Real.sqrt (pii⁻¹) * Real.sqrt z := by
  have hratio : (pij / pii) * (pij⁻¹ * z) = pii⁻¹ * z := by
    field_simp [ne_of_gt hpii, ne_of_gt hpij]
  rw [← Real.sqrt_mul (div_nonneg hpij.le hpii.le) (pij⁻¹ * z), hratio,
    Real.sqrt_mul (inv_nonneg.mpr hpii.le) z]

theorem pfcSchurRootScale (pii pij ν s c p n z : ℝ)
    (hpii : 0 < pii) (hpij : 0 < pij) (hν : 0 < ν) (hp : 0 < p) :
    Real.sqrt (pii⁻¹) * s * (c / p) * n * Real.sqrt z =
      ν * (Real.sqrt (pij / pii) * n * (s * c / (ν * p))) *
        Real.sqrt (pij⁻¹ * z) := by
  have hroot := pfcSchurRootProduct pii pij z hpii hpij
  calc
    Real.sqrt (pii⁻¹) * s * (c / p) * n * Real.sqrt z =
        ν * (Real.sqrt (pii⁻¹) * Real.sqrt z) * n * (s * c / (ν * p)) := by
          field_simp [ne_of_gt hν, ne_of_gt hp]
    _ = ν * (Real.sqrt (pij / pii) * Real.sqrt (pij⁻¹ * z)) * n *
        (s * c / (ν * p)) := by rw [← hroot]
    _ = ν * (Real.sqrt (pij / pii) * n * (s * c / (ν * p))) *
        Real.sqrt (pij⁻¹ * z) := by ring

/-- **The kernel-flux mass bound** against an arbitrary energy `X`. -/
theorem pfc_flux_mass_schur
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
    [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]
    {μ : Measure (Vec 2)} (ρ ν θ : ℝ) (hν : 0 < ν) (k D : ℕ)
    (t₀ t₁ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => E i)))
    (C : ∀ i j (α : Γ i j), E j →L[ℝ] G i j α)
    (c : ℕ → ℝ) (r : ∀ i j, Γ i j → ℝ) (hr : ∀ i j α, 0 < r i j α)
    (hc : ∀ (i j : ι) (_α : Γ i j) (m : ℕ), m + 2 ≤ D → 0 ≤ c m)
    (A : ∀ i, JetL2 μ k (PiLp 2 (fun _ : Fin 2 => E i)))
    (X : ι → ℝ) (hX : ∀ j, 0 ≤ X j)
    (T : ∀ i j (_α : Γ i j) (_d : ↥(Finset.Icc 2 D)),
      JetL2 μ k (PiLp 2 (fun _ : Fin 2 => E i)))
    (hA : ∀ i, A i = ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)
    (hTerm : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)),
      Real.sqrt (factorialNormSq ρ (T i j α d)) ≤
        (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
          (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
            Real.sqrt (X j))
    (hschur : SchurBound θ (kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B)) :
    massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => E i)) (K := fun _ => k)
        ρ π A ≤ (ν * θ) ^ 2 * ∑ j : ι, (π j)⁻¹ * X j := by
  classical
  let b : ι → ι → ℝ := kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B
  let x (j : ι) : ℝ := Real.sqrt ((π j)⁻¹ * X j)
  let y (i : ι) : ℝ := Real.sqrt ((π i)⁻¹ * factorialNormSq ρ (A i))
  let σ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) : ℝ :=
    (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal
  let q (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) : ℝ :=
    σ i j α d * c (d.1 - 2) / (ν * r i j α ^ (d.1 - 2))
  have hschur' : SchurBound θ b := by simpa only [b] using hschur
  rcases hschur' with ⟨hrow, hcol⟩
  have hb (i j : ι) : 0 ≤ b i j := by
    change 0 ≤ Real.sqrt (π j / π i) *
      ∑ α : Γ i j, ‖C i j α‖ * ∑ d : ↥(Finset.Icc 2 D), q i j α d
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg
    intro α _
    apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro d _
    have hd := Finset.mem_Icc.1 d.2
    have hs : 0 ≤ σ i j α d := by dsimp [σ]; exact ENNReal.toReal_nonneg
    have hc' : 0 ≤ c (d.1 - 2) := hc i j α (d.1 - 2) (by omega)
    have hden : 0 < ν * r i j α ^ (d.1 - 2) :=
      mul_pos hν (pow_pos (hr i j α) _)
    exact div_nonneg (mul_nonneg hs hc') hden.le
  have hroot (i : ι) :
      Real.sqrt (factorialNormSq ρ (A i)) ≤
        ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
            (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
              Real.sqrt (X j) := by
    calc
      _ = Real.sqrt (factorialNormSq ρ
            (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)) := by rw [hA i]
      _ ≤ ∑ j : ι, Real.sqrt (factorialNormSq ρ
            (∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)) :=
        factorialNorm_root_sum_le ρ (Finset.univ : Finset ι)
          (fun j => ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)
      _ ≤ ∑ j : ι, ∑ α : Γ i j, Real.sqrt (factorialNormSq ρ
            (∑ d : ↥(Finset.Icc 2 D), T i j α d)) := by
        apply Finset.sum_le_sum
        intro j _
        exact factorialNorm_root_sum_le ρ (Finset.univ : Finset (Γ i j))
          (fun α => ∑ d : ↥(Finset.Icc 2 D), T i j α d)
      _ ≤ ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            Real.sqrt (factorialNormSq ρ (T i j α d)) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro α _
        exact factorialNorm_root_sum_le ρ (Finset.univ : Finset (↥(Finset.Icc 2 D)))
          (fun d => T i j α d)
      _ ≤ ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
              (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
                Real.sqrt (X j) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro α _
        apply Finset.sum_le_sum
        intro d _
        exact hTerm i j α d
  have hscale (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      Real.sqrt ((π i)⁻¹) * σ i j α d *
          (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
          Real.sqrt (X j) =
        ν * (Real.sqrt (π j / π i) * ‖C i j α‖ * q i j α d) * x j := by
    dsimp only [x, σ, q]
    exact pfcSchurRootScale (π i) (π j) ν (coefficientSeminorm ρ k t₀ t₁
      (B i j α d)).toReal (c (d.1 - 2)) (r i j α ^ (d.1 - 2))
      ‖C i j α‖ (X j) (hπ i) (hπ j) hν
      (pow_pos (hr i j α) _)
  have hpair (i j : ι) :
      Real.sqrt ((π i)⁻¹) *
          (∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
              (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
                Real.sqrt (X j)) = ν * b i j * x j := by
    calc
      _ = ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            Real.sqrt ((π i)⁻¹) * σ i j α d *
              (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
              Real.sqrt (X j) := by
        simp_rw [Finset.mul_sum]
        dsimp only [σ]
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            ν * (Real.sqrt (π j / π i) * ‖C i j α‖ * q i j α d) * x j := by
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro d _
        exact hscale i j α d
      _ = ν * (Real.sqrt (π j / π i) *
            ∑ α : Γ i j, ‖C i j α‖ * ∑ d : ↥(Finset.Icc 2 D), q i j α d) * x j := by
        calc
          _ = ∑ α : Γ i j, (ν * Real.sqrt (π j / π i) * x j * ‖C i j α‖) *
                ∑ d : ↥(Finset.Icc 2 D), q i j α d := by
            apply Finset.sum_congr rfl
            intro α _
            calc
              _ = ∑ d : ↥(Finset.Icc 2 D),
                    (ν * Real.sqrt (π j / π i) * x j * ‖C i j α‖) * q i j α d := by
                apply Finset.sum_congr rfl
                intro d _
                ring
              _ = _ := by rw [Finset.mul_sum]
          _ = (ν * Real.sqrt (π j / π i) * x j) *
                ∑ α : Γ i j, ‖C i j α‖ * ∑ d : ↥(Finset.Icc 2 D), q i j α d := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro α _
            ring
          _ = _ := by ring
      _ = ν * b i j * x j := by dsimp only [b, kernelSchurMatrix, q, σ]
  have hyBound (i : ι) : 0 ≤ y i ∧ y i ≤ ν * ∑ j : ι, b i j * x j := by
    constructor
    · exact Real.sqrt_nonneg _
    · have hInv : 0 ≤ (π i)⁻¹ := inv_nonneg.mpr (hπ i).le
      have hsplit : y i = Real.sqrt ((π i)⁻¹) * Real.sqrt (factorialNormSq ρ (A i)) := by
        dsimp [y]
        rw [Real.sqrt_mul hInv (factorialNormSq ρ (A i))]
      rw [hsplit]
      calc
        Real.sqrt ((π i)⁻¹) * Real.sqrt (factorialNormSq ρ (A i)) ≤
            Real.sqrt ((π i)⁻¹) *
              ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
                (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
                  (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
                    Real.sqrt (X j) :=
          mul_le_mul_of_nonneg_left (hroot i) (Real.sqrt_nonneg _)
        _ = ∑ j : ι, ν * b i j * x j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          exact hpair i j
        _ = ν * ∑ j : ι, b i j * x j := by
          symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
  have hfinite := AVRegularity.KernelEnergy.finiteRootSchur b x y ν θ hν
    hb hrow hcol hyBound
  have hxSq : (∑ j : ι, x j ^ 2) = ∑ j : ι, (π j)⁻¹ * X j := by
    unfold x
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ j).le) (hX j))]
  have hySq : (∑ i : ι, y i ^ 2) = massNormSq
      (E := fun i => PiLp 2 (fun _ : Fin 2 => E i)) (K := fun _ => k) ρ π A := by
    unfold y massNormSq
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ i).le)
      (factorialNormSq_nonneg ρ (A i)))]
  rw [← hySq]
  calc
    (∑ i : ι, y i ^ 2) ≤ (ν * θ) ^ 2 * ∑ j : ι, x j ^ 2 := hfinite
    _ = (ν * θ) ^ 2 * ∑ j : ι, (π j)⁻¹ * X j := by rw [hxSq]

/-- The price constant of one identity at the order `K_w`, for arbitrary kernel constants. -/
def pfcPriceConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (cc : ℕ → ℝ) : ℝ :=
  (weakKernelPhysicalData A R.sZ R.Kw).C *
    ∑ d ∈ Finset.Icc 2 (1 + A.Jw * A.Nw), max 0 (cc (d - 2))

theorem pfcPriceConst_nonneg {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (cc : ℕ → ℝ) : 0 ≤ pfcPriceConst R cc :=
  mul_nonneg (weakKernelPhysicalData A R.sZ R.Kw).nonneg
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- **The paired kernel matrix of `Gw` at the order `K_w` and the capped radius has both Schur
sums at most `C ε_M^{χ_w}`.** -/
theorem pfc_schur {plan : WeakEntryGluePlan} (hok : WeakEntryPairedPlanOK plan)
    {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
    {x : WeakEntryData plan C} (g : WeakEntryStages x) (law : BirthLaw)
    (hm : law.rootMass = g.rootM)
    (e : ∀ v u, (g.stage x.M).fam.Γ v u ≃ g.Gw.fam.Γ (g.relabel v) (g.relabel u))
    (hB : ∀ v u (γ : (g.stage x.M).fam.Γ v u) d,
      g.Gw.physCoeff (g.relabel v) (g.relabel u) (e v u γ) d = (g.stage x.M).physCoeff v u γ d)
    (a b : ℝ) (cc : ℕ → ℝ) :
    SchurBound (pfcPriceConst R cc * (weakStoredLedgerData A).C *
        x.D.eps x.M ^ weakChi B.α B.q A.η₀)
      (kernelSchurMatrix (ι := CompIn g.Gw.comps) (h := fun v => ScalarH v.1.root)
        (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (x.D.κ x.M)
        (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) R.Kw x.Dm a b
        (cc) (fun _ _ _ => x.D.termRW A.σw x.M)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun v u γ d => g.Gw.physCoeff v u γ d.1)) := by
  obtain ⟨hVs, hSs, -, -⟩ := weakPairedLevelFloor_spec hok x
  have h128 := x.base128
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans h128
  have hζ : IsFastProfile x.D.ζ := by rw [x.profile_eq]; exact B.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.alpha, x.q_eq, x.base_eq, x.profile_eq, x.terminal]; exact x.band
  have hε : 0 < x.D.eps x.M := Construction.Stream.ocEpsilon_pos hΛ1
  have hε' : 0 < x.D.eps (x.M + 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hε1 : x.D.eps x.M ≤ 1 := by
    simpa only [OCData.eps, x.q_eq, x.base_eq] using
      (Scales.epsilon_basic (m := x.M) B.hq.1 h128).2.1
  have hν : 0 < x.D.κ x.M := CycleReference.bandChain_pos hΛ1 hζ hband (by rw [x.terminal])
  set ρ := x.D.termRStar (plan.radius R) x.M with hρdef
  set r := x.D.termRW A.σw x.M with hrdef
  have hcK := weak_entry_radius_spec (plan.radiusBudget R)
  have hρ : 0 ≤ ρ := mul_nonneg hcK.1.le hε.le
  have hρe : ρ ≤ x.D.eps x.M := mul_le_of_le_one_left hε.le hcK.2.1
  have hr : 0 < r := Real.rpow_pos_of_pos hε _
  have hre : r ≤ x.D.eps x.M := by
    change x.D.eps x.M ^ (1 + A.σw) ≤ _
    rw [Real.rpow_add hε, Real.rpow_one]
    exact mul_le_of_le_one_right hε.le (Real.rpow_le_one hε.le hε1 A.σw_pos.le)
  have hhr : x.D.eps (x.M + 1) ≤ r := by
    simpa only [r, OCData.eps, OCData.termRW, x.q_eq, x.base_eq] using
      (weakStoredLedgerData A).price h128 x.M hSs
  set G := g.stage x.M
  set V := weakKernelPhysicalData A R.sZ R.Kw
  set Cp := pfcPriceConst R cc
  have hC : 0 ≤ Cp := pfcPriceConst_nonneg R cc
  have hprod := V.bound h128 x.D (by rw [x.terminal]; exact hVs) x.alpha x.q_eq x.base_eq
    x.profile_eq x.streams hband x.Dm x.order_ge x.j₀ g.stage x.P x.M R.sX 0 A.η₀ r x.terminal
    g.construction x.M le_rfl (by have := A.Jw_pos; omega)
  have horder := EntryWeakProofs.weakConstruction_output_maxOrder_bound x.P
    ⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, x.M + A.Jw⟩ x.M A.Jw r 0 g.stage g.construction x.M le_rfl
    (by have := A.Jw_pos; omega)
  have htotal := (weakStoredLedgerData A).total h128 x.M hSs x.D x.alpha x.q_eq x.base_eq
    x.terminal x.band x.Dm x.j₀ x.P R.sX R.sZ g.stage g.construction
  have hprice (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      (∑ d : ↥(Finset.Icc 2 x.Dm),
        (coefficientSeminorm ρ R.Kw a b (G.physCoeff v u γ d.1)).toReal *
          cc (d.1 - 2) / (x.D.κ x.M * r ^ (d.1 - 2))) ≤
        Cp * (G.fam.identity v u γ).record.size := by
    apply weak_kernel_identity_price (fun d => G.physCoeff v u γ d) (x.D.κ x.M) V.C
      (G.fam.identity v u γ).record.size (x.D.eps (x.M + 1)) (x.D.eps x.M) r ρ
      (cc) (G.fam.identity v u γ).maxOrder (1 + A.Jw * A.Nw) x.Dm R.Kw a b
      hν V.nonneg (G.fam.identity v u γ).record.size_nonneg hε hε'.le hr hhr hre hρ hρe
      (horder v u γ)
    · intro d hd
      funext t y
      exact CycleJointProofs.constituentPhysical_zero_above_max G.fam
        (x.D.kap G.level) (x.D.eps G.level) (x.D.eps (G.level - 1)) G.actual v u γ d hd t y
    · intro d hd hdn
      exact hprod v u γ d R.Kw hd hdn le_rfl a b
  have hschur := weakRelabel_schur_of_stored A.Nw A.Jw A.η₀ G g.Gw g.relabel Cp hC
    (kernelSchurMatrix (ι := CompIn g.Gw.comps) (h := fun v => ScalarH v.1.root)
      (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (x.D.κ x.M) ρ (g.Gw.mass law) R.Kw
      x.Dm a b (cc) (fun _ _ _ => r)
      (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
      (fun v u γ d => g.Gw.physCoeff v u γ d.1))
  have hpoint (v u : CompIn G.comps) :
      kernelSchurMatrix (ι := CompIn g.Gw.comps) (h := fun v => ScalarH v.1.root)
        (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (x.D.κ x.M) ρ (g.Gw.mass law)
        R.Kw x.Dm a b (cc) (fun _ _ _ => r)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun v u γ d => g.Gw.physCoeff v u γ d.1) (g.relabel v) (g.relabel u) ≤
        Cp * Real.sqrt (weakMass x.D A.Nw A.Jw A.η₀ u.1 / weakMass x.D A.Nw A.Jw A.η₀ v.1) *
          ∑ γ : G.fam.Γ v u, (G.fam.identity v u γ).record.size := by
    unfold kernelSchurMatrix
    rw [weakEncoding_mass A.Nw A.Jw A.η₀ _ _ G g.Gw g.relabel g.encoding law hm u,
      weakEncoding_mass A.Nw A.Jw A.η₀ _ _ G g.Gw g.relabel g.encoding law hm v,
      ← (e v u).sum_comp]
    simp only [ContinuousLinearMap.norm_id, one_mul, hB]
    calc
      _ ≤ Real.sqrt _ * ∑ γ : G.fam.Γ v u, Cp * (G.fam.identity v u γ).record.size :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ _ => hprice v u γ) (Real.sqrt_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hs := hschur hpoint
  have hfinal : Cp * weakStoredTotal G A.Nw A.Jw A.η₀ ≤
      Cp * (weakStoredLedgerData A).C * x.D.eps x.M ^ weakChi B.α B.q A.η₀ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left htotal hC
  exact ⟨fun v => (hs.1 v).trans hfinal, fun u => (hs.2 u).trans hfinal⟩

end AVRegularity.WeakEntryProofs
end
end
end
