-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseEnergy.LiftedRun
import AVRegularity.Proofs.WeakGen.Reduction.PassageEnergy
import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh
import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.EntryWeakAssembly.Assembly.WeakReadoutBound
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import Mathlib.Algebra.Order.Chebyshev

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The passage energy at general masses: proof**.

`weakFrontier_row_recursion` is the row recursion of `weakPassage_core_row_recursion` at an
arbitrary positive mass function `μ` with stored total at most `T₀`; `weakGeneralPassageEnergy`
unrolls it with `frontier_sum_unrolled_le`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  Construction.Preservation.Ledger CycleJointProofs.PathReduction CoupledEnergy.Variational

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The stored edge weight at the masses `μ`. -/
def frontierEdgeWeight (S : WeakRawSetting R) (L : ℕ) (μ : CompIn (S.stage L).comps → ℝ)
    (e : LedgerEdge (S.stage L)) : ℝ :=
  Real.sqrt (μ e.2.1 / μ e.1) * ((S.stage L).fam.identity e.1 e.2.1 e.2.2).record.size

theorem frontierEdgeWeight_nonneg (S : WeakRawSetting R) (L : ℕ)
    (μ : CompIn (S.stage L).comps → ℝ) (e : LedgerEdge (S.stage L)) :
    0 ≤ frontierEdgeWeight S L μ e :=
  mul_nonneg (Real.sqrt_nonneg _) ((S.stage L).fam.identity e.1 e.2.1 e.2.2).record.size_nonneg

/-- The row sums of the stored weights at the masses `μ` are at most the total. -/
theorem frontier_row_le (S : WeakRawSetting R) (L : ℕ) (μ : CompIn (S.stage L).comps → ℝ)
    (T₀ : ℝ) (hT : ∑ e : LedgerEdge (S.stage L), frontierEdgeWeight S L μ e ≤ T₀)
    (v : CompIn (S.stage L).comps) :
    ∑ u, ∑ γ : (S.stage L).fam.Γ v u, frontierEdgeWeight S L μ ⟨v, u, γ⟩ ≤ T₀ := by
  classical
  refine le_trans ?_ hT
  have hrow : (∑ u, ∑ γ : (S.stage L).fam.Γ v u, frontierEdgeWeight S L μ ⟨v, u, γ⟩) ≤
      ∑ v', ∑ u, ∑ γ : (S.stage L).fam.Γ v' u, frontierEdgeWeight S L μ ⟨v', u, γ⟩ :=
    Finset.single_le_sum (f := fun v' => ∑ u, ∑ γ : (S.stage L).fam.Γ v' u,
      frontierEdgeWeight S L μ ⟨v', u, γ⟩)
      (fun v' _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun γ _ =>
        frontierEdgeWeight_nonneg S L μ _) (Finset.mem_univ v)
  refine hrow.trans (le_of_eq ?_)
  simp only [LedgerEdge, Fintype.sum_sigma]

/-- The edge constant of a row against the stored weights at the masses `μ`. -/
theorem frontier_edge_le_stored (S : WeakRawSetting R)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (L : ℕ) (hL : S.M ≤ L) (hLJ : L < S.M + A.Jw)
    (a b rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (hsmooth : ∀ v u (γ : (S.stage L).fam.Γ v u) d, 2 ≤ d → ∀ k ≤ weakEntryKmax R, ∀ t,
      ContDiff ℝ (k : ℕ) ((S.stage L).physCoeff v u γ d t))
    (μ : CompIn (S.stage L).comps → ℝ) (hμ : ∀ v, 0 < μ v) (v u : CompIn (S.stage L).comps) :
    ∑ d : admissibleOrders (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1)
        (1 + A.Jw * A.Nw) v u,
      (coefficientSeminorm (rad * S.D.eps L) (weakReductionReserve R m v.1) a b
        (fun t y => ∑ γ : (S.stage L).fam.Γ v u, (S.stage L).physCoeff v u γ d.1 t y)).toReal *
        derivativeReserveFactor (rad * S.D.eps L) (weakReductionReserve R m v.1) (d.1 - 2) ≤
      S.D.κ S.M * weakRawEdgeConst rad R * Real.sqrt (μ v / μ u) *
        ∑ γ : (S.stage L).fam.Γ v u, frontierEdgeWeight S L μ ⟨v, u, γ⟩ := by
  refine (weakRaw_edge_le S hfloor L hL hLJ a b rad hrad hrad1 m hm hsmooth v u).trans
    (le_of_eq ?_)
  have hs : Real.sqrt (μ v / μ u) * Real.sqrt (μ u / μ v) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg (hμ v).le (hμ u).le), div_mul_div_comm,
      mul_comm (μ v), div_self (mul_pos (hμ u) (hμ v)).ne', Real.sqrt_one]
  rw [mul_assoc (S.D.κ S.M * weakRawEdgeConst rad R)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  unfold frontierEdgeWeight
  rw [← mul_assoc, hs, one_mul]

/-- **The recursion of the rows of a passage at general masses.** -/
theorem weakFrontier_row_recursion (S : WeakRawSetting R)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M)
    (L : ℕ) (hL : S.M ≤ L) (hLJ : L < S.M + A.Jw) (a b rad : ℝ) (hab : a ≤ b)
    (hrad : 0 < rad) (hrad1 : rad ≤ 1) (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (hsmooth : ∀ v u (γ : (S.stage L).fam.Γ v u) d, 2 ≤ d → ∀ k ≤ weakEntryKmax R, ∀ t,
      ContDiff ℝ (k : ℕ) ((S.stage L).physCoeff v u γ d t))
    (μ : CompIn (S.stage L).comps → ℝ) (hμ : ∀ v, 0 < μ v) (T₀ : ℝ)
    (hT : ∑ e : LedgerEdge (S.stage L), frontierEdgeWeight S L μ e ≤ T₀)
    {Ac : ∀ v u, (d : admissibleOrders
        (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u) →
        ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => ScalarH u.1.root) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)}
    (hA : ∀ v u d, Ac v u d = fun t y => ∑ γ : (S.stage L).fam.Γ v u,
      (S.stage L).physCoeff v u γ d.1 t y)
    (Rd : TorusCoefficientData (rad * S.D.eps L)
      (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) a b Ac)
    (hd : TorusDriftData (S.D.κ S.M) (rad * S.D.eps L) a b (streamVel (S.D.Φ L))
      (weakEntryKmax R))
    (hA_meas : ∀ v u d, Measurable fun p : Set.Icc a b × Vec 2 => Ac v u d p.1 p.2)
    {f : ∀ v : CompIn (S.stage L).comps, TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)}
    {u : ∀ v : CompIn (S.stage L).comps, ℝ →
      TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)}
    {w : ∀ v : CompIn (S.stage L).comps, ℝ →
      TorusHk (weakReductionReserve R m v.1 + 1) (ScalarH v.1.root)}
    (hs : IsCoupledWeakSolutionTorus (S.D.κ S.M) a b (streamVel (S.D.Φ L)) (1 + A.Jw * A.Nw)
      (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) Ac f
      (fun _ _ => 0) (fun _ _ => 0) u w)
    (v : CompIn (S.stage L).comps) :
    rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f (rowForcingFlux Rd (fun _ _ => 0) w)
        (fun _ _ => 0) v ≤
      2 * factorialNormSq (rad * S.D.eps L) (f v).val +
        32 * T₀ * weakRawEdgeConst rad R ^ 2 * ∑ j, (∑ γ : (S.stage L).fam.Γ v j,
          frontierEdgeWeight S L μ ⟨v, j, γ⟩) * (μ v / μ j) *
          rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f (rowForcingFlux Rd (fun _ _ => 0) w)
            (fun _ _ => 0) j := by
  have hK : ∀ v : CompIn (S.stage L).comps, weakReductionReserve R m v.1 ≤ weakEntryKmax R :=
    fun v => weakReductionReserve_le_kmax R hm v.1
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have hF : ∀ v : CompIn (S.stage L).comps, MemLp (fun _ : ℝ => (0 : TorusHk
      (weakReductionReserve R m v.1) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))) 2
      (volume.restrict (Set.Icc a b)) := fun v => memLp_const _
  have hg : ∀ v : CompIn (S.stage L).comps, Integrable (fun _ : ℝ => (0 : TorusHk
      (weakReductionReserve R m v.1) (ScalarH v.1.root))) (volume.restrict (Set.Icc a b)) :=
    fun v => integrable_const _
  have hrec := coupledRowData_recursion (F := fun _ _ => 0) (g := fun _ _ => 0) Rd hd
    S.kappa_pos (by omega : 2 ≤ 1 + A.Jw * A.Nw) hK hab hA_meas hF hg hs
    μ hμ (weakRawEdgeConst rad R) T₀
    (fun v u => ∑ γ : (S.stage L).fam.Γ v u,
      frontierEdgeWeight S L μ ⟨v, u, γ⟩)
    (fun v u => Finset.sum_nonneg fun γ _ => frontierEdgeWeight_nonneg S L μ _)
    (fun v => frontier_row_le S L μ T₀ hT v)
    (fun v u => by
      simp only [hA]
      exact frontier_edge_le_stored S hfloor L hL hLJ a b rad hrad hrad1 m hm hsmooth μ hμ v u) v
  have h0 := rowData_phi_zero (S.D.κ S.M) (rad * S.D.eps L) a b (f v)
  rw [h0] at hrec
  exact hrec
end

/-! **The passage energy at general masses** (`weakGeneralPassageEnergy`). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  Construction.Preservation.Ledger CycleJointProofs.PathReduction CoupledEnergy.Variational

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

theorem weakGeneralPassageEnergy (R : WeakPassageRequest A) (T₀ : ℝ) :
    WeakGeneralPassageEnergy R T₀ := by
  intro S hfloor _hstored L hL hLJ a b rad hab hrad hrad1 m hm hsmooth μ hμ hT Ac hA Rd hd hA_meas f u w hs t ht
  classical
  have hπ := hμ
  have hT' : ∑ e : LedgerEdge (S.stage L), frontierEdgeWeight S L μ e ≤ T₀ := hT
  have hX0 : ∀ v : CompIn (S.stage L).comps, 0 ≤ rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f
      (rowForcingFlux Rd (fun _ _ => 0) w) (fun _ _ => 0) v :=
    fun v => rowDataBound_nonneg _ _ _ _ S.kappa_pos _ _ _ v
  have hrec := weakFrontier_row_recursion S hfloor L hL hLJ a b rad hab hrad hrad1 m hm
    hsmooth μ hμ T₀ hT' hA Rd hd hA_meas hs
  have hsum := frontier_sum_unrolled_le (S.stage L) (frontierEdgeWeight S L μ)
    (frontierEdgeWeight_nonneg S L μ) T₀ hT' μ
    (fun v => rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f
      (rowForcingFlux Rd (fun _ _ => 0) w) (fun _ _ => 0) v)
    (fun v => 2 * factorialNormSq (rad * S.D.eps L) (f v).val) hπ hX0
    (fun v => mul_nonneg (by norm_num) (factorialNormSq_nonneg _ _))
    (32 * T₀ * weakRawEdgeConst rad R ^ 2) (by
      have := weakRawEdgeConst_nonneg hrad.le R
      have hT0 : 0 ≤ T₀ := le_trans (Finset.sum_nonneg fun e _ =>
        frontierEdgeWeight_nonneg S L μ e) hT'
      positivity)
    hrec (A.Jw * A.Rw)
    ⟨fun π' => absurd (weakConstruction_path_length_bound S.P _ S.M A.Jw 0 _ S.stage
      S.construction L hL hLJ.le _ π') (by simp)⟩
  have hgi : ∀ v : CompIn (S.stage L).comps,
      Integrable (fun s => gradFactorialNormSq (rad * S.D.eps L) (w v s).val)
        (volume.restrict (Set.Icc a b)) := fun v =>
    CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hs.2.1 v)
  have hint : ∫ s in Set.Icc a b, ∑ v : CompIn (S.stage L).comps,
        (μ v)⁻¹ * gradFactorialNormSq (rad * S.D.eps L) (w v s).val =
      ∑ v : CompIn (S.stage L).comps, (μ v)⁻¹ *
        ∫ s in Set.Icc a b, gradFactorialNormSq (rad * S.D.eps L) (w v s).val := by
    rw [integral_finsetSum _ fun v _ => (hgi v).const_mul _]
    exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _
  have hlhs : ∑ v, (μ v)⁻¹ *
        factorialNormSq (rad * S.D.eps L) (u v t).val +
      S.D.κ S.M / 2 * ∫ s in Set.Icc a b, ∑ v, (μ v)⁻¹ *
        gradFactorialNormSq (rad * S.D.eps L) (w v s).val ≤
      ∑ v : CompIn (S.stage L).comps, rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f
        (rowForcingFlux Rd (fun _ _ => 0) w) (fun _ _ => 0) v /
          μ v := by
    rw [hint, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have := weakPassage_core_row_energy S L a b rad m hm Rd hd hA_meas hs v t ht
    calc _ = (μ v)⁻¹ * (factorialNormSq (rad * S.D.eps L) (u v t).val +
          S.D.κ S.M / 2 * ∫ s in Set.Icc a b,
            gradFactorialNormSq (rad * S.D.eps L) (w v s).val) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_nonneg.2 (hπ v).le)
      _ = _ := (div_eq_inv_mul _ _).symm
  have hq : ∑ v : CompIn (S.stage L).comps, 2 * factorialNormSq (rad * S.D.eps L) (f v).val /
      μ v = 2 * ∑ v : CompIn (S.stage L).comps,
        (μ v)⁻¹ * factorialNormSq (rad * S.D.eps L) (f v).val := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  refine hlhs.trans (hsum.trans (le_of_eq ?_))
  rw [hq]
  unfold weakFrontierPassageConst
  have hg : ∑ n ∈ Finset.range (A.Jw * A.Rw + 1), (32 * T₀ * weakRawEdgeConst rad R ^ 2 * T₀) ^ n =
      ∑ n ∈ Finset.range (A.Jw * A.Rw + 1), (32 * T₀ ^ 2 * weakRawEdgeConst rad R ^ 2) ^ n :=
    Finset.sum_congr rfl fun n _ => by ring_nf
  rw [hg]
  ring
end

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Coarse readout energy: the energy of passage `i` in the passage world.**

`weakCoarse_terminal_drift`: the drift data of the stream velocity at the terminal level `M`
(radius `ρ ε_M`, diffusivity `κ_M`) of a passage instance, from the radius cap `1/2048` and the
paired level floor; the restatement over a passage instance of `weakPaired_drift` (entry) via
`stream_torusDriftData_strain`. `weakCoarse_passage_drift`: the drift data at every level `L ≥ M`
(Péclet smallness above `M`, `weakComparison_rowDrift`).

`weakCoarse_passage_energy`: the corollary, over a passage instance and any raw clock, of the
core `weakPassage_core_energy`: for the families solving passage `i`, at the radius
`plan.radius R · ε_{i-1}`,
```
‖U_{i-1}(t)‖²_{ρ,π} + (κ_M/2) ∫_{[t_i, a+T₀]} ‖∇W_{i-1}‖²_{ρ,π}
  ≤ C_pass ‖trace of U_i at t_i‖²_{ρ,π},       C_pass = weakRawPassageConst (plan.radius R) R.
```
The degenerate cases are included: `i = M + 1` is the terminal level (the paired drift); `m = 0`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  CycleJointProofs.PathReduction CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Reduction

/-- **The floors of the coarse readout energy**: the radius cap `1/2048` and the level floors of
the passage energy (coefficients at `K_max`, Péclet smallness, stored ledger) and of the terminal
drift (the paired level floor). -/
def WeakCoarseFloorsOK (plan : WeakPassagePlan) : Prop :=
  (∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    plan.radius R ≤ 1 / 2048) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (j₀ : ℕ),
    weakEntryPassageCoeffFloor R ≤ plan.levelFloor R j₀ ∧
      weakComparisonDriftFloor A ≤ plan.levelFloor R j₀ ∧
      weakQuietStoredFloor A ≤ plan.levelFloor R j₀ ∧
      weakPairedLevelFloor R ≤ plan.levelFloor R j₀

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The drift data of the terminal level `M`** at the radius `ρ ε_M`, from the radius cap and the
paired level floor. -/
theorem weakCoarse_terminal_drift (c : WeakPassageInstance plan R)
    (hrad : plan.radius R ≤ 1 / 2048) (hfl : weakPairedLevelFloor R ≤ c.M) (hM1 : 1 ≤ c.M)
    (t₀ t₁ : ℝ) (Kmax : ℕ) :
    TorusDriftData (c.D.κ c.M) (plan.radius R * c.D.eps c.M) t₀ t₁ (streamVel (c.D.Φ c.M))
      Kmax := by
  have hΛ : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have heps : c.D.eps c.M = ocEpsilon B.q A.Λ c.M := by
    simp only [OCData.eps, c.q_eq, c.base_eq]
  have hε : 0 < ocEpsilon B.q A.Λ c.M :=
    Construction.Stream.ocEpsilon_pos ((by norm_num : 1 ≤ 128).trans hΛ)
  have hrpos := plan.radius_pos R
  have hγ : ocEpsilon B.q A.Λ c.M ^ ocGamma B.α B.q ≤
      256 / (Construction.Preservation.Buffer.actualDriftJetConstant + 1) := by
    unfold weakPairedLevelFloor at hfl
    rw [dite_eq_left hΛ] at hfl
    exact Classical.choose_spec (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1 hΛ
      (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).1
      (c := 256 / (Construction.Preservation.Buffer.actualDriftJetConstant + 1))
      (by have := Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
          positivity)) c.M ((le_max_right _ _).trans ((le_max_right _ _).trans hfl))
  rw [heps]
  refine stream_torusDriftData_strain B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ A.Λ hΛ
    c.D.Φ c.streams c.M hM1 t₀ t₁ Kmax _ ?_ ?_
  · rw [show 1024 * (plan.radius R * ocEpsilon B.q A.Λ c.M) / ocEpsilon B.q A.Λ c.M =
      1024 * plan.radius R by field_simp]
    linarith
  · exact weakPaired_strain_arith Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
      hrpos.le hrad hε c.band.1.1 hγ

/-- **The drift data of the passage at the level `L ≥ M`.** -/
theorem weakCoarse_passage_drift (hok : WeakCoarseFloorsOK plan) (c : WeakPassageInstance plan R)
    (hM1 : 1 ≤ c.M) (L : ℕ) (hL : c.M ≤ L) (t₀ t₁ : ℝ) (Kmax : ℕ) :
    TorusDriftData (c.D.κ c.M) (plan.radius R * c.D.eps L) t₀ t₁ (streamVel (c.D.Φ L)) Kmax := by
  obtain ⟨hr, hfl⟩ := hok
  obtain ⟨-, hdf, -, hpf⟩ := hfl R c.j₀
  rcases hL.eq_or_lt with h | h
  · subst h
    exact weakCoarse_terminal_drift c (hr R) (hpf.trans c.level_ge) hM1 t₀ t₁ Kmax
  · exact weakComparison_rowDrift c (hdf.trans c.level_ge) (hr R) L h t₀ t₁ Kmax

/-- **The energy of one passage over raw data** (`C_pass = weakRawPassageConst`), with the
drift data as a hypothesis. -/
theorem weakCoarse_raw_energy (S : WeakRawSetting R) (hreg : S.CoeffRegular)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (hstored : weakQuietStoredFloor A ≤ S.M)
    (ρ : ℝ) (hrpos : 0 < ρ) (hrad1 : ρ ≤ 1) (a b : ℝ)
    (hdrift : ∀ L, S.M ≤ L → TorusDriftData (S.D.κ S.M) (ρ * S.D.eps L) a b
      (streamVel (S.D.Φ L)) (weakEntryKmax R))
    (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (Uhi : ∀ i, WeakStageFamily S m i) (Whi : ∀ i, WeakStageLift S m i) (i : ℕ)
    (hMi : S.M < i) (hi : i ≤ S.M + A.Jw) (hab : a ≤ b)
    (hs : IsCoupledWeakSolutionTorus (S.D.κ S.M) a b (streamVel (S.D.Φ (i - 1)))
      (1 + A.Jw * A.Nw)
      (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (weakStageCoeff S m (i - 1)) (weakStageTrace S m i (Uhi i) a)
      (fun _ _ => 0) (fun _ _ => 0) (Uhi (i - 1)) (Whi (i - 1)))
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ENNReal.ofReal (massNormSq (ρ * S.D.eps (i - 1))
        (fun v : CompIn (S.stage (i - 1)).comps => weakMass S.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (Uhi (i - 1) v t).val)) +
      ENNReal.ofReal (S.D.κ S.M / 2) *
        ∫⁻ τ in Set.Icc a b,
          ENNReal.ofReal (massGradNormSq (ρ * S.D.eps (i - 1))
            (fun v : CompIn (S.stage (i - 1)).comps => weakMass S.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Whi (i - 1) v τ).val)) ≤
    ENNReal.ofReal (weakRawPassageConst ρ R *
      massNormSq (ρ * S.D.eps (i - 1))
        (fun v : CompIn (S.stage (i - 1)).comps => weakMass S.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (weakStageTrace S m i (Uhi i) a v).val)) := by
  classical
  have hL : S.M ≤ i - 1 := by omega
  have hLJ : i - 1 < S.M + A.Jw := by omega
  have hΛ' : 128 ≤ S.D.Λ := by rw [S.base_eq]; exact S.base128
  have hq' : 1 < S.D.q := by rw [S.q_eq]; exact B.hq.1
  have hεL : 0 < S.D.eps (i - 1) := S.eps_pos _
  have hρpos : 0 < ρ * S.D.eps (i - 1) := mul_pos hrpos hεL
  have hρe : ρ * S.D.eps (i - 1) ≤ S.D.eps (i - 1 - 1) :=
    (mul_le_of_le_one_left hεL.le hrad1).trans
      (EntryScales.epsilon_antitone hq' hΛ' (Nat.sub_le _ _))
  have hgate := fun v u d => weakStageCoeff_gate S hreg m (i - 1) hL hLJ a b _ hρpos hρe v u d
  have Rd : TorusCoefficientData (ρ * S.D.eps (i - 1))
      (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) a b (weakStageCoeff S m (i - 1)) :=
    { radius_pos := hρpos
      finite := fun v u d => (hgate v u d).2.2.2
      smooth := fun t ht v u d => (hgate v u d).2.1 t ht
      periodic := fun t ht v u d => (hgate v u d).2.2.1 t ht }
  have hcore := weakPassage_core_energy S hfloor hstored (i - 1) hL hLJ a b ρ hab hrpos hrad1 m hm
    (fun v u γ d hd' k _ t' => (hreg (i - 1) hL hLJ v u γ k d 0 0).2.1 t')
    (fun v u d => rfl) Rd (hdrift (i - 1) hL) (fun v u d => (hgate v u d).1) hs t ht
  have hgi : ∀ v : CompIn (S.stage (i - 1)).comps,
      Integrable (fun τ => gradFactorialNormSq (ρ * S.D.eps (i - 1))
        (Whi (i - 1) v τ).val) (volume.restrict (Set.Icc a b)) := fun v =>
    CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hs.2.1 v)
  have hπ := fun v : CompIn (S.stage (i - 1)).comps => S.mass_pos v.1
  simp only [massNormSq, massGradNormSq]
  exact ofReal_energy_le (by have := S.kappa_pos; positivity)
    (integrable_finsetSum _ fun v _ => (hgi v).const_mul _)
    (fun τ => Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _))
    (Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (factorialNormSq_nonneg _ _)) hcore

/-- **The energy of one passage, in the passage world.** -/
theorem weakCoarse_passage_energy (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseFloorsOK plan) (c : WeakPassageInstance plan R)
    (K : WeakRawClock (weakPassageRawSetting c)) (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) m i) (i : ℕ)
    (hMi : c.M < i) (hi : i ≤ c.M + A.Jw)
    (hpass : WeakStagePassage (weakPassageRawSetting c) K m Uhi Whi i)
    (t : ℝ) (ht : t ∈ Set.Icc (K.tq i) (K.a + A.T₀)) :
    ENNReal.ofReal (massNormSq (plan.radius R * c.D.eps (i - 1))
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (Uhi (i - 1) v t).val)) +
      ENNReal.ofReal (c.D.κ c.M / 2) *
        ∫⁻ τ in Set.Icc (K.tq i) (K.a + A.T₀),
          ENNReal.ofReal (massGradNormSq (plan.radius R * c.D.eps (i - 1))
            (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Whi (i - 1) v τ).val)) ≤
    ENNReal.ofReal (weakRawPassageConst (plan.radius R) R *
      massNormSq (plan.radius R * c.D.eps (i - 1))
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (K.tq i) v).val)) := by
  have hok' := hok
  obtain ⟨hrad2048, hfl⟩ := hok
  obtain ⟨hcf, hdf, hsf, hpf⟩ := hfl R c.j₀
  have hlevel := c.level_ge
  have hL : c.M ≤ i - 1 := by omega
  have hLJ : i - 1 < c.M + A.Jw := by omega
  have hlev : ((weakPassageRawSetting c).stage (i - 1)).level = i - 1 :=
    (weakPassageRawSetting c).level_eq (i - 1) hL hLJ.le
  have hkap : (weakPassageRawSetting c).D.kap ((weakPassageRawSetting c).stage (i - 1)).level =
      (weakPassageRawSetting c).D.κ (weakPassageRawSetting c).M := by
    rw [hlev]; exact (weakPassageRawSetting c).kap_eq _ hL
  have hs := hpass
  unfold WeakStagePassage at hs
  rw [hkap, hlev] at hs
  exact weakCoarse_raw_energy (weakPassageRawSetting c) (weakPassage_coeffRegular hcommon c)
    (hcf.trans hlevel) (hsf.trans hlevel) (plan.radius R) (plan.radius_pos R)
    ((hrad2048 R).trans (by norm_num)) (K.tq i) (K.a + A.T₀)
    (fun L hL' => weakCoarse_passage_drift hok' c (by have := weakPassage_two_le_M hcommon c; omega)
      L hL' _ _ _) m hm Uhi Whi i hMi hi (K.tq_le i hMi hi) hs t ht
end

/-! **The raw frontier estimate, the passage energy at general masses over a raw setting**.

`weakFrontier_raw_energy` is `weakCoarse_raw_energy` with the general-mass
passage energy `weakGeneralPassageEnergy` in place of the core energy, in real form. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  CycleJointProofs.PathReduction CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Reduction
  Construction.Preservation.Ledger

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- **The energy of one passage at general masses with stored total `T₀`**, in real form. -/
theorem weakFrontier_raw_energy (S : WeakRawSetting R) (hreg : S.CoeffRegular)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (hstored : weakQuietStoredFloor A ≤ S.M)
    (ρ : ℝ) (hrpos : 0 < ρ) (hrad1 : ρ ≤ 1) (a b : ℝ)
    (hdrift : ∀ L, S.M ≤ L → TorusDriftData (S.D.κ S.M) (ρ * S.D.eps L) a b
      (streamVel (S.D.Φ L)) (weakEntryKmax R))
    (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (Uhi : ∀ i, WeakStageFamily S m i) (Whi : ∀ i, WeakStageLift S m i) (i : ℕ)
    (hMi : S.M < i) (hi : i ≤ S.M + A.Jw) (hab : a ≤ b)
    (hs : IsCoupledWeakSolutionTorus (S.D.κ S.M) a b (streamVel (S.D.Φ (i - 1)))
      (1 + A.Jw * A.Nw)
      (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (weakStageCoeff S m (i - 1)) (weakStageTrace S m i (Uhi i) a)
      (fun _ _ => 0) (fun _ _ => 0) (Uhi (i - 1)) (Whi (i - 1)))
    (T₀ : ℝ) (μ : CompIn (S.stage (i - 1)).comps → ℝ) (hμ : ∀ v, 0 < μ v)
    (hT : ∑ e : LedgerEdge (S.stage (i - 1)), Real.sqrt (μ e.2.1 / μ e.1) *
      ((S.stage (i - 1)).fam.identity e.1 e.2.1 e.2.2).record.size ≤ T₀)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∑ v, (μ v)⁻¹ * factorialNormSq (ρ * S.D.eps (i - 1)) (Uhi (i - 1) v t).val +
      S.D.κ S.M / 2 * ∫ s in Set.Icc a b, ∑ v, (μ v)⁻¹ *
        gradFactorialNormSq (ρ * S.D.eps (i - 1)) (Whi (i - 1) v s).val ≤
      weakFrontierPassageConst T₀ ρ R * ∑ v, (μ v)⁻¹ *
        factorialNormSq (ρ * S.D.eps (i - 1)) (weakStageTrace S m i (Uhi i) a v).val := by
  classical
  have hL : S.M ≤ i - 1 := by omega
  have hLJ : i - 1 < S.M + A.Jw := by omega
  have hΛ' : 128 ≤ S.D.Λ := by rw [S.base_eq]; exact S.base128
  have hq' : 1 < S.D.q := by rw [S.q_eq]; exact B.hq.1
  have hεL : 0 < S.D.eps (i - 1) := S.eps_pos _
  have hρpos : 0 < ρ * S.D.eps (i - 1) := mul_pos hrpos hεL
  have hρe : ρ * S.D.eps (i - 1) ≤ S.D.eps (i - 1 - 1) :=
    (mul_le_of_le_one_left hεL.le hrad1).trans
      (EntryScales.epsilon_antitone hq' hΛ' (Nat.sub_le _ _))
  have hgate := fun v u d => weakStageCoeff_gate S hreg m (i - 1) hL hLJ a b _ hρpos hρe v u d
  have Rd : TorusCoefficientData (ρ * S.D.eps (i - 1))
      (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) a b (weakStageCoeff S m (i - 1)) :=
    { radius_pos := hρpos
      finite := fun v u d => (hgate v u d).2.2.2
      smooth := fun t ht v u d => (hgate v u d).2.1 t ht
      periodic := fun t ht v u d => (hgate v u d).2.2.1 t ht }
  exact weakGeneralPassageEnergy R T₀ S hfloor hstored (i - 1) hL hLJ a b ρ hab hrpos hrad1 m hm
    (fun v u γ d hd' k _ t' => (hreg (i - 1) hL hLJ v u γ k d 0 0).2.1 t') μ hμ hT
    (fun v u d => rfl) Rd (hdrift (i - 1) hL) (fun v u d => (hgate v u d).1) hs t ht
end

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Coarse readout energy: the energy at a high reserve** (`weakCoarse_high_energy_at`).

The higher order of the reduction on the clock with root time `t_{M+J_w+1}` gives the families; the
energy of passage `i` is `weakCoarse_passage_energy`; the trace at `t_i` is the high-reserve quiet
trace (`weak_passage_quiet_trace_high`) on the joint plan, applied to the lifted run
(`weakCoarse_lifted_run`). The plan condition is floors and the radius cap only. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- The seed of the joint quiet plan. -/
def weakCoarseQuietSeed : WeakPassagePlan :=
  weakQuietJointSeed weakQuietBasePlan weakQuietBasePrices

/-- The joint quiet plan. -/
def weakCoarseQuietPlan : WeakPassagePlan := weakQuietCoefficientPlan weakCoarseQuietSeed

/-- **The plan condition of the coarse readout energy**: the floors of the passage energy and the
radius cap, and the floors of the plan dominate those of the joint quiet plan at the lifted
requests. -/
def WeakCoarsePlanOK (plan : WeakPassagePlan) : Prop :=
  WeakCoarseFloorsOK plan ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (m : ℕ),
    m ≤ weakEntryMmax R →
      (weakQuietCoefficientPlan weakCoarseQuietSeed).baseFloor B ≤ plan.baseFloor B ∧
      (weakQuietCoefficientPlan weakCoarseQuietSeed).momentFloor A ≤ plan.momentFloor A ∧
      (∀ j, (weakQuietCoefficientPlan weakCoarseQuietSeed).levelFloor (weakEntryLiftRequest R m) j ≤
        plan.levelFloor R j) ∧
      plan.radius R ≤ (weakQuietCoefficientPlan weakCoarseQuietSeed).radius
        (weakEntryLiftRequest R m)

/-- The order-zero values of `Uhi i` are those of `r.Ur i` on `[t_{i+1}, a + T₀]`. -/
theorem weakCoarse_zero_values {plan : WeakPassagePlan}
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (m : ℕ)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (hvr : ∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
        ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
          r.Ur (c.M + A.Jw) v t)
    (hval : ∀ i, c.M < i → i ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (i - 1)).comps,
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
          r.Ur (i - 1) v t)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v : CompIn (c.stage i).comps) (t' : ℝ)
    (ht' : t' ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀)) :
    truncateTorusHk (Nat.zero_le (weakReductionReserve R m v.1)) (Uhi i v t') =
      truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t') := by
  have htrunc : truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi i v t') =
      r.Ur i v t' := by
    by_cases hJ : i = c.M + A.Jw
    · subst hJ
      exact hvr v t' ht'
    · have hJ' : i < c.M + A.Jw := lt_of_le_of_ne hit hJ
      exact hval (i + 1) (Nat.lt_succ_of_lt hi) (by omega) v t' ht'
  rw [← htrunc]
  rfl

/-- The supremum of the order-zero mass norms over `[t_{i+1}, t_i]` is at most `Φ²`. -/
theorem weakCoarse_sup_bound {plan : WeakPassagePlan}
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (m : ℕ)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (i : ℕ)
    (hzv : ∀ (v : CompIn (c.stage i).comps) (t' : ℝ), t' ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀) →
      truncateTorusHk (Nat.zero_le (weakReductionReserve R m v.1)) (Uhi i v t') =
        truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t'))
    (hwin : r.tq (i + 1) ≤ r.tq i) (hit : r.tq i ≤ r.a + A.T₀) (Φ : ℝ)
    (hΦ : ∀ t ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀),
          weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ Φ) :
    (⨆ t' ∈ Set.Icc (r.tq (i + 1)) (r.tq i),
      ENNReal.ofReal (massNormSq 1
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (truncateTorusHk (Nat.zero_le _) (Uhi i v t')).val))) ≤
      ENNReal.ofReal (Φ ^ 2) := by
  have hΦ0 : 0 ≤ Φ := by
    have := hΦ (r.tq (i + 1)) ⟨le_rfl, hwin.trans hit⟩
    exact (by unfold weightedNorm; positivity : (0:ℝ) ≤ _).trans this
  refine iSup₂_le fun t' ht' => ENNReal.ofReal_le_ofReal ?_
  have htime : t' ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀) := ⟨ht'.1, ht'.2.trans hit⟩
  have h1 := hΦ t' htime
  have h2 : weightedNorm (hr := ScalarH) 1
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t')) =
      Real.sqrt (massNormSq 1
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (truncateTorusHk (Nat.zero_le _) (Uhi i v t')).val)) := by
    simp only [weightedNorm, one_pow, div_one]
    apply congrArg Real.sqrt
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [hzv v t' htime]
  rw [h2] at h1
  exact (Real.sqrt_le_left hΦ0).1 h1

/-- The quiet trace at the lifted run. -/
theorem weakCoarse_quiet_apply {plan : WeakPassagePlan} (hcommon : WeakPassageCommonOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (m : ℕ)
    (hfit : (weakQuietCoefficientPlan weakCoarseQuietSeed).baseFloor B ≤ plan.baseFloor B ∧
      (weakQuietCoefficientPlan weakCoarseQuietSeed).momentFloor A ≤ plan.momentFloor A ∧
      (∀ j, (weakQuietCoefficientPlan weakCoarseQuietSeed).levelFloor (weakEntryLiftRequest R m) j ≤
        plan.levelFloor R j) ∧
      plan.radius R ≤ (weakQuietCoefficientPlan weakCoarseQuietSeed).radius
        (weakEntryLiftRequest R m))
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (hstart : r.a < r.tq (c.M + A.Jw + 1))
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (hzv : ∀ (v : CompIn (c.stage i).comps) (t' : ℝ), t' ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀) →
      truncateTorusHk (Nat.zero_le (weakReductionReserve R m v.1)) (Uhi i v t') =
        truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t')) :
    ENNReal.ofReal (massNormSq (plan.radius R * c.D.eps (i - 1))
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i) v).val)) ≤
      ENNReal.ofReal ((max 1 ((weakQuietCoefficientPlan weakCoarseQuietSeed).traceC
        (weakEntryLiftRequest R m))) ^ 2) *
      ⨆ t' ∈ Set.Icc (r.tq (i + 1)) (r.tq i),
        ENNReal.ofReal (massNormSq 1
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (truncateTorusHk (Nat.zero_le _) (Uhi i v t')).val)) := by
  obtain ⟨hb, hmo, hl, hradius⟩ := hfit
  have hspec := weak_quiet_joint_spec weakQuietBasePlan weakQuietBasePrices (fun _ => le_rfl)
    (fun _ => le_rfl)
  have hwin := weak_quiet_window c r i hi hit
  obtain ⟨rr, hclock, -, hagree⟩ := weakCoarse_lifted_run hcommon weakCoarseQuietPlan m hb hmo hl r
    hstart
  have hzero (t' : ℝ) (ht' : t' ∈ Set.Icc (rr.tq (i + 1)) (rr.tq i))
      (v : CompIn (c.stage i).comps) :
      truncateTorusHk (Nat.zero_le (weakReductionReserve R m v.1)) (Uhi i v t') =
        truncateTorusHk (Nat.zero_le (weakEntryLiftRequest R m).Kw) (rr.Ur i v t') := by
    rw [hclock] at ht'
    have htime : t' ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀) := ⟨ht'.1, ht'.2.trans hwin.2.1⟩
    exact (hzv v t' htime).trans (hagree i hi.le hit v t' htime).symm
  have hspec' : WeakQuietRowsPlanOK weakCoarseQuietPlan
      (weakQuietJointPrices weakQuietBasePlan weakQuietBasePrices) ∧
    (∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 ≤ weakCoarseQuietPlan.coeffC R) ∧
    WeakQuietScalarPricesOK weakCoarseQuietPlan
      (weakQuietJointPrices weakQuietBasePlan weakQuietBasePrices) ∧
    WeakQuietMarginPriceStatement weakCoarseQuietPlan
      (weakQuietJointPrices weakQuietBasePlan weakQuietBasePrices) :=
    hspec
  have hq := weak_passage_quiet_trace_high weakCoarseQuietSeed
    (weakQuietJointPrices weakQuietBasePlan weakQuietBasePrices) hspec'.1 hspec'.2.1 hspec'.2.2.1
    hspec'.2.2.2 (weakCoarseLiftCase weakCoarseQuietPlan m hb hmo hl c) rr i hi hit
    (weakReductionReserve R m) (fun v => weakReductionReserve_le R m v) (fun v t' => Uhi i v t')
    hzero (plan.radius R) (plan.radius_pos R).le hradius
  rw [hclock] at hq
  exact hq

/-- **The trace bound of the high-reserve energy**: the mass norm at `ρ` of the trace of `Uhi i` at
`t_i` is at most `cQ² Φ²`. -/
theorem weakCoarse_trace_bound {plan : WeakPassagePlan} (hcommon : WeakPassageCommonOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (m : ℕ)
    (hfit : (weakQuietCoefficientPlan weakCoarseQuietSeed).baseFloor B ≤ plan.baseFloor B ∧
      (weakQuietCoefficientPlan weakCoarseQuietSeed).momentFloor A ≤ plan.momentFloor A ∧
      (∀ j, (weakQuietCoefficientPlan weakCoarseQuietSeed).levelFloor (weakEntryLiftRequest R m) j ≤
        plan.levelFloor R j) ∧
      plan.radius R ≤ (weakQuietCoefficientPlan weakCoarseQuietSeed).radius
        (weakEntryLiftRequest R m))
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (hstart : r.a < r.tq (c.M + A.Jw + 1))
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (hvr : ∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
        ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
          r.Ur (c.M + A.Jw) v t)
    (hval : ∀ i, c.M < i → i ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (i - 1)).comps,
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
          r.Ur (i - 1) v t)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (Φ : ℝ)
    (hΦ : ∀ t ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀),
          weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ Φ) :
    ENNReal.ofReal (massNormSq (plan.radius R * c.D.eps (i - 1))
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i) v).val)) ≤
      ENNReal.ofReal ((max 1 ((weakQuietCoefficientPlan weakCoarseQuietSeed).traceC
        (weakEntryLiftRequest R m))) ^ 2 * Φ ^ 2) := by
  have hwin := weak_quiet_window c r i hi hit
  have hzv := fun v t' ht' => weakCoarse_zero_values m c r Uhi hvr hval i hi hit v t' ht'
  have hq := weakCoarse_quiet_apply hcommon m hfit c r hstart Uhi i hi hit hzv
  have hsup := weakCoarse_sup_bound m c r Uhi i hzv hwin.2.2.1.le hwin.2.1 Φ hΦ
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  exact hq.trans (mul_le_mul' le_rfl hsup)

/-- **The constant of the high-reserve energy**: the passage constant at the radius times the square
of the trace constant of the fixed quiet seed. A function of the radius and the request (note
40). -/
def weakCoarseHighConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (ρ : ℝ)
    (R : WeakPassageRequest A) (m : ℕ) : ℝ :=
  weakRawPassageConst ρ R *
    (max 1 ((weakQuietCoefficientPlan weakCoarseQuietSeed).traceC (weakEntryLiftRequest R m))) ^ 2

theorem weakCoarseHighConst_nonneg {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (ρ : ℝ) (R : WeakPassageRequest A) (m : ℕ) : 0 ≤ weakCoarseHighConst ρ R m :=
  mul_nonneg (weakRawPassageConst_nonneg _ _) (sq_nonneg _)

/-- **The high-reserve energy at the named constant** `weakCoarseHighConst (plan.radius R) R m`. -/
theorem weakCoarse_high_energy_at {plan : WeakPassagePlan} (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarsePlanOK plan) {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (m : ℕ) (hm : m ≤ weakEntryMmax R) :
    WeakCoarseHighEnergyAt plan R m (weakCoarseHighConst (plan.radius R) R m) := by
  classical
  obtain ⟨hfl, hfit⟩ := hok
  intro c r hstart
  obtain ⟨Uhi, Whi, hroot, hpass, hvr, hval, -⟩ := weakStage_higher (weakPassageRawSetting c)
    (weakPassage_two_le_M hcommon c) (weakPassage_coeffRegular hcommon c)
    (weakCoarseClock r hstart) r.f r.θ r.scalar r.reduction m
  refine ⟨Uhi, Whi, fun i h1 h2 => hpass i h1 h2, hvr, hval, ?_⟩
  intro i hi hit Φ hΦ t ht
  have henergy := weakCoarse_passage_energy hcommon hfl c (weakCoarseClock r hstart) m hm Uhi Whi
    i hi hit (hpass i hi hit) t ht
  have hq := weakCoarse_trace_bound hcommon m (hfit R m hm) c r hstart Uhi hvr hval i hi hit Φ hΦ
  refine henergy.trans ?_
  unfold weakCoarseHighConst
  rw [ENNReal.ofReal_mul (weakRawPassageConst_nonneg _ _)]
  calc _ ≤ ENNReal.ofReal (weakRawPassageConst (plan.radius R) R) *
          ENNReal.ofReal ((max 1 ((weakQuietCoefficientPlan weakCoarseQuietSeed).traceC
            (weakEntryLiftRequest R m))) ^ 2 * Φ ^ 2) :=
        mul_le_mul' le_rfl hq
    _ = _ := by
        rw [← ENNReal.ofReal_mul (weakRawPassageConst_nonneg _ _)]
        congr 1; ring
end

/-! **Coarse readout energy: statements.**

* `WeakCoarseRawFrontierAt`: the raw word-block estimate at a named constant, with the clause
  `hvr` on the top family: the blocks of length `R_w` of the high family are measured with the OLD
  masses of their parents and the readout weight, and carry the gain `x^{4 a_* R_w}` in the
  squared energy.
* `WeakCoarseReadoutEnergyBody`: the body of the readout energy at a named constant.
* `WeakCoarseReadoutPlanOK`: plan condition of the readout energy.
-/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **The raw frontier estimate at a constant** `CF`: for every family `Uhi`, `Whi` solving the passages, equal to
the run's at the top level on `[t_{M+J_w+1}, a + T₀]` (`hvr`) and truncating to `r.Ur`
below it, the components of word length `R_w`, measured with the mass of their parent and the
readout weight, have squared energy at most `C_F x^{4 a_* R_w} Φ²`. -/
def WeakCoarseRawFrontierAt (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (m : ℕ) (CF : ℝ) : Prop :=
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c), r.a < r.tq (c.M + A.Jw + 1) →
    ∀ (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
      (Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) m i),
      (∀ i, c.M < i → i ≤ c.M + A.Jw →
        WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i) →
      (∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
        ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
          r.Ur (c.M + A.Jw) v t) →
      (∀ i, c.M < i → i ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (i - 1)).comps,
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
          truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
            r.Ur (i - 1) v t) →
      ∀ i, c.M < i → i ≤ c.M + A.Jw → ∀ Φ : ℝ,
        (∀ t ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀),
          weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ Φ) →
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
          ENNReal.ofReal (∑ v : CompIn (c.stage (i - 1)).comps,
              if (compWord i v.1).length = A.Rw then
                (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
                  ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
                  factorialNormSq (plan.radius R * c.D.eps (i - 1)) (Uhi (i - 1) v t).val
              else 0) +
            ENNReal.ofReal (c.D.κ c.M / 2) *
              ∫⁻ τ in Set.Icc (r.tq i) (r.a + A.T₀),
                ENNReal.ofReal (∑ v : CompIn (c.stage (i - 1)).comps,
                  if (compWord i v.1).length = A.Rw then
                    (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
                      ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
                      gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val
                  else 0) ≤
          ENNReal.ofReal (CF * c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) * Φ ^ 2)

/-- **The body of (iv) at a constant** `C`: the four clauses of
`WeakCoarseReadoutEnergyStatement` for every instance, run, passage and input, with the constant
named. The level floor of the common plan is chosen after this constant (note 40). -/
def WeakCoarseReadoutEnergyBody (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : ℝ) : Prop :=
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
    (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v',
      ContDiff ℝ ((kOf R + 1 : ℕ) : ℕ∞) (h.aU t v')) ∧
    (∀ v' n, n ≤ kOf R + 1 → ∀ w : DerivativeWord2 n,
      ContinuousOn (fun p : ℝ × Vec 2 => orderedDerivative w (h.aU p.1 v') p.2)
        (Set.Icc (r.tq i) (r.a + A.T₀) ×ˢ Set.univ)) ∧
    classicalStrongEnergy (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (Set.Icc (r.tq i) (r.a + A.T₀)) (kOf R)
        (weakResidualReadout i A.η₀ (c.stage i) (c.stage (i - 1)) h.aU) ≤
      ENNReal.ofReal (C * h.Φ) ∧
    classicalStrongEnergy (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (Set.Icc (r.tq i) (r.a + A.T₀)) (kOf R)
        (fun t x v => weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v x) ≤
      ENNReal.ofReal (C * c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ)

/-- **Plan condition of the readout energy**: the plan condition of the high-reserve energy statement and the order condition
`k(R) + 3 ≤ K_w + J_w N_w + L_floor`. -/
def WeakCoarseReadoutPlanOK (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ) :
    Prop :=
  WeakCoarsePlanOK plan ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    kOf R + 3 ≤ R.Kw + (A.Jw * A.Nw + plan.momentFloor A)
end

/-! **Coarse readout energy: the four statements of the assembly**.

The readout `𝓡_i` of the weak construction is a weighted SUM of component fields without
derivatives (`weakReadoutStep`: `∑_{v' : parent v' = v} (E^{η₀})^{|w(v')|} a_{v'}`), so its energy
is a Cauchy--Schwarz over the fibre of the parent.

* `WeakReadoutCSStatement`: Cauchy--Schwarz for the classical factorial norms of a finite weighted
  sum (the factorial norm and the gradient factorial norm).
* `WeakReadoutMassStatement`: per child, the inverse-mass domination
  `π_parent⁻¹ ρ² ≤ π_child⁻¹` for the readout factor `ρ = (E^{η₀})^{|w|}` (consequence of
  `weakMass_succComp`, `E ≤ 1`, `c_w ≤ 1`), and `ρ ≤ 1`.
* The count: the number of components of each stage and the size of the fibre of a parent are
  bounded by a constant depending on the request only.
* `WeakCoarseFamilyRepStatement`: the classical representative of the coarse family is one of the
  high family `Uhi` to the order `k + 1` (clause 1 at the family level).
-/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **Cauchy--Schwarz** for the classical factorial norms of a finite weighted sum of
`C^k` (resp. `C^{k+1}`) real fields. -/
def WeakReadoutCSStatement : Prop :=
  ∀ {ι : Type} (s : Finset ι) (ρ : ℝ) (k : ℕ) (a : ι → Vec 2 → ℝ) (r : ι → ℝ),
    ((∀ c ∈ s, ContDiff ℝ k (a c)) →
      classicalFactorialSq ρ k (fun x => ∑ c ∈ s, r c * a c x) ≤
        (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (r c ^ 2) * classicalFactorialSq ρ k (a c)) ∧
    ((∀ c ∈ s, ContDiff ℝ (k + 1 : ℕ) (a c)) →
      classicalGradFactorialSq ρ k (fun x => ∑ c ∈ s, r c * a c x) ≤
        (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (r c ^ 2) * classicalGradFactorialSq ρ k (a c))

/-- **The mass bound** of the readout factor of a component: with `ρ = (E^{η₀})^{|w(c)|}`,
`E = ε_{i-1}`, `π_{parent}⁻¹ ρ² ≤ π_c⁻¹` and `ρ ≤ 1`. -/
def WeakReadoutMassStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (c' : Comp),
    (weakMass c.D A.Nw A.Jw A.η₀ (compParent i c'))⁻¹ *
        ((c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length) ^ 2 ≤
      (weakMass c.D A.Nw A.Jw A.η₀ c')⁻¹ ∧
    (c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length ≤ 1

/-- **Clause 1 at the family level**: the classical representative `h.aU t v` of the coarse
family is a classical representative of the high family `Uhi (i-1) v t` to the order `k(R) + 1`. -/
def WeakCoarseFamilyRepStatement (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ) :
    Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (m : ℕ),
    m ≤ weakEntryMmax R → kOf R + 3 ≤ R.Kw + m →
    ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i) (i : ℕ),
      c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
      (∀ v : CompIn (c.stage (i - 1)).comps,
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
          truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
            r.Ur (i - 1) v t) →
      ∀ v : CompIn (c.stage (i - 1)).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        IsClassicalRep (Uhi (i - 1) v t) (h.aU t v) (kOf R + 1)
end

/-! **Coarse readout energy, Part B: Cauchy--Schwarz for the classical factorial norms**.

`weakReadoutCS`: `WeakReadoutCSStatement`. The ordered derivative of a finite weighted sum of
smooth fields is the weighted sum of the ordered derivatives (`MixedTail.orderedDerivative_sum`,
`CoarseFluxDiff.orderedDerivative_const_smul`); pointwise `‖∑ y_c‖² ≤ #s ∑ ‖y_c‖²`; integrate on
the cell and regroup the finite sums.
-/

theorem partBCS_enorm_sq (z : ℝ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg z), sq_abs]

theorem partBCS_enorm_sum_sq {ι : Type} (s : Finset ι) (y : ι → ℝ) :
    ‖∑ c ∈ s, y c‖ₑ ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ c ∈ s, ‖y c‖ₑ ^ 2 := by
  simp only [partBCS_enorm_sq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => sq_nonneg _), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (sq_sum_le_card_mul_sum_sq)

theorem partBCS_derivative_sum {ι : Type} (s : Finset ι) {j : ℕ} (w : DerivativeWord2 j)
    (a : ι → Vec 2 → ℝ) (r : ι → ℝ) (ha : ∀ c ∈ s, ContDiff ℝ (j : ℕ∞) (a c)) :
    orderedDerivative w (fun x => ∑ c ∈ s, r c * a c x) =
      fun x => ∑ c ∈ s, r c * orderedDerivative w (a c) x := by
  have h1 := MixedTail.orderedDerivative_sum s w (g := fun c x => r c * a c x)
    (fun c hc => contDiff_const.mul (ha c hc))
  rw [h1]
  funext x
  refine Finset.sum_congr rfl fun c hc => ?_
  have := congrFun (CoarseFluxDiff.orderedDerivative_const_smul w (r c) (ha c hc)) x
  simpa only [smul_eq_mul] using this

theorem partBCS_continuous {j : ℕ} (w : DerivativeWord2 j) {g : Vec 2 → ℝ}
    (hg : ContDiff ℝ (j : ℕ∞) g) : Continuous (orderedDerivative w g) := by
  rw [Sampling.orderedDerivative_eq_iteratedFDeriv w g hg]
  exact (continuous_eval_const _).comp (hg.continuous_iteratedFDeriv le_rfl)

/-- The cell integral of the squared ordered derivative of a weighted sum. -/
theorem partBCS_word {ι : Type} (s : Finset ι) {j : ℕ} (w : DerivativeWord2 j)
    (a : ι → Vec 2 → ℝ) (r : ι → ℝ) (ha : ∀ c ∈ s, ContDiff ℝ (j : ℕ∞) (a c)) :
    ∫⁻ x in unitCube, ‖orderedDerivative w (fun x => ∑ c ∈ s, r c * a c x) x‖ₑ ^ 2 ≤
      (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (r c ^ 2) *
        ∫⁻ x in unitCube, ‖orderedDerivative w (a c) x‖ₑ ^ 2 := by
  rw [partBCS_derivative_sum s w a r ha]
  have hpt : ∀ x, ‖∑ c ∈ s, r c * orderedDerivative w (a c) x‖ₑ ^ 2 ≤
      (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (r c ^ 2) * ‖orderedDerivative w (a c) x‖ₑ ^ 2 :=
    fun x => (partBCS_enorm_sum_sq s _).trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun c _ => by
      rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
        sq_abs]))
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  refine mul_le_mul' le_rfl ?_
  rw [lintegral_finsetSum' _ (fun c hc => ?_)]
  · refine Finset.sum_le_sum fun c _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · exact (((partBCS_continuous w (ha c hc)).measurable.enorm).pow_const 2).const_mul _
      |>.aemeasurable

/-- Regrouping the finite sums of the factorial norms. -/
theorem partBCS_regroup {ι : Type} (s : Finset ι) (ρ : ℝ) (k : ℕ) (d : ℕ → ℕ)
    (a : ι → Vec 2 → ℝ) (r : ι → ℝ) (ha : ∀ c ∈ s, ∀ j ≤ k, ContDiff ℝ (d j : ℕ∞) (a c)) :
    (∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∑ w : DerivativeWord2 (d j), ∫⁻ x in unitCube,
        ‖orderedDerivative w (fun x => ∑ c ∈ s, r c * a c x) x‖ₑ ^ 2) ≤
    (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (r c ^ 2) *
      ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
        ∑ w : DerivativeWord2 (d j), ∫⁻ x in unitCube, ‖orderedDerivative w (a c) x‖ₑ ^ 2 := by
  calc _ ≤ ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
        ∑ w : DerivativeWord2 (d j), (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (r c ^ 2) *
          ∫⁻ x in unitCube, ‖orderedDerivative w (a c) x‖ₑ ^ 2 :=
        Finset.sum_le_sum fun j hj => mul_le_mul' le_rfl (Finset.sum_le_sum fun w _ =>
          partBCS_word s w a r (fun c hc => ha c hc j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))))
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
        ring

/-- **Cauchy--Schwarz for the classical factorial norms** (`WeakReadoutCSStatement`). -/
theorem weakReadoutCS : WeakReadoutCSStatement := by
  intro ι s ρ k a r
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold classicalFactorialSq
    exact partBCS_regroup s ρ k (fun j => j) a r
      (fun c hc j hj => (h c hc).of_le (by exact_mod_cast hj))
  · unfold classicalGradFactorialSq
    exact partBCS_regroup s ρ k (fun j => j + 1) a r
      (fun c hc j hj => (h c hc).of_le (by exact_mod_cast Nat.succ_le_succ hj))

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal Classical
namespace AVRegularity.Providers.WeakGen.Residual.PartB

/-! **Coarse readout energy, Part B: the transfer from the children to the parents**.

Abstract Cauchy--Schwarz bookkeeping, independent of the weak construction: a field on the
parents that is, at each parent `v`, the weighted sum over the children `c` selected by
`sel c v` of fields `a c`. If `p_v ρ_c² ≤ u_c` on selected pairs and the fibres have at most `n`
elements, then the classical strong energy sum over the parents is bounded by
`#V · (2 n Q)`, where `Q` bounds (the sum over the children of `u_c ·` the classical factorial
norms of `a_c`) + `(B/2) ∫` (the same for the gradient).
-/

/-- The fibre bound at one parent, for an abstract seminorm `F` satisfying Cauchy--Schwarz. -/
theorem partB_fiber_abstract {V C : Type} [Fintype C]
    (F : (Vec 2 → ℝ) → ℝ≥0∞) (a : C → Vec 2 → ℝ)
    (hF : ∀ (s : Finset C) (r : C → ℝ), F (fun x => ∑ c ∈ s, r c * a c x) ≤
        (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (r c ^ 2) * F (a c))
    (sel : C → V → Prop) (P : C → Prop) [∀ c v, Decidable (sel c v)] [∀ c, Decidable (P c)]
    (hsel : ∀ c v, sel c v → P c)
    (rc u : C → ℝ) (p : V → ℝ) (n : ℕ) (hp : ∀ v, 0 ≤ p v)
    (hcard : ∀ v, (Finset.univ.filter fun c => sel c v).card ≤ n)
    (hw : ∀ v c, sel c v → p v * rc c ^ 2 ≤ u c) (v : V) :
    ENNReal.ofReal (p v) * F (fun x => ∑ c, if sel c v then rc c * a c x else 0) ≤
      (n : ℝ≥0∞) * ∑ c, if P c then ENNReal.ofReal (u c) * F (a c) else 0 := by
  set s : Finset C := Finset.univ.filter fun c => sel c v with hs
  have hfun : (fun x => ∑ c, if sel c v then rc c * a c x else 0) =
      fun x => ∑ c ∈ s, rc c * a c x := by
    funext x
    rw [hs, Finset.sum_filter]
  rw [hfun]
  calc ENNReal.ofReal (p v) * F (fun x => ∑ c ∈ s, rc c * a c x)
      ≤ ENNReal.ofReal (p v) * ((s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (rc c ^ 2) * F (a c)) :=
        mul_le_mul' le_rfl (hF s rc)
    _ = (s.card : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (p v * rc c ^ 2) * F (a c) := by
        have h1 : ENNReal.ofReal (p v) * ∑ c ∈ s, ENNReal.ofReal (rc c ^ 2) * F (a c) =
            ∑ c ∈ s, ENNReal.ofReal (p v * rc c ^ 2) * F (a c) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_mul (hp v), mul_assoc]
        rw [mul_left_comm, h1]
    _ ≤ (n : ℝ≥0∞) * ∑ c ∈ s, ENNReal.ofReal (u c) * F (a c) :=
        mul_le_mul' (by exact_mod_cast hcard v) (Finset.sum_le_sum fun c hc =>
          mul_le_mul' (ENNReal.ofReal_le_ofReal (hw v c (Finset.mem_filter.1 hc).2)) le_rfl)
    _ ≤ (n : ℝ≥0∞) * ∑ c, if P c then ENNReal.ofReal (u c) * F (a c) else 0 := by
        refine mul_le_mul' le_rfl ?_
        calc ∑ c ∈ s, ENNReal.ofReal (u c) * F (a c)
            = ∑ c ∈ s, if P c then ENNReal.ofReal (u c) * F (a c) else 0 :=
              Finset.sum_congr rfl fun c hc => by simp [hsel c v (Finset.mem_filter.1 hc).2]
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ s)

/-- A supremum over a nonempty set plus a constant. -/
theorem partB_iSup_add_le {I : Set ℝ} (hI : I.Nonempty) (T : ℝ → ℝ≥0∞) (c Q : ℝ≥0∞)
    (h : ∀ t ∈ I, T t + c ≤ Q) : (⨆ t ∈ I, T t) + c ≤ Q := by
  obtain ⟨t0, ht0⟩ := hI
  have hcQ : c ≤ Q := le_trans le_add_self (h t0 ht0)
  by_cases hc : c = ⊤
  · rw [hc] at hcQ ⊢
    rw [top_le_iff.1 hcQ]
    exact le_top
  · calc (⨆ t ∈ I, T t) + c ≤ (Q - c) + c :=
          add_le_add_left (iSup₂_le fun t ht => ENNReal.le_sub_of_add_le_right hc (h t ht)) _
      _ = Q := tsub_add_cancel_of_le hcQ

/-- **The transfer**: the sum over the parents of the strong-energy summands is at most
`#V · (n · 2Q)`. -/
theorem partB_strongEnergy_sum_le (hCS : WeakReadoutCSStatement)
    {V C : Type} [Fintype V] [Fintype C]
    (sel : C → V → Prop) (P : C → Prop) [∀ c v, Decidable (sel c v)] [∀ c, Decidable (P c)]
    (hsel : ∀ c v, sel c v → P c)
    (ρ B : ℝ) (π : V → ℝ) (I : Set ℝ) (hIm : MeasurableSet I) (hI : I.Nonempty) (k : ℕ)
    (a : ℝ → C → Vec 2 → ℝ) (rc u : C → ℝ) (n : ℕ)
    (hπ : ∀ v, 0 ≤ π v)
    (hcard : ∀ v, (Finset.univ.filter fun c => sel c v).card ≤ n)
    (hw : ∀ v c, sel c v → (π v)⁻¹ * rc c ^ 2 ≤ u c)
    (hd : ∀ t ∈ I, ∀ c, ContDiff ℝ (k + 1 : ℕ) (a t c)) (Q : ℝ≥0∞)
    (hQ : ∀ t ∈ I,
      (∑ c, if P c then ENNReal.ofReal (u c) * classicalFactorialSq ρ k (a t c) else 0) +
        ENNReal.ofReal (B / 2) * ∫⁻ τ in I,
          (∑ c, if P c then ENNReal.ofReal (u c) * classicalGradFactorialSq ρ k (a τ c)
            else 0) ≤ Q) :
    (∑ v, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ I, classicalFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) +
        ENNReal.ofReal B * ∫⁻ t in I,
          classicalGradFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0))) ≤
      (Fintype.card V : ℝ≥0∞) * ((n : ℝ≥0∞) * (2 * Q)) := by
  have hp : ∀ v, 0 ≤ (π v)⁻¹ := fun v => inv_nonneg.2 (hπ v)
  have hdk : ∀ t ∈ I, ∀ c, ContDiff ℝ (k : ℕ) (a t c) := fun t ht c =>
    (hd t ht c).of_le (by exact_mod_cast Nat.le_succ k)
  set T : ℝ → ℝ≥0∞ := fun t =>
    ∑ c, if P c then ENNReal.ofReal (u c) * classicalFactorialSq ρ k (a t c) else 0 with hT
  set Tg : ℝ → ℝ≥0∞ := fun t =>
    ∑ c, if P c then ENNReal.ofReal (u c) * classicalGradFactorialSq ρ k (a t c) else 0 with hTg
  have hsup : (⨆ t ∈ I, T t) + ENNReal.ofReal (B / 2) * ∫⁻ τ in I, Tg τ ≤ Q :=
    partB_iSup_add_le hI T _ Q hQ
  have hB : ENNReal.ofReal B = 2 * ENNReal.ofReal (B / 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hper : ∀ v : V, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ I, classicalFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) +
        ENNReal.ofReal B * ∫⁻ t in I,
          classicalGradFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) ≤
      (n : ℝ≥0∞) * (2 * Q) := by
    intro v
    have f1 : ∀ t ∈ I, ENNReal.ofReal (π v)⁻¹ *
        classicalFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0) ≤
        (n : ℝ≥0∞) * T t := fun t ht =>
      partB_fiber_abstract (classicalFactorialSq ρ k) (a t)
        (fun s r => (hCS s ρ k (a t) r).1 (fun c _ => hdk t ht c)) sel P hsel rc u
        (fun v => (π v)⁻¹) n hp hcard hw v
    have f2 : ∀ t ∈ I, ENNReal.ofReal (π v)⁻¹ *
        classicalGradFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0) ≤
        (n : ℝ≥0∞) * Tg t := fun t ht =>
      partB_fiber_abstract (classicalGradFactorialSq ρ k) (a t)
        (fun s r => (hCS s ρ k (a t) r).2 (fun c _ => hd t ht c)) sel P hsel rc u
        (fun v => (π v)⁻¹) n hp hcard hw v
    have e1 : ENNReal.ofReal (π v)⁻¹ * (⨆ t ∈ I, classicalFactorialSq ρ k
        (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) ≤ (n : ℝ≥0∞) * (⨆ t ∈ I, T t) := by
      simp only [ENNReal.mul_iSup]
      exact iSup₂_le fun t ht => (f1 t ht).trans
        (le_iSup₂ (f := fun t (_ : t ∈ I) => (n : ℝ≥0∞) * T t) t ht)
    have e2 : ENNReal.ofReal (π v)⁻¹ * ∫⁻ t in I,
        classicalGradFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0) ≤
        (n : ℝ≥0∞) * ∫⁻ τ in I, Tg τ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _
        (ENNReal.natCast_ne_top n)]
      exact setLIntegral_mono' hIm f2
    calc ENNReal.ofReal (π v)⁻¹ * ((⨆ t ∈ I, classicalFactorialSq ρ k
          (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) + ENNReal.ofReal B *
          ∫⁻ t in I, classicalGradFactorialSq ρ k
            (fun x => ∑ c, if sel c v then rc c * a t c x else 0))
        = ENNReal.ofReal (π v)⁻¹ * (⨆ t ∈ I, classicalFactorialSq ρ k
          (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) + ENNReal.ofReal B *
          (ENNReal.ofReal (π v)⁻¹ * ∫⁻ t in I, classicalGradFactorialSq ρ k
            (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) := by
          rw [mul_add, mul_left_comm]
      _ ≤ (n : ℝ≥0∞) * (⨆ t ∈ I, T t) + ENNReal.ofReal B * ((n : ℝ≥0∞) * ∫⁻ τ in I, Tg τ) :=
          add_le_add e1 (mul_le_mul' le_rfl e2)
      _ = (n : ℝ≥0∞) * ((⨆ t ∈ I, T t) + ENNReal.ofReal B * ∫⁻ τ in I, Tg τ) := by
          rw [mul_add, mul_left_comm (ENNReal.ofReal B)]
      _ ≤ (n : ℝ≥0∞) * (2 * Q) := by
          refine mul_le_mul' le_rfl ?_
          calc (⨆ t ∈ I, T t) + ENNReal.ofReal B * ∫⁻ τ in I, Tg τ
              ≤ 2 * (⨆ t ∈ I, T t) + 2 * (ENNReal.ofReal (B / 2) * ∫⁻ τ in I, Tg τ) := by
                rw [hB, mul_assoc]
                exact add_le_add (le_mul_of_one_le_left bot_le (by norm_num)) le_rfl
            _ = 2 * ((⨆ t ∈ I, T t) + ENNReal.ofReal (B / 2) * ∫⁻ τ in I, Tg τ) := by
                rw [mul_add]
            _ ≤ 2 * Q := mul_le_mul' le_rfl hsup
  calc _ ≤ ∑ _v : V, (n : ℝ≥0∞) * (2 * Q) := Finset.sum_le_sum fun v _ => hper v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end AVRegularity.Providers.WeakGen.Residual.PartB
end
end
end
