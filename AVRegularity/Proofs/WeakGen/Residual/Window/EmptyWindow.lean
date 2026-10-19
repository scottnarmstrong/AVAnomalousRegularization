-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.Window.PartitionAdapter
public import AVRegularity.Proofs.WeakGen.Residual.Recon.PartitionPrice
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.ReadoutEnergy.Main
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.Mean.PathDecomposition
public import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh
import AVRegularity.CycleComparison.Coarse.Defect.DFBound

section
@[expose] public noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.ChartTransport
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Window

/-! **The lifted comparison of a weak passage from the pieces in their own forms**
(the core of the top assembly).

`weakLifted_core`: `weakLifted_of_window` at the proved physical lift `reconPhysicalLift`, with
the window built from the bodies of the four steps (`mkWeakReconWindow`) and every coarse and
analytic hypothesis taken in the form its proof gives it, on `[t_i, a + T₀]`:

* the coarse setting, the coarse defect of a flux `F_c⁰`, the mass
  bound of that flux, the classical representative of the readout, the mean
  presentations: the measurable version of the flux and the coarse body are made here
  (`weakFlux_at_window`, `weakCoarseBody_of_parts`);
* the continuity of the readout, the drift and edge bounds, the two energies:
  converted by `weakAnalytic_at_window`;
* the partition hypothesis as a function of the continuity of the Galerkin coefficients of the
  readout (the adapter `weakWindowPartition_of_recon`); that continuity is read here from the
  coarse defect on the window (`coarseCoeff_prim`).

The orders are those of `weakReconOrders` (`p_c = 1`, `J_c = 0`, `K_max = weakKmax A k₀`,
`A_cl = 1`), for any `k_c ≥ weakKcFloor A k₀`. Nothing is estimated here: the theorem only
converts forms and applies `weakLifted_of_window` once.

The degenerate cases are included: the scale body has `0 < T_obs`, so the window has positive length
(the window of length zero is treated separately, `weakLifted_top_empty`); `bill = 0` or `M = 0`
gives zero forcing
cost. -/

open WeakEntryProofs WeakEntryProofs.Assembly Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The lifted comparison of a weak passage with a window of positive length**, from the bodies
of the steps and the coarse and analytic pieces on `[t_i, a + T₀]`. -/
theorem weakLifted_core
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (k₀ : ℕ)
    (hk₀J : A.Jw * A.Nw ≤ k₀ + 1) (hk₀f : plan.forcingOrder R ≤ k₀)
    (hΛ : 1 ≤ c.D.Λ)
    (hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    {T : (weakWindowFamily c i hi hit).Atlas} {qs qf : ℕ}
    {CGl Cw : ℕ → ℝ} {Ca Sb Cg : ℝ}
    {bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ}
    (hfam : WeakFamilyBody c r i hi hit k₀ T weakCpart)
    (hset : WeakSettingBody c r i hi hit h k₀ qs qf CGl Cw Ca Sb Cg bM)
    (hseq : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
      IsLiftSequence (wLiftData c i hi hit k) (weakKlift A k₀ + weakDw A + 2)
        (max (weakLlift A k₀ + 1) (weakLlift A k₀ + 2))
        (wSeqStart c r i k) (wSeqEnd c r i k) A.Nw (weakH A) (h.CcR i k))
    (hsc : WeakScaleBody c r i) (hSb : 0 ≤ Sb) (hCg : 0 ≤ Cg)
    {aC B₀C lamC : ℝ} {kc : ℕ} (hkc : weakKcFloor A k₀ ≤ kc)
    {AD : ∀ d : Finset.Icc 2 (A.Nw + weakDw A), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 (A.Nw + weakDw A)),
      ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ} {Cstar Θc : ℝ}
    {f0 : ∀ v : CompIn (c.stage i).comps,
      TorusHk (kc + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) (ScalarH v.1.root)}
    {W : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (kc + 1 + (A.Nw + weakDw A)) (ScalarH v.1.root)}
    {Fc₀ : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    (hcs : IsCoarseSetting (r.tq i) (r.a + A.T₀) (wRhoC c i) (c.D.κ c.M) aC B₀C lamC
      (streamVel (c.D.Φ (i - 1))) (A.Nw + weakDw A) (weakH A) 1 0 kc
      ((A.Nw + weakDw A) + 8 * 1 + 4)
      (kc + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) (wJm c) AD CE
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) Aedge Cstar Θc)
    (hcd₀ : IsCoarseDefect (r.tq i) (r.a + A.T₀) (c.D.κ c.M)
      (streamVel (c.D.Φ (i - 1))) (A.Nw + weakDw A) (weakH A) kc
      (kc + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) AD CE (wJm c) f0 W Fc₀)
    {Y : ℝ}
    (hF : FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => kc) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ (i - 1))
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (Set.Icc (r.tq i) (r.a + A.T₀)) Fc₀ Y)
    (hrep : ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v,
      IsClassicalRep (W v t)
        (fun x => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v x)
        (kc + (A.Nw + weakDw A) - 1))
    (hmean : ∀ ρ ∈ Finset.range (weakH A + 1),
      IsMeanPresentation (Set.Icc (r.tq i) (r.a + A.T₀)) (A.Nw + weakDw A) ρ AD CE (wJm c)
        (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀))
          (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
          (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (ocEpsilon c.D.q c.D.Λ (i - 1))
          (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
          A.Nw ρ (fun k => wLiftData c i hi hit k) (h.CcR i)
          (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
          (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))))
    (hWc₀ : ∀ v, ContinuousOn (W v) (Set.Icc (r.tq i) (r.a + A.T₀)))
    {Vb CA : ℝ} (hb : Residual.WeakReconBoundsAt c r i (weakWindowSlots c i k₀) Vb CA)
    {X M tt bill Cs Cy Cpx : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hM : 0 ≤ M) (htt : 0 ≤ tt)
    (hCs : 0 ≤ Cs) (hCy : 0 ≤ Cy) (hCpx : 0 ≤ Cpx)
    {ord : ℕ} (hordE : ord + 1 ≤ kc + 1 + (A.Nw + weakDw A))
    (hEn₀ : strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.a + A.T₀) ord W ≤ ENNReal.ofReal X)
    (hX₀ : strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.a + A.T₀) (weakMprime A k₀) W ≤ ENNReal.ofReal X)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon c.D.q c.D.Λ i)
    (hrsρ : rs ≤ ocEpsilon c.D.q c.D.Λ (i - 1)) {Xp : ℝ} (hXp : 0 ≤ Xp)
    (hPB : (∀ n (r' : CoupledFourierModeIndex
          (h := fun v : CompIn (c.stage i).comps => ScalarH v.1.root) n),
        ContinuousOn (coarseCoeff n W r') (Set.Icc (r.tq i) (r.tq i + wTobs c r i))) →
      WeakWindowPartitionAt c r i hi hit h (weakKmax A k₀) ord rs Xp W)
    (hXM : X ≤ Cs * M) (hYM : Y ≤ Cy * M * tt) (hPM : Xp ≤ Cpx * bill)
    (hb1 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ A.Nw ≤ bill)
    (hb2 : Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt ≤ bill)
    (hb3 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ 2 * tt ≤ bill)
    (hb4 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ A.Nw *
      (Real.sqrt (wTobs c r i) / ocEll c.D.q c.D.Λ i (c.D.κ c.M) *
        (ocEpsilon c.D.q c.D.Λ i / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ weakAcl) ≤ bill)
    (hb5 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ 2 *
      (Real.sqrt (wTobs c r i) / ocEll c.D.q c.D.Λ i (c.D.κ c.M) *
        (ocEpsilon c.D.q c.D.Λ i / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ weakAcl) * tt ≤ bill)
    (Mv : CompIn (c.stage i).comps → ℕ) (X0 : ∀ v, TorusHk (Mv v) (ScalarH v.1.root))
    (hNM : ∀ v, kc + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4) ≤ Mv v)
    (hKM : ∀ v, weakWindowSlots c i k₀ v ≤ Mv v)
    (hXst : ∀ v, truncateTorusHk (hNM v) (X0 v) = f0 v)
    (hinit : ∀ v, truncateTorusHk (Nat.zero_le _) (X0 v) = weakIncomingInit r i v)
    {L : ℝ} (hL : 1 ≤ L) (hrad : plan.radius R * c.D.eps i ≤ L * rs) :
    ∃ (F : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
      (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root))
      (uΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (wΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
      (YΛ : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ →
        TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
      (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        (uΛ v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
          fun x => weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) t
            (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t)) v x) ∧
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
        truncateTorusHk (Nat.le_succ 0) (wΛ v t) = uΛ v t) ∧
      WeakErrSol c r i (weakIncomingInit r i) (weakNegTruncF c i F) (weakNegTruncG c i g)
        uΛ wΛ YΛ ∧
      weakComparisonForcingCost r i F g ≤ ENNReal.ofReal
        (L ^ weakKmax A k₀ * (reconBillConst (weakH A) A.Nw (weakDw A) weakAcl (weakKmax A k₀) (weakMprime A k₀) (weakKres A k₀) (weakNchi A k₀)
            (weakKlift A k₀) (weakLlift A k₀) CGl Cw Ca Sb Cg Cs Cy (Cpx * Cs) * bill * M) +
          L ^ weakKmax A k₀ * (reconBillConst (weakH A) A.Nw (weakDw A) weakAcl (weakKmax A k₀) (weakMprime A k₀) (weakKres A k₀) (weakNchi A k₀)
            (weakKlift A k₀) (weakLlift A k₀) CGl Cw Ca Sb Cg Cs Cy (Cpx * Cs) * bill * M)) := by
  have hsc' := hsc
  obtain ⟨-, -, -, -, -, -, -, -, -, hκ, -, hTobs, -, -, -, -⟩ := hsc'
  have hle : r.tq i ≤ r.tq i + wTobs c r i := by linarith
  obtain ⟨Fc, hcd, hFm, hFcm, hY⟩ := weakFlux_at_window c r i hle hκ hπ hcd₀ hF
  have hco := weakCoarseBody_of_parts c r i hi hit h
    (aRep := fun s y w' => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU s) w' y)
    hcs hcd hrep hmean
  have hkc1 : 1 ≤ kc := (Nat.le_add_left 1 _).trans hkc
  have w := mkWeakReconWindow c r i hi hit h k₀ T qs qf CGl Cw Ca Sb Cg bM aC B₀C lamC 1 0 kc
    AD CE Aedge Cstar Θc f0 W Fc
    (fun s y w' => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU s) w' y)
    hkc1 hfam hset hseq hsc hco
  obtain ⟨hWc, hbm, hVb, hAb, hAm, hEn, hX⟩ :=
    weakAnalytic_at_window c r i hi hit k₀ hWc₀ hb hEn₀ hX₀
  have hcc : ∀ n (r' : CoupledFourierModeIndex
      (h := fun v : CompIn (c.stage i).comps => ScalarH v.1.root) n),
      ContinuousOn (coarseCoeff n W r') (Set.Icc (r.tq i) (r.tq i + wTobs c r i)) :=
    fun n r' => (coarseCoeff_prim hcd hle n r').continuousOn hle
  exact weakLifted_of_window reconPhysicalLift c r i hi hit h k₀ hk₀J hk₀f hΛ hκ hπ hw w
    (weakReconOrders A k₀ kc hkc) (weakWindowSlots_le c i k₀) hSb hCg hset.2 hrs hrse hrsρ hWc
    hle hFm hFcm hbm hVb hb.1 hAb hAm hX0 hY0 hM htt hCs hCy hCpx hordE hXp (hPB hcc) hEn hX hY
    hXM hYM hPM hb1 hb2 hb3 hb4 hb5 Mv X0 hNM hKM hXst hinit hL hrad

end AVRegularity.Providers.WeakGen.Window
end

section
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.Providers.WeakGen.Window

/-! **The plan of the top assembly of the weak window** (the common plan
of the passage side).

Everything the top assembly chooses is chosen here, as a function of the menu `A`, the request
`R` and (for the constants) the radius `ρ` and the forcing constant `c_f` of the plan; nothing
reads an instance, the level, the datum or `D_m`.

* Orders (functions of the menu): the slot shift `weakTopK₀ A = J_wR_w(J_wN_w - 1) + 1 + J_wN_w`
  (above the forcing order of the comparison and with `J_wN_w ≤ k₀ + 1`); the partition orders
  `weakTopOrders A` (`A_cl = 1`, `K_max = weakKmax A k₀`); the coarse order
  `weakTopKc A = weakKcFloor A k₀ + (the partition order)`; the order `weakTopNhi A` of the initial
  datum; the order `weakTopKOf A` asked of the request (`kOf + 3 ≤ K_w + J_wN_w + L`); the
  order of the slot lifts `weakTopLr A = weakWindowLrFloor A k₀`.
* Constants: `weakTopCs ρ R` (the readout energy at the two energy orders), `weakTopCy ρ R` (the
  frontier flux at the lift length), `weakTopL ρ = max 1 ρ`, the constant `weakTopBillConst ρ R` of
  the bill of the reconstruction at the constants of the slot lifts, and the price
  `weakTopDelta ρ c_f R = c_f / (2 L^{K_max} |C_b| + 1)`.
* `WeakTopPlanOK plan`: the plan conditions. Every one is a lower bound on a floor of the plan
  (base, moment, lift, level), except `0 < forceC`, `forcingOrder ≤ weakTopK₀` and the radius
  bounds inside `WeakCoarsePlanOK`. The level floor of the price is chosen after the radius and
  the forcing constant, which is the order of the fields of a plan.

The degenerate cases are included: `J_w = N_w = 1`, `R_w = 1`: `k₀ = 2`; with `forceC = 1` the
price is `1/(2L^{K_max}|C_b| + 1) ≤ 1`. The bundle mentions no instance. -/

open WeakEntryProofs WeakEntryProofs.Assembly Residual Residual.CoarseDefect
  Residual.CoarseDefect.Mean AVRegularity.Providers.WeakGen.Reduction

variable {B : WeakCoefficientBase}

/-! ### Orders -/

/-- The slot shift `k₀` of the top assembly. -/
def weakTopK₀ (A : WeakCoefficientPhysical B) : ℕ :=
  A.Jw * A.Rw * (A.Jw * A.Nw - 1) + 1 + A.Jw * A.Nw

theorem weakTopK₀_ge (A : WeakCoefficientPhysical B) : A.Jw * A.Nw ≤ weakTopK₀ A + 1 := by
  unfold weakTopK₀
  generalize A.Jw * A.Rw * (A.Jw * A.Nw - 1) = P
  omega

/-- The partition orders of the top assembly. -/
def weakTopOrders (A : WeakCoefficientPhysical B) : WeakReconPartitionOrders A where
  Acl := weakAcl
  Kmax := weakKmax A (weakTopK₀ A)
  Lr := weakGluingReadoutOrder A.Jw A.Nw (A.Jw * A.Rw) weakAcl (weakKmax A (weakTopK₀ A))
  Acl_pos := le_rfl
  reserve := le_rfl

/-- The coarse order `k_c`. -/
def weakTopKc (A : WeakCoefficientPhysical B) : ℕ :=
  weakKcFloor A (weakTopK₀ A) + weakReconPartitionOrder (weakTopOrders A)

/-- The order of the initial datum `X₀`. -/
def weakTopNhi (A : WeakCoefficientPhysical B) : ℕ :=
  weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4) + weakKmax A (weakTopK₀ A)

/-- The order asked of the request: `kOf + 3 ≤ K_w + J_wN_w + L`. -/
def weakTopKOf (A : WeakCoefficientPhysical B) : ℕ :=
  weakTopNhi A + weakTopKc A + (A.Nw + weakDw A)

/-- The order of the slot lifts. -/
def weakTopLr (A : WeakCoefficientPhysical B) : ℕ := weakWindowLrFloor A (weakTopK₀ A)

theorem weakTopKc_floor (A : WeakCoefficientPhysical B) :
    weakKcFloor A (weakTopK₀ A) ≤ weakTopKc A := Nat.le_add_right _ _

theorem weakTopKc_ord (A : WeakCoefficientPhysical B) :
    weakReconPartitionOrder (weakTopOrders A) + 1 ≤ weakTopKc A + 1 + (A.Nw + weakDw A) := by
  have h : weakReconPartitionOrder (weakTopOrders A) ≤ weakTopKc A := Nat.le_add_left _ _
  generalize weakReconPartitionOrder (weakTopOrders A) = a at h ⊢
  generalize weakTopKc A = b at h ⊢
  generalize A.Nw + weakDw A = d
  omega

theorem weakTopKc_mprime (A : WeakCoefficientPhysical B) :
    weakMprime A (weakTopK₀ A) + 1 ≤ weakTopKc A + 1 + (A.Nw + weakDw A) := by
  have h1 : weakMprime A (weakTopK₀ A) ≤ weakKcFloor A (weakTopK₀ A) :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ 4))
  have h := h1.trans (weakTopKc_floor A)
  generalize weakMprime A (weakTopK₀ A) = a at h ⊢
  generalize weakTopKc A = b at h ⊢
  generalize A.Nw + weakDw A = d
  omega

/-! ### Constants -/

variable {A : WeakCoefficientPhysical B}

theorem weakReadoutWindowConst_nonneg (ρ : ℝ) (R : WeakPassageRequest A) (m ord : ℕ) :
    0 ≤ weakReadoutWindowConst ρ R m ord :=
  mul_nonneg (radiusChangeFactor_nonneg _ _) (Real.sqrt_nonneg _)

/-- The energy constant `C_s`: the readout energy bound at the two energy orders of the window. -/
def weakTopCs (ρ : ℝ) (R : WeakPassageRequest A) : ℝ :=
  max (weakReadoutWindowConst ρ R (weakEntryMmax R) (weakReconPartitionOrder (weakTopOrders A)))
    (weakReadoutWindowConst ρ R (weakEntryMmax R) (weakMprime A (weakTopK₀ A)))

theorem weakTopCs_nonneg (ρ : ℝ) (R : WeakPassageRequest A) : 0 ≤ weakTopCs ρ R :=
  (weakReadoutWindowConst_nonneg ρ R _ _).trans (le_max_left _ _)

/-- The flux constant `C_y`: the frontier flux bound at the lift length. -/
def weakTopCy (ρ : ℝ) (R : WeakPassageRequest A) : ℝ :=
  |max 1 ρ⁻¹ ^ weakTopKc A * weakFrontierFluxConst ρ R|

/-- The radius factor `L = max 1 ρ`. -/
def weakTopL (ρ : ℝ) : ℝ := max 1 ρ

/-- The constant of the bill of the reconstruction at the weak window. -/
def weakTopBillConst (ρ : ℝ) (R : WeakPassageRequest A) : ℝ :=
  reconBillConst (weakH A) A.Nw (weakDw A) weakAcl (weakKmax A (weakTopK₀ A)) (weakMprime A (weakTopK₀ A))
    (weakKres A (weakTopK₀ A)) (weakNchi A (weakTopK₀ A)) (weakKlift A (weakTopK₀ A)) (weakLlift A (weakTopK₀ A))
    (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).CG (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).Cw (weakSettingCa (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ) (weakSettingQs A (weakTopK₀ A)) (weakSettingQf A (weakTopK₀ A))) (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).S
    (weakGradeConst A (weakTopK₀ A) (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).CG (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).Cw (weakSettingCa (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ) (weakSettingQs A (weakTopK₀ A)) (weakSettingQf A (weakTopK₀ A))))
    (weakTopCs ρ R) (weakTopCy ρ R)
    (weakReconPartitionBillConstant (weakTopOrders A) R * weakTopCs ρ R)

/-- The price of the bill: `δ = c_f / (2 L^{K_max} |C_b| + 1)`. -/
def weakTopDelta (ρ fc : ℝ) (R : WeakPassageRequest A) : ℝ :=
  fc / (2 * (weakTopL ρ ^ weakKmax A (weakTopK₀ A) * |weakTopBillConst ρ R|) + 1)

theorem weakTopDelta_pos {ρ fc : ℝ} (hfc : 0 < fc) (R : WeakPassageRequest A) :
    0 < weakTopDelta ρ fc R := by
  have hL : 0 ≤ weakTopL ρ ^ weakKmax A (weakTopK₀ A) :=
    pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have h := mul_nonneg hL (abs_nonneg (weakTopBillConst ρ R))
  exact div_pos hfc (by linarith)

/-- The flux bound in the form `C_y · M · tt`. -/
theorem weakTop_flux_const {a b tt Φ : ℝ} (hΦ : 0 ≤ Φ) (htt : 0 ≤ tt) :
    a * (b * tt * Φ) ≤ |a * b| * Φ * tt :=
  calc a * (b * tt * Φ) = a * b * (Φ * tt) := by ring
    _ ≤ |a * b| * (Φ * tt) := mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hΦ htt)
    _ = |a * b| * Φ * tt := by ring

/-! ### The plan conditions -/

/-- **The plan conditions of the top assembly of the weak window.** -/
structure WeakTopPlanOK (plan : WeakPassagePlan) : Prop where
  common : WeakPassageCommonOK plan
  coarse : WeakCoarseReadoutPlanOK plan (fun {_B} {A} _ => weakTopKOf A)
  ell : WeakPassageEllOK plan
  slotLifts : WeakSlotLiftUPlanOK plan (fun {_B} {A} _ => weakTopLr A)
  mean : WeakCoarseMeanPlanOK plan
  partition : WeakReconPartitionPlanOK plan (fun {_B} {A} _ => weakTopOrders A)
  partitionPrice : WeakReconPartitionPricePlanOK plan (fun {_B} {A} _ => weakTopOrders A)
  force : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    0 < plan.forceC R
  forcing : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A), plan.forcingOrder R ≤ weakTopK₀ A
  lift : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
    max (weakKlift A (weakTopK₀ A) + weakDw A + 2) (weakLlift A (weakTopK₀ A) + 2) ≤
      plan.liftFloor A
  price : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (j₀ : ℕ),
    weakReconPriceFloor (weakTopOrders A) R
      (weakTopDelta (plan.radius R) (plan.forceC R) R) ≤ plan.levelFloor R j₀

variable {plan : WeakPassagePlan} {R : WeakPassageRequest A}

/-- **The orders of the top assembly fit the request** of an instance. -/
theorem weakTop_request_orders
    (hcoarse : WeakCoarseReadoutPlanOK plan (fun {_B} {A} _ => weakTopKOf A))
    (c : WeakPassageInstance plan R) :
    weakTopKOf A + 3 ≤ R.Kw + weakEntryMmax R ∧
    weakTopKc A + 1 + (A.Nw + weakDw A) ≤ R.Kw + weakEntryMmax R ∧
    weakTopNhi A ≤ R.Kw + weakEntryMmax R ∧
    weakTopKc A + (A.Nw + weakDw A) - 1 ≤ weakTopKOf A ∧
    weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4) ≤ weakTopNhi A ∧
    weakKmax A (weakTopK₀ A) ≤ weakTopNhi A := by
  have h1 : weakTopKOf A + 3 ≤ R.Kw + (A.Jw * A.Nw + plan.momentFloor A) := hcoarse.2 R
  have h2 : plan.momentFloor A ≤ R.L := c.moment_ge
  rw [show weakEntryMmax R = A.Jw * A.Nw + R.L from rfl]
  unfold weakTopKOf weakTopNhi at h1 ⊢
  generalize (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4) = P at h1 ⊢
  generalize A.Nw + weakDw A = D at h1 ⊢
  generalize weakKmax A (weakTopK₀ A) = Km at h1 ⊢
  generalize weakTopKc A = kc at h1 ⊢
  generalize A.Jw * A.Nw = JN at h1 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The lift orders of the request are above those of the window. -/
theorem weakTop_lift_orders (hlift : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
      max (weakKlift A (weakTopK₀ A) + weakDw A + 2) (weakLlift A (weakTopK₀ A) + 2) ≤
        plan.liftFloor A) {sX sZ : ℕ} (hX : plan.liftFloor A ≤ sX) (hZ : plan.liftFloor A ≤ sZ) :
    weakKlift A (weakTopK₀ A) + weakDw A + 2 ≤ sX ∧
    max (weakLlift A (weakTopK₀ A) + 1) (weakLlift A (weakTopK₀ A) + 2) ≤ sZ :=
  ⟨(le_max_left _ _).trans ((hlift A).trans hX),
    (max_le (Nat.le_succ _) le_rfl).trans ((le_max_right _ _).trans ((hlift A).trans hZ))⟩

end AVRegularity.Providers.WeakGen.Window
end
end
end

section
@[expose] public noncomputable section

section
namespace AVRegularity.Providers.WeakGen.Window

/-! **The passage plan of the weak-entry argument** (the common plan of the passage side exists).

`weakTopSeedPlan` is a passage plan whose comparison refinement
`weakComparisonPassagePlan weakTopSeedPlan` satisfies `WeakTopPlanOK` (`weakTopSeedPlan_ok`).
The choices:

1. radius `1/2048` (the refinement takes `min · (1/2048)`; the quiet plan of the fixed seed has
   the radius `1/2048`), `forcingOrder = 0` (the refinement takes the maximum with
   `J_wR_w(J_wN_w - 1) + 1 ≤ weakTopK₀`), `forceC = 1`;
2. the moment floor `max (quiet) (weakTopKOf A + 3)` and the lift floor
   `max 2 (max (K_lift + D_w + 2) (L_lift + 2))`: functions of the menu;
3. the base floor: `128`, the common threshold, the quiet plan's, the two slot-lift floors;
4. the level floor, last: the common threshold, the floors of the passage energy, the supremum
   over the offsets `m ≤ m_max(R)` of the quiet plan's floor at the lifted request, the
   ellipticity floor, the three slot-lift levels (the window's, the mean's, the partition's), the
   flow and count floors of the partition and the price floor of the bill at
   `δ = weakTopDelta (1/2048) 1 R`.

Every condition of `WeakTopPlanOK` is then a chain of `le_max`. Nothing is read back from a
statement about the plan: every floor above is a named function of the base, the menu, the
request and `j₀`.

The degenerate case `m_max(R) = 0` gives a supremum of one term. The price floor reads the radius
`min (1/2048) (1/2048)` and `forceC = 1`, the values of the refinement, by `rfl`. -/

open WeakEntryProofs WeakEntryProofs.Assembly Residual Residual.CoarseDefect
  Residual.CoarseDefect.Mean AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Comparison

/-! ### The floors -/

/-- The base floor of the passage plan. -/
def weakTopBaseFloor (B : WeakCoefficientBase) : ℕ :=
  max (max 128 (weakCommonCoeffPlan.baseThreshold B))
    (max ((weakQuietCoefficientPlan weakCoarseQuietSeed).baseFloor B)
      (max (weakSlotLiftUFloor B) (weakSlotLiftAtFloor B)))

variable {B : WeakCoefficientBase}

/-- The moment floor of the passage plan. -/
def weakTopMomentFloor (A : WeakCoefficientPhysical B) : ℕ :=
  max ((weakQuietCoefficientPlan weakCoarseQuietSeed).momentFloor A) (weakTopKOf A + 3)

/-- The lift floor of the passage plan. -/
def weakTopLiftFloor (A : WeakCoefficientPhysical B) : ℕ :=
  max 2 (max (weakKlift A (weakTopK₀ A) + weakDw A + 2) (weakLlift A (weakTopK₀ A) + 2))

variable {A : WeakCoefficientPhysical B}

/-- The supremum, over the offsets `m ≤ m_max(R)`, of the level floor of the quiet plan at the
lifted request. -/
def weakTopQuietLevelSup (R : WeakPassageRequest A) (j₀ : ℕ) : ℕ :=
  (Finset.range (weakEntryMmax R + 1)).sup fun m =>
    (weakQuietCoefficientPlan weakCoarseQuietSeed).levelFloor (weakEntryLiftRequest R m) j₀

theorem le_weakTopQuietLevelSup (R : WeakPassageRequest A) (j₀ m : ℕ)
    (hm : m ≤ weakEntryMmax R) :
    (weakQuietCoefficientPlan weakCoarseQuietSeed).levelFloor (weakEntryLiftRequest R m) j₀ ≤
      weakTopQuietLevelSup R j₀ :=
  Finset.le_sup (f := fun m =>
    (weakQuietCoefficientPlan weakCoarseQuietSeed).levelFloor (weakEntryLiftRequest R m) j₀)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

/-- The level floor of the passage plan. -/
def weakTopLevelFloor (R : WeakPassageRequest A) (j₀ : ℕ) : ℕ :=
  max (max (max (weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀)
        (weakEntryPassageCoeffFloor R))
      (max (weakComparisonDriftFloor A) (weakQuietStoredFloor A)))
    (max (max (max (weakPairedLevelFloor R) (weakTopQuietLevelSup R j₀))
        (max (weakEllLevel B A.Λ) (weakSlotLiftULevel A (weakTopLr A) R.sX R.sZ j₀)))
      (max (max (weakSlotLiftLevel A (weakWindowLrFloor A 0) R.sX R.sZ j₀)
          (weakSlotLiftLevel A (weakTopOrders A).Lr R.sX R.sZ j₀))
        (max (max (weakReconPartitionFlowFloor (weakTopOrders A))
            (weakReconPartitionCountFloor (weakTopOrders A) R))
          (weakReconPriceFloor (weakTopOrders A) R
            (weakTopDelta (min (1 / 2048) (1 / 2048)) 1 R)))))

/-! ### The plan -/

/-- **The passage plan of the weak-entry argument** (before its comparison refinement). -/
def weakTopSeedPlan : WeakPassagePlan where
  baseFloor := weakTopBaseFloor
  base_ge := fun _ => (le_max_left _ _).trans (le_max_left _ _)
  momentFloor := fun A => weakTopMomentFloor A
  radius := fun _ => 1 / 2048
  radius_pos := fun _ => by norm_num
  traceC := fun _ => 0
  jetOrder := fun _ => 0
  coeffC := fun _ => 0
  forcingOrder := fun _ => 0
  forceC := fun _ => 1
  energyC := fun _ => 1
  energyC_nonneg := fun _ => zero_le_one
  levelFloor := fun R j₀ => weakTopLevelFloor R j₀
  liftFloor := fun A => weakTopLiftFloor A

/-! ### Each floor is below the maximum -/

theorem weakTopBase_common (B : WeakCoefficientBase) :
    weakCommonCoeffPlan.baseThreshold B ≤ weakTopBaseFloor B :=
  le_max_of_le_left (le_max_right _ _)

theorem weakTopBase_quiet (B : WeakCoefficientBase) :
    (weakQuietCoefficientPlan weakCoarseQuietSeed).baseFloor B ≤ weakTopBaseFloor B :=
  le_max_of_le_right (le_max_left _ _)

theorem weakTopBase_slotLiftU (B : WeakCoefficientBase) :
    weakSlotLiftUFloor B ≤ weakTopBaseFloor B :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

theorem weakTopBase_slotLiftAt (B : WeakCoefficientBase) :
    weakSlotLiftAtFloor B ≤ weakTopBaseFloor B :=
  le_max_of_le_right (le_max_of_le_right (le_max_right _ _))

theorem weakTopLevel_common (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_left (le_max_of_le_left (le_max_left _ _))

theorem weakTopLevel_passageCoeff (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakEntryPassageCoeffFloor R ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_left (le_max_of_le_left (le_max_right _ _))

theorem weakTopLevel_drift (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakComparisonDriftFloor A ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_left (le_max_of_le_right (le_max_left _ _))

theorem weakTopLevel_stored (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakQuietStoredFloor A ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_left (le_max_of_le_right (le_max_right _ _))

theorem weakTopLevel_paired (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakPairedLevelFloor R ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))

theorem weakTopLevel_quietSup (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakTopQuietLevelSup R j₀ ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))

theorem weakTopLevel_ell (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakEllLevel B A.Λ ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_left (le_max_of_le_right (le_max_left _ _)))

theorem weakTopLevel_slotLiftU (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakSlotLiftULevel A (weakTopLr A) R.sX R.sZ j₀ ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_left (le_max_of_le_right (le_max_right _ _)))

theorem weakTopLevel_slotLiftMean (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakSlotLiftLevel A (weakWindowLrFloor A 0) R.sX R.sZ j₀ ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))

theorem weakTopLevel_slotLiftPart (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakSlotLiftLevel A (weakTopOrders A).Lr R.sX R.sZ j₀ ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))

theorem weakTopLevel_flow (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakReconPartitionFlowFloor (weakTopOrders A) ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (le_max_left _ _))))

theorem weakTopLevel_count (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakReconPartitionCountFloor (weakTopOrders A) R ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (le_max_right _ _))))

theorem weakTopLevel_price (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakReconPriceFloor (weakTopOrders A) R
      (weakTopDelta (min (1 / 2048) (1 / 2048)) 1 R) ≤ weakTopLevelFloor R j₀ :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

/-- A floor below `weakTopLevelFloor` is below the level floor of the refinement. -/
theorem le_weakTop_level {R : WeakPassageRequest A} {j₀ x : ℕ}
    (h : x ≤ weakTopLevelFloor R j₀) :
    x ≤ (weakComparisonPassagePlan weakTopSeedPlan).levelFloor R j₀ :=
  h.trans (le_max_left _ _)

/-! ### The conditions, one by one -/

theorem weakTopSeedPlan_common :
    WeakPassageCommonOK (weakComparisonPassagePlan weakTopSeedPlan) :=
  ⟨fun B => weakTopBase_common B, fun R j₀ => le_weakTop_level (weakTopLevel_common R j₀)⟩

theorem weakTopSeedPlan_coarse :
    WeakCoarseReadoutPlanOK (weakComparisonPassagePlan weakTopSeedPlan)
      (fun {_B} {A} _ => weakTopKOf A) :=
  ⟨⟨⟨fun _ => min_le_right _ _, fun R j₀ =>
        ⟨le_weakTop_level (weakTopLevel_passageCoeff R j₀),
          le_weakTop_level (weakTopLevel_drift R j₀),
          le_weakTop_level (weakTopLevel_stored R j₀),
          le_weakTop_level (weakTopLevel_paired R j₀)⟩⟩,
      fun {B} {_A} R m hm =>
        ⟨weakTopBase_quiet B, le_max_left _ _,
          fun j => le_weakTop_level ((le_weakTopQuietLevelSup R j m hm).trans
            (weakTopLevel_quietSup R j)),
          (min_le_right _ _).trans (le_of_eq rfl)⟩⟩,
    fun {_B} {_A} _ => ((le_max_right _ _).trans (Nat.le_add_left _ _)).trans
      (Nat.le_add_left _ _)⟩

theorem weakTopSeedPlan_ell : WeakPassageEllOK (weakComparisonPassagePlan weakTopSeedPlan) :=
  fun R j₀ => le_weakTop_level (weakTopLevel_ell R j₀)

theorem weakTopSeedPlan_slotLifts :
    WeakSlotLiftUPlanOK (weakComparisonPassagePlan weakTopSeedPlan)
      (fun {_B} {A} _ => weakTopLr A) :=
  ⟨fun B => weakTopBase_slotLiftU B, fun R j₀ => le_weakTop_level (weakTopLevel_slotLiftU R j₀)⟩

theorem weakTopSeedPlan_mean :
    WeakCoarseMeanPlanOK (weakComparisonPassagePlan weakTopSeedPlan) :=
  ⟨⟨fun B => weakTopBase_slotLiftAt B,
      fun R j₀ => le_weakTop_level (weakTopLevel_slotLiftMean R j₀)⟩,
    fun _ => le_max_left _ _⟩

theorem weakTopSeedPlan_partition :
    WeakReconPartitionPlanOK (weakComparisonPassagePlan weakTopSeedPlan)
      (fun {_B} {A} _ => weakTopOrders A) :=
  ⟨weakTopSeedPlan_common,
    ⟨fun B => weakTopBase_slotLiftAt B,
      fun R j₀ => le_weakTop_level (weakTopLevel_slotLiftPart R j₀)⟩,
    fun R j₀ => le_weakTop_level (weakTopLevel_flow R j₀)⟩

theorem weakTopSeedPlan_partitionPrice :
    WeakReconPartitionPricePlanOK (weakComparisonPassagePlan weakTopSeedPlan)
      (fun {_B} {A} _ => weakTopOrders A) :=
  fun R j₀ => le_weakTop_level (weakTopLevel_count R j₀)

theorem weakTopSeedPlan_price {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (j₀ : ℕ) :
    weakReconPriceFloor (weakTopOrders A) R
      (weakTopDelta ((weakComparisonPassagePlan weakTopSeedPlan).radius R)
        ((weakComparisonPassagePlan weakTopSeedPlan).forceC R) R) ≤
      (weakComparisonPassagePlan weakTopSeedPlan).levelFloor R j₀ :=
  le_weakTop_level (weakTopLevel_price R j₀)

/-- **The comparison refinement of the passage plan satisfies the plan conditions of the top
assembly.** -/
theorem weakTopSeedPlan_ok : WeakTopPlanOK (weakComparisonPassagePlan weakTopSeedPlan) where
  common := weakTopSeedPlan_common
  coarse := weakTopSeedPlan_coarse
  ell := weakTopSeedPlan_ell
  slotLifts := weakTopSeedPlan_slotLifts
  mean := weakTopSeedPlan_mean
  partition := weakTopSeedPlan_partition
  partitionPrice := weakTopSeedPlan_partitionPrice
  force := fun _ => zero_lt_one
  forcing := fun {_B} {_A} _ => max_le (Nat.zero_le _) (Nat.le_add_right _ _)
  lift := fun _ => le_max_right _ _
  price := fun R j₀ => weakTopSeedPlan_price R j₀

/-! ### Lift orders available on the plan (the hypotheses of the mean presentation's leaves) -/

/-- The lift floor of the refinement is above `N_w + 1 + D_w`. -/
theorem weakTopSeedPlan_liftCap {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) :
    A.Nw + 1 + (1 + A.Jw * A.Nw) ≤ (weakComparisonPassagePlan weakTopSeedPlan).liftFloor A := by
  have hD : 0 < weakDw A := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)
  have h1 : A.Nw ≤ weakDw A * (weakH A + 1) * A.Nw :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hD (Nat.succ_pos _))
  have h2 : A.Nw + 1 + (1 + A.Jw * A.Nw) ≤ weakKlift A (weakTopK₀ A) + weakDw A + 2 := by
    show A.Nw + 1 + (1 + A.Jw * A.Nw) ≤
      2 * weakAcl + 2 + weakKmax A (weakTopK₀ A) + weakDw A * (weakH A + 1) * A.Nw + 2 +
        (1 + A.Jw * A.Nw) + 2
    generalize weakDw A * (weakH A + 1) * A.Nw = P at h1 ⊢
    generalize weakKmax A (weakTopK₀ A) = K
    generalize A.Jw * A.Nw = JN
    omega
  exact h2.trans ((le_max_left _ _).trans (le_max_right _ _))

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Window

/-! **The lifted comparison of a weak passage whose window has length zero**
(`IsWeakReduction` gives `t_{M+1} ≤ T` only).

When `t_i = a + T₀` the window `[t_i, a + T₀]` is a point. The data of
`WeakLiftedComparisonStatement` are then: zero forcing, the constant family `u_Λ = U(t_i)`
(`weakIncomingInit`), any lifts.

* `isKernelWeakSolutionTorus_of_empty`: on an interval of length zero the constant family at the
  initial value solves every kernel system (the measure of the interval is zero and the tested
  identity at `t = t₀` is `u(t₀) = f`).
* `mixedCost_of_null`: the forcing cost over a null window is zero.
* `weakLifted_of_empty_window`: the six clauses, from the one fact that at `t_i` the glued lift
  of the readout is the incoming value a.e.
* `weakLifted_top_empty`: that fact under the plan conditions: the readout `W(t_i)` of the high
  family is the readout of the trace (the initial clause of the passage), which at order zero is
  `U(t_i)` (`weakCoarseInitial`); its classical representative is the readout of `h.aU`
  (`cdW_isClassicalRep`); and the glued lift at `t_i` is the identity (`weakGluedLiftStart`).

The degenerate cases are included: the conclusion's cost is `0 ≤` any bound, also a negative one
(`ofReal` of it is `0`); the root `i = M + J_w` is allowed; an empty component type makes every
clause vacuous. -/

open WeakEntryProofs WeakEntryProofs.Assembly Residual Residual.CoarseDefect
  AVRegularity.Providers.WeakGen.Reduction

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)]

/-- Lebesgue measure restricted to an interval of length zero is zero. -/
theorem restrict_Icc_eq_zero {a b : ℝ} (hab : a = b) :
    (volume.restrict (Set.Icc a b) : Measure ℝ) = 0 := by
  subst hab
  rw [Set.Icc_self]
  exact Measure.restrict_eq_zero.2 Real.volume_singleton

/-- **On an interval of length zero the constant family at the initial value solves every kernel
system.** -/
theorem isKernelWeakSolutionTorus_of_empty {t₀ t₁ : ℝ} (ht : t₀ = t₁) (ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (k D : ℕ)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g (fun i _ => f i) w y := by
  have hμ := restrict_Icc_eq_zero ht
  subst ht
  refine ⟨fun i => continuousOn_const, fun i => ?_, fun i => ?_, fun i => rfl, fun i j α => ?_,
    fun i j α => ?_, fun i t ht φ => ?_⟩
  · rw [hμ]; exact memLp_measure_zero
  · rw [hμ]; simp
  · rw [hμ]; exact memLp_measure_zero
  · rw [hμ]; simp
  · obtain rfl : t = t₀ := le_antisymm ht.2 ht.1
    refine ⟨CycleJointProofs.integrable_inner_of_memLp_two _ _ _
        (CycleComparison.Coarse.memLp_jet _ _) (CycleComparison.Coarse.memLp_jet _ _),
      CycleJointProofs.integrable_inner_of_memLp_two _ _ _
        (CycleComparison.Coarse.memLp_jet _ _) (CycleComparison.Coarse.memLp_jet _ _),
      fun s hs => ?_, ?_, ?_⟩
    · exact absurd hs (by simp)
    · rw [Set.Ioc_self]; exact integrableOn_empty
    · rw [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]; exact sub_self _

/-- **The forcing cost over a null window is zero.** -/
theorem mixedCost_of_null {k : ℕ} (ν ρ : ℝ) (π : ι → ℝ) {a b : ℝ}
    (hab : (volume.restrict (Set.Icc a b) : Measure ℝ) = 0)
    (F : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (g : ∀ v, ℝ → TorusHk k (h v)) :
    (∑ v, (ENNReal.ofReal (π v))⁻¹ *
      ((ENNReal.ofReal ν)⁻¹ *
        (∫⁻ t in Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (F v t).val)) +
        (∫⁻ t in Set.Icc a b,
          ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g v t).val))) ^ 2)) ^ (1 / 2 : ℝ) = 0 := by
  have h0 : ∀ v, (ENNReal.ofReal (π v))⁻¹ *
      ((ENNReal.ofReal ν)⁻¹ * (0 : ℝ≥0∞) + (0 : ℝ≥0∞) ^ 2) = 0 := fun v => by simp
  simp only [hab, lintegral_zero_measure, h0, Finset.sum_const_zero]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

/-- The order-zero value of the truncation of a class with a classical representative. -/
theorem jet_truncate_of_rep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K r : ℕ} (X : TorusHk K E)
    (a : Vec 2 → E) (hrep : IsClassicalRep X a r) :
    (truncateTorusHk (Nat.zero_le K) X).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict AVenhance.unitCube] a :=
  (KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.zero_le K) X (valueIndex2 0)).trans
    (Construction.Preservation.FullLift.classicalRep_value_ae X a hrep)

end Generic

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The lifted comparison on a window of length zero**, from the value of the glued lift at
`t_i`; the forcing cost is zero. -/
theorem weakLifted_of_empty_window (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i : ℕ) (h : WeakComparisonInput r i) (heq : r.tq i = r.a + A.T₀)
    (hstart : ∀ v, (weakIncomingInit r i v).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict unitCube] fun x =>
        weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) (r.tq i)
          (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU (r.tq i))) v x)
    (X : ℝ) :
    ∃ (F : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
      (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root))
      (uΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (wΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
      (YΛ : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ →
        TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
      (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        (uΛ v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
          fun x => weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) t
            (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t)) v x) ∧
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
        truncateTorusHk (Nat.le_succ 0) (wΛ v t) = uΛ v t) ∧
      WeakErrSol c r i (weakIncomingInit r i) (weakNegTruncF c i F) (weakNegTruncG c i g)
        uΛ wΛ YΛ ∧
      weakComparisonForcingCost r i F g ≤ ENNReal.ofReal X := by
  have hμ := restrict_Icc_eq_zero heq
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun v _ => weakIncomingInit r i v, fun _ _ => 0,
    fun _ _ _ _ => 0, fun v => aestronglyMeasurable_const, fun v => aestronglyMeasurable_const,
    fun v t ht => ?_, fun v => ?_, ?_, ?_⟩
  · obtain rfl : t = r.tq i := le_antisymm (ht.2.trans heq.ge) ht.1
    exact hstart v
  · rw [hμ]; simp
  · exact isKernelWeakSolutionTorus_of_empty heq _ _ _ _ _ _ _ _ _ _ _ _
  · have h0 : weakComparisonForcingCost r i (fun _ _ => 0) (fun _ _ => 0) = 0 :=
      mixedCost_of_null _ _ _ hμ _ _
    rw [h0]
    exact zero_le

/-- **The lifted comparison on a window of length zero, under the plan conditions.** -/
theorem weakLifted_top_empty (hplan : WeakTopPlanOK plan) (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonInput r i) (heq : r.tq i = r.a + A.T₀) (X : ℝ) :
    ∃ (F : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
      (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root))
      (uΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (wΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
      (YΛ : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ →
        TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
      (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        (uΛ v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
          fun x => weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) t
            (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t)) v x) ∧
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
        truncateTorusHk (Nat.le_succ 0) (wΛ v t) = uΛ v t) ∧
      WeakErrSol c r i (weakIncomingInit r i) (weakNegTruncF c i F) (weakNegTruncG c i g)
        uΛ wΛ YΛ ∧
      weakComparisonForcingCost r i F g ≤ ENNReal.ofReal X := by
  have hcommon := hplan.common
  obtain ⟨Uhi, Whi, hpass, hvr, hval, -⟩ :=
    weakCoarse_high_energy_at hcommon hplan.coarse.1 R (weakEntryMmax R) le_rfl c r h.start
  have hkOf3 := (weakTop_request_orders hplan.coarse c).1
  refine weakLifted_of_empty_window c r i h heq (fun v => ?_) X
  have hrep := cdW_isClassicalRep plan (fun {_B} {A} _ => weakTopKOf A) R (weakEntryMmax R) 0 0
    le_rfl hkOf3 (Nat.zero_le _) le_rfl (Nat.zero_le _) c r Uhi i hi hit h (hval i hi hit) v
    (r.tq i) ⟨le_rfl, heq.le⟩
  have hinit := weakCoarseInitial plan R (weakEntryMmax R) 0 (Nat.zero_le _) c r Uhi hvr hval i
    hi hit heq.le v
  have hWF : cdW c (weakEntryMmax R) 0
      (fun w => (Nat.zero_le (R.Kw + weakEntryMmax R)).trans
        (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v (r.tq i) =
      cdF c r (weakEntryMmax R) 0
        (fun w => (Nat.zero_le (R.Kw + weakEntryMmax R)).trans
          (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v :=
    congrArg (fun U => cdReadout c (weakEntryMmax R) 0
      (fun w => (Nat.zero_le (R.Kw + weakEntryMmax R)).trans
        (weakReductionReserve_kw R (weakEntryMmax R) w)) i (fun _ => True) U v)
      (funext fun v' => (hpass i hi hit).2.2.2.1 v')
  have hjet := jet_truncate_of_rep _ _ hrep
  rw [hWF, hinit] at hjet
  refine hjet.trans (Filter.Eventually.of_forall fun x => ?_)
  exact (weakGluedLiftStart ⟨hcommon, hplan.ell⟩ c r i hi hit h _ v x).symm

end AVRegularity.Providers.WeakGen.Window
end
end
end
