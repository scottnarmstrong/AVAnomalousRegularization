-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.CoarseFlux
import AVRegularity.CycleComparison.ActualMeans.Main
import AVRegularity.CycleComparison.Coarse.Defect.Final
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.CycleComparison.QuietDecay.Final.Main
import AVRegularity.CycleComparison.Coarse.Bound.Main
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.SettingTailFluxCoefficientCellBound
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseDefect
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseResponses
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseWitness
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedMean
public import AVRegularity.Statements.Intermediate.CycleOutput.IsMeanPresentation
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseAnalyticEnvelope
import AVRegularity.CycleComparison.LiftMeanEntrywise.Assembly
import AVRegularity.Proofs.Intermediate.CycleComparison.OcFlowJets

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_residual_coarse_flux_presentation`: the sampled lift
of a coarse flux divergence is the identity flux at grade zero plus, at each positive degree, the
cleanup presentation of `cycle_residual_cleanup`. -/

/-- **Cycle residual: presentation of the lift of a coarse flux divergence** (Lemma 12.6 of the
    paper). -/
theorem cycle_residual_coarse_flux_presentation (Acl N D H kl Ll : ℕ) (hA : 1 ≤ Acl)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ)
      (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
      IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N s0 kl Ll qs qf CG Cw Cj b Θ →
      (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (s0 + D + 2) (max (kl + 1) (Ll + 2)) t₀ t₁ N H Cc →
      ∀ hh, hh ≤ H →
      ∀ Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i,
        (∀ t, ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc t x k)) →
        (∀ t, ∀ k, AVenhance.IsZ2Periodic (fun x => Fc t x k)) →
      ∀ Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
        (∀ n, 1 ≤ n → n ≤ N → ∀ τ ∈ Set.Icc t₀ t₁,
          IsCleanupChain s0 (max (kl + 1) (Ll + 2)) Acl (liftApply n (Cc hh n) (fun s X => ∑ k : Fin 2, fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k)) τ) (fun _ _ _ => 0)
            (fun j => Vn n j τ)) →
      ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), ∀ x,
        diagSample (ℓ ^ 2)⁻¹ ρ e (fun s X z => ρ⁻¹ • ∑ n ∈ Finset.range (N + 1),
            εc ^ n • liftApply n (Cc hh n) (fun s X => ∑ k : Fin 2, fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k)) s X z) t x
          = ∑ k : Fin 2, fderiv ℝ (fun x' =>
              (if hh = 0 then Fc t x' k else 0)
                + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x' k)
              x (basisVec k)
            + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x := by
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ kres s0 hkres hs0 hset
    hM Cc hseq hh hhH Fc hFc hFcper Vn hVn t ht x
  have hℓ : 0 < ℓ := by
    rw [hset.ℓ_eq]; exact div_pos hset.e_pos (Real.sqrt_pos.2 hset.ν_pos)
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hρ := hset.ρ_pos
  set τ := (ℓ ^ 2)⁻¹ * t with hτdef
  have hτ : τ ∈ Set.Icc t₀ t₁ := by
    constructor
    · rw [hτdef, le_inv_mul_iff₀ hℓ2]; linarith [ht.1]
    · rw [hτdef, inv_mul_le_iff₀ hℓ2]; linarith [ht.2]
  have hℓτ : ℓ ^ 2 * τ = t := by rw [hτdef]; field_simp
  set g : ℝ → Vec 2 → ∀ i, h i := fun s X => ∑ k : Fin 2,
    fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k) with hg
  have hsZ : 1 ≤ max (kl + 1) (Ll + 2) := by omega
  have hsX : 1 ≤ s0 := by omega
  -- the chains are box smooth
  have hbox : ∀ n ∈ Finset.Icc 1 N, ∀ j, j < Acl → IsBoxSmooth s0 (max (kl + 1) (Ll + 2))
      (Vn n j ((ℓ ^ 2)⁻¹ * t)) := fun n hn =>
    IsCleanupChain.isBoxSmooth (isBoxSmooth_zero _ _)
      (hVn n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 τ hτ)
  -- each positive degree is presented by its cleanup chain
  have hdeg : ∀ n ∈ Finset.Icc 1 N, liftApply n (Cc hh n) g τ (ρ⁻¹ • x) (e⁻¹ • x) =
      ∑ k : Fin 2, fderiv ℝ (fun x' => cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x' k) x
          (basisVec k) + cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x := by
    intro n hn
    have hc := cycle_residual_cleanup Acl s0 (max (kl + 1) (Ll + 2)) hA (by omega) hsZ ρ e
      (ℓ ^ 2)⁻¹ (Set.Icc t₀ t₁) hρ hset.e_pos (fun τ => liftApply n (Cc hh n) g τ)
      (fun _ _ _ _ => 0) (Vn n) (fun _ _ => isBoxSmooth_zero _ _)
      (fun τ' hτ' => hVn n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 τ' hτ') t hτ x
    rw [← hc]
    simp [diagSample, fastPartial, τ]
  -- the identity term
  have hid : ρ⁻¹ • liftApply 0 (Cc hh 0) g τ (ρ⁻¹ • x) (e⁻¹ • x) =
      ∑ k : Fin 2, fderiv ℝ (fun x' => if hh = 0 then Fc t x' k else 0) x (basisVec k) := by
    rw [hseq.liftApply_zero hhH g hτ]
    split_ifs with hh0
    · simp only [hg, hℓτ, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hd : DifferentiableAt ℝ (fun x' => Fc t x' k) (ρ • ρ⁻¹ • x) :=
        ((hFc t k).differentiable (by simp) _)
      rw [fderiv_comp_smul_apply ρ hd, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul,
        smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
    · simp
  -- differentiability for splitting the right side
  have hdid : ∀ k : Fin 2, DifferentiableAt ℝ (fun x' => if hh = 0 then Fc t x' k else 0) x := by
    intro k
    split_ifs
    · exact (hFc t k).differentiable (by simp) _
    · exact differentiableAt_const _
  have hdflux : ∀ k : Fin 2, ∀ n ∈ Finset.Icc 1 N, DifferentiableAt ℝ
      (fun x' => εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x' k) x := fun k n hn =>
    (differentiableAt_cleanupFlux hsX hsZ _ ρ e t (hbox n hn) x k).fun_const_smul _
  have hsplit : ∀ k : Fin 2, fderiv ℝ (fun x' => (if hh = 0 then Fc t x' k else 0)
      + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x' k) x
        (basisVec k) =
      fderiv ℝ (fun x' => if hh = 0 then Fc t x' k else 0) x (basisVec k)
        + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
          fderiv ℝ (fun x' => cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x' k) x (basisVec k) := by
    intro k
    rw [fderiv_fun_add (hdid k) ((DifferentiableAt.fun_sum (hdflux k)).fun_const_smul _),
      fderiv_fun_const_smul (DifferentiableAt.fun_sum (hdflux k)), fderiv_fun_sum (hdflux k)]
    simp only [add_apply, FunLike.coe_smul, FunLike.coe_sum,
      Pi.smul_apply, Finset.sum_apply]
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [fderiv_fun_const_smul (differentiableAt_cleanupFlux hsX hsZ _ ρ e t (hbox n hn) x k)]
    rfl
  -- assemble
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  simp only [diagSample]
  change ρ⁻¹ • ∑ n ∈ Finset.range (N + 1), εc ^ n • liftApply n (Cc hh n) g τ (ρ⁻¹ • x) (e⁻¹ • x) = _
  rw [hrange, Finset.sum_insert h0, Finset.sum_congr rfl fun n hn => by rw [hdeg n hn]]
  simp only [hsplit]
  simp only [pow_zero, one_smul, smul_add, hid, Finset.sum_add_distrib, Finset.smul_sum]
  rw [Finset.sum_comm]
  abel

/-! Proof of `cycle_residual_quiet_mean`, from `cycle_residual_quiet_mean_of_fastOrder`. -/

/-- **Cycle residual: the exact quiet mean** (Proposition 9.6(d) and Lemma 12.5 of the paper). -/
theorem cycle_residual_quiet_mean (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (hDsZ : D ≤ max (k + 1) (L + 2)) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
      IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
      ∀ S : Set ℝ, S ⊆ Set.Icc t₀ t₁ →
        IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S →
      ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ hh, hh ≤ H →
        ∀ n, 2 ≤ n → n ≤ N + D → ∀ t ∈ S, ∀ X,
          liftMean Q Cc (fun _ => a₀) hh n t X
            = if hh = 0 then (if n = 2 then cellB2 Q.η Q.G t (fun X' _ => a₀ X') X 0 else 0)
              else if hh = 1 then -sourceCoeff Q.edge Q.η n t (fun X' _ => a₀ X') X 0
              else 0 :=
  AVRegularity.cycle_residual_quiet_mean_of_fastOrder N K k L D H CG Cw Cj hDsZ

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Exact diagonal mean identities for every lift sequence. -/

/-- **Cycle lift: the diagonal means** (Proposition 9.6(a) of the paper). -/
theorem cycle_lift_means_diagonal (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
          liftMean Q Cc (fun _ => a₀) 0 2 t X
            = ∑ k : Fin 2, fderiv ℝ (fun X' =>
                fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k) •
                    liftApply 1 (Cc 0 1) (fun _ => a₀) t X' z)
                  - Q.η • ∑ j : Fin 2, Q.G t X' k j • fderiv ℝ a₀ X' (basisVec j)) X (basisVec k) ∧
          (∀ n, 3 ≤ n → n ≤ N + 1 →
            liftMean Q Cc (fun _ => a₀) 0 n t X
              = ∑ k : Fin 2, fderiv ℝ (fun X' =>
                  fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k) •
                    liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => a₀) t X' z)) X (basisVec k)) ∧
          (∀ n, N + 2 ≤ n → n ≤ N + D → liftMean Q Cc (fun _ => a₀) 0 n t X = 0) :=
  by
    intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ P Cc hseq a₀ ha₀ t ht X
    have hX : 2 ≤ K + D + 2 := by omega
    have hZ : 2 ≤ max (k + 1) (L + 2) := by omega
    refine ⟨CycleComparison.Lift.liftMean_diagonal_second P _ _ hX hZ Cc hseq a₀ ha₀ t ht X, ?_, ?_⟩
    · intro n hn _
      exact CycleComparison.Lift.liftMean_diagonal_ge_three P _ _ hX hZ Cc hseq a₀ ha₀ n hn t ht X
    · intro n hn _
      exact CycleComparison.Lift.liftMean_diagonal_above_cutoff P _ _ hX hZ Cc hseq a₀ ha₀ n hn t ht X

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_residual_bound`, from `cycle_residual_bound_of_measurable`. -/

/-- **Cycle residual: presentation and bound of the lift tail** (Lemma 12.4 of the paper). -/
theorem cycle_residual_bound (Acl N D H kl Ll : ℕ) (hA : 1 ≤ Acl)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CL : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ)
        (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N s0 kl Ll qs qf CG Cw Cj b Θ →
        (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (s0 + D + 2) (max (kl + 1) (Ll + 2)) t₀ t₁ N H Cc →
        ∀ (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h) (hh : ℕ), hh ≤ H →
          (∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
            IsLiftTailPresentation Q Cc (s0 + D + 2) (max (kl + 1) (Ll + 2)) π t₀ t₁ N s0 CL Θ hh n (f n) (F n)) →
        ∀ a : ℝ → Vec 2 → ∀ i, h i,
          (∀ t, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (a t)) → (∀ t, AVenhance.IsZ2Periodic (a t)) →
          (∀ j, j ≤ kres + 1 → ∀ (w : DerivativeWord2 j) (v : ι), Measurable
            (fun p : ℝ × Vec 2 => ‖orderedDerivative w (fun x => a p.1 x v) p.2‖ₑ)) →
        ∀ Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ τ ∈ Set.Icc t₀ t₁,
            IsCleanupChain s0 (max (kl + 1) (Ll + 2)) Acl (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ)
              (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) (fun j => Vc j τ)) →
        ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
          residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
              (fun t x k => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl Vc t x k)
              (fun t x => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl Vc t x)
            ≤ ENNReal.ofReal (C * Θ ^ hh * εc ^ N * (1 + Z)) *
              classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres a :=
  AVRegularity.cycle_residual_bound_of_measurable Acl N D H kl Ll hA CG Cw Cj CL

/-! Proof of `cycle_comparison_actual_means`, from
`AVRegularity.CycleComparison.ActualMeans.actual_means`. -/

/-- **The actual means in the Eulerian frame.** -/
theorem cycle_comparison_actual_means (N D H Kt : ℕ) (hD : 2 ≤ D) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (T₀ T₁ c ρ εc lam Rχ : ℝ)
        (Q : ℤ → LiftOperatorData ι h D) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
        (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
        (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
        (Ls : ℤ → ℕ → (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
        1 ≤ Kt → 0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ →
        (∀ i j, Measurable fun t => Jm t i j) →
        -- the time partition: measurable, and active only inside the lift windows
        (∀ k ∈ kset, Measurable (ϖ k)) →
        (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k)) →
        -- exact volume-preserving, lattice-equivariant, smooth charts (qualitative)
        (∀ k ∈ kset, ∀ t y, label k t (chart k t y) = y) →
        (∀ k ∈ kset, ∀ t x, chart k t (label k t x) = x) →
        (∀ k ∈ kset, ∀ t (p : Fin 2 → ℤ) y,
          chart k t (y + AVenhance.latticeShift p) = chart k t y + AVenhance.latticeShift p) →
        (∀ k ∈ kset, ∀ t y, (jacMatrix (chart k t) y).det = 1) →
        (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => chart k q.1 q.2)) →
        (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => label k q.1 q.2)) →
        -- normalized chart jets at the chart scale `Rχ`, on the lift window of the pulse
        (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
          ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
          ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
        -- the chart-frame mean letters of every pulse
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
              liftMean (Q k) (Cc k) (fun _ => a₀) r n s X =
                meanApply n (Lb k r n) (fun _ => a₀) s X) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
              ContDiff ℝ (Kt : ℕ∞) (fun X => Lb k r n d α s X k₀ v u)) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
            Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lb k r n d α s X k₀ v u)) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ (p : Fin 2 → ℤ) (X : Vec 2),
              Lb k r n d α s (X + ρ⁻¹ • AVenhance.latticeShift p) k₀ v u =
                Lb k r n d α s X k₀ v u) →
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            (∀ v, Lb k 0 n d α s X k₀ v v = Ls k n d α s X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
            (∀ v u, v ≠ u → Lb k 0 n d α s X k₀ v u = 0)) →
      ∃ (AD : ∀ d : Finset.Icc 2 (N + D), ℝ → Vec 2 →
            PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (N + D)), ℝ → Vec 2 →
            (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
              (PiLp 2 (fun _ : Fin 2 => h v))),
        -- (1) the Eulerian presentation of the glued mean of every grade
        (∀ r, r ≤ H → IsMeanPresentation (Set.Icc T₀ T₁) (N + D) r AD CE Jm
          (gluedMean kset ϖ c ρ εc N r Q Cc chart label)) ∧
        -- (2) the flux identity: the letters are the glued Piola transports of the
        --     dimensional chart-frame fluxes (at `r = 0`, minus the `Jm` part)
        (∀ r, r ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) →
          ∀ t ∈ Set.Icc T₀ T₁, ∀ x (v : ι) (k' : Fin 2),
            classicalGradeFlux (N + D) r AD CE Jm a v t x k' =
              -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 (N + D), (c⁻¹ * εc ^ n) •
                ∑ l : Fin 2, jacMatrix (chart k t) (label k t x) k' l •
                  ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
                    Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
                      (orderedDerivative α (fun y => a t (chart k t y)) (label k t x) u)) ∧
        -- (3) regularity of the diagonal letters
        (∀ d, ∀ t ∈ Set.Icc T₀ T₁, ContDiff ℝ (Kt : ℕ∞) (AD d t)) ∧
        (∀ d, Measurable fun q : Set.Icc T₀ T₁ × Vec 2 => AD d q.1 q.2) ∧
        (∀ d, ∀ t ∈ Set.Icc T₀ T₁, AVenhance.IsZ2Periodic (AD d t)) ∧
        -- (3') regularity of the edge letters
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc T₀ T₁,
          ContDiff ℝ (Kt : ℕ∞) (CE r v u d t)) ∧
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d,
          Measurable fun q : Set.Icc T₀ T₁ × Vec 2 => CE r v u d q.1 q.2) ∧
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc T₀ T₁,
          AVenhance.IsZ2Periodic (CE r v u d t)) ∧
        -- (4) the entrywise transfer bound through the chart jets
        (∀ r, 1 ≤ r → r ≤ H → ∀ (v u : ι) (M : ℝ), 0 ≤ M →
          (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
            ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ i, i ≤ Kt →
              ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
                ‖iteratedFDeriv ℝ i (fun X' => Lb k r n d α s X' k₀ v u) X‖ ≤
                  M * lam ^ (n - d + i)) →
          ∀ (d : Finset.Icc 2 (N + D)) (j : ℕ), j ≤ Kt → ∀ t ∈ Set.Icc T₀ T₁, ∀ x,
            ‖coefficientDerivativeArray (CE r v u d t) j x‖ ≤
              C * M * (∑ k ∈ kset, |ϖ k t|) *
                ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1)) :=
  CycleComparison.ActualMeans.actual_means N D H Kt hD Cχ

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers

/-! Proof of `cycle_coarse_defect`: the exact defects
`(M I - E) W = div F_coarse`, `W(t₀) = f` for the retained field and flux of every coarse response
family. The witness is the `𝖯_p`-adjoint of the total response and the combination of the formal
adjoints of the parts of the dual flux expression. The identity holds for smooth tests by the
product rule in time, the conjugation identity `(∂_t - 𝒞)𝖯_p = 𝖯_p(∂_t - 𝒞) + …` at each time and
the response system summed over the box of cells; it extends to first-order tests by density of
the Galerkin projections. -/

/-- **Coarse comparison: the exact defects**. -/
theorem cycle_coarse_defect (D H p J k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B₀ Cstar Θ : ℝ), 1 ≤ B₀ → 0 ≤ Cstar → 0 ≤ Θ →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (t₀ t₁ ρ B a lam : ℝ) (b : ℝ → Vec 2 → Vec 2) (L N : ℕ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => h v)))
        (π : ι → ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ →
        ∀ (f : ∀ v, TorusHk N (h v))
          (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
          (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
          (G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
            (PiLp 2 (fun _ : Fin 2 => h v))),
          IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G →
          ∃ (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
            (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))),
            IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc ∧
            IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc :=
  by
    refine ⟨0, le_rfl, ?_⟩
    intro B₀ Cstar Θ _ _ _ ι _ _ h _ _ _ _ _ _ t₀ t₁ ρ B a lam b L N Jm AD CE π Aedge P f U Uw G
      hR
    obtain ⟨W, Fc, hWit⟩ := CycleComparison.Coarse.exists_coarse_witness P U
    exact ⟨W, Fc, hWit, CycleComparison.Coarse.coarseDefect_of_witness P hR hWit⟩

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_comparison_lift_setting`, from
`AVRegularity.CycleComparison.LiftSetting.lift_setting`. -/

/-- **The lift setting of every observed pulse.** -/
theorem cycle_comparison_lift_setting (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ (Λ₀ : ℕ) (Cw : ℕ → ℝ), 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (g₀ Ca : ℝ) (CG : ℕ → ℝ), g₀ ≤ 1 / 4 → ∃ CGl : ℕ → ℝ,
      ∀ (H D N K k L qs qf Ks Ls qJ Kmax : ℕ), 2 ≤ D → 1 ≤ N →
        qs = K + 4 * (H + 1) * (N + D) ^ 2 →
        qf = max k (L + 2) + H * D + 2 * N + 2 * D →
        qs ≤ Ks → qf ≤ Ls → qs ≤ qJ →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmM : m ≤ M') (ν B : ℝ) (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1))) (tp Tobs ρs g a B₀ lam₀ Cb : ℝ)
        (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) ρs g g₀ a B₀ lam₀ Cb
          qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hmeas : F.IsTimeMeasurable)
        (b : ι → ι → ℝ) (S : ℝ) (_hb : ∀ v u, 0 ≤ b v u)
        (_hrow : ∀ v, ∑ u, b v u ≤ S) (_hcol : ∀ u, ∑ v, b v u ≤ S)
        (_hpointwiseAn : IsPointwiseAnalyticEnvelope F π
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) (ocEpsilon q Λ (m - 1))
          Ca Ks Ls b)
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp (tp + Tobs))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
        (pp : ℤ → P') (k₁ : ℤ) (_hk₁ : k₁ ∈ ocObsPulses α q Λ m tp (tp + Tobs))
        (_hout : ocPulseWindow α q Λ m k₁ ∩ Set.Icc tp (tp + Tobs) ⊆
          (F.piece (pp k₁)).output),
        ∃ (par : Fin 2) (V : ℝ → ℝ → ℝ),
          IsLiftSetting
            (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
              (Real.sqrt (B * ocTauPP α q Λ m))
              (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k₁
              (F.fiber (pp k₁) (actual (pp k₁)))) π
            (max (((k₁ : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
            (min (((k₁ : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2)
            (ocEpsilon q Λ m) ν B (Real.sqrt (B * ocTauPP α q Λ m)) (ocEpsilon q Λ (m - 1))
            (ocEll q Λ m ν) (ocDStar q Λ m ν B)
            (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))
            par V H N K k L qs qf CGl Cw (fun _ _ => Ca) b S :=
  CycleComparison.LiftSetting.lift_setting α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_residual_partition_differentiated` (Lemma 12.5 of the paper), with its
statement spelled out, from `AVRegularity.QuietDecay.statement` (the quiet-gap decay of the lift
recursion). -/

/-- **Differentiated partition source, one transition**. -/
theorem cycle_residual_partition_differentiated (Acl N D H kl Ll : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    1 ≤ Acl →
    ∀ r : ℕ, ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ rs E ℓ dstar εc lam : ℝ)
        (_hrs : 0 < rs) (_hrse : rs ≤ e) (_heρ : e ≤ ρ)
        (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ) (b : ι → ι → ℝ) (Θ : ℝ) (kres s0 : ℕ),
        kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V
          H N (s0 + r + D * (H + 1) * N) (kl + r + D * (H + 1) * N)
          (Ll + r + D * (H + 1) * N) qs qf CG Cw Cj b Θ →
        (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequenceFrom Q (s0 + r + D * (H + 1) * N + D + 2)
          (max (kl + r + D * (H + 1) * N + 1) (Ll + r + D * (H + 1) * N + 2))
          t₀ t₁ N H Cc →
        ∀ g d : ℝ, 0 < d → ℓ ^ 2 * t₀ ≤ g → g + d ≤ ℓ ^ 2 * t₁ →
        IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z)
          (Set.Icc (g / ℓ ^ 2) ((g + d) / ℓ ^ 2)) →
        ∀ I : ℕ → ℝ,
        HasQuietEntranceTrace π Cc (g / ℓ ^ 2) lam N H
          (s0 + r + D * (H + 1) * N) (max (kl + r) (Ll + r + 2) + D * (H + 1) * N) I →
        ∀ (ψ : ℝ → ℝ) (M δ : ℝ), 0 ≤ δ → δ ≤ d →
        (∀ t, |ψ t| ≤ M) → Function.support ψ ⊆ Set.Icc (g + δ) (g + d) →
        ∀ hh, hh ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i,
        (∀ t, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t)) →
        (∀ t, AVenhance.IsZ2Periodic (a t)) →
        ∀ j : ℕ, j ≤ r → ∀ β : DerivativeWord2 j,
          residualNorm ν π (Set.Icc g (g + d)) (fun _ _ _ => 0)
            (fun t x => rs ^ j • orderedDerivative β
              (transitionSourceField N hh ℓ ρ e εc ψ Cc a t) x)
          ≤ ENNReal.ofReal
              (C * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
                M * ℓ * Real.sqrt d * Real.exp (-(c * δ / ℓ ^ 2))) *
            classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (kres + r) a :=
  AVRegularity.QuietDecay.statement Acl N D H kl Ll CG Cw Cj

/-! Proof of `cycle_coarse_exists`: the finite causal coarse family
of genuine second-order energy solutions exists. Each response flux is the formal adjoint of the
flux operators applied to the predecessors (square integrable in time), and each response is the
solution given by the coupled energy theorem `coupled_energy_torus` with that flux. -/

/-- **Coarse comparison: existence of the coarse vector**. -/
theorem cycle_coarse_exists (D H p J k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B₀ Cstar Θ : ℝ), 1 ≤ B₀ → 0 ≤ Cstar → 0 ≤ Θ →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (t₀ t₁ ρ B a lam : ℝ) (b : ℝ → Vec 2 → Vec 2) (L N : ℕ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => h v)))
        (π : ι → ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ →
        ∀ f : ∀ v, TorusHk N (h v),
          ∃ (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
            (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
            (G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
              (PiLp 2 (fun _ : Fin 2 => h v))),
            IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G :=
  by
    refine ⟨0, le_rfl, ?_⟩
    intro B₀ Cstar Θ _ _ _ ι _ _ h _ _ _ _ _ _ t₀ t₁ ρ B a lam b L N Jm AD CE π Aedge P f
    exact CycleComparison.Coarse.coarseResponses_of_cellFlux P
      (fun _ hi _ hj => CycleComparison.Coarse.hasCellFlux_of_setting P hi hj) f

/-! Proof of `cycle_coarse_word_energy`: the binomial word energy bound
`𝓔(U_{i,h}) ≤ 4 binom(i+h,i) (4q₀)^i (4q₁)^h |f|_{ρ,N;π}` for every coarse response family. Each
cell obeys the letter recursion: its energy is bounded by its initial datum and its response flux,
the flux is the gradient-form adjoint of the flux operators applied to the predecessors and
so is bounded by their gradient energies (mass-weighted Schur test for the edges), and the
recursion closes by Pascal's identity. -/

/-- **Coarse comparison: the letter sizes and the word energy**. -/
theorem cycle_coarse_word_energy (D H p J k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B₀ Cstar Θ : ℝ), 1 ≤ B₀ → 0 ≤ Cstar → 0 ≤ Θ →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (t₀ t₁ ρ B a lam : ℝ) (b : ℝ → Vec 2 → Vec 2) (L N : ℕ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => h v)))
        (π : ι → ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ →
        ∀ (f : ∀ v, TorusHk N (h v))
          (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
          (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
          (G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
            (PiLp 2 (fun _ : Fin 2 => h v))),
          IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G →
          ∀ q₀ q₁ : ℝ,
            q₀ = C * (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
            + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
                (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) →
            q₁ = C * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r) →
            ∀ i, i ≤ J → ∀ j, j ≤ H →
              strongEnergy ρ B π t₀ t₁ (U i j) (Uw i j)
                ≤ ENNReal.ofReal (4 * (Nat.choose (i + j) i : ℝ) * (4 * q₀) ^ i * (4 * q₁) ^ j *
                  Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) :=
  by
    refine ⟨CycleComparison.Coarse.wordConst D H p J k,
      CycleComparison.Coarse.wordConst_nonneg D H p J k, ?_⟩
    intro B₀ Cstar Θ _ hC hΘ ι _ _ h _ _ _ _ _ _ t₀ t₁ ρ B a lam b L N Jm AD CE π Aedge P f U Uw G
      hR q₀ q₁ hq₀ hq₁ i hi j hj
    exact CycleComparison.Coarse.word_energy P hC hΘ hR hq₀ hq₁ hi hj

/-! Proof of `cycle_coarse_defect_bound`: the defect bounds for the retained pair of every coarse
response family, with the explicit constant `boundC D H p J k`.

* The retained field is the `𝖯_p`-adjoint of the total response; its value and gradient energies
  are bounded cell by cell through the factorial bound of `𝖯_p` (whose cost is uniform since
  `‖H_cov‖ ≤ ρ²`), and the cells by the binomial word energies.
* The retained flux is, at almost every time, the sum of the gradient-form adjoints of
  `F_p^*(I - 𝖰_p𝖯_p)`, `𝖯_p F_E^*(I - 𝖰_p𝖯_p)`, `F_p^*` and the Taylor flux applied to the
  truncated response sums; the terminal edge part vanishes by acyclicity (support induction with
  uniqueness of the responses). In `I - 𝖰_p𝖯_p` the degrees `1, …, p` cancel, so its cost carries
  `ω^{p+1}`; the Taylor part costs `k₀ ω^p`. The mass-weighted Schur test controls the edge part,
  and the time integral is bounded by the gradient energies of the cells. -/

/-- **Coarse comparison: the defect bounds**. -/
theorem cycle_coarse_defect_bound (D H p J k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B₀ Cstar Θ : ℝ), 1 ≤ B₀ → 0 ≤ Cstar → 0 ≤ Θ →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (t₀ t₁ ρ B a lam : ℝ) (b : ℝ → Vec 2 → Vec 2) (L N : ℕ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => h v)))
        (π : ι → ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ →
        ∀ (f : ∀ v, TorusHk N (h v))
          (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
          (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
          (G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
            (PiLp 2 (fun _ : Fin 2 => h v))),
          IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G →
          ∀ (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
            (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))),
            IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc →
            ∀ q₀ q₁ : ℝ,
              q₀ = C * (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
            + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
                (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) →
              q₁ = C * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r) →
              ∀ Sig ω k₀ : ℝ,
                Sig = ∑ i ∈ Finset.range (J + 1), ∑ j ∈ Finset.range (H + 1),
                  (Nat.choose (i + j) i : ℝ) * (4 * q₀) ^ i * (4 * q₁) ^ j →
                ω = (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / ρ ^ 2 →
                k₀ = (matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁).toReal / B →
                strongEnergyUpTo ρ B π t₀ t₁ k W
                    ≤ ENNReal.ofReal (C * Sig *
                      Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) ∧
                ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal
                    (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
                      (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ)
                  ≤ ENNReal.ofReal (C * Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val)) *
                    ((ω ^ (p + 1) * (q₀ + q₁) + k₀ * ω ^ p) * Sig
                      + q₀ * ∑ j ∈ Finset.range (H + 1),
                        (Nat.choose (J + j) J : ℝ) * (4 * q₀) ^ J * (4 * q₁) ^ j)) :=
  by
    refine ⟨CycleComparison.Coarse.boundC D H p J k,
      CycleComparison.Coarse.boundC_nonneg D H p J k, ?_⟩
    intro B₀ Cstar Θ _ hC hΘ ι _ _ h _ _ _ _ _ _ t₀ t₁ ρ B a lam b L N Jm AD CE π Aedge P f U Uw G
      hR W Fc hWit q₀ q₁ hq₀ hq₁ Sig ω k₀ hSig hω hk₀
    exact CycleComparison.Coarse.coarse_defect_bound_main P hC hΘ hR hWit hq₀ hq₁ hSig hω hk₀

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Positive lifts and their means annihilate constants, and all first means vanish. -/

/-- **Cycle lift: structure of the recursion** (Proposition 9.6(a) and Lemma 12.2 of the paper). -/
theorem cycle_lift_structure (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        (∀ c0 : ∀ i, h i, ∀ hh, hh ≤ H → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
          (∀ n, 1 ≤ n → n ≤ N → liftApply n (Cc hh n) (fun _ _ => c0) t X z = 0) ∧
          (∀ n, 2 ≤ n → n ≤ N + D → liftMean Q Cc (fun _ _ => c0) hh n t X = 0)) ∧
        (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ hh, hh ≤ H →
          ∀ t ∈ Set.Icc t₀ t₁, ∀ X, liftMean Q Cc (fun _ => a₀) hh 1 t X = 0) :=
by
  classical
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  constructor
  · intro c0 hh hhh t ht X z
    constructor
    · intro n hn _
      exact congrFun (congrFun
        (CycleComparison.Lift.liftSequence_constants_zero P _ _ Cc hseq c0 hh hhh n hn t ht) X) z
    · intro n hn _
      exact congrFun
        (CycleComparison.Lift.liftSequence_constant_means_zero P _ _ Cc hseq c0 hh hhh n (by omega) t ht) X
  · intro a₀ ha₀ hh hhh t ht X
    by_cases hh0 : hh = 0
    · subst hh
      exact CycleComparison.Lift.liftMean_first_diagonal_zero P _ _ Cc hseq a₀ ha₀ t ht X
    · exact CycleComparison.Lift.liftMean_first_positive_zero_ambient P _ _ (by omega)
        Cc hseq a₀ ha₀ hh (by omega) hhh t ht X

/-! The exact positive-grade mean identity and constant-input flux cancellation. -/

/-- **Cycle lift: the means at positive source degree** (Proposition 9.6(a) of the paper). -/
theorem cycle_lift_means_source (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ hh, 1 ≤ hh → hh ≤ H →
          ∀ n, 2 ≤ n → n ≤ N + D → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
            liftMean Q Cc (fun _ => a₀) hh n t X
              = -∑ k : Fin 2, fderiv ℝ (fun X' =>
                  Real.sqrt Q.η • fieldCellMean (fun z =>
                    sourceFluxCoeff Q.edge Q.η (n - 1) t
                      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => a₀) t) k X' z)
                  - fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k) •
                    liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t X' z)) X (basisVec k)) ∧
        (∀ c0 : ∀ i, h i, ∀ hh, 1 ≤ hh → hh ≤ H → ∀ j, j ≤ N + D → ∀ t ∈ Set.Icc t₀ t₁,
          ∀ k X z, sourceFluxCoeff Q.edge Q.η j t
            (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ _ => c0) t) k X z = 0) :=
  by
    classical
    intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq
    let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
    have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
    constructor
    · intro a₀ ha₀ hh hhpos hhh n hn _ t ht X
      exact CycleComparison.Lift.setting_positive_mean_flux_difference P _ _ (by omega) (by omega)
        Cc hseq hh hhpos hhh n hn a₀ ha₀ t ht X
    · intro c0 hh _ hhh j _ t ht k X z
      exact congrFun (congrFun
        (CycleComparison.Lift.liftPolynomial_sourceFluxCoeff_const P _ _ Cc hseq
          c0 (hh - 1) (by omega) j t ht k) X) z

/-! Entrywise path-product bounds for the lift means. -/

/-- **Entrywise path-product bounds for the lift means** (Proposition 9.7(c) of the paper). -/
theorem cycle_lift_mean_entrywise (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∃ Lb : MeanCoeff ι h,
            -- (a) word symmetry
            (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
              Lb d (α ∘ σ) = Lb d α) ∧
            -- (b) slow regularity on the window
            (∀ d α k₀ v u, ∀ t ∈ Set.Icc t₀ t₁,
              ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun X => Lb d α t X k₀ v u)) ∧
            -- (c) time measurability on the window, for each slow position
            (∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
              Measurable (fun t : Set.Icc t₀ t₁ => Lb d α t X k₀ v u)) ∧
            -- (d) the divergence-form presentation of the mean `L_n^{(hh)}`
            (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
              liftMean Q Cc (fun _ => a₀) hh n t X = meanApply n Lb (fun _ => a₀) t X) ∧
            -- (e) entrywise path-product bound, pointwise in `t` on the window
            (∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
              ∀ j, j ≤ K + 1 → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
                ‖iteratedFDeriv ℝ j (fun X' => Lb d α t X' k₀ v u) X‖ ≤
                  C * ((Matrix.of fun v' u' => b v' u' / Real.sqrt (π u' / π v')) ^ hh) v u *
                    lam ^ (n - d + j)) ∧
            -- (f) source degree zero: scalar diagonal, `L_n^{(0)} = M_n I`
            (hh = 0 → ∃ Ls : (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ,
              ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2),
                ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
                  (∀ v, Lb d α t X k₀ v v = Ls d α t X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
                  (∀ v u, v ≠ u → Lb d α t X k₀ v u = 0)) ∧
            -- (g) invariance under slow translations of the data
            (∀ T : Vec 2, (∀ t X i j, Q.G t (X + T) i j = Q.G t X i j) →
              (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
                γ.coeff α t (X + T) z = γ.coeff α t X z) →
              ∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
                ∀ t ∈ Set.Icc t₀ t₁, ∀ X, Lb d α t (X + T) k₀ v u = Lb d α t X k₀ v u) := by
  refine ⟨CycleComparison.Lift.ambientMeanGradeConstant K N k L D H CG Cw Cj,
    CycleComparison.Lift.ambientMeanGradeConstant_nonneg K N k L D H CG Cw Cj, ?_⟩
  intro ι _ _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ P Cc hseq
    hh hhh n hn hnR
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  exact CycleComparison.LiftMeanEntrywise.setting_lift_mean_entrywise P Cc hseq hh hhh n hn hnR

/-! Fixed-reserve lift grading in the literal energy and Wiener norms. -/

/-- **Cycle lift: regularity and grading of the lifts** (Proposition 9.7(a) of the paper). -/
theorem cycle_lift_grading (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ K →
          schurEnergyJet π (Set.Icc t₀ t₁) k j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j)) ∧
          schurWienerJet π (Set.Icc t₀ t₁) L j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j)) :=
by
  obtain ⟨C, hC, hg⟩ := CycleComparison.Lift.cycle_lift_grading_upto K N K k L D H CG Cw Cj
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq
  exact (hg Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P
    (CycleComparison.Lift.setting_ambient_output_supported P) Cc hseq).1

/-! Actual divergence coefficients with uniform slow grading. -/

/-- **Cycle lift: the means in divergence form** (Propositions 9.6(a) and 9.7(b) of the paper). -/
theorem cycle_lift_mean_grading (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∃ Lb : MeanCoeff ι h,
            (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))), Lb d (α ∘ σ) = Lb d α) ∧
            (∀ d α k v u, ∀ t ∈ Set.Icc t₀ t₁,
              ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun X => Lb d α t X k v u)) ∧
            (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
              liftMean Q Cc (fun _ => a₀) hh n t X = meanApply n Lb (fun _ => a₀) t X) ∧
            (∀ d, 2 ≤ d → d ≤ n → ∀ j, j ≤ K →
              schurSlowJet π (Set.Icc t₀ t₁) j
                (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => Lb d p.1 t X p.2)
                ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - d + j))) :=
by
  obtain ⟨C, hC, hg⟩ := CycleComparison.Lift.cycle_lift_grading_upto K N K k L D H CG Cw Cj
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq
  exact (hg Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P
    (CycleComparison.Lift.setting_ambient_output_supported P) Cc hseq).2

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.Providers

/-! Physical divergence coefficients and their factorial Schur bounds restore the normalized mean grading. -/

/-- **Cycle lift: the restored dimensions** (Proposition 9.7(b) and display (12.7) of the paper). -/
theorem cycle_lift_dimensional (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∃ Bp : MeanCoeff ι h,
            (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))), Bp d (α ∘ σ) = Bp d α) ∧
            (∀ d α k v u, ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
              ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun x => Bp d α t x k v u)) ∧
            (∀ ap : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ap t)) →
              ∀ τ ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), ∀ x,
                ((ℓ ^ 2)⁻¹ * εc ^ n) • liftMean Q Cc (fun s X => ap (ℓ ^ 2 * s) (ρ • X)) hh n
                    (τ / ℓ ^ 2) (ρ⁻¹ • x)
                  = meanApply n Bp ap τ x) ∧
            (∀ d, 2 ≤ d → d ≤ n →
              schurFactorialJet π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) E K
                (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => Bp d p.1 t X p.2)
                ≤ ENNReal.ofReal (C * Θ ^ hh * B * dstar ^ (n - 2) * (E ^ d / E ^ n))) :=
by
  obtain ⟨C, hC, hg⟩ := cycle_lift_mean_grading N K k L D H CG Cw Cj
  refine ⟨((K + 1 : ℕ) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq hh hhh n hn hnR
  obtain ⟨b₀, hsym, hreg, hact, hbound⟩ :=
    hg Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq hh hhh n hn hnR
  let Bp := scaledMeanCoefficient ((ℓ ^ 2)⁻¹ * εc ^ n) ρ (fun t => t / ℓ ^ 2) b₀
  refine ⟨Bp, ?_, ?_, ?_, ?_⟩
  · exact scaledMeanCoefficient_perm _ _ _ b₀ hsym
  · intro d α k₀ v u t ht
    exact scaledMeanCoefficient_contDiff _ _ _ b₀ (K + 1) d α t k₀ v u
      (hreg d α k₀ v u (t / ℓ ^ 2) (setting_physical_time_mem P t ht))
  · exact setting_physical_mean_action P Cc hh n b₀ hact
  · intro d hd hdn
    rcases isEmpty_or_nonempty ι with hι | hι
    · have := hι
      simp [schurFactorialJet, schurSums]
    · have := hι
      have hΘ : 0 ≤ Θ := (Finset.sum_nonneg (fun u _ =>
        P.envelope.nonneg (Classical.choice hι) u)).trans (P.envelope.row_sum (Classical.choice hι))
      exact setting_dimensional_factorial_bound P b₀ C hC hΘ hh n d hn hdn
        (hreg d) (hbound d hd hdn)

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! The exact truncated lift identity, with its explicit mean-zero tail and measurable-time primitive. -/

/-- **Cycle lift: the exact identity** (Lemma 12.2 of the paper). -/
theorem cycle_lift_identity (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ hh, hh ≤ H →
          (∀ n, N + 1 ≤ n → n ≤ 2 * N + D → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
            fieldCellMean (fun z => liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z) = 0) ∧
          ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
            IntervalIntegrable (fun s =>
                -(cellOperator (Q.G s X) (Q.v s) (fun z' => liftPolyField Cc N εc hh (fun _ => a₀) s X z') z
                  + εc • cellB1 Q.η Q.G Q.v s (liftPolyField Cc N εc hh (fun _ => a₀) s) X z
                  + εc ^ 2 • cellB2 Q.η Q.G s (liftPolyField Cc N εc hh (fun _ => a₀) s) X z)
                + (if hh = 0 then 0 else
                    sourceOp Q.edge Q.η εc s (liftPolyField Cc N εc (hh - 1) (fun _ => a₀) s) X z)
                + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
                    liftPolyField Cc N εc p.1 (liftMeanPoly Q Cc N εc (fun _ => a₀) p.2) s X z
                + ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
                    εc ^ n • liftTailCoeff Q Cc N (fun _ => a₀) hh n s X z) volume t₀ t ∧
            liftPolyField Cc N εc hh (fun _ => a₀) t X z - (if hh = 0 then a₀ X else 0)
              = ∫ s in t₀..t,
                  (-(cellOperator (Q.G s X) (Q.v s) (fun z' => liftPolyField Cc N εc hh (fun _ => a₀) s X z') z
                    + εc • cellB1 Q.η Q.G Q.v s (liftPolyField Cc N εc hh (fun _ => a₀) s) X z
                    + εc ^ 2 • cellB2 Q.η Q.G s (liftPolyField Cc N εc hh (fun _ => a₀) s) X z)
                  + (if hh = 0 then 0 else
                      sourceOp Q.edge Q.η εc s (liftPolyField Cc N εc (hh - 1) (fun _ => a₀) s) X z)
                  + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
                      liftPolyField Cc N εc p.1 (liftMeanPoly Q Cc N εc (fun _ => a₀) p.2) s X z
                  + ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
                      εc ^ n • liftTailCoeff Q Cc N (fun _ => a₀) hh n s X z) :=
  by
    classical
    intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq a₀ ha₀ hh hhh
    let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
    have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
    have hsX : 2 ≤ K + D + 2 := by omega
    have hsZ : 2 ≤ max (k + 1) (L + 2) := by omega
    constructor
    · intro n hn _ t ht X
      exact CycleComparison.Lift.setting_liftTailCoeff_mean_zero P _ _ hsX hsZ
        Cc hseq hh hhh n (by omega) a₀ ha₀ t ht X
    · intro t ht X z
      obtain ⟨hi, he⟩ := CycleComparison.Lift.setting_liftPoly_time_integral P _ _ hsX hsZ
        Cc hseq hh hhh εc a₀ ha₀ t ht X z
      have hR s (hs : s ∈ Set.uIcc t₀ t) :=
        CycleComparison.Lift.setting_liftPositiveTimeRhs_identity P _ _ hsX hsZ Cc hseq
          hh hhh εc a₀ ha₀ s (by
            rw [Set.uIcc_of_le ht.1] at hs
            exact ⟨hs.1, hs.2.trans ht.2⟩) X z
      refine ⟨hi.congr (fun s hs => hR s (Set.uIoc_subset_uIcc hs)), ?_⟩
      rw [he]
      exact intervalIntegral.integral_congr hR

end AVRegularity.Providers
end
end
