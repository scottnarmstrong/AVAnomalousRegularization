-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.TailPresentation.ArraysProof
import AVRegularity.CycleComparison.Lift.SettingTailFluxCoefficientCellBound
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
import AVRegularity.CycleComparison.Residual.CoarseFlux.Main
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.Main

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_lift_tail_constructed`: the constructed centered
tail arrays (`TailPresentation.arrays_statement_holds`) satisfy every clause of
`IsConstructedLiftTailPresentation` (`TailPresentation.o6_of_arrays`). -/

/-- **The constructed tail presentation and its slow bound**. -/
theorem cycle_lift_tail_constructed (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
          ∃ (f : LiftCoeff ι h) (F : Fin 2 → LiftCoeff ι h),
            IsConstructedLiftTailPresentation Q Cc (max (k + 1) (L + 2)) π t₀ t₁ N K C Θ
              hh n f F :=
  CycleComparison.TailPresentation.o6_of_arrays N K k L D H CG Cw Cj
    (CycleComparison.TailPresentation.arrays_statement_holds N K k L D H CG Cw Cj)

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Metric stability of the actual height-zero lift and its divergence-form mean arrays. -/

open AVRegularity.CycleComparison.Lift

/-- **Cycle lift: metric stability**. -/
theorem cycle_lift_metric_stability (N K k L D : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (CGI : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ g : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj b Θ →
        0 ≤ g →
        (∀ r, r ≤ qs →
          (⨆ t ∈ Set.Icc t₀ t₁, ⨆ X : Vec 2,
            ‖iteratedFDeriv ℝ r (fun X' => fun i j : Fin 2 => Q.G t X' i j - (if i = j then 1 else 0)) X‖ₑ)
            ≤ ENNReal.ofReal (CGI r * g * lam ^ r)) →
        ∀ (Cc Cc' : ℕ → ℕ → LiftCoeff ι h),
          IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N 0 Cc →
          IsLiftSequence ⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N 0 Cc' →
          (∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ K →
            schurEnergyJet π (Set.Icc t₀ t₁) k j (fun α t X z v u => Cc 0 n m α t X z v u - Cc' 0 n m α t X z v u)
              ≤ ENNReal.ofReal (C * g * lam ^ (n - m + j))) ∧
          (∀ n, 2 ≤ n → n ≤ N + D →
            ∃ Lb Lb' : MeanCoeff ι h,
              (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
                liftMean Q Cc (fun _ => a₀) 0 n t X = meanApply n Lb (fun _ => a₀) t X) ∧
              (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
                liftMean ⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ Cc'
                  (fun _ => a₀) 0 n t X = meanApply n Lb' (fun _ => a₀) t X) ∧
              ∀ d, 2 ≤ d → d ≤ n → ∀ j, j ≤ K →
                schurSlowJet π (Set.Icc t₀ t₁) j
                  (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ =>
                    Lb d p.1 t X p.2 - Lb' d p.1 t X p.2)
                  ≤ ENNReal.ofReal (C * g * lam ^ (n - d + j))) :=
  by
    classical
    let Bd := pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI
    let CE := pairedEnergyScalarBudget N K k Bd
    let CM := pairedMeanScalarBudget (N + D) K Bd Cw CGI
    have hBd n : 0 ≤ Bd n := pairedCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _
    have hCE : 0 ≤ CE := pairedEnergyScalarBudget_nonneg N K k Bd hBd
    have hCM : 0 ≤ CM := pairedMeanScalarBudget_nonneg (N + D) K Bd Cw CGI hBd
    refine ⟨CE + CM, add_nonneg hCE hCM, ?_⟩
    intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ g P hg hGI Cc Ci hseq hseqi
    let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
    have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
    have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
    constructor
    · intro n _ hnN m _ hm j hj
      have hb := setting_paired_energy_original_reserve P Cc Ci hseq hseqi g hg CGI hGI n hnN m hm j hj
      apply hb.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCM) hg) (pow_nonneg hlam _)
    · intro n hn hnR
      obtain ⟨Lb, Lbi, hb, hbi, hjet⟩ :=
        setting_paired_mean_coefficients_original_reserve P Cc Ci hseq hseqi g hg CGI hGI n hn hnR
      refine ⟨Lb, Lbi, hb, hbi, ?_⟩
      intro d hd hdn j hj
      apply (hjet d hd hdn j hj).trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCE) hg) (pow_nonneg hlam _)

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_residual_coarse_flux`, from
`cycle_residual_coarse_flux_of_lift` and the proofs of `cycle_lift_grading` and
`cycle_lift_structure`. -/

/-- **Cycle residual: bound for the lift of a coarse flux divergence** (Lemma 12.6 of the
    paper). -/
theorem cycle_residual_coarse_flux (Acl N D H kl Ll : ℕ) (hA : 1 ≤ Acl)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
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
        ∀ hh, hh ≤ H →
        ∀ Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ t, ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc t x k)) →
          (∀ t, ∀ k, AVenhance.IsZ2Periodic (fun x => Fc t x k)) →
        ∀ Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ n, 1 ≤ n → n ≤ N → ∀ τ ∈ Set.Icc t₀ t₁,
            IsCleanupChain s0 (max (kl + 1) (Ll + 2)) Acl (liftApply n (Cc hh n) (fun s X => ∑ k : Fin 2, fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k)) τ) (fun _ _ _ => 0)
              (fun j => Vn n j τ)) →
        ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
          residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
              (fun t x k => (if hh = 0 then Fc t x k else 0)
                + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x k)
              (fun t x => ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
                εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x)
            ≤ ENNReal.ofReal (C * ((if hh = 0 then Real.sqrt (B / ν) else 0)
                + Θ ^ hh * εc ^ 2 * (1 + Z)) * (Real.sqrt B)⁻¹) *
              classicalFluxL2H ρ π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres Fc :=
  AVRegularity.cycle_residual_coarse_flux_of_lift Acl N D H kl Ll hA CG Cw Cj
    (cycle_lift_grading N (Acl + 2) kl Ll D H CG Cw Cj)
    (cycle_lift_structure N (Acl + 2) kl Ll D H CG Cw Cj)

/-! Proof of `cycle_residual_coarse_flux_differentiated`, with its statement spelled out, from
`cycle_residual_coarse_flux_differentiated_of_lift` and the proofs of
`cycle_lift_grading` and `cycle_lift_structure` at every raised order. -/

/-- **Differentiated lifted coarse-flux reconstruction**. -/
theorem cycle_residual_coarse_flux_differentiated (Acl N D H kl Ll : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    1 ≤ Acl →
      ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
          [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
          [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
          (Q : LiftOperatorData ι h D) (π : ι → ℝ)
          (t₀ t₁ e ν B ρ rs E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
          (b : ι → ι → ℝ) (Θ : ℝ)
          (_hrs : 0 < rs) (_hrse : rs ≤ e) (_heρ : e ≤ ρ)
          (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
          IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N (s0 + r) (kl + r) (Ll + r) qs qf CG Cw Cj b Θ →
          (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
          ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (s0 + r + D + 2) (max (kl + r + 1) (Ll + r + 2)) t₀ t₁ N H Cc →
          ∀ hh, hh ≤ H →
          ∀ Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i,
            (∀ t, ∀ k, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (fun x => Fc t x k)) →
            (∀ t, ∀ k, AVenhance.IsZ2Periodic (fun x => Fc t x k)) →
          ∀ Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
            (∀ n, 1 ≤ n → n ≤ N → ∀ τ ∈ Set.Icc t₀ t₁,
              IsCleanupChain (s0 + r) (max (kl + r + 1) (Ll + r + 2)) Acl (liftApply n (Cc hh n) (fun s X => ∑ k : Fin 2, fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k)) τ) (fun _ _ _ => 0)
                (fun j => Vn n j τ)) →
          ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
            ∀ j : ℕ, j ≤ r → ∀ β : DerivativeWord2 j,
            residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
                (fun t x k => rs ^ j • orderedDerivative β (fun x' =>
                  (if hh = 0 then Fc t x' k else 0)
                  + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x' k) x)
                (fun t x => rs ^ j • orderedDerivative β (fun x' => ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
                  εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x') x)
              ≤ ENNReal.ofReal (C * ((if hh = 0 then Real.sqrt (B / ν) else 0)
                  + Θ ^ hh * εc ^ 2 * (1 + Z)) * (Real.sqrt B)⁻¹) *
                classicalFluxL2H ρ π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) (kres + r) Fc :=
  AVRegularity.cycle_residual_coarse_flux_differentiated_of_lift Acl N D H kl Ll CG Cw Cj
    (fun r => cycle_lift_grading N (Acl + 2 + r) (kl + r) (Ll + r) D H CG Cw Cj)
    (fun r => cycle_lift_structure N (Acl + 2 + r) (kl + r) (Ll + r) D H CG Cw Cj)

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! The lift tail statement `cycle_lift_tail`, using the exact supported centered primitive
presentation. -/

section
open AVRegularity.CycleComparison.Lift

/-- **Cycle lift: the centered presentation of the tail** (Lemma 12.2 of the paper). -/
theorem cycle_lift_tail (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
          ∃ (f : LiftCoeff ι h) (F : Fin 2 → LiftCoeff ι h),
            IsLiftTailPresentation Q Cc (K + D + 2) (max (k + 1) (L + 2)) π t₀ t₁ N K C Θ hh n f F :=
  by
    classical
    refine ⟨tailPresentationScalarBudget K k L D H N CG Cw Cj,
      tailPresentationScalarBudget_nonneg K k L D H N CG Cw Cj, ?_⟩
    intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ P Cc hseq hh hhh n hn hnR
    let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
    have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
    refine ⟨0, tailFluxCoefficient par Q Cc N hh n, ?_⟩
    exact setting_tail_presentation P (K + D + 2) (max (k + 1) (L + 2))
      (by omega) (by omega) Cc hseq hh hhh n (by omega) hnR
end

/-! The explicit finite coefficient construction proves existence with the original data reserve. -/

/-- **Cycle lift: the construction** (Proposition 9.6(a) of the paper). -/
theorem cycle_lift_exists (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∃ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc :=
by
  classical
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  exact ⟨CycleComparison.Lift.constructedLiftCoefficients Q t₀ t₁ P.window par N,
    CycleComparison.Lift.setting_constructed_lift_sequence P⟩

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_residual_differentiated`, with its statement spelled out. Any presentation
satisfying the constructed relation equals the constructed arrays on the window; their mixed jets
feed the conditional differentiated residual estimate `TailDiff.statement_holds`
(`TailPresentation.d1_of_arrays`). -/

/-- **Differentiated cell-tail reconstruction**. -/
theorem cycle_residual_differentiated (Acl N D H kl Ll : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CL : ℝ) :
  1 ≤ Acl →
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ rs E ℓ dstar εc lam : ℝ) (_hrs : 0 < rs) (_hrse : rs ≤ e) (_heρ : e ≤ ρ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ)
        (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N (s0 + r) (kl + r) (Ll + r) qs qf CG Cw Cj b Θ →
        (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (s0 + r + D + 2) (max (kl + r + 1) (Ll + r + 2)) t₀ t₁ N H Cc →
        ∀ (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h) (hh : ℕ), hh ≤ H →
          (∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
            IsConstructedLiftTailPresentation Q Cc (max (kl + r + 1) (Ll + r + 2)) π t₀ t₁ N (s0 + r)
              CL Θ hh n (f n) (F n)) →
        ∀ a : ℝ → Vec 2 → ∀ i, h i,
          (∀ t, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t)) → (∀ t, AVenhance.IsZ2Periodic (a t)) →
          (∀ j, j ≤ kres + r + 1 → ∀ (w : DerivativeWord2 j) (v : ι), Measurable
            (fun p : ℝ × Vec 2 => ‖orderedDerivative w (fun x => a p.1 x v) p.2‖ₑ)) →
        ∀ Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ τ ∈ Set.Icc t₀ t₁,
            IsCleanupChain (s0 + r) (max (kl + r + 1) (Ll + r + 2)) Acl (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ)
              (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) (fun j => Vc j τ)) →
        ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
          ∀ (j : ℕ), j ≤ r → ∀ β : DerivativeWord2 j,
          residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
              (fun t x k => rs ^ j • orderedDerivative β
                (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl Vc t x' k) x)
              (fun t x => rs ^ j • orderedDerivative β
                (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl Vc t x') x)
            ≤ ENNReal.ofReal (C * Θ ^ hh * εc ^ N * (1 + Z)) *
              classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) (kres + r) a :=
  CycleComparison.TailPresentation.d1_of_arrays Acl N D H kl Ll CG Cw Cj CL
    (fun r => CycleComparison.TailPresentation.arrays_statement_holds N (Acl + 2 + r) (kl + r)
      (Ll + r) D H CG Cw Cj)
    (fun r hA => TailDiff.statement_holds Acl N D r hA)

end AVRegularity.Providers
end
end
