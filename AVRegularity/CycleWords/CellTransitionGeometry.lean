-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.GeometryPieceNonempty
import AVRegularity.CycleReference.TransitionTaylorBounds
import AVRegularity.CycleWords.FiniteSmoothPeriodicCarrier
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.SlowJet
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.CycleReference.SpacetimeGradientPairing

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Original measurable scalar potentials preserve higher Bochner torus jets. -/

theorem torusHigherScalar_time_memLp {μ : Measure ℝ} (K : ℕ)
    (c : ℝ → ℂ) (hc : MemLp c ⊤ μ) (U : ℝ → TorusHk K ℂ) (hU : MemLp U 2 μ) :
    MemLp (fun t => torusHigherScalarCLM K (c t) (U t)) 2 μ := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  have hr := Complex.reCLM.comp_memLp' hc
  have hi := Complex.imCLM.comp_memLp' hc
  have hIU := (torusHigherScalarCLM K Complex.I).comp_memLp' hU
  have he : (fun t => torusHigherScalarCLM K (c t) (U t)) =
      (fun t => (c t).re • U t + (c t).im • torusHigherScalarCLM K Complex.I (U t)) :=
    funext (fun t => torusHigherScalarCLM_real_im K (c t) (U t))
  rw [he]
  apply MemLp.add
  · exact hr.smul hU
  · exact hi.smul hIU

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Bounded complex potentials give uniform bounds on the actual higher real Sobolev carrier. -/

theorem torusHigherScalarCLM_norm_le (K : ℕ) (c : ℂ) (k : ℝ) (hk : ‖c‖ ≤ k) :
    ‖torusHigherScalarCLM K c‖ ≤ k * (1 + ‖torusHigherScalarCLM K Complex.I‖) := by
  have hk0 : 0 ≤ k := (norm_nonneg c).trans hk
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hk0 (by positivity))
  intro U
  rw [torusHigherScalarCLM_real_im]
  have hr : ‖c.re • U‖ ≤ k * ‖U‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm c).trans hk) (norm_nonneg _)
  have hi : ‖c.im • torusHigherScalarCLM K Complex.I U‖ ≤
      k * (‖torusHigherScalarCLM K Complex.I‖ * ‖U‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul ((Complex.abs_im_le_norm c).trans hk)
      ((torusHigherScalarCLM K Complex.I).le_opNorm U) (norm_nonneg _) hk0
  exact ((norm_add_le _ _).trans (add_le_add hr hi)).trans_eq (by ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The literal adjoint coordinate solves the exact physical scalar adjoint equation. -/

theorem adjointCoordinate_equation {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    deriv (fun s => adjointCoordinate α q Λ ζ m ν s y j) t +
      (∑ i : Fin 2, streamVel (ocPulseStream α q Λ ζ m) t y i *
        fderiv ℝ (fun z => adjointCoordinate α q Λ ζ m ν t z j) y (basisVec i)) +
      ν * (∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ
        (fun x => adjointCoordinate α q Λ ζ m ν t x j) z (basisVec i)) y (basisVec i)) =
          adjointResidual α q Λ ζ m ν t y j := by
  rw [adjointCoordinate_time_equation hΛ hζ, adjointCoordinate_transport_equation hΛ hζ,
    adjointCoordinate_diffusion_equation hΛ hζ]
  ring

end AVRegularity.CycleWords
end
end

section
/-! A scoped complex normed space structure on the original native higher periodic carrier. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleWords.NativeComplex

scoped instance torusHigherComplexModule (K : ℕ) : Module ℂ (TorusHk K ℂ) where
  smul c U := torusHigherScalarCLM K c U
  one_smul U := by
    change torusHigherScalarCLM K 1 U = U
    simpa only [Complex.ofReal_one, one_smul] using torusHigherScalarCLM_real K 1 U
  mul_smul c d U := torusHigherScalarCLM_mul K c d U
  smul_add c U V := (torusHigherScalarCLM K c).map_add U V
  smul_zero c := (torusHigherScalarCLM K c).map_zero
  add_smul c d U := torusHigherScalarCLM_add K c d U
  zero_smul U := by
    change torusHigherScalarCLM K 0 U = 0
    simpa only [Complex.ofReal_zero, zero_smul] using torusHigherScalarCLM_real K 0 U

end AVRegularity.CycleWords.NativeComplex

open scoped AVRegularity.CycleWords.NativeComplex

namespace AVRegularity.CycleWords.NativeComplex

scoped instance torusHigherComplexNormedSpace (K : ℕ) : NormedSpace ℂ (TorusHk K ℂ) where
  norm_smul_le c U := (torusHigherScalarCLM_norm K c U).le

scoped instance torusHigherComplexScalarTower (K : ℕ) : IsScalarTower ℝ ℂ (TorusHk K ℂ) where
  smul_assoc r c U := by
    change torusHigherScalarCLM K (r • c) U = r • torusHigherScalarCLM K c U
    rw [Complex.real_smul, torusHigherScalarCLM_mul, torusHigherScalarCLM_real]

scoped instance torusHigherComplexSMulComm (K : ℕ) : SMulCommClass ℝ ℂ (TorusHk K ℂ) where
  smul_comm r c U := ((torusHigherScalarCLM K c).map_smul r U).symm

end AVRegularity.CycleWords.NativeComplex

namespace AVRegularity.CycleWords

theorem torusHigher_complex_smul (K : ℕ) (c : ℂ) (U : TorusHk K ℂ) :
    c • U = torusHigherScalarCLM K c U := rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleWords

/-! Joint smoothness and symmetry of the actual chart metric and its centre freeze. -/

theorem ocMaterialMetric_joint_contDiff (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocMaterialMetric α q Λ m φ hφ l p.1 p.2 i j) := by
  let s := (l : ℝ) * ocTauPP α q Λ m
  have hi0 := CycleReference.chartJac_inverse_entry_smooth hφ s i 0
  have hi1 := CycleReference.chartJac_inverse_entry_smooth hφ s i 1
  have hj0 := CycleReference.chartJac_inverse_entry_smooth hφ s j 0
  have hj1 := CycleReference.chartJac_inverse_entry_smooth hφ s j 1
  have he : (fun p : ℝ × Vec 2 => ocMaterialMetric α q Λ m φ hφ l p.1 p.2 i j) =
      fun p => (CycleReference.chartJac hφ s p.1 p.2)⁻¹ i 0 *
          (CycleReference.chartJac hφ s p.1 p.2)⁻¹ j 0 +
        (CycleReference.chartJac hφ s p.1 p.2)⁻¹ i 1 *
          (CycleReference.chartJac hφ s p.1 p.2)⁻¹ j 1 := by
    funext p
    change (((CycleReference.chartJac hφ s p.1 p.2)⁻¹ *
      ((CycleReference.chartJac hφ s p.1 p.2)⁻¹)ᵀ) i j) = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

  rw [he]
  exact (hi0.mul hj0).add (hi1.mul hj1)

theorem ocCellMetric_joint_contDiff (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocCellMetric α q Λ m φ hφ l ν yc p.1 p.2 i j) := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      (ocEll q Λ m ν ^ 2 * p.1, yc + ocEpsilon q Λ m • p.2)) := by fun_prop
  have hs := (ocMaterialMetric_joint_contDiff α q Λ m hφ l i j).comp hm
  simpa only [Function.comp_def, ocCellMetric] using hs

theorem ocCellMetric_symmetric (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2) (t : ℝ) (z : Vec 2) :
    (ocCellMetric α q Λ m φ hφ l ν yc t z).IsSymm := by
  unfold ocCellMetric ocMaterialMetric
  exact Matrix.isSymm_mul_transpose_self _

theorem ocCellMetric_frozen_joint_contDiff (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocCellMetric α q Λ m φ hφ l ν yc p.1 0 i j) := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (p.1, (0 : Vec 2))) := by fun_prop
  have hs := (ocCellMetric_joint_contDiff α q Λ m hφ l ν yc i j).comp hm
  simpa only [Function.comp_def] using hs

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Reducing uniform exponential rates preserves the chosen fibre coefficients and all four propagation clauses. -/

def scalarConstantsWithGapRates (K : ScalarConstants) (c : ℕ → ℝ) : ScalarConstants :=
  { K with cj := c }

theorem scalar_fibre_decay_budget_mono {A c d τ : ℝ}
    (hA : 0 ≤ A) (hcd : d ≤ c) (hτ : 0 ≤ τ) :
    ENNReal.ofReal (A * Real.exp (-c * τ)) ≤ ENNReal.ofReal (A * Real.exp (-d * τ)) := by
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hcd) hτ

def fibreScalarDataWithGapRates {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K η G v t₀ S) (c : ℕ → ℝ)
    (hc : ∀ j, c j ≤ K.cj j) (hC : ∀ j, 0 ≤ K.Cj j) :
    FibreScalarData (scalarConstantsWithGapRates K c) η G v t₀ S := by
  have hp (j : ℕ) : 0 ≤ K.Cj j * peFactor η ^ K.Qj j :=
    mul_nonneg (hC j) (by unfold peFactor; positivity)
  refine
    { r := d.r
      lam := d.lam
      ell := d.ell
      graph := d.graph
      row_summable := d.row_summable
      row_mean := d.row_mean
      row_taylor := d.row_taylor
      real_ratio := d.real_ratio
      graph_jets := d.graph_jets
      row_jets := d.row_jets
      fast_decay := ?_
      fast_smoothing := ?_
      adjoint_decay := ?_
      adjoint_smoothing := ?_ }
  · intro j ξ hr hξ s t hs hst ht D hD g₀ hg₀ hpg₀ he₀
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.fast_decay j ξ hr hξ s t hs hst ht D hD
      g₀ hg₀ hpg₀ he₀
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (scalar_fibre_decay_budget_mono (hp j) (hc j) (sub_nonneg.mpr hst)) _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.fast_smoothing j ξ hr hξ s t hs hst ht D hD
    have htime : 0 ≤ 1 + (t - s) ^ (-(j : ℝ) / 2) := by positivity
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (scalar_fibre_decay_budget_mono (mul_nonneg (hp j) htime) (hc j)
        (sub_nonneg.mpr hst.le)) _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD g₀ hg₀ hpg₀ he₀
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.adjoint_decay j ξ hr hξ s t hs hst ht D hD
      g₀ hg₀ hpg₀ he₀
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (scalar_fibre_decay_budget_mono (hp j) (hc j) (sub_nonneg.mpr hst)) _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.adjoint_smoothing j ξ hr hξ s t hs hst ht D hD
    have htime : 0 ≤ 1 + (t - s) ^ (-(j : ℝ) / 2) := by positivity
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (scalar_fibre_decay_budget_mono (mul_nonneg (hp j) htime) (hc j)
        (sub_nonneg.mpr hst.le)) _)⟩

/-! Initial graph and row difference budgets before using buffered forgetting. -/

theorem cellSobolevNorm_neg (j : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (j : ℕ∞) f) : cellSobolevNorm j (-f) = cellSobolevNorm j f := by
  have he : -f = (-1 : ℂ) • f := by ext x; simp
  rw [he, cellSobolevNorm_const_smul j (-1) f hf]
  norm_num

theorem cellSobolevNorm_sub_le (j : ℕ) (f g : Vec 2 → ℂ)
    (hf : ContDiff ℝ (j : ℕ∞) f) (hg : ContDiff ℝ (j : ℕ∞) g) :
    cellSobolevNorm j (f - g) ≤ cellSobolevNorm j f + cellSobolevNorm j g := by
  rw [sub_eq_add_neg]
  exact (cellSobolevNorm_add_le j f (-g) hf hg.neg).trans_eq
    (by rw [cellSobolevNorm_neg j g hg])

theorem fibreScalarData_graph_difference_bound {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v w : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K η G v t₀ S) (e : FibreScalarData K η G w t₀ S)
    (j : ℕ) (ξ : Fin 2 → ℂ) (hr : ∀ i, (ξ i).im = 0)
    (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    cellSobolevNorm j (fun x => cellValue (fibreSeriesJet d.r ξ) t x -
      cellValue (fibreSeriesJet e.r ξ) t x) ≤
      ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ) +
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ) := by
  obtain ⟨hd, hb⟩ := d.graph_jets j ξ hr hξ t
  obtain ⟨he, hc⟩ := e.graph_jets j ξ hr hξ t
  exact (cellSobolevNorm_sub_le j _ _ (hd.of_le (by simp)) (he.of_le (by simp))).trans
    (add_le_add hb hc)

theorem fibreScalarData_row_difference_bound {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v w : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K η G v t₀ S) (e : FibreScalarData K η G w t₀ S)
    (j : ℕ) (ξ : Fin 2 → ℂ) (hr : ∀ i, (ξ i).im = 0)
    (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    cellSobolevNorm j (fun x => fibreSeriesFun d.ell ξ t x - fibreSeriesFun e.ell ξ t x) ≤
      ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ) +
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ) := by
  obtain ⟨hd, hb⟩ := d.row_jets j ξ hr hξ t
  obtain ⟨he, hc⟩ := e.row_jets j ξ hr hξ t
  have heq : (fun x => fibreSeriesFun d.ell ξ t x - fibreSeriesFun e.ell ξ t x) =
      (fun x => fibreSeriesFun d.ell ξ t x - 1) -
        (fun x => fibreSeriesFun e.ell ξ t x - 1) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact (cellSobolevNorm_sub_le j _ _ (hd.of_le (by simp)) (he.of_le (by simp))).trans
    (add_le_add hb hc)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Enlarging uniform spatial prices preserves all fibre data and its literal coefficients. -/

def scalarConstantsWithJetPrices (K : ScalarConstants) (C : ℕ → ℝ) : ScalarConstants :=
  { K with Cj := C }

theorem scalar_fibre_jet_budget_mono {a b p x : ℝ} (hab : a ≤ b)
    (hp : 0 ≤ p) (hx : 0 ≤ x) :
    ENNReal.ofReal (a * p * x) ≤ ENNReal.ofReal (b * p * x) :=
  ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hp) hx)

def fibreScalarDataWithJetPrices {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K η G v t₀ S) (C : ℕ → ℝ) (hC : ∀ j, K.Cj j ≤ C j) :
    FibreScalarData (scalarConstantsWithJetPrices K C) η G v t₀ S := by
  have hp (j : ℕ) : 0 ≤ peFactor η ^ K.Qj j := by unfold peFactor; positivity
  refine
    { r := d.r
      lam := d.lam
      ell := d.ell
      graph := d.graph
      row_summable := d.row_summable
      row_mean := d.row_mean
      row_taylor := d.row_taylor
      real_ratio := d.real_ratio
      graph_jets := ?_
      row_jets := ?_
      fast_decay := ?_
      fast_smoothing := ?_
      adjoint_decay := ?_
      adjoint_smoothing := ?_ }
  · intro j ξ hr hξ t
    obtain ⟨hs, hb⟩ := d.graph_jets j ξ hr hξ t
    exact ⟨hs, hb.trans (scalar_fibre_jet_budget_mono (hC j) (hp j) (fibreNorm_nonneg ξ))⟩
  · intro j ξ hr hξ t
    obtain ⟨hs, hb⟩ := d.row_jets j ξ hr hξ t
    exact ⟨hs, hb.trans (scalar_fibre_jet_budget_mono (hC j) (hp j) (fibreNorm_nonneg ξ))⟩
  · intro j ξ hr hξ s t hs hst ht D hD g₀ hg₀ hpg₀ he₀
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.fast_decay j ξ hr hξ s t hs hst ht D hD
      g₀ hg₀ hpg₀ he₀
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (scalar_fibre_jet_budget_mono (hC j) (hp j) (Real.exp_pos (-(K.cj j) * (t - s))).le) _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.fast_smoothing j ξ hr hξ s t hs hst ht D hD
    have htime : 0 ≤ 1 + (t - s) ^ (-(j : ℝ) / 2) := by positivity
    have hprod := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hC j) (hp j)) htime
    have hfinal := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(K.cj j) * (t - s))).le)
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left hfinal _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD g₀ hg₀ hpg₀ he₀
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.adjoint_decay j ξ hr hξ s t hs hst ht D hD
      g₀ hg₀ hpg₀ he₀
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (scalar_fibre_jet_budget_mono (hC j) (hp j) (Real.exp_pos (-(K.cj j) * (t - s))).le) _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.adjoint_smoothing j ξ hr hξ s t hs hst ht D hD
    have htime : 0 ≤ 1 + (t - s) ^ (-(j : ℝ) / 2) := by positivity
    have hprod := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hC j) (hp j)) htime
    have hfinal := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(K.cj j) * (t - s))).le)
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left hfinal _)⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.FastJets
namespace AVRegularity.CycleWords

/-! Diagonal jets of a reserved slow coefficient retain the graded mixed molecular budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sampledSlowCoefficient_jet_le {r J : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : ContDiff ℝ (J + r : ℕ) (Function.uncurry f)) (w : DerivativeWord2 r)
    (ρ δ τ B : ℝ) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hB : 0 ≤ B)
    (hb : ∀ a b : ℕ, a + b ≤ J → ∀ X z,
      ρ ^ (a + b) * |δ| ^ a *
        ‖iteratedFDeriv ℝ (r + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B)
    (j : ℕ) (hj : j ≤ J) (z : Vec 2) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun z =>
      iteratedFDeriv ℝ r (fun X' => f X' z) ((τ * δ) • z)
        (fun i => basisVec (w i))) z‖ ≤ 4 ^ J * B := by
  let W := fun X z => iteratedFDeriv ℝ r (fun X' => f X' z) X (fun i => basisVec (w i))
  have hW : ContDiff ℝ (J : ℕ) (Function.uncurry W) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) E
      (fun i => basisVec (w i))).contDiff.comp
      (Weighted.joint_partialIteratedFDeriv_left_contDiff J r (Function.uncurry f) hf)
  have hm (γ β : List (Fin 2)) (h : γ.length + β.length ≤ J) (X z : Vec 2) :
      ρ ^ (γ.length + β.length) * |termCoef (τ * δ)⁻¹ 1 (γ, β)| *
        ‖mixL γ β W X z‖ ≤ B := by
    have hc := norm_slowCoefficient_mixL_le hf w γ β h X z
    have he : |termCoef (τ * δ)⁻¹ 1 (γ, β)| = τ ^ γ.length * |δ| ^ γ.length := by
      simp only [termCoef, inv_inv, inv_one, one_pow, mul_one, abs_pow, abs_mul, abs_of_nonneg hτ, mul_pow]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (pow_nonneg hρ (γ.length + β.length))
        (mul_nonneg (pow_nonneg hτ γ.length) (pow_nonneg (abs_nonneg δ) γ.length)))
    have hs := mul_le_mul_of_nonneg_left (hb γ.length β.length h X z) (pow_nonneg hτ γ.length)
    have ht := mul_le_mul_of_nonneg_right (pow_le_one₀ hτ hτ1 (n := γ.length)) hB
    apply hh.trans
    have hh' := hs.trans (by simpa only [one_mul] using ht)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh'
  have hh := joint_diagonal_jet_budget hW (τ * δ)⁻¹ 1 ρ B hρ hB hm j hj z
  simpa only [inv_inv, inv_one, one_smul, W] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Increasing contrast orders preserves all fibre data and its literal coefficients. -/

def scalarConstantsWithContrastOrders (K : ScalarConstants) (Q : ℕ → ℕ) : ScalarConstants :=
  { K with Qj := Q }

def fibreScalarDataWithContrastOrders {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K η G v t₀ S) (Q : ℕ → ℕ) (hQ : ∀ j, K.Qj j ≤ Q j) (hC : ∀ j, 0 ≤ K.Cj j) :
    FibreScalarData (scalarConstantsWithContrastOrders K Q) η G v t₀ S := by
  have hscale (j : ℕ) : K.Cj j * peFactor η ^ K.Qj j ≤ K.Cj j * peFactor η ^ Q j :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_peFactor η) (hQ j)) (hC j)
  have hbudget (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
      ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * x) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ Q j * x) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hscale j) hx)
  refine
    { r := d.r
      lam := d.lam
      ell := d.ell
      graph := d.graph
      row_summable := d.row_summable
      row_mean := d.row_mean
      row_taylor := d.row_taylor
      real_ratio := d.real_ratio
      graph_jets := ?_
      row_jets := ?_
      fast_decay := ?_
      fast_smoothing := ?_
      adjoint_decay := ?_
      adjoint_smoothing := ?_ }
  · intro j ξ hr hξ t
    obtain ⟨hs, hb⟩ := d.graph_jets j ξ hr hξ t
    exact ⟨hs, hb.trans (hbudget j (fibreNorm ξ) (fibreNorm_nonneg ξ))⟩
  · intro j ξ hr hξ t
    obtain ⟨hs, hb⟩ := d.row_jets j ξ hr hξ t
    exact ⟨hs, hb.trans (hbudget j (fibreNorm ξ) (fibreNorm_nonneg ξ))⟩
  · intro j ξ hr hξ s t hs hst ht D hD g₀ hg₀ hpg₀ he₀
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.fast_decay j ξ hr hξ s t hs hst ht D hD
      g₀ hg₀ hpg₀ he₀
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (hbudget j _ (Real.exp_pos (-(K.cj j) * (t - s))).le) _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.fast_smoothing j ξ hr hξ s t hs hst ht D hD
    have htime : 0 ≤ 1 + (t - s) ^ (-(j : ℝ) / 2) := by positivity
    have hprod := mul_le_mul_of_nonneg_right
      (hscale j) htime
    have hfinal := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(K.cj j) * (t - s))).le)
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left hfinal _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD g₀ hg₀ hpg₀ he₀
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.adjoint_decay j ξ hr hξ s t hs hst ht D hD
      g₀ hg₀ hpg₀ he₀
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left
      (hbudget j _ (Real.exp_pos (-(K.cj j) * (t - s))).le) _)⟩
  · intro j ξ hr hξ s t hs hst ht D hD
    obtain ⟨g₁, hg₁, hpg₁, he₁, hb⟩ := d.adjoint_smoothing j ξ hr hξ s t hs hst ht D hD
    have htime : 0 ≤ 1 + (t - s) ^ (-(j : ℝ) / 2) := by positivity
    have hprod := mul_le_mul_of_nonneg_right
      (hscale j) htime
    have hfinal := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(K.cj j) * (t - s))).le)
    exact ⟨g₁, hg₁, hpg₁, he₁, hb.trans (mul_le_mul_left hfinal _)⟩

/-! A smaller common low-frequency disc preserves every chosen fibre coefficient and propagation clause. -/

def scalarConstantsWithRadius (K : ScalarConstants) (R : ℝ) : ScalarConstants :=
  { K with ξ0 := R }

def fibreScalarDataWithRadius {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K η G v t₀ S) (R : ℝ) (hR : 0 < R)
    (hRK : R ≤ K.ξ0) (hCg : 0 ≤ K.Cg) :
    FibreScalarData (scalarConstantsWithRadius K R) η G v t₀ S := by
  have hξ (ξ : Fin 2 → ℂ) (h : fibreNorm ξ < R) : fibreNorm ξ < K.ξ0 := h.trans_le hRK
  refine
    { r := d.r
      lam := d.lam
      ell := d.ell
      graph := isFibreGraph_radius_restriction d.graph hR hRK hCg le_rfl
      row_summable := fun ξ h => d.row_summable ξ (hξ ξ h)
      row_mean := fun ξ h => d.row_mean ξ (hξ ξ h)
      row_taylor := ?_
      real_ratio := fun ξ hr h => d.real_ratio ξ hr (hξ ξ h)
      graph_jets := fun j ξ hr h => d.graph_jets j ξ hr (hξ ξ h)
      row_jets := fun j ξ hr h => d.row_jets j ξ hr (hξ ξ h)
      fast_decay := fun j ξ hr h => d.fast_decay j ξ hr (hξ ξ h)
      fast_smoothing := fun j ξ hr h => d.fast_smoothing j ξ hr (hξ ξ h)
      adjoint_decay := fun j ξ hr h => d.adjoint_decay j ξ hr (hξ ξ h)
      adjoint_smoothing := fun j ξ hr h => d.adjoint_smoothing j ξ hr (hξ ξ h) }
  intro n ξ t
  apply (d.row_taylor n ξ t).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (fibreNorm_nonneg ξ) n)
  apply mul_le_mul_of_nonneg_left _ hCg
  apply pow_le_pow_left₀ (div_nonneg (by norm_num) (hR.le.trans hRK))
  exact div_le_div_of_nonneg_left (by norm_num) hR hRK

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Absolute slow anchors and arbitrary fast phases preserve the graded diagonal jet budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jointSample_normalized_jet_le {N : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : ContDiff ℝ (N : ℕ) (Function.uncurry f))
    (ρ δ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hb : ∀ a b : ℕ, a + b ≤ N → ∀ X z,
      ρ ^ (a + b) * |δ| ^ a *
        ‖iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B)
    (X0 φ : Vec 2) (j : ℕ) (hj : j ≤ N) (z : Vec 2) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => f (X0 + δ • y) (y + φ)) z‖ ≤ 4 ^ N * B := by
  let F := fun X z => f (X0 + X) (z + φ)
  have hF : ContDiff ℝ (N + 0 : ℕ) (Function.uncurry F) := by
    change ContDiff ℝ (N + 0 : ℕ) (fun w : Vec 2 × Vec 2 => f (X0 + w.1) (w.2 + φ))
    have hh := hf.comp (((contDiff_const (c := X0)).add contDiff_fst).prodMk
      (contDiff_snd.add (contDiff_const (c := φ))))
    simpa only [Nat.add_zero, Function.comp_def, Function.uncurry_apply_pair] using hh
  have hFb (a b : ℕ) (hab : a + b ≤ N) (X z : Vec 2) :
      ρ ^ (a + b) * |δ| ^ a *
        ‖iteratedFDeriv ℝ (0 + a) (fun X' => iteratedFDeriv ℝ b (F X') z) X‖ ≤ B := by
    have he : (fun X' => iteratedFDeriv ℝ b (F X') z) =
        (fun X' => iteratedFDeriv ℝ b (f (X0 + X')) (z + φ)) := by
      funext X'
      exact iteratedFDeriv_comp_add_right b φ z
    rw [he, Nat.zero_add,
      iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun X' => iteratedFDeriv ℝ b (f X') (z + φ)) a X0 X]
    exact hb a b hab (X0 + X) (z + φ)
  have hh := sampledSlowCoefficient_jet_le hF (fun i : Fin 0 => Fin.elim0 i)
    ρ δ 1 B hρ zero_le_one le_rfl hB hFb j hj z
  simpa only [one_mul, iteratedFDeriv_zero_apply, F] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.ChartTransport
namespace AVRegularity.CycleWords

/-! A slow coefficient word retains the actual mixed slow/fast derivative budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowCoefficient_fast_jet_le {r j : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r j f) (w : DerivativeWord2 r) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun z => iteratedFDeriv ℝ r (fun X' => f X' z) X
      (fun i => basisVec (w i))) z‖ ≤
      2 ^ j * ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ := by
  let v : DerivativeWord2 r := fun i => w i.rev
  let c := fun z => iteratedFDeriv ℝ r (fun X' => f X' z) X (fun i => basisVec (w i))
  have hc : ContDiff ℝ (j : ℕ∞) c :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) E
      (fun i => basisVec (w i))).contDiff.comp (CoarseFluxDiff.contDiff_slowJet hf X)
  have he (z : Vec 2) : c z = orderedDerivative v (fun X' => f X' z) X := by
    rw [orderedDerivative_eq_iteratedFDeriv v (hf.contDiff_slow z)]
    simp only [v, Fin.rev_rev, c]
  apply (norm_iteratedFDeriv_le_sum_words hc z).trans
  have hword (β : DerivativeWord2 j) :
      ‖orderedDerivative β c z‖ ≤ ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ := by
    have hcomm := MixedTail.fastL_slowL_comm (List.ofFn v) (List.ofFn β) (F := f)
      (by simpa using hf)
    have hcword : orderedDerivative β c z =
        orderedDerivative v (fun X' => orderedDerivative β (f X') z) X := by
      have hh := congrFun (congrFun hcomm X) z
      change orderedDerivative β (fun z => orderedDerivative v (fun X' => f X' z) X) z = _ at hh
      simp_rw [← he] at hh
      exact hh
    rw [hcword]
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) E
      (fun i => basisVec (β i.rev))
    have heval : (fun X' => orderedDerivative β (f X') z) =
        fun X' => L (iteratedFDeriv ℝ j (f X') z) := by
      funext X'
      rw [orderedDerivative_eq_iteratedFDeriv β (hf.1 X')]
      rfl
    rw [heval, orderedDerivative_clm_comp L v (hf.2.1 j le_rfl z)]
    have hL : ‖L‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro a
      simpa only [L, ContinuousMultilinearMap.apply_apply, norm_basisVec,
        Finset.prod_const_one, mul_one, one_mul] using a.le_opNorm (fun i => basisVec (β i.rev))
    exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
      (by simpa only [one_mul] using norm_orderedDerivative_le (hf.2.1 j le_rfl z) v X))
  calc
    _ ≤ ∑ _β : DerivativeWord2 j,
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ :=
      Finset.sum_le_sum (fun β _ => hword β)
    _ = _ := by simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleWords

/-! Smoothness, measure preservation, and the actual moving centre of a renewal. -/

def cellTransitionHomeomorph (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (y y' : Vec 2)
    (he : ocEpsilon q Λ m ≠ 0) : Vec 2 ≃ₜ Vec 2 :=
  cellRescaledHomeomorph (CycleReference.streamFlowHomeomorph hφ
    ((l : ℝ) * ocTauPP α q Λ m) (((l + 1 : ℤ) : ℝ) * ocTauPP α q Λ m))
    (ocEpsilon q Λ m) he y y'

@[simp] theorem cellTransitionHomeomorph_apply (α q : ℝ) (Λ m : ℕ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ) (y y' z : Vec 2)
    (he : ocEpsilon q Λ m ≠ 0) :
    cellTransitionHomeomorph α q Λ m hφ l y y' he z =
      ocCellTransition α q Λ m φ hφ l y y' z := rfl

theorem cellTransition_contDiff (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (y y' : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (ocCellTransition α q Λ m φ hφ l y y') := by
  have h := CycleReference.streamFlow_spatial_smooth hφ
    ((l : ℝ) * ocTauPP α q Λ m) (((l + 1 : ℤ) : ℝ) * ocTauPP α q Λ m)
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 => y' + ocEpsilon q Λ m • z) := by
    fun_prop
  have hh := ((h.comp ha).sub (contDiff_const (c := y))).const_smul ((ocEpsilon q Λ m)⁻¹)
  exact hh

theorem cellTransition_measurePreserving (α q : ℝ) (Λ m : ℕ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ)
    (y y' : Vec 2) (he : ocEpsilon q Λ m ≠ 0) :
    MeasurePreserving (ocCellTransition α q Λ m φ hφ l y y') volume volume := by
  exact cell_rescaled_measurePreserving _ (CycleReference.streamFlow_measurePreserving hφ _ _)
    _ he y y'

theorem cellTransition_centre_zero (α q : ℝ) (Λ m : ℕ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l₀ : ℤ) (y₀ : Vec 2) (i : ℕ) :
    ocCellTransition α q Λ m φ hφ (l₀ + i)
      (ocCellCentre α q Λ m φ hφ l₀ y₀ i)
      (ocCellCentre α q Λ m φ hφ l₀ y₀ (i + 1)) 0 = 0 := by
  let X := CycleReference.streamFlowHomeomorph hφ
    (((l₀ + i : ℤ) : ℝ) * ocTauPP α q Λ m)
    (((l₀ + i + 1 : ℤ) : ℝ) * ocTauPP α q Λ m)
  have hi := X.apply_symm_apply (ocCellCentre α q Λ m φ hφ l₀ y₀ i)
  change ocTransition α q Λ m φ hφ (l₀ + i) (l₀ + i + 1)
    (ocTransition α q Λ m φ hφ (l₀ + i + 1) (l₀ + i)
      (ocCellCentre α q Λ m φ hφ l₀ y₀ i)) =
      ocCellCentre α q Λ m φ hφ l₀ y₀ i at hi
  simp only [ocCellTransition, ocCellCentre, smul_zero, add_zero, hi, sub_self]

end AVRegularity.CycleWords
end
end
