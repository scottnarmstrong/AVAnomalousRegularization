-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.PlaneFluxTerm
import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
public import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Lift.CellB1LeftTerms
import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps
public import AVRegularity.EntryWeak.WeakTransferPartitionBudget
public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets

section
section
/-! A high-order kernel Schur price converges linearly to its certified order-zero price. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]


theorem kernelSchurMatrix_radius_slope {a b R ρ ν : ℝ} {D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b R ν 0 D (h := h) (Γ := Γ) (G := G))
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (K : ℕ)
    (hfin : ∀ i j α d, coefficientSeminorm R K a b (P.B i j α d) ≠ ⊤)
    (i j : ι) :
    kernelSchurMatrix ν ρ P.π K D a b P.c P.r P.C P.B i j ≤
      kernelSchurMatrix ν R P.π 0 D a b P.c P.r P.C P.B i j +
        (ρ / R) * kernelSchurMatrix ν R P.π K D a b P.c P.r P.C P.B i j := by
  classical
  have he : ∀ α (d : ↥(Finset.Icc 2 D)),
      ((coefficientSeminorm ρ K a b (P.B i j α d)).toReal * P.c (d.1 - 2)) /
          (ν * P.r i j α ^ (d.1 - 2)) ≤
        ((coefficientSeminorm R 0 a b (P.B i j α d)).toReal * P.c (d.1 - 2)) /
          (ν * P.r i j α ^ (d.1 - 2)) +
        (ρ / R) * (((coefficientSeminorm R K a b (P.B i j α d)).toReal * P.c (d.1 - 2)) /
          (ν * P.r i j α ^ (d.1 - 2))) := by
    intro α d
    have hc : 0 ≤ P.c (d.1 - 2) := (P.hS i j α).2.2.1 _
      (by have hd := Finset.mem_Icc.mp d.property; omega)
    have hh := coefficientSeminorm_real_slope hρ P.radius_pos hρR K a b (P.B i j α d)
      (hfin i j α d)
    rw [coefficientSeminorm_order_zero_radius ρ R a b (P.B i j α d)] at hh
    have hden : 0 ≤ ν * P.r i j α ^ (d.1 - 2) :=
      mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr i j α).le (d.1 - 2))
    have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc) hden
    exact hb.trans_eq (by ring)
  unfold kernelSchurMatrix
  have hs : (∑ α : Γ i j, ‖P.C i j α‖ * ∑ d : ↥(Finset.Icc 2 D),
      ((coefficientSeminorm ρ K a b (P.B i j α d)).toReal * P.c (d.1 - 2)) /
        (ν * P.r i j α ^ (d.1 - 2))) ≤
      (∑ α : Γ i j, ‖P.C i j α‖ * ∑ d : ↥(Finset.Icc 2 D),
        ((coefficientSeminorm R 0 a b (P.B i j α d)).toReal * P.c (d.1 - 2)) /
          (ν * P.r i j α ^ (d.1 - 2))) +
      (ρ / R) * (∑ α : Γ i j, ‖P.C i j α‖ * ∑ d : ↥(Finset.Icc 2 D),
        ((coefficientSeminorm R K a b (P.B i j α d)).toReal * P.c (d.1 - 2)) /
          (ν * P.r i j α ^ (d.1 - 2))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro α _
    have hd := Finset.sum_le_sum (s := Finset.univ)
      (fun (d : ↥(Finset.Icc 2 D)) _ => he α d)
    have hb := mul_le_mul_of_nonneg_left hd (norm_nonneg (P.C i j α))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
    exact hb.trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)).trans_eq (by ring)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Strict zero-order Schur slack gives an auxiliary higher-order absorption radius. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]


theorem kernelSchurBound_auxiliary_radius {a b R ν : ℝ} {D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b R ν 0 D (h := h) (Γ := Γ) (G := G))
    (hθ : P.θ < 1 / 8) (K : ℕ)
    (hfin : ∀ i j α d, coefficientSeminorm R K a b (P.B i j α d) ≠ ⊤) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      SchurBound (1 / 8) (kernelSchurMatrix ν ρ P.π K D a b P.c P.r P.C P.B) := by
  obtain ⟨M, hM, hbudget⟩ := finite_matrix_schur_budget
    (kernelSchurMatrix ν R P.π K D a b P.c P.r P.C P.B)
  have hslack : 0 < 1 / 8 - P.θ := sub_pos.mpr hθ
  obtain ⟨ρ, hρ, hρR, hprice⟩ := radius_linear_budget R (1 / 8 - P.θ) M
    P.radius_pos hslack (zero_le_one.trans hM)
  refine ⟨ρ, hρ, hρR, ?_⟩
  apply schur_slope_budget
    (kernelSchurMatrix ν R P.π 0 D a b P.c P.r P.C P.B)
    (kernelSchurMatrix ν ρ P.π K D a b P.c P.r P.C P.B)
    (kernelSchurMatrix ν R P.π K D a b P.c P.r P.C P.B)
    P.θ (1 / 8) M (ρ / R) (div_nonneg hρ.le P.radius_pos.le) P.hschur hbudget
    (kernelSchurMatrix_radius_slope P hρ.le hρR K hfin)
  calc
    P.θ + (ρ / R) * M ≤ P.θ + (1 / 8 - P.θ) := add_le_add_right hprice P.θ
    _ = 1 / 8 := by ring

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Copy-adapt the bounded diagonal Cauchy argument to independent slow and fast parameters. -/
@[expose] public noncomputable section
open Homogenization Complex Metric MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer

theorem base_fast_joint_regular {d : ℕ}
    (S T : ℝ) (hS : 0 < S) (hST : S ≤ T) (n : ℕ)
    (Lslow Lfast : Vec d →L[ℝ] Vec 2)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    (F : (Fin 2 → ℂ) → Vec 2 → ℂ)
    (hhol : ∀ z, DifferentiableOn ℂ (fun Z => F Z z) {Z | (∑ a, |(Z a).im|) < T})
    (hfast : ∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z : Vec 2,
      ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 => F Z (z + X)))
    (M : ℝ) (hM : 0 ≤ M)
    (hvalue : ∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z, ‖F Z z‖ ≤ M)
    (hjet : ∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z : Vec 2,
      ∀ j ≤ n, ∀ X, ‖iteratedFDeriv ℝ j (fun X : Vec 2 => F Z (z + X)) X‖ ≤ A j * M)
    (Y z : Vec 2) :
    ContDiffAt ℝ (n : ℕ∞) (fun X : Vec d =>
      F (fun a => ((Y + Lslow X) a : ℂ)) (z + Lfast X)) 0 := by
  let R := S / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hRS : 2 * R < S := by dsimp [R]; linarith only [hS]
  obtain ⟨χ, hχ, heχ, hbχ, hout⟩ := exists_smooth_bounded_local_identity
    (E := Vec 2) (R / 2) (by positivity)
  have hzχ : χ 0 = 0 := heχ.eq_of_nhds
  let μ := cauchyAngleMeasure.prod cauchyAngleMeasure
  let a₀ := ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ ^ 2 * R ^ 2
  have ha₀ : 0 ≤ a₀ := by dsimp [a₀]; positivity
  let D : ℝ × ℝ → Fin 2 → ℂ := fun p => complexBaseShift Y (circleMap 0 R p.1) (circleMap 0 R p.2)
  have hD (p : ℝ × ℝ) : (∑ a, |(D p a).im|) < S :=
    (complex_base_shift_im_sum_le Y R _ _
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl])
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl])).trans_lt hRS
  let pref : ℝ × ℝ → ℂ := cauchyBoundaryCoefficient R (fun _ _ => 1)
  have hpref : Measurable pref := cauchy_boundary_coefficient_measurable R _ continuous_const
  have hpb (p : ℝ × ℝ) : ‖pref p‖ ≤ a₀ := by
    simpa only [mul_one] using cauchy_boundary_coefficient_norm_le R hR (fun _ _ => 1) 1
      (fun _ _ => by simp only [norm_one, le_refl]) p
  let f : (ℝ × ℝ) → Vec d → ℂ := fun p X => pref p * F (D p) (z + Lfast X)
  have hm (X : Vec d) : Measurable (fun p => f p X) := by
    have hc := (base_strip_coordinate_slices (fun Z => F Z (z + Lfast X)) T R hR
      (hRS.trans_le hST) (hhol _) Y).2.2
    exact hpref.mul hc.measurable
  have hlinear (p : ℝ × ℝ) := linear_parameter_regular_and_jets
    (fun X : Vec 2 => F (D p) (z + X)) n (hfast (D p) (hD p) z) Lfast
    (fun j => A j * M) (hjet (D p) (hD p) z)
  have hs (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞) (f p) :=
    hlinear p |>.1.const_smul (pref p)
  have hf : ∀ l ≤ n, ∀ p X, ‖iteratedFDeriv ℝ l (f p) X‖ ≤ (a₀ * (A l * ‖Lfast‖ ^ l)) * M := by
    intro l hl p X
    change ‖iteratedFDeriv ℝ l (fun X => pref p •
      ((fun Y : Vec 2 => F (D p) (z + Y)) ∘ Lfast) X) X‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hlinear p).1.contDiffAt.of_le
      (by exact_mod_cast hl)), norm_smul]
    exact (mul_le_mul (hpb p) ((hlinear p).2 l hl X) (norm_nonneg _) ha₀).trans_eq
      (by ring)
  have hreg := localized_joint_cauchy_regular R hR χ hχ hbχ hzχ hout μ n Lslow
    (fun j => a₀ * (A j * ‖Lfast‖ ^ j)) (fun j => by have hj := hA j; positivity)
    f hm hs M hM hf
  let H : Vec d → ℂ := fun X => ∫ p, f p X * localizedCauchyKernel R χ (p, Lslow X) ∂μ
  have he : (fun X : Vec d => F (fun a => ((Y + Lslow X) a : ℂ)) (z + Lfast X)) =ᶠ[𝓝 0] H := by
    have heχ' : ∀ᶠ X : Vec d in 𝓝 0, χ (Lslow X) = Lslow X := by
      have ht : Tendsto Lslow (𝓝 0) (𝓝 0) := by
        simpa only [map_zero] using Lslow.continuous.tendsto 0
      exact heχ.comp_tendsto ht
    filter_upwards [heχ'] with X hX
    obtain ⟨h₀, h₁, hc⟩ := base_strip_coordinate_slices (fun Z => F Z (z + Lfast X)) T R hR
      (hRS.trans_le hST) (hhol _) Y
    have hh := localized_double_cauchy_representation R hR χ hχ hbχ hzχ hout
      (fun w v => F (complexBaseShift Y w v) (z + Lfast X)) h₀ h₁ hc M hM
      (fun θ φ => hvalue (D (θ, φ)) (hD (θ, φ)) _) (Lslow X)
    rw [hX, complex_base_shift_real] at hh
    simpa only [H, D, pref, f, cauchyBoundaryCoefficient, mul_one, smul_eq_mul, id_eq] using hh
  exact hreg.contDiffAt.congr_of_eventuallyEq he

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Uniform quantitative Cauchy bounds for genuinely independent slow and fast increments. -/
@[expose] public noncomputable section
open Homogenization Complex Metric MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer

theorem base_fast_joint_exists_jet_bounds {d : ℕ}
    (S T : ℝ) (hS : 0 < S) (hST : S ≤ T) (n : ℕ)
    (Lslow Lfast : Vec d →L[ℝ] Vec 2)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ F : (Fin 2 → ℂ) → Vec 2 → ℂ,
        (∀ z, DifferentiableOn ℂ (fun Z => F Z z) {Z | (∑ a, |(Z a).im|) < T}) →
        (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z : Vec 2,
          ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 => F Z (z + X))) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z, ‖F Z z‖ ≤ M) →
          (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z : Vec 2,
            ∀ j ≤ n, ∀ X, ‖iteratedFDeriv ℝ j (fun X : Vec 2 => F Z (z + X)) X‖ ≤ A j * M) →
          ∀ Y z : Vec 2,
            ContDiffAt ℝ (n : ℕ∞) (fun X : Vec d =>
              F (fun a => ((Y + Lslow X) a : ℂ)) (z + Lfast X)) 0 ∧
            ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun X : Vec d =>
              F (fun a => ((Y + Lslow X) a : ℂ)) (z + Lfast X)) 0‖ ≤ B j * M := by
  let R := S / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hRS : 2 * R < S := by dsimp [R]; linarith only [hS]
  obtain ⟨χ, hχ, heχ, hbχ, hout⟩ := exists_smooth_bounded_local_identity
    (E := Vec 2) (R / 2) (by positivity)
  have hzχ : χ 0 = 0 := heχ.eq_of_nhds
  let μ := cauchyAngleMeasure.prod cauchyAngleMeasure
  let a₀ := ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ ^ 2 * R ^ 2
  have ha₀ : 0 ≤ a₀ := by dsimp [a₀]; positivity
  obtain ⟨Q, hQ, hInt⟩ := localized_joint_cauchy_exists_jet_bounds R hR χ hχ hbχ hzχ hout
    μ n Lslow (fun j => a₀ * (A j * ‖Lfast‖ ^ j))
    (fun j => by have hj := hA j; positivity)
  let B : ℕ → ℝ := fun j => Q j * μ.real Set.univ
  refine ⟨B, fun j => mul_nonneg (hQ j) (measureReal_nonneg), ?_⟩
  intro F hhol hfast M hM hvalue hjet Y z
  let D : ℝ × ℝ → Fin 2 → ℂ := fun p => complexBaseShift Y (circleMap 0 R p.1) (circleMap 0 R p.2)
  have hD (p : ℝ × ℝ) : (∑ a, |(D p a).im|) < S :=
    (complex_base_shift_im_sum_le Y R _ _
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl])
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl])).trans_lt hRS
  let pref : ℝ × ℝ → ℂ := cauchyBoundaryCoefficient R (fun _ _ => 1)
  have hpref : Measurable pref := cauchy_boundary_coefficient_measurable R _ continuous_const
  have hpb (p : ℝ × ℝ) : ‖pref p‖ ≤ a₀ := by
    simpa only [mul_one] using cauchy_boundary_coefficient_norm_le R hR (fun _ _ => 1) 1
      (fun _ _ => by simp only [norm_one, le_refl]) p
  let f : (ℝ × ℝ) → Vec d → ℂ := fun p X => pref p * F (D p) (z + Lfast X)
  have hm (X : Vec d) : Measurable (fun p => f p X) := by
    have hc := (base_strip_coordinate_slices (fun Z => F Z (z + Lfast X)) T R hR
      (hRS.trans_le hST) (hhol _) Y).2.2
    exact hpref.mul hc.measurable
  have hlinear (p : ℝ × ℝ) := linear_parameter_regular_and_jets
    (fun X : Vec 2 => F (D p) (z + X)) n (hfast (D p) (hD p) z) Lfast
    (fun j => A j * M) (hjet (D p) (hD p) z)
  have hs (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞) (f p) :=
    hlinear p |>.1.const_smul (pref p)
  have hf : ∀ l ≤ n, ∀ p X, ‖iteratedFDeriv ℝ l (f p) X‖ ≤ (a₀ * (A l * ‖Lfast‖ ^ l)) * M := by
    intro l hl p X
    change ‖iteratedFDeriv ℝ l (fun X => pref p •
      ((fun Y : Vec 2 => F (D p) (z + Y)) ∘ Lfast) X) X‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hlinear p).1.contDiffAt.of_le
      (by exact_mod_cast hl)), norm_smul]
    exact (mul_le_mul (hpb p) ((hlinear p).2 l hl X) (norm_nonneg _) ha₀).trans_eq
      (by ring)
  obtain ⟨hreg, hjets⟩ := hInt f hm hs M hM hf
  let H : Vec d → ℂ := fun X => ∫ p, f p X * localizedCauchyKernel R χ (p, Lslow X) ∂μ
  have he : (fun X : Vec d => F (fun a => ((Y + Lslow X) a : ℂ)) (z + Lfast X)) =ᶠ[𝓝 0] H := by
    have heχ' : ∀ᶠ X : Vec d in 𝓝 0, χ (Lslow X) = Lslow X := by
      have ht : Tendsto Lslow (𝓝 0) (𝓝 0) := by
        simpa only [map_zero] using Lslow.continuous.tendsto 0
      exact heχ.comp_tendsto ht
    filter_upwards [heχ'] with X hX
    obtain ⟨h₀, h₁, hc⟩ := base_strip_coordinate_slices (fun Z => F Z (z + Lfast X)) T R hR
      (hRS.trans_le hST) (hhol _) Y
    have hh := localized_double_cauchy_representation R hR χ hχ hbχ hzχ hout
      (fun w v => F (complexBaseShift Y w v) (z + Lfast X)) h₀ h₁ hc M hM
      (fun θ φ => hvalue (D (θ, φ)) (hD (θ, φ)) _) (Lslow X)
    rw [hX, complex_base_shift_real] at hh
    simpa only [H, D, pref, f, cauchyBoundaryCoefficient, mul_one, smul_eq_mul, id_eq] using hh
  refine ⟨hreg.contDiffAt.congr_of_eventuallyEq he, ?_⟩
  intro j hj
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  apply (hjets j hj 0).trans_eq
  dsimp [B]
  ring

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Upgrade the certified zero-order operator at an auxiliary radius, preserving its literal coefficients. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]


def higherOrderKernelOperator {a b R ν : ℝ} {D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b R ν 0 D (h := h) (Γ := Γ) (G := G))
    (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R) (K : ℕ)
    (hfin : ∀ i j α d, coefficientSeminorm R K a b (P.B i j α d) ≠ ⊤)
    (hsmooth : ∀ i j α d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (P.B i j α d t))
    (hschur : SchurBound (1 / 8)
      (kernelSchurMatrix ν ρ P.π K D a b P.c P.r P.C P.B)) :
    KernelEnergy.TorusKernelOperator a b ρ ν K D (h := h) (Γ := Γ) (G := G) where
  htime := P.htime
  radius_pos := hρ
  diffusivity_pos := P.diffusivity_pos
  order_ge_two := P.order_ge_two
  π := P.π
  hπ := P.hπ
  B := P.B
  hB_meas := P.hB_meas
  hB_smooth := hsmooth
  hB_per := P.hB_per
  hB_fin := fun i j α d => CycleJointProofs.coefficientSeminorm_radius_ne_top ρ R hρ.le hρR
    K a b (P.B i j α d) (hfin i j α d)
  C := P.C
  S := P.S
  c := P.c
  r := P.r
  hr := P.hr
  hS := fun i j α => spatial_regularizer_all_orders ρ D a b P.c (P.r i j α) (P.S i j α)
    (spatial_regularizer_zero_radius ρ R D a b P.c (P.r i j α) (P.S i j α) (P.hS i j α)) K
  θ := 1 / 8
  hθ := le_rfl
  hschur := hschur

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Normalize the native base strip before taking data-independent Cauchy constants. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem complex_base_real_scale_im_sum (e : ℝ) (he : 0 ≤ e) (Z : Fin 2 → ℂ) :
    (∑ a, |(((e : ℂ) • Z) a).im|) = e * ∑ a, |(Z a).im| := by
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, abs_mul, abs_of_nonneg he]
  rw [Finset.mul_sum]

theorem complex_base_scale_differentiableOn (e T : ℝ) (he : 0 < e)
    (F : (Fin 2 → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F {Z | (∑ a, |(Z a).im|) < e * T}) :
    DifferentiableOn ℂ (fun Z => F ((e : ℂ) • Z)) {Z | (∑ a, |(Z a).im|) < T} := by
  apply hF.comp (differentiable_id.const_smul (e : ℂ)).differentiableOn
  intro Z hZ
  change (∑ a, |(((e : ℂ) • Z) a).im|) < e * T
  rw [complex_base_real_scale_im_sum e he.le]
  exact mul_lt_mul_of_pos_left hZ he

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Normalize the native base length to obtain Cauchy constants fixed before the physical data. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem normalized_base_fast_joint_exists_jet_bounds {d : ℕ} (n : ℕ)
    (Lslow Lfast : Vec d →L[ℝ] Vec 2) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (e mres : ℝ), 0 < e → 0 ≤ mres →
      ∀ F : (Fin 2 → ℂ) → Vec 2 → ℂ,
        (∀ z, DifferentiableOn ℂ (fun Z => F Z z)
          {Z | (∑ a, |(Z a).im|) < e * (3 / 200)}) →
        (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < ((1 + mres / 4) / 100) * e → ∀ z : Vec 2,
          ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 => F Z (z + X))) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < ((1 + mres / 4) / 100) * e →
            ∀ z, ‖F Z z‖ ≤ M) →
          (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < ((1 + mres / 4) / 100) * e → ∀ z : Vec 2,
            ∀ j ≤ n, ∀ X, ‖iteratedFDeriv ℝ j (fun X : Vec 2 => F Z (z + X)) X‖ ≤ A j * M) →
          ∀ Y z : Vec 2,
            ContDiffAt ℝ (n : ℕ∞) (fun X : Vec d =>
              F (fun a => ((e • (Y + Lslow X)) a : ℂ)) (z + Lfast X)) 0 ∧
            ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun X : Vec d =>
              F (fun a => ((e • (Y + Lslow X)) a : ℂ)) (z + Lfast X)) 0‖ ≤ B j * M := by
  obtain ⟨B, hB, hC⟩ := base_fast_joint_exists_jet_bounds (1 / 100) (3 / 200)
    (by norm_num) (by norm_num) n Lslow Lfast A hA
  refine ⟨B, hB, ?_⟩
  intro e mres he hm F hhol hfast M hM hvalue hjet Y z
  have hscale (Z : Fin 2 → ℂ) (hZ : (∑ a, |(Z a).im|) < 1 / 100) :
      (∑ a, |(((e : ℂ) • Z) a).im|) < ((1 + mres / 4) / 100) * e := by
    rw [complex_base_real_scale_im_sum e he.le]
    refine (mul_lt_mul_of_pos_left hZ he).trans_le ?_
    calc
      e * (1 / 100) = (1 / 100) * e := mul_comm _ _
      _ ≤ ((1 + mres / 4) / 100) * e :=
        mul_le_mul_of_nonneg_right (by linarith only [hm]) he.le
  have hc := hC (fun Z z => F ((e : ℂ) • Z) z)
    (fun z => complex_base_scale_differentiableOn e (3 / 200) he (fun Z => F Z z) (hhol z))
    (fun Z hZ z => hfast _ (hscale Z hZ) z) M hM
    (fun Z hZ z => hvalue _ (hscale Z hZ) z)
    (fun Z hZ z => hjet _ (hscale Z hZ) z) Y z
  have heq : (fun X : Vec d => F ((e : ℂ) • fun a => ((Y + Lslow X) a : ℂ))
      (z + Lfast X)) =
      fun X : Vec d => F (fun a => ((e • (Y + Lslow X)) a : ℂ)) (z + Lfast X) := by
    funext X
    congr 1
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [heq] at hc
  exact hc

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Empty high source degrees vanish for genuine smooth inputs, including finite Hilbert coefficients. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ}

theorem sourceCoeff_above_effective_degree_general (K : ℕ) (hK : 1 ≤ K) (hKD : K ≤ D)
    (edge : ConstituentEdges D h) (hz : ∀ v u d, K < d.1 → edge v u d = [])
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : GoodField K Φ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ I,
      GoodField 1 (fun X z => γ.coeff I t X z)) (j : ℕ) (hj : K < j) :
    sourceCoeff edge η j t Φ = fun _ _ => 0 := by
  rw [EntryWeakProofs.sourceCoeff_restrict_effective_order K hKD edge hz]
  rw [sourceCoeff_eq_sourceCoefficientArray
    (EntryWeakProofs.restrictConstituentEdges K hKD edge) hK η t Φ hΦ
    (fun v u d γ hγ I => hΓ v u
      ⟨d.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp d.2).1, (Finset.mem_Icc.mp d.2).2.trans hKD⟩⟩ γ hγ I) j]
  exact sourceCoefficientArray_above_degree _ hK η t Φ j hj

theorem sum_sourceCoeff_restrict_all_degrees (K : ℕ) (hK : 1 ≤ K) (hKD : K ≤ D)
    (edge : ConstituentEdges D h) (hz : ∀ v u d, K < d.1 → edge v u d = [])
    (η t : ℝ) (n : ℕ) (Φ : ℕ → Vec 2 → Vec 2 → ∀ i, h i)
    (hΦ : ∀ j ∈ Finset.range (min D n + 1), GoodField K (Φ j))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ I,
      GoodField 1 (fun X z => γ.coeff I t X z)) :
    (∑ j ∈ Finset.range (min D n + 1), sourceCoeff edge η j t (Φ j)) =
      ∑ j ∈ Finset.range (min K n + 1),
        sourceCoeff (EntryWeakProofs.restrictConstituentEdges K hKD edge) η j t (Φ j) := by
  simp_rw [EntryWeakProofs.sourceCoeff_restrict_effective_order K hKD edge hz]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hnot
  have hjK : K < j := by
    have hb := Finset.mem_range.mp hj
    simp only [Finset.mem_range] at hnot
    omega
  rw [← EntryWeakProofs.sourceCoeff_restrict_effective_order K hKD edge hz]
  exact sourceCoeff_above_effective_degree_general K hK hKD edge hz η t (Φ j)
    (hΦ j hj) hΓ j hjK

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Read the homogeneous kernel initial energy in the actual weighted family norm. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem initial_energy_from_weighted_norm {S : Finset Comp} {K : ℕ}
    (ρ : ℝ) (π w : CompIn S → ℝ) (f : ∀ v : CompIn S, TorusHk K (hr v.1.root))
    (A : ℝ) (hbound : weightedNorm ρ π w f ≤ A) :
    ENNReal.ofReal (Real.sqrt (2 * massNormSq ρ (fun v => π v / w v ^ 2) (fun v => (f v).val))) ≤
      ENNReal.ofReal (Real.sqrt 2 * A) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg 2)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Monotonicity of the actual weighted family norm for positive component weights. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem weightedNorm_mono {S : Finset Comp} {K : ℕ}
    (ρ : ℝ) (π w z : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (hw : ∀ v, 0 ≤ w v) (hmono : ∀ v, w v ≤ z v)
    (f : ∀ v : CompIn S, TorusHk K (hr v.1.root)) :
    weightedNorm ρ π w f ≤ weightedNorm ρ π z f := by
  unfold weightedNorm massNormSq
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (factorialNormSq_nonneg ρ (f v).val)
  simp only [inv_div]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (hw v) (hmono v) 2) (hπ v).le

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The literal dependent-root readout satisfies the scalar factorial-amplitude bound. Root
casts are isometries; no dimension or closed-submodule instance chain is involved. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem factorialNormSq_rootCast {r r' K : ℕ} (h : r = r') (ρ : ℝ)
    (X : TorusHk K (hr r)) :
    factorialNormSq ρ (cast (congrArg (fun s => TorusHk K (hr s)) h) X).val =
      factorialNormSq ρ X.val := by
  subst r'
  rfl

theorem readout_factorial_amplitude {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η ρ : ℝ) (hE : 0 ≤ E)
    (X : ∀ c : CompIn S', TorusHk K (hr c.1.root)) (v : CompIn S) :
    Real.sqrt (factorialNormSq ρ (succReadout m E η K X v).val) ≤
      ∑ c : CompIn S', if compParent m c.1 = v.1 then
        E ^ (η * (compWord m c.1).length) * Real.sqrt (factorialNormSq ρ (X c).val)
        else 0 := by
  classical
  unfold succReadout
  apply (CycleComparison.Coarse.sqrt_fNSq_torus_sum_le ρ Finset.univ _).trans
  apply Finset.sum_le_sum
  intro c _
  split_ifs with h
  · rw [CycleComparison.Coarse.sqrt_fNSq_torus_smul,
      factorialNormSq_rootCast ((compParent_root m c.1).symm.trans (congrArg Comp.root h)),
      abs_of_nonneg (Real.rpow_nonneg hE _)]
  · exact (CycleComparison.Coarse.sqrt_fNSq_torus_zero ρ).le

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Covariance duality survives truncation of the output carrier at the same value class. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem covImage_truncate {K L R : ℕ} (hKL : K ≤ L)
    (P : (Vec 2 → E) → Vec 2 → E) (Z : TorusHk R E) (W : TorusHk L E)
    (hW : IsCovImage P Z W) : IsCovImage P Z (truncateTorusHk hKL W) := by
  have hj := KernelEnergy.truncateTorusHk_toFunction_jet_ae hKL W (valueIndex2 K)
  have hi : truncateJetIndex hKL (valueIndex2 K) = valueIndex2 L := rfl
  rw [hi] at hj
  intro φ hφ hpφ
  calc
    _ = cellInner (W.toFunction.jet (valueIndex2 L)) φ := by
      apply integral_congr_ae
      filter_upwards [hj] with x hx
      rw [hx]
    _ = _ := hW φ hφ hpφ

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Upgrade the certified zero-order operator at an auxiliary radius, preserving its literal coefficients. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]


theorem kernel_operator_order_upgrade {a b R ν : ℝ} {D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b R ν 0 D (h := h) (Γ := Γ) (G := G))
    (hθ : P.θ < 1 / 8) (K : ℕ)
    (hfin : ∀ i j α d, coefficientSeminorm R K a b (P.B i j α d) ≠ ⊤)
    (hsmooth : ∀ i j α d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (P.B i j α d t)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∃ Q : KernelEnergy.TorusKernelOperator a b ρ ν K D (h := h) (Γ := Γ) (G := G),
        Q.π = P.π ∧ Q.B = P.B ∧ Q.C = P.C ∧ Q.S = P.S ∧ Q.c = P.c ∧ Q.r = P.r := by
  obtain ⟨ρ, hρ, hρR, hschur⟩ := kernelSchurBound_auxiliary_radius P hθ K hfin
  exact ⟨ρ, hρ, hρR, higherOrderKernelOperator P ρ hρ hρR K hfin hsmooth hschur,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual lift recursion ignores empty high source degrees at every cell order. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ}

theorem liftA_restrict_all_degrees (K : ℕ) (hK : 1 ≤ K) (hKD : K ≤ D)
    (Q : LiftOperatorData ι h D) (hz : ∀ v u d, K < d.1 → Q.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ)
    (hΦ : ∀ j ∈ Finset.range (min D n + 1),
      GoodField K (liftApply (n - j) (Cc (hh - 1) (n - j)) a t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ I,
      GoodField 1 (fun X z => γ.coeff I t X z)) :
    liftA Q Cc a hh n t = liftA (EntryWeakProofs.restrictLiftData K hKD Q) Cc a hh n t := by
  have hs := sum_sourceCoeff_restrict_all_degrees K hK hKD Q.edge hz Q.η t n
    (fun j => liftApply (n - j) (Cc (hh - 1) (n - j)) a t) hΦ hΓ
  funext X z
  have he := congrArg (fun f : Vec 2 → Vec 2 → ∀ i, h i => f X z) hs
  simp only [Finset.sum_apply] at he
  simp only [liftA, EntryWeakProofs.restrictLiftData]
  rw [he]
end

/-! Every centered recurrence source agrees after removing empty degrees, with explicit smooth-input reserves. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ}

theorem liftCellSource_restrict_all_degrees (K : ℕ) (hK : 1 ≤ K) (hKD : K ≤ D)
    (Q : LiftOperatorData ι h D) (hz : ∀ v u d, K < d.1 → Q.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ)
    (hΦ : ∀ p ≤ hh, ∀ m ≤ n, ∀ j ∈ Finset.range (min D m + 1),
      GoodField K (liftApply (m - j) (Cc (p - 1) (m - j)) a t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ I,
      GoodField 1 (fun X z => γ.coeff I t X z)) :
    liftCellSource Q Cc a hh n t =
      liftCellSource (EntryWeakProofs.restrictLiftData K hKD Q) Cc a hh n t := by
  let Q' := EntryWeakProofs.restrictLiftData K hKD Q
  have hA (p m : ℕ) (hp : p ≤ hh) (hm : m ≤ n) :
      liftA Q Cc a p m t = liftA Q' Cc a p m t :=
    liftA_restrict_all_degrees K hK hKD Q hz Cc a p m t (hΦ p hp m hm) hΓ
  have hmean (p m : ℕ) (hp : p ≤ hh) (hm : m ≤ n) :
      liftMean Q Cc a p m t = liftMean Q' Cc a p m t := by
    funext X
    simp only [liftMean, hA p m hp hm]
  funext X z
  have hs : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q' Cc a p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p hp
    have hp₂ : p.2 ≤ hh := by have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega
    exact congrFun (congrFun (CycleComparison.Lift.liftApply_input_congr_at_time j (Cc p.1 j)
      (liftMean Q Cc a p.2 (n - j)) (liftMean Q' Cc a p.2 (n - j)) t
      (hmean p.2 (n - j) hp₂ (Nat.sub_le _ _))) X) z
  simp only [liftCellSource, hA hh n le_rfl le_rfl, hmean hh n le_rfl le_rfl, hs]
  rfl
end

end AVRegularity.Construction.Preservation.FullLift
end
end
