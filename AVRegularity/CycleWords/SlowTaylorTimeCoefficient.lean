-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CenteredCellBlochGradientLp
public import AVRegularity.Weighted.BoundedWeightRoot
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.SlowJet
import AVRegularity.CycleWords.CellComplexH1Separability
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.TaylorIntegral

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The positive sampled slow Taylor polynomial has a uniform normalized fast-jet and moment budget. -/

theorem positiveSlowTaylor_sample_jet_budget (K J : ℕ) (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → Vec 2 → ℝ), IsBoxSmooth K J f →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → ζ ≤ 1 → 0 ≤ B → δ = ζ * ϖ →
      (∀ r ≤ K, ∀ j ≤ J, ∀ X z, ρ ^ j *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ ≤ M r * B) →
      ∀ X j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => taylorSlow 1 K (fun X' => f X' z) X (δ • z)) z‖ ≤
          C * B * ζ * polynomialMomentRoot ϖ z ^ K := by
  have hh (r : ℕ) := slowHomogeneous_sample_jet_budget r J
  choose C hC hb using hh
  let price := ∑ r ∈ Finset.Icc 1 K, ((r.factorial : ℝ))⁻¹ * C r * |M r|
  refine ⟨price, Finset.sum_nonneg (fun r _ =>
    mul_nonneg (mul_nonneg (by positivity) (hC r)) (abs_nonneg _)), ?_⟩
  intro f hf ϖ ρ δ ζ B hϖ hρ hscale hζ hζ1 hB hδ hjet X j hj z
  let p := fun r (z : Vec 2) => iteratedFDeriv ℝ r (fun X' => f X' z) X (fun _ => δ • z)
  have hp (r : ℕ) (hr : r ≤ K) : ContDiff ℝ (j : ℕ) (p r) :=
    Weighted.multilinear_diagonal_contDiff j _
      ((CoarseFluxDiff.contDiff_slowJet (hf.mono hr le_rfl) X).of_le (by exact_mod_cast hj)) δ
  have he : (fun z => taylorSlow 1 K (fun X' => f X' z) X (δ • z)) =
      ∑ r ∈ Finset.Icc 1 K, ((r.factorial : ℝ))⁻¹ • p r := by
    funext y
    simp only [taylorSlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, p]
  rw [he, iteratedFDeriv_sum_apply (fun r hr => by
    have hs : ContDiffAt ℝ (j : ℕ) (p r) z := (hp r (Finset.mem_Icc.mp hr).2).contDiffAt
    rw [show ((r.factorial : ℝ))⁻¹ • p r = (fun y => ((r.factorial : ℝ))⁻¹ • p r y) by funext y; rfl]
    exact hs.const_smul _)]
  calc
    _ ≤ ρ ^ j * ∑ r ∈ Finset.Icc 1 K,
        ‖iteratedFDeriv ℝ j (((r.factorial : ℝ))⁻¹ • p r) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hρ j)
    _ ≤ ∑ r ∈ Finset.Icc 1 K,
        ((r.factorial : ℝ))⁻¹ * C r * |M r| * B * ζ * polynomialMomentRoot ϖ z ^ K := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hrK := (Finset.mem_Icc.mp hr).2
      have hbound : ∀ k ≤ J, ∀ X z, ρ ^ k *
          ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ k (f X') z) X‖ ≤ |M r| * B := by
        intro k hk X' z'
        exact (hjet r hrK k hk X' z').trans (mul_le_mul_of_nonneg_right (le_abs_self _) hB)
      have ht := hb r f (hf.mono hrK le_rfl) ϖ ρ δ ζ (|M r| * B)
        hϖ hρ hscale hζ (mul_nonneg (abs_nonneg _) hB) hδ hbound X j hj z
      have hroot : polynomialMomentRoot ϖ z ^ r ≤ polynomialMomentRoot ϖ z ^ K :=
        pow_le_pow_right₀ (polynomialMomentRoot_one_le ϖ z) hrK
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hzpow : ζ ^ r ≤ ζ := by
        rw [show r = (r - 1) + 1 by omega, pow_succ]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (pow_le_one₀ hζ hζ1 (n := r - 1)) hζ
      have hsmall : ζ ^ r * polynomialMomentRoot ϖ z ^ r ≤ ζ * polynomialMomentRoot ϖ z ^ K :=
        mul_le_mul hzpow hroot
          (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) r) hζ
      have hs := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (hC r) (mul_nonneg (abs_nonneg (M r)) hB))
      rw [iteratedFDeriv_const_smul_apply (hp r hrK).contDiffAt, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      have ht' := mul_le_mul_of_nonneg_left (ht.trans (by simpa only [mul_assoc] using hs))
        (inv_nonneg.mpr (Nat.cast_nonneg r.factorial))
      convert ht' using 1 <;> ring
    _ = _ := by dsimp only [price]; rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

/-! The sampled slow Taylor polynomial has a uniform normalized fast-jet and moment budget. -/

theorem slowTaylor_sample_jet_budget (lo K J : ℕ) (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → Vec 2 → ℝ), IsBoxSmooth K J f →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → ζ ≤ 1 → 0 ≤ B → δ = ζ * ϖ →
      (∀ r ≤ K, ∀ j ≤ J, ∀ X z, ρ ^ j *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ ≤ M r * B) →
      ∀ X j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => taylorSlow lo K (fun X' => f X' z) X (δ • z)) z‖ ≤
          C * B * polynomialMomentRoot ϖ z ^ K := by
  have hh (r : ℕ) := slowHomogeneous_sample_jet_budget r J
  choose C hC hb using hh
  let price := ∑ r ∈ Finset.Icc lo K, ((r.factorial : ℝ))⁻¹ * C r * |M r|
  refine ⟨price, Finset.sum_nonneg (fun r _ =>
    mul_nonneg (mul_nonneg (by positivity) (hC r)) (abs_nonneg _)), ?_⟩
  intro f hf ϖ ρ δ ζ B hϖ hρ hscale hζ hζ1 hB hδ hjet X j hj z
  let p := fun r (z : Vec 2) => iteratedFDeriv ℝ r (fun X' => f X' z) X (fun _ => δ • z)
  have hp (r : ℕ) (hr : r ≤ K) : ContDiff ℝ (j : ℕ) (p r) :=
    Weighted.multilinear_diagonal_contDiff j _
      ((CoarseFluxDiff.contDiff_slowJet (hf.mono hr le_rfl) X).of_le (by exact_mod_cast hj)) δ
  have he : (fun z => taylorSlow lo K (fun X' => f X' z) X (δ • z)) =
      ∑ r ∈ Finset.Icc lo K, ((r.factorial : ℝ))⁻¹ • p r := by
    funext y
    simp only [taylorSlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, p]
  rw [he, iteratedFDeriv_sum_apply (fun r hr => by
    have hs : ContDiffAt ℝ (j : ℕ) (p r) z := (hp r (Finset.mem_Icc.mp hr).2).contDiffAt
    rw [show ((r.factorial : ℝ))⁻¹ • p r = (fun y => ((r.factorial : ℝ))⁻¹ • p r y) by funext y; rfl]
    exact hs.const_smul _)]
  calc
    _ ≤ ρ ^ j * ∑ r ∈ Finset.Icc lo K,
        ‖iteratedFDeriv ℝ j (((r.factorial : ℝ))⁻¹ • p r) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hρ j)
    _ ≤ ∑ r ∈ Finset.Icc lo K,
        ((r.factorial : ℝ))⁻¹ * C r * |M r| * B * polynomialMomentRoot ϖ z ^ K := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hrK := (Finset.mem_Icc.mp hr).2
      have hbound : ∀ k ≤ J, ∀ X z, ρ ^ k *
          ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ k (f X') z) X‖ ≤ |M r| * B := by
        intro k hk X' z'
        exact (hjet r hrK k hk X' z').trans (mul_le_mul_of_nonneg_right (le_abs_self _) hB)
      have ht := hb r f (hf.mono hrK le_rfl) ϖ ρ δ ζ (|M r| * B)
        hϖ hρ hscale hζ (mul_nonneg (abs_nonneg _) hB) hδ hbound X j hj z
      have hroot : polynomialMomentRoot ϖ z ^ r ≤ polynomialMomentRoot ϖ z ^ K :=
        pow_le_pow_right₀ (polynomialMomentRoot_one_le ϖ z) hrK
      have hsmall : ζ ^ r * polynomialMomentRoot ϖ z ^ r ≤ polynomialMomentRoot ϖ z ^ K :=
        (mul_le_mul_of_nonneg_right (pow_le_one₀ hζ hζ1)
          (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) r)).trans
            (by simpa only [one_mul] using hroot)
      have hs := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (hC r) (mul_nonneg (abs_nonneg (M r)) hB))
      rw [iteratedFDeriv_const_smul_apply (hp r hrK).contDiffAt, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      have ht' := mul_le_mul_of_nonneg_left (ht.trans (by simpa only [mul_assoc] using hs))
        (inv_nonneg.mpr (Nat.cast_nonneg r.factorial))
      convert ht' using 1 <;> ring
    _ = _ := by dsimp only [price]; rw [Finset.sum_mul, Finset.sum_mul]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! An unweighted spatial L2 curve has finite integrated literal quadratic energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unweightedSpatialLpTimeEnergy_ne_top (μ : Measure ℝ)
    (R : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hR : MemLp R 2 μ) :
    (∫⁻ t, Weighted.chartScalarEnergy (fun _ : Vec 2 => (1 : ℝ)) (R t) ∂μ) ≠ ⊤ := by
  have he : ∀ᵐ t ∂μ, R t =ᵐ[volume] (fun x => (1 : ℝ) • R t x) := by
    filter_upwards with t
    filter_upwards with x
    rw [one_smul]
  have hh := Weighted.weighted_representative_time_energy_ne_top
    (fun _ : Vec 2 => (1 : ℝ)) μ R R hR he
  simpa only [one_pow] using hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A fixed integrability bound for the real-frequency cell generator. -/

def cellPhysicalDerivativeBound (i : Fin 2) : ℝ :=
  ‖cellDerivativeCLM i‖ + (2 * Real.pi) * ‖torusHkValueCLM (E := ℂ) (K := 1)‖

theorem cellPhysicalDerivativeBound_nonneg (i : Fin 2) :
    0 ≤ cellPhysicalDerivativeBound i := by unfold cellPhysicalDerivativeBound; positivity

theorem cellPhysicalShiftedDerivative_norm_le (θ : Vec 2)
    (hθ : ∀ i, ‖Complex.I * planePhysicalBlochShift θ i‖ ≤ 2 * Real.pi)
    (i : Fin 2) (u : TorusHk 1 ℂ) :
    ‖cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i u‖ ≤
      cellPhysicalDerivativeBound i * ‖u‖ := by
  change ‖cellDerivativeCLM i u +
    (Complex.I * planePhysicalBlochShift θ i) • torusHkValueCLM u‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have hd := (cellDerivativeCLM i).le_opNorm u
  have hv := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm u
  have hp := mul_le_mul (hθ i) hv (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.pi)
  calc
    _ ≤ ‖cellDerivativeCLM i‖ * ‖u‖ +
      (2 * Real.pi) * (‖torusHkValueCLM (E := ℂ) (K := 1)‖ * ‖u‖) := add_le_add hd hp
    _ = _ := by unfold cellPhysicalDerivativeBound; ring

def cellPhysicalGeneratorBound (V : ℝ) : ℝ :=
  (∑ i : Fin 2, ∑ j : Fin 2, 2 * cellPhysicalDerivativeBound i * cellPhysicalDerivativeBound j) +
    ∑ i : Fin 2, |V| * cellPhysicalDerivativeBound i * ‖torusHkValueCLM (E := ℂ) (K := 1)‖

theorem cellPhysicalGenerator_abs_le
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Vec 2) (hθ : ∀ i, ‖Complex.I * planePhysicalBlochShift θ i‖ ≤ 2 * Real.pi)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    |cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb t u z| ≤
      cellPhysicalGeneratorBound V * ‖u‖ * ‖z‖ := by
  have hbnd := cellGeneratorForm_abs_le
    ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V 0 hv hb (fun _ => by simp) t u z
  have hstar : (fun i => star (planePhysicalBlochShift θ i)) = planePhysicalBlochShift θ :=
    funext (planePhysicalBlochShift_real θ)
  simp only [hstar, zero_mul, add_zero] at hbnd
  apply hbnd.trans
  have hu i := cellPhysicalShiftedDerivative_norm_le θ hθ i u
  have hz i := cellPhysicalShiftedDerivative_norm_le θ hθ i z
  have hvz := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm z
  calc
    _ ≤ (∑ i : Fin 2, ∑ j : Fin 2,
        2 * (cellPhysicalDerivativeBound i * ‖u‖) * (cellPhysicalDerivativeBound j * ‖z‖)) +
      ∑ i : Fin 2, |V| * (cellPhysicalDerivativeBound i * ‖u‖) *
        (‖torusHkValueCLM (E := ℂ) (K := 1)‖ * ‖z‖) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hu i) (by norm_num))
            (hz j) (norm_nonneg _) (mul_nonneg (by norm_num)
              (mul_nonneg (cellPhysicalDerivativeBound_nonneg i) (norm_nonneg u)))
      · exact Finset.sum_le_sum fun i _ => by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hu i) (abs_nonneg V)) hvz
            (norm_nonneg _) (mul_nonneg (abs_nonneg V)
              (mul_nonneg (cellPhysicalDerivativeBound_nonneg i) (norm_nonneg u)))
    _ = _ := by unfold cellPhysicalGeneratorBound; simp only [Fin.sum_univ_two]; ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Jointly measurable generator pairings of genuine variable H1 fields. -/

local instance cellPhysicalGeneratorVariableStateMeasurable : MeasurableSpace CellComplexH1 :=
  borel CellComplexH1

local instance cellPhysicalGeneratorVariableStateBorel : BorelSpace CellComplexH1 := ⟨rfl⟩

theorem cellPhysicalGenerator_variable_stronglyMeasurable
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u z : Vec 2 × ℝ → CellComplexH1) (hu : StronglyMeasurable u)
    (hz : StronglyMeasurable z) :
    StronglyMeasurable (fun p : Vec 2 × ℝ => cellGeneratorForm
      ⟨fun t _ => G t, v, planePhysicalBlochShift p.1, 0⟩ hG V hv hb p.2
        (cellComplexH1RealEquiv (u p)) (cellComplexH1RealEquiv (z p))) := by
  apply caratheodoryFamily_stronglyMeasurable
    (fun p : Vec 2 × ℝ => fun w : CellComplexH1 × CellComplexH1 => cellGeneratorForm
      ⟨fun t _ => G t, v, planePhysicalBlochShift p.1, 0⟩ hG V hv hb p.2
        (cellComplexH1RealEquiv w.1) (cellComplexH1RealEquiv w.2)) _ _
    (fun p => (u p, z p)) (hu.prodMk hz)
  · intro p
    exact (cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift p.1, 0⟩
      hG V hv hb p.2).continuous.comp
        (cellComplexH1RealEquiv.continuous.comp continuous_fst) |>.clm_apply
          (cellComplexH1RealEquiv.continuous.comp continuous_snd)
  · intro w
    exact cellPhysicalGenerator_fixedPair_stronglyMeasurable G hG v V hv hb
      (cellComplexH1RealEquiv w.1) (cellComplexH1RealEquiv w.2)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The actual polynomial weights have uniformly controlled scalar adjoint defects. -/

theorem adjointCellQuadratic_space_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2) (t : ℝ) (n : ℕ) :
    ContDiff ℝ n (adjointCellQuadratic α q Λ ζ m ν B T yc t) := by
  exact ((contDiff_const.add ((adjointCellCoordinate_space_contDiff hΛ hζ ν B T yc t 0 n).pow 2)).add
    ((adjointCellCoordinate_space_contDiff hΛ hζ ν B T yc t 1 n).pow 2))

theorem adjointCellQuadratic_time_differentiable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc z : Vec 2) :
    Differentiable ℝ (fun t => adjointCellQuadratic α q Λ ζ m ν B T yc t z) := by
  have h0 := (adjointCellCoordinate_time_contDiff (α := α) (q := q) (m := m)
    hΛ hζ ν B T yc z 0 1).differentiable (by norm_num)
  have h1 := (adjointCellCoordinate_time_contDiff (α := α) (q := q) (m := m)
    hΛ hζ ν B T yc z 1 1).differentiable (by norm_num)
  exact ((differentiable_const 1).fun_add (h0.fun_pow 2)).fun_add (h1.fun_pow 2)

theorem adjointCellPolynomialWeight_defect {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (hdur : Real.sqrt T * ocEll q Λ m ν / ocTau α q Λ m *
      Real.exp (-Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) ≤ 1)
    (yc : Vec 2) (n : ℕ) (t : ℝ) (z : Vec 2) :
    scalarAdjointOperator (ocCellDrift α q Λ ζ m ν yc)
      (adjointCellPolynomialWeight α q Λ ζ m ν B T yc n) t z ≤
      ((n : ℝ) * (4 * K * (1 + C) + 16 * C) + (n : ℝ) ^ 2 * (32 * C)) *
        (ocEll q Λ m ν ^ 2 / T) * adjointCellPolynomialWeight α q Λ ζ m ν B T yc n t z := by
  change scalarAdjointOperator _ (fun s x => adjointCellQuadratic α q Λ ζ m ν B T yc s x ^ n) t z ≤ _
  rw [scalarAdjointOperator_power _ _
    (fun s => adjointCellQuadratic_space_contDiff hΛ hζ ν B T yc s 2)
    (fun x => adjointCellQuadratic_time_differentiable hΛ hζ ν B T yc x)]
  have hU : 1 ≤ adjointCellQuadratic α q Λ ζ m ν B T yc t z := by
    unfold adjointCellQuadratic
    nlinarith only [sq_nonneg (adjointCellCoordinate α q Λ ζ m ν B T yc t z 0),
      sq_nonneg (adjointCellCoordinate α q Λ ζ m ν B T yc t z 1)]
  have hh := polynomial_power_defect_budget _ _ _ _ _ n hU (by positivity) (by positivity)
    (adjointCellQuadratic_defect hΛ hζ hν hB hT hC he K hK hb hdur yc t z)
    (adjointCellQuadratic_gradient_budget hΛ hζ hν hB hT hC he yc t z)
  convert hh using 1
  unfold adjointCellPolynomialWeight adjointCellQuadratic
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Reserved normalized jets of the literal slow Taylor remainder. -/

theorem geometryTaylor_remainder_jet_budget (K J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → ℝ), ContDiff ℝ (J + (K + 1) : ℕ) f →
      ∀ (ϖ ρ ζ A : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → ζ ≤ 1 → 0 ≤ A →
      (∀ j ≤ J, ∀ y, ‖iteratedFDeriv ℝ (j + (K + 1)) f y‖ ≤
        A * (ζ * ϖ) ^ (j + (K + 1))) →
      ∀ j ≤ J, ∀ z : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => f z - taylorSlow 0 K f 0 z) z‖ ≤
          C * A * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  obtain ⟨C, hC, hb⟩ := integralMultilinear_polynomial_jet_budget (K + 1) J
  refine ⟨((K.factorial : ℝ))⁻¹ * 2 ^ (K + 1) * C, by positivity, ?_⟩
  intro f hf ϖ ρ ζ A hϖ hρ hscale hζ hζ1 hA hjet j hj z
  let τ : ℝ → ℝ := fun t => max 0 (min 1 t)
  have ht₀ (t : ℝ) : 0 ≤ τ t := le_max_left _ _
  have ht₁ (t : ℝ) : τ t ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
  let a := fun t (x : Vec 2) => ((1 - τ t) ^ K * (ϖ ^ (K + 1))⁻¹) •
    iteratedFDeriv ℝ (K + 1) f ((τ t / ϖ) • x)
  have hfield : ContDiff ℝ (J : ℕ) (iteratedFDeriv ℝ (K + 1) f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast le_refl (J + (K + 1)))
  have ha (t : ℝ) : ContDiff ℝ (J : ℕ) (a t) :=
    (hfield.comp (contDiff_id.const_smul (τ t / ϖ))).const_smul _
  have hab (t : ℝ) (w : DerivativeWord2 (K + 1)) (k : ℕ) (hk : k ≤ J) (x : Vec 2) :
      ‖iteratedFDeriv ℝ k (fun x => a t x (fun i => basisVec (w i))) x‖ ≤ A * ζ ^ (K + 1) := by
    exact taylorIntegral_coefficient_jet_le (K + 1) J K hf hϖ hζ hζ1
      (ht₀ t) (ht₁ t) hA hjet w k hk x
  have hm (x : Vec 2) : Measurable (fun t => a t x (fun _ => x)) := by
    apply Continuous.measurable
    have ht : Continuous τ := continuous_const.max (continuous_const.min continuous_id)
    have harg : Continuous (fun t => (τ t / ϖ) • x) := (ht.div_const ϖ).smul continuous_const
    exact ((((continuous_const.sub ht).pow K).mul continuous_const).smul
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin (K + 1) => Vec 2) ℝ
        (fun _ => x)).continuous.comp (hfield.continuous.comp harg)))
  let F := fun x : Vec 2 => ∫ t, a t x (fun _ => x) ∂μ
  have hB : 0 ≤ A * ζ ^ (K + 1) := mul_nonneg hA (pow_nonneg hζ _)
  have hbudget : ∀ k ≤ J, ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤
      C * (A * ζ ^ (K + 1)) * (1 + ‖x‖) ^ (K + 1) := by
    intro k hk x
    have hh := hb μ a hm ha (A * ζ ^ (K + 1)) hB hab k hk x
    have hmass : μ.real Set.univ = 1 := by
      simp [μ, measureReal_def, Real.volume_Ioc]
    simpa only [hmass, mul_one] using hh
  obtain ⟨C₁, hC₁, hb₁⟩ := variableMultilinear_polynomial_jet_budget (K + 1) J
  have hFsmooth : ContDiff ℝ (J : ℕ∞) F := by
    apply parameter_integral_contDiff_growth μ J (fun t x => a t x (fun _ => x)) hm
      (fun t => ?_) (fun _ => C₁ * (A * ζ ^ (K + 1)))
      (fun _ => mul_nonneg hC₁ hB) (K + 1)
      (fun k hk t x => hb₁ a ha (A * ζ ^ (K + 1)) hB hab t k hk x)
    have hh := Weighted.multilinear_diagonal_contDiff J (a t) (ha t) 1
    simpa only [one_smul] using hh.of_le (by exact_mod_cast le_refl J)
  have he : (fun z : Vec 2 => f z - taylorSlow 0 K f 0 z) =
      fun z => ((K.factorial : ℝ))⁻¹ • F (ϖ • z) := by
    funext y
    have ht := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := 0) (y := y) (n := K)
      (fun t _ => (hf.of_le (by exact_mod_cast Nat.le_add_left (K + 1) J)).contDiffAt)
    have hp : taylorSlow 0 K f 0 y =
        ∑ k ∈ Finset.range (K + 1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 (fun _ => y) := by
      simp only [taylorSlow, ← Nat.range_succ_eq_Icc_zero, smul_eq_mul]
    rw [hp]
    simp only [zero_add] at ht
    rw [ht, add_sub_cancel_left]
    congr 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htau : τ t = t := by
      dsimp only [τ]
      rw [min_eq_right ht.2, max_eq_right ht.1.le]
    dsimp only [F, μ, a]
    rw [htau, smul_smul, div_mul_cancel₀ _ hϖ.ne']
    rw [smul_apply,
      (iteratedFDeriv ℝ (K + 1) f (t • y)).map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]
    congr 1
    field_simp
  rw [he]
  have hFj : ContDiff ℝ (j : ℕ) F := hFsmooth.of_le (by exact_mod_cast hj)
  have hcomp : ContDiff ℝ (j : ℕ) (fun z : Vec 2 => F (ϖ • z)) :=
    hFj.comp (contDiff_id.const_smul ϖ)
  rw [iteratedFDeriv_const_smul_apply' hcomp.contDiffAt, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hr := polynomialJet_rescaling_le (K + 1) j hFj hϖ.le hρ hscale
    (mul_nonneg hC hB) (hbudget j hj) z
  convert mul_le_mul_of_nonneg_left hr
    (inv_nonneg.mpr (Nat.cast_nonneg K.factorial)) using 1 <;> ring

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! The actual finite derivative envelope determines a uniform remainder insertion constant. -/

theorem geometryTaylor_remainder_envelope (K J : ℕ) (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → ℝ), ContDiff ℝ (K + 1 + J : ℕ) f →
      ∀ (ϖ ρ ζ g : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → ζ ≤ 1 → 0 ≤ g →
      (∀ r, K + 1 ≤ r → r ≤ K + 1 + J → ∀ y,
        ‖iteratedFDeriv ℝ r f y‖ ≤ M r * g * (ζ * ϖ) ^ r) →
      ∀ j ≤ J, ∀ z : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => f z - taylorSlow 0 K f 0 z) z‖ ≤
          C * g * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  obtain ⟨C, hC, hb⟩ := geometryTaylor_remainder_jet_budget K J
  let A := ∑ j ∈ Finset.range (J + 1), |M (j + (K + 1))|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C * A, mul_nonneg hC hA, ?_⟩
  intro f hf ϖ ρ ζ g hϖ hρ hscale hζ hζ1 hg hjet j hj z
  have hjets : ∀ k ≤ J, ∀ y, ‖iteratedFDeriv ℝ (k + (K + 1)) f y‖ ≤
      (A * g) * (ζ * ϖ) ^ (k + (K + 1)) := by
    intro k hk y
    have hM : M (k + (K + 1)) ≤ A :=
      (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (M (i + (K + 1))))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    exact (hjet (k + (K + 1)) (by omega) (by omega) y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hg)
        (pow_nonneg (mul_nonneg hζ hϖ.le) _))
  have hh := hb f (by simpa only [Nat.add_comm J (K + 1)] using hf)
    ϖ ρ ζ (A * g) hϖ hρ hscale hζ hζ1 (mul_nonneg hA hg) hjets j hj z
  simpa only [mul_assoc] using hh

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The native integrated identity includes integrability of its scalar spatial action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_rhs_integrableOn
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (F : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (PiLp 2 (fun _ : Fin 2 => h p.2)))
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun p : Fin 1 × ι => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w)
    (i : Fin 1 × ι) (φ : PlaneHk Set.univ 1 (h i.2)) :
    IntegrableOn (fun t => ∫ x, Weighted.planeScalarRawRhs (κ i.1 i.2)
      (v t) (G t) (w i t) (F i t) φ x) (Icc a b) := by
  have he := (hsln.2.2.2.2 i b ⟨hab, le_rfl⟩ φ).2.2.2.1
  change IntegrableOn (fun t => ∫ x,
    -(∑ k : Fin 2, v t x k * inner ℝ
      ((w i t).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
      (φ.toFunction.jet (valueIndex2 1) x))
    - 1 * (∑ k : Fin 2, inner ℝ
      ((w i t).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
      (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x))
    - (∑ k : Fin 2, inner ℝ
      (Weighted.scalarChainFlux G κ (fun p => w p t) i t x k +
        (F i t).toFunction.jet (valueIndex2 (κ i.1 i.2)) x k)
      (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x))
    + inner ℝ ((0 : PlaneHk Set.univ (κ i.1 i.2) (h i.2)).toFunction.jet
      (valueIndex2 (κ i.1 i.2)) x) (φ.toFunction.jet (valueIndex2 1) x)
    ∂(volume.restrict Set.univ)) (Ioc a b) at he
  simpa only [IntegrableOn, Measure.restrict_univ, restrict_Ioc_eq_restrict_Icc,
    Weighted.scalarChainFlux_eq, one_mul, Weighted.planeScalarRawRhs] using he

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! A bounded family slot gives one sampled Taylor constant for all original positive prices. -/

theorem slowTaylor_uniform_reserved_budget (K Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≤ Nmax, ∀ (f : Vec 2 → Vec 2 → ℝ),
      ContDiff ℝ (K + N : ℕ) (Function.uncurry f) →
      ∀ (ϖ ρ δ ζ R : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
        0 ≤ ζ → ζ ≤ 1 → 0 < R → δ = ζ * ϖ →
      ∀ (M : ℕ → ℝ), (∀ r, 0 ≤ M r) →
      (∀ r ≤ K, ∀ b ≤ N, ∀ X z, ρ ^ b *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ M r / R) →
      ∀ X0 j, j ≤ N → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z =>
          taylorSlow 0 K (fun X' => f X' z) X0 (δ • z)) z‖ ≤
          C * (∑ r ∈ Finset.range (K + 1), M r) / R * polynomialMomentRoot ϖ z ^ K := by
  classical
  have hs (N : ℕ) := slowTaylor_sample_jet_budget 0 K N (fun _ => 1)
  choose C₀ hC₀ h₀ using hs
  let C := ∑ N ∈ Finset.range (Nmax + 1), C₀ N
  have hC : 0 ≤ C := Finset.sum_nonneg (fun N _ => hC₀ N)
  refine ⟨C, hC, ?_⟩
  intro N hN f hf ϖ ρ δ ζ R hϖ hρ hscale hζ hζ1 hR hδ M hM hb X0 j hj z
  let B := (∑ r ∈ Finset.range (K + 1), M r) / R
  have hB : 0 ≤ B := div_nonneg (Finset.sum_nonneg (fun r _ => hM r)) hR.le
  have hb' (r : ℕ) (hr : r ≤ K) (b : ℕ) (hbN : b ≤ N) (X z : Vec 2) :
      ρ ^ b * ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ 1 * B := by
    rw [one_mul]
    exact (hb r hr b hbN X z).trans (div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun r _ => hM r) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))) hR.le)
  have hh := h₀ N f (Weighted.isBoxSmooth_of_joint_contDiff K N f hf)
    ϖ ρ δ ζ B hϖ hρ hscale hζ hζ1 hB hδ hb' X0 j hj z
  have hCN : C₀ N ≤ C := Finset.single_le_sum (fun N _ => hC₀ N)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hN))
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCN hB)
    (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) K)
  have hh' := hh.trans hm
  simpa only [B, mul_div_assoc] using hh'

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The actual polynomial weights have a contrast uniform logarithmic gradient bound. -/

theorem adjointCellPolynomialWeight_gradient_budget {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (yc : Vec 2) (n : ℕ) (t : ℝ) (z : Vec 2) :
    (∑ i : Fin 2, (fderiv ℝ (adjointCellPolynomialWeight α q Λ ζ m ν B T yc n t) z (basisVec i)) ^ 2) /
        adjointCellPolynomialWeight α q Λ ζ m ν B T yc n t z ^ 2 ≤
      (n : ℝ) ^ 2 * (32 * C) * (ocEll q Λ m ν ^ 2 / T) := by
  have hW := adjointCellPolynomialWeight_pos α q Λ ζ m ν B T yc n t z
  apply (div_le_iff₀ (pow_pos hW 2)).2
  change (∑ i : Fin 2, (fderiv ℝ
      (fun x => adjointCellQuadratic α q Λ ζ m ν B T yc t x ^ n) z (basisVec i)) ^ 2) ≤ _
  simp_rw [polynomial_weight_gradient _
    ((adjointCellQuadratic_space_contDiff hΛ hζ ν B T yc t 1).differentiable (by norm_num))]
  have hg := adjointCellQuadratic_gradient_budget hΛ hζ hν hB hT hC he yc t z
  have hh := polynomial_power_gradient_budget n hg
  simp only [Fin.sum_univ_two] at hh ⊢
  convert hh using 1 <;> simp only [adjointCellPolynomialWeight, adjointCellQuadratic] <;> ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.EntryWeakProofs
namespace AVRegularity.CycleWords

/-! A common geometric native coefficient radius yields smooth literal spatial Taylor series. -/

theorem fibreRowCoefficients_series_contDiff_of_native_coefficients
    (k : ℕ × ℕ → ℝ → ℂ) (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (t : ℝ)
    (ha : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (a p t))
    (hp : ∀ p, AVenhance.IsZ2Periodic (a p t)) (A : ℝ) (hA : 0 ≤ A)
    (M : ℕ → ℝ)
    (hex : ∀ K : ℕ, ∃ U : ℕ × ℕ → TorusHk K ℂ,
      (∀ p, a p t =ᵐ[volume.restrict AVenhance.unitCube] (torusHkValueCLM (U p) : Vec 2 → ℂ)) ∧
      (∀ p, ‖U p‖ ≤ M K * A ^ (p.1 + p.2)))
    (ξ : Fin 2 → ℂ) (hξ : A * ‖ξ‖ < 1)
    (hk : Summable (fun p => ‖fibreMonomial ξ p * k p t‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun (fibreRowCoefficients k a) ξ t) := by
  apply fibreRowCoefficients_series_contDiff_of_geometric_jets k a t ha A hA
    (fun j => torusHigherClassicalSobolevConstant (j + 2) j * M (j + 2)) _ ξ hξ hk
  exact native_coefficients_periodic_derivative_geometric_bound a t ha hp A M hex

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A periodic smooth column gives a periodic representative of the entrance projection. -/

theorem torusHigher_periodic_projection_representative (J : ℕ)
    (g₀ f : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀) (hf : ContDiff ℝ (J : ℕ∞) f)
    (hpf : AVenhance.IsZ2Periodic f) (R : TorusHk J ℂ)
    (hRf : (torusHkValueCLM R : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f)
    (ell : ComplexCellL2) (L B : ℝ) (hL : ‖ell‖ ≤ L) (hB : ‖R‖ ≤ B) :
    let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
    let c := cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((torusHkValueCLM initial - cellScalarCLM c (torusHkValueCLM R) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (1 + L * B) * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) *
            cellSobolevNorm J g₀ := by
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  let c := cellComplexPair (torusHkValueCLM initial)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)
  let W := initial - torusHigherScalarCLM J c R
  let g₁ := fun x => g₀ x - c * f x
  have hg₁ : ContDiff ℝ (J : ℕ∞) g₁ := hg₀.sub (contDiff_const.mul hf)
  have hp₁ : AVenhance.IsZ2Periodic g₁ := by
    intro n x
    dsimp only [g₁]
    rw [hp₀ n x, hpf n x]
  have he : ((torusHkValueCLM initial - cellScalarCLM c (torusHkValueCLM R) : ComplexCellL2) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] g₁ := by
    filter_upwards [Lp.coeFn_sub (torusHkValueCLM initial) (cellScalarCLM c (torusHkValueCLM R)),
      finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀, cellScalarCLM_ae c (torusHkValueCLM R), hRf]
      with x hx hi hc hr
    rw [hx]
    simp only [Pi.sub_apply]
    rw [hi, hc, hr]
  have hC : 0 ≤ 1 + L * B := by
    have hL0 := (norm_nonneg ell).trans hL
    have hB0 := (norm_nonneg R).trans hB
    positivity
  have hn := torusHigher_normalized_projection_norm J initial R ell L B hL hB
  have hn2 : ‖W‖ ^ 2 ≤ (1 + L * B) ^ 2 * ‖initial‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg W) hn 2
    simpa only [mul_pow] using hh
  refine ⟨g₁, hg₁, hp₁, he, ?_⟩
  exact torusHigher_periodic_entrance_sobolev_transfer J g₀ g₁ hg₀ hp₀ hg₁ W
    (by dsimp only [W, c]; rw [torusHigher_normalized_projection_value]; exact he) (1 + L * B) hC hn2

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Integrating the pointwise cutoff flux production gives the actual weak energy production. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_planeScalarDual_cutoff_production_identity
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ 1 (fun x => G x k j)) (hGs : ∀ x, (G x).IsSymm)
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (q χ : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q) (hχ : ContDiff ℝ 2 χ)
    (hsχ : HasCompactSupport χ) (Φ : Fin 2 → Vec 2 → ℝ)
    (hΦ : ∀ i, ContDiff ℝ 1 (Φ i)) (dt : Vec 2 → ℝ) (hdt : Continuous dt)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => (χ x ^ 2 * q x) • planeHkValueOperator (E := E) 1 u x) :
    (2 * inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v (fun k => (contDiff_pi.mp hv k).continuous) hMv hvb)
      (planeScalarDiffusion G (fun k j => (hG k j).continuous) hMG hGb) u F) z +
    (∫ x, χ x ^ 2 * dt x * ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) +
    (∫ x, (1 / 2) * χ x ^ 2 * q x * ‖(WithLp.toLp 2
      (fun i => planeH1GradientOperator (E := E) u i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) =
    ∫ x, cellMetricCutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) u i x))
      (WithLp.toLp 2 (fun i => F i x)) (planeHkValueOperator (E := E) 1 u x)) ∧
    Integrable (fun x => cellMetricCutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) u i x))
      (WithLp.toLp 2 (fun i => F i x)) (planeHkValueOperator (E := E) 1 u x)) volume := by
  let U := planeHkValueOperator (E := E) 1 u
  let du := planeH1GradientOperator (E := E) u
  let qt := fun x => χ x ^ 2 * q x
  let c : Fin 2 → Vec 2 → ℝ := fun i x => qt x * v x i +
    ∑ j : Fin 2, G x j i * fderiv ℝ qt x (basisVec j)
  let a := cutoffMainFlux v G q χ Φ
  let b := cutoffCorrectionFlux G q χ Φ
  have hqt : ContDiff ℝ 2 qt := (hχ.pow 2).mul hq
  have hst : HasCompactSupport qt := by
    convert (hsχ.mul_right (f' := χ)).mul_right (f' := q) using 1
    funext x
    exact congrArg (fun r => r * q x) (pow_two (χ x))
  obtain ⟨ha, hsa, hb, hsb, hsplit⟩ := cutoff_flux_split_regular v hv G hG q χ hq hχ hsχ Φ hΦ
  have hc i x : c i x = a i x + b i x := by
    change qt x * v x i + (∑ j : Fin 2, G x j i * fderiv ℝ qt x (basisVec j)) = _
    have he : (∑ j : Fin 2, G x j i * fderiv ℝ qt x (basisVec j)) =
        ∑ j : Fin 2, G x i j * fderiv ℝ qt x (basisVec j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(hGs x).apply i j]
    rw [he]
    exact hsplit i x
  have hprod := planeScalarDual_compact_production_of_value v hv hMv hvb G hG hMG hGb
    qt hqt hst u z F hz
  have hdiv := planeH1_compact_divergence_split u c a b ha hb hsa hsb hc
  let mass := fun x => χ x ^ 2 * dt x * ‖U x‖ ^ 2
  let diva := fun x => (∑ i : Fin 2, fderiv ℝ (a i) x (basisVec i)) * ‖U x‖ ^ 2
  let T := fun x => inner ℝ (∑ i : Fin 2, b i x • du i x) (U x)
  let H := fun x => ∑ i : Fin 2, inner ℝ (F i x) (planeH1GradientOperator (E := E) z i x)
  let P := fun x => qt x * ∑ k : Fin 2, ∑ j : Fin 2,
    G x k j * inner ℝ (du k x) (du j x)
  let D := fun x => (1 / 2) * χ x ^ 2 * q x * ‖(WithLp.toLp 2 (fun i => du i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  have hmass : Integrable mass volume := by
    apply compact_scalar_normSq_integrable U _ ((hχ.continuous.pow 2).mul hdt)
    convert (hsχ.mul_right (f' := χ)).mul_right (f' := dt) using 1
    funext x
    exact congrArg (fun r => r * dt x) (pow_two (χ x))
  have hdiva : Integrable diva volume := compact_divergence_integrable U a ha hsa
  have hT : Integrable T volume := compact_scalar_gradient_pairing_integrable du U b
    (fun i => (hb i).continuous) hsb
  have hH : Integrable H volume := integrable_finsetSum _
    (fun i _ => L2.integrable_inner (F i) (planeH1GradientOperator (E := E) z i))
  obtain ⟨Mq, hMq⟩ := hqt.continuous.bounded_above_of_compact_support hst
  have hMq0 : 0 ≤ Mq := (norm_nonneg (qt 0)).trans (hMq 0)
  have hP : Integrable P volume := bounded_metric_quadratic_integrable du G
    (fun k j => (hG k j).continuous) hMG hGb qt hqt.continuous hMq0
    (by simpa only [← Real.norm_eq_abs] using hMq)
  have hD : Integrable D volume := by
    have hh := (bounded_scalar_finiteLp_normSq_integrable du qt
      hqt.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hMq)).const_mul (1 / 2 : ℝ)
    simpa only [D, qt, mul_assoc] using hh
  have hpoint : (fun x => cellMetricCutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)) =ᵐ[volume]
      fun x => mass x + diva x - 2 * T x - 2 * H x - 2 * P x + D x := by
    have hdz := planeH1_cutoff_gradient_ae χ q hχ hq hsχ u z hz
    filter_upwards [hdz] with x hx
    have hbvec : (χ x ^ 2 • (WithLp.toLp 2 (fun i => Φ i x) : PiLp 2 (fun _ : Fin 2 => ℝ)) +
        (2 * χ x * q x) • finiteMetricFlux (G x)
          (WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i)))) =
        WithLp.toLp 2 (fun i => b i x) := by
      apply PiLp.ext
      intro i
      rfl
    have hsource : inner ℝ (WithLp.toLp 2 (fun i => F i x))
        ((χ x ^ 2 * q x) • WithLp.toLp 2 (fun i => du i x) +
          χ x ^ 2 • scalarHilbertTensor (WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))) (U x) +
          (2 * χ x * q x) • scalarHilbertTensor
            (WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))) (U x)) = H x := by
      rw [← hx]
      exact PiLp.inner_apply _ _
    unfold cellMetricCutoffFluxProduction
    dsimp only
    rw [hbvec, finite_gradient_tensor_inner, hsource]
    have hdA : (∑ i : Fin 2, fderiv ℝ
        (fun y => χ y ^ 2 * scalarChartFlux v G q Φ i y) x (basisVec i)) =
        ∑ i : Fin 2, fderiv ℝ (a i) x (basisVec i) := rfl
    rw [hdA]
    dsimp only [mass, diva, T, H, P, D, qt]
    ring
  have hint : (∫ x, cellMetricCutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)) =
      (∫ x, mass x) + (∫ x, diva x) - 2 * (∫ x, T x) -
      2 * (∫ x, H x) - 2 * (∫ x, P x) + ∫ x, D x := by
    rw [integral_congr_ae hpoint]
    rw [integral_add
      (f := fun x => mass x + diva x - 2 * T x - 2 * H x - 2 * P x) (g := D)
      (((hmass.add hdiva).sub (hT.const_mul 2)).sub (hH.const_mul 2) |>.sub (hP.const_mul 2)) hD,
      integral_sub (f := fun x => mass x + diva x - 2 * T x - 2 * H x)
      (g := fun x => 2 * P x)
      (((hmass.add hdiva).sub (hT.const_mul 2)).sub (hH.const_mul 2)) (hP.const_mul 2),
      integral_sub (f := fun x => mass x + diva x - 2 * T x) (g := fun x => 2 * H x)
      ((hmass.add hdiva).sub (hT.const_mul 2)) (hH.const_mul 2),
      integral_sub (f := fun x => mass x + diva x) (g := fun x => 2 * T x)
      (hmass.add hdiva) (hT.const_mul 2),
      integral_add (f := mass) (g := diva) hmass hdiva,
      integral_const_mul, integral_const_mul, integral_const_mul]
  refine ⟨?_, ?_⟩
  · have hF : inner ℝ F (planeH1GradientOperator (E := E) z) = ∫ x, H x :=
      planeFlux_inner_eq_integral _ _
    have hPe : (∫ x, qt x * ∑ k : Fin 2, ∑ j : Fin 2,
        G x k j * inner ℝ (du j x) (du k x)) = ∫ x, P x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only [P]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        rw [real_inner_comm (du j x) (du k x)])
    rw [hF, hPe] at hprod
    change 2 * _ + 2 * (∫ x, P x) + 2 * (∫ x, H x) = _ at hprod
    change (∫ x, _) = (∫ x, diva x) - 2 * (∫ x, T x) at hdiv
    change 2 * _ + (∫ x, mass x) + (∫ x, D x) = _
    rw [hint]
    linarith only [hprod, hdiv]
  
  · exact (((((hmass.add hdiva).sub (hT.const_mul 2)).sub (hH.const_mul 2)).sub
      (hP.const_mul 2)).add hD).congr hpoint.symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The large shear transport vanishes on the genuine transverse weak H¹ sector. -/

theorem cellTransverseH1Projection_drift_zero
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (e : Fin 2) (hs : ∀ t x, v t x e.rev = 0)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellDriftForm v V hv hb t (cellTransverseH1Projection e u) z = 0 := by
  simp only [cellDriftForm, sum_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = e
  · subst j
    rw [cellTransverseH1Projection_parallel_derivative_zero, map_zero, inner_zero_left]
  · have hjr : j = e.rev := by
      fin_cases e <;> fin_cases j <;> simp_all
    subst j
    have hzero : cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv hb t e.rev
        (cellDerivativeCLM e.rev (cellTransverseH1Projection e u)) = 0 := by
      apply Lp.ext
      filter_upwards [cellDriftEntryCLM_ae ⟨0, v, 0, 0⟩ V hv hb t e.rev
        (cellDerivativeCLM e.rev (cellTransverseH1Projection e u)),
        Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with x hx hz
      change cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv hb t e.rev
          (cellDerivativeCLM e.rev (cellTransverseH1Projection e u)) x =
        (v t x e.rev : ℂ) * cellDerivativeCLM e.rev (cellTransverseH1Projection e u) x at hx
      rw [hx, hs t x, Complex.ofReal_zero, zero_mul, hz]
      rfl
    rw [hzero, inner_zero_left]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The polynomial adjoint defect with the exact metric correction flux. -/

theorem adjointPolynomial_metric_defect {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (hdur : Real.sqrt T * ocEll q Λ m ν / ocTau α q Λ m *
      Real.exp (-Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) ≤ 1)
    (yc : Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t k j, Differentiable ℝ (fun z => G t z k j)) (n : ℕ) (t : ℝ) (z : Vec 2) :
    let W := adjointCellPolynomialWeight α q Λ ζ m ν B T yc n
    deriv (fun s => W s z) t +
      (∑ k : Fin 2, ocCellDrift α q Λ ζ m ν yc t z k * fderiv ℝ (W t) z (basisVec k)) +
      (∑ k : Fin 2, fderiv ℝ (fun x => ∑ j : Fin 2, G t x k j *
        fderiv ℝ (W t) x (basisVec j)) z (basisVec k)) ≤
      (adjointWeightRate C K n * (ocEll q Λ m ν ^ 2 / T)) * W t z +
        ∑ k : Fin 2, fderiv ℝ (fun x => metricCorrectionFlux (W t) (G t) x k) z (basisVec k) := by
  dsimp only
  let W := adjointCellPolynomialWeight α q Λ ζ m ν B T yc n
  have hsp : ContDiff ℝ 2 (W t) :=
    adjointCellPolynomialWeight_space_contDiff hΛ hζ ν B T yc n t 2
  rw [metricCorrectionFlux_divergence (W t) hsp (G t) (hG t) z]
  have hd := adjointCellPolynomialWeight_defect (α := α) (q := q) (m := m)
    hΛ hζ hν hB hT hC he K hK hb hdur yc n t z
  have hr := mul_le_mul_of_nonneg_right (adjointWeightRate_defect hC hK n)
    (div_nonneg (sq_nonneg (ocEll q Λ m ν)) hT.le)
  have hw := mul_le_mul_of_nonneg_right hr
    (adjointCellPolynomialWeight_pos α q Λ ζ m ν B T yc n t z).le
  unfold scalarAdjointOperator at hd
  linarith only [hd, hw]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution Metric
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Compatible smooth native realizations preserve the individual original Taylor coefficients. -/

theorem torusHigher_native_taylor_coefficients (c : ℕ × ℕ → ComplexCellL2)
    (R : ℝ≥0) (hR : 0 < R)
    (hs : Summable (fun p => ‖c p‖ * (R : ℝ) ^ (p.1 + p.2)))
    (hex : ∀ K : ℕ, ∃ F : (Fin 2 → ℂ) → TorusHk K ℂ,
      (∀ ξ ∈ ball (0 : Fin 2 → ℂ) (R : ℝ), torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p) ∧
      ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) F 0) :
    ∀ (p : ℕ × ℕ) (K : ℕ), ∃ U : TorusHk K ℂ, torusHkValueCLM U = c p := by
  intro p K
  obtain ⟨F, hF, hf⟩ := hex K
  have hh : ∀ ξ : Fin 2 → ℂ, ∃ U : TorusHk K ℂ,
      torusHkValueCLM U = ∑ a ∈ Finset.HasAntidiagonal.antidiagonal (p.1 + p.2),
        fibreMonomial ξ a • c a :=
    torusHigher_native_homogeneous_coefficient K (p.1 + p.2) c R hR hs F hF (hf.of_le (by simp))
  have hc := torusHigher_native_bivariate_coefficients K (p.1 + p.2) c hh
    (⟨p.1, by omega⟩ : Fin (p.1 + p.2 + 1))
  simpa only [Nat.add_sub_cancel_left, Prod.mk.eta] using hc

theorem torusHigher_taylor_coefficients_smooth_representatives (c : ℕ × ℕ → ComplexCellL2)
    (R : ℝ≥0) (hR : 0 < R)
    (hs : Summable (fun p => ‖c p‖ * (R : ℝ) ^ (p.1 + p.2)))
    (hex : ∀ K : ℕ, ∃ F : (Fin 2 → ℂ) → TorusHk K ℂ,
      (∀ ξ ∈ ball (0 : Fin 2 → ℂ) (R : ℝ), torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p) ∧
      ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) F 0) (p : ℕ × ℕ) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (c p : Vec 2 → ℂ) :=
  torusHigher_all_order_smooth_representative (c p)
    (torusHigher_native_taylor_coefficients c R hR hs hex p)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The original all-time raw solution supplies every native Hilbert premise locally. -/

theorem cellSolution_allTime_native
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : ∀ a b : ℝ, a ≤ b → MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : ∀ a b : ℝ, a ≤ b → MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution univ C src F D) :
    Continuous (cellRawTrace D) ∧
    (∀ t, (cellRawTrace D t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
    (∀ᵐ t ∂volume, ∀ a, ((cellH1Slice D t).val a : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] D t a) ∧
    (∀ a b : ℝ, a ≤ b → CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun t => cellDualDerivative C hG V hv hb t (cellH1Slice D t)
        (cellSourceSlice src t) (fun j => cellSourceSlice (fun r x => F r x j) t))) := by
  refine ⟨continuousOn_univ.mp (cellRawTrace_continuous univ D
    (fun t _ => (hD.2.2.1 t (mem_univ t)).1) hD.2.2.2.2.1), ?_, ?_, ?_⟩
  · intro t
    exact cellRawTrace_ae D t (hD.2.2.1 t (mem_univ t)).1
  · have hw : ∀ᵐ t ∂volume, HasPeriodicOrderedWeakJet (D t) := by
      simpa only [Measure.restrict_univ] using hD.2.1
    filter_upwards [hw] with t ht a
    rw [cellH1Slice_eq_toHk D t ht]
    exact torusJetToL2_ae (D t) ht.2.1 a
  · intro a b hab
    exact cellSolution_to_Hilbert hab C hG V k hv hb hκ hκb src F
      (hsrc a b hab) (hF a b hab) D
      (cellSolution_restrict (subset_univ _) ordConnected_Icc hD)

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Exact subtraction of normalized generators with different scalar gauges. -/

theorem cellDualDerivative_normalized_gauge_difference
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (lam mu : ℝ → ℂ) (t : ℝ) (u w : TorusHk 1 ℂ) :
    cellDualDerivative ⟨G, v, θ, fun t => -lam t⟩ hG V hv hb t u 0 (fun _ => 0) -
      cellDualDerivative ⟨G, v, θ, fun t => -mu t⟩ hG V hv hb t w 0 (fun _ => 0) =
    cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (u - w) 0 (fun _ => 0) -
      cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM (u - w))) -
      cellPivotDualCLM (cellScalarCLM (lam t - mu t) (torusHkValueCLM w)) := by
  rw [cellDualDerivative_negative_potential, cellDualDerivative_negative_potential,
    ← cellDualDerivative_sub_same_source ⟨G, v, θ, 0⟩ hG V hv hb t u w 0 (fun _ => 0)]
  have he : cellScalarCLM (lam t) (torusHkValueCLM (u - w)) +
      cellScalarCLM (lam t - mu t) (torusHkValueCLM w) =
      cellScalarCLM (lam t) (torusHkValueCLM u) -
        cellScalarCLM (mu t) (torusHkValueCLM w) := by
    simp only [map_sub, cellScalarCLM_smul, sub_smul]
    abel
  conv_rhs => rw [sub_sub, ← map_add, he, map_sub]
  abel

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! The literal Taylor polynomial, extended by zero off a time window, retains its normalized moment budget. -/

def slowTaylorTimeCoefficient (K : ℕ) (f : ℝ → Vec 2 → Vec 2 → ℝ)
    (a b : ℝ) (X0 : Vec 2) (δ : ℝ) (t : ℝ) (z : Vec 2) : ℝ :=
  if t ∈ Set.Icc a b then taylorSlow 0 K (fun X => f t X z) X0 (δ • z) else 0

theorem slowTaylor_time_coefficient_budget (K Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≤ Nmax, ∀ (f : ℝ → Vec 2 → Vec 2 → ℝ)
      (a b : ℝ) (X0 : Vec 2) (ϖ ρ δ ζ R : ℝ),
      (∀ X z, Measurable (fun t => f t X z)) →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (K + N : ℕ) (Function.uncurry (f t))) →
      0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 < R → δ = ζ * ϖ →
      ∀ (M : ℕ → ℝ), (∀ r, 0 ≤ M r) →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r ≤ K, ∀ j ≤ N, ∀ X z,
        ρ ^ j * ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f t X') z) X‖ ≤ M r / R) →
      (∀ z, Measurable (fun t => slowTaylorTimeCoefficient K f a b X0 δ t z)) ∧
      (∀ t, ContDiff ℝ (N : ℕ) (slowTaylorTimeCoefficient K f a b X0 δ t)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ N, ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (slowTaylorTimeCoefficient K f a b X0 δ t) z‖ ≤
          C * (∑ r ∈ Finset.range (K + 1), M r) / R * polynomialMomentRoot ϖ z ^ K) := by
  obtain ⟨C, hC, hb⟩ := slowTaylor_uniform_reserved_budget K Nmax
  refine ⟨C, hC, ?_⟩
  intro N hN f a b X0 ϖ ρ δ ζ R hm hf hϖ hρ hscale hζ hζ1 hR hδ M hM hjet
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have hfs : ∀ t ∈ Set.Icc a b, ∀ z, ContDiff ℝ (K : ℕ) (fun X => f t X z) := by
      intro t ht z
      have hs := (hf t ht).comp (contDiff_id.prodMk (contDiff_const (c := z)))
      exact hs.of_le (by exact_mod_cast Nat.le_add_right K N)
    convert Weighted.taylorSlow_time_window_measurable (Set.Icc a b) measurableSet_Icc 0 K f hm hfs X0 δ z using 1
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp only [slowTaylorTimeCoefficient, ite_eq_left ht]
    · simp only [slowTaylorTimeCoefficient, ite_eq_right ht]
  · intro t
    by_cases ht : t ∈ Set.Icc a b
    · have heq : slowTaylorTimeCoefficient K f a b X0 δ t =
          (fun z => taylorSlow 0 K (fun X => f t X z) X0 (δ • z)) := by
        funext z
        simp only [slowTaylorTimeCoefficient, ite_eq_left ht]
      rw [heq]
      exact Weighted.taylorSlow_spatial_contDiff 0 K N (f t) (hf t ht) X0 δ
    · have heq : slowTaylorTimeCoefficient K f a b X0 δ t = (fun _ : Vec 2 => (0 : ℝ)) := by
        funext z
        simp only [slowTaylorTimeCoefficient, ite_eq_right ht]
      rw [heq]
      exact contDiff_const
  · filter_upwards [hjet, ae_restrict_mem measurableSet_Icc] with t ht htI
    have heq : slowTaylorTimeCoefficient K f a b X0 δ t =
        (fun z => taylorSlow 0 K (fun X => f t X z) X0 (δ • z)) := by
      funext z
      simp only [slowTaylorTimeCoefficient, ite_eq_left htI]
    rw [heq]
    exact hb N hN (f t) (hf t htI) ϖ ρ δ ζ R hϖ hρ hscale hζ hζ1 hR hδ M hM ht X0

end AVRegularity.CycleWords
end
