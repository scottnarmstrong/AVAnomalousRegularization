-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.GradientCarrierJet
public import AVRegularity.CycleWords.CellWeakValueCongruence
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
public import AVRegularity.CycleEvolution.CellWeakIdentityAbsoluteSeries
import AVRegularity.Analysis.Convolution.Kernel.ApproximationBounds

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! The scalar weak RHS with zero forcing has its literal source-free representative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeScalarRawRhsZeroFlux (K : ℕ) (v : Vec 2 → Vec 2)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : PlaneHk Set.univ (K + 1) E) (φ : PlaneHk Set.univ 1 E) (x : Vec 2) : ℝ :=
  -(∑ i : Fin 2, v x i * inner ℝ
    (w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x)
    (φ.toFunction.jet (valueIndex2 1) x)) -
  (∑ i : Fin 2, inner ℝ
    (w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x)
    (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x)) -
  ∑ i : Fin 2, inner ℝ
    (∑ j : Fin 2, (G x - 1) i j • w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => j⟩ x)
    (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x)

theorem planeScalarRawRhs_zeroFlux_ae (K : ℕ) (v : Vec 2 → Vec 2)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : PlaneHk Set.univ (K + 1) E) (φ : PlaneHk Set.univ 1 E) :
    planeScalarRawRhs K v G w 0 φ =ᵐ[volume] planeScalarRawRhsZeroFlux K v G w φ := by
  filter_upwards [planeZeroJetRepresentative_ae (E := E) K (valueIndex2 K),
    planeZeroJetRepresentative_ae (E := PiLp 2 (fun _ : Fin 2 => E)) K (valueIndex2 K)]
    with x hg hF
  simp only [planeScalarRawRhs, planeScalarRawRhsZeroFlux, hg, hF,
    PiLp.zero_apply, add_zero, inner_zero_left]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Genuine higher torus multiplier curves using coefficient smoothness only on a time window. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

variable {K : ℕ} (a b : ℝ) (C : ℝ → Vec 2 → E →L[ℝ] F)
  (hC : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (C t))
  (hp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (C t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l)

def torusWindowMultiplier (t : ℝ) (u : TorusHk K E) : TorusHk K F :=
  u.mulCoefficient (windowCoefficient a b C t) (windowCoefficient_contDiff a b K C hC t)
    (windowCoefficient_periodic a b C hp t) (windowCoefficient_derivative_bound a b K C A hA hb t)

theorem torusWindowMultiplier_memLp (hm : Measurable (Function.uncurry C))
    (u : ℝ → TorusHk K E) (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    MemLp (fun t => torusWindowMultiplier a b C hC hp A hA hb t (u t)) 2
      (volume.restrict (Icc a b)) :=
  torusCoefficient_time_memLp (volume.restrict (Icc a b)) (windowCoefficient a b C)
    (windowCoefficient_measurable a b C hm) (windowCoefficient_contDiff a b K C hC)
    (windowCoefficient_periodic a b C hp) A
    (windowCoefficient_derivative_bound a b K C A hA hb) u hu

omit [FiniteDimensional ℝ F] in
theorem torusWindowMultiplier_agrees (t : ℝ) (ht : t ∈ Icc a b) (u : TorusHk K E) :
    torusWindowMultiplier a b C hC hp A hA hb t u =
      u.mulCoefficient (C t) (hC t ht) (hp t ht) (hb t ht) := by
  unfold torusWindowMultiplier
  simp only [windowCoefficient_eq C ht]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The H1 Fourier modes have exactly the actual torus Fourier values and gradients. -/

local instance cellComplexFourierModeReadoutMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem cellComplexFourierModeH1_value_ae (n : Fin 2 → ℤ) :
    torusHkValueCLM (cellComplexFourierModeH1 n) =ᵐ[volume.restrict AVenhance.unitCube]
      cellComplexFourierMode n := by
  have h := torusJetToL2_ae (cellComplexFourierJet n)
    (cellComplexFourierJet_hasPeriodicWeakJet n).2.1 (valueIndex2 1)
  change torusHkValueCLM (cellComplexFourierModeH1 n) =ᵐ[volume.restrict AVenhance.unitCube]
    cellComplexFourierJet n (valueIndex2 1) at h
  have he : cellComplexFourierJet n (valueIndex2 1) = cellComplexFourierMode n := by
    funext x
    simp [cellComplexFourierJet, valueIndex2, valueIndex]
  rw [he] at h
  exact h

theorem cellComplexFourierModeH1_value (n : Fin 2 → ℤ) :
    torusHkValueCLM (cellComplexFourierModeH1 n) = scalarTorusToCell (mFourierLp 2 n) := by
  rw [scalarTorusToCell_mode]
  apply Lp.ext
  exact (cellComplexFourierModeH1_value_ae n).trans
    (cellComplexFourierMode_memLp n).coeFn_toLp.symm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Multiplicative periodic interpolation retains a small value norm in each derivative estimate. -/

theorem cellDerivative_multiplicative_interpolation
    (j : Fin 2) (u z : TorusHk 1 ℂ) (hz : torusHkValueCLM z = cellDerivativeCLM j u) :
    ‖cellDerivativeCLM j u‖ ^ 2 ≤ ‖torusHkValueCLM u‖ * ‖cellDerivativeCLM j z‖ := by
  have hi := cellDerivative_skew j u z
  rw [hz, real_inner_self_eq_norm_sq] at hi
  exact hi.trans_le ((neg_le_abs _).trans (abs_real_inner_le_norm _ _))

theorem cellDerivative_higher_multiplicative_interpolation (j : Fin 2) (U : TorusHk 2 ℂ) :
    ‖cellDerivativeCLM j (truncateTorusHk (by decide : 1 ≤ 2) U)‖ ^ 2 ≤
      ‖torusHkValueCLM U‖ * ‖U‖ := by
  have hz : torusHkValueCLM (derivativeTorusHk (K := 1) (fun _ : Fin 1 => j) U) =
      cellDerivativeCLM j (truncateTorusHk (by decide : 1 ≤ 2) U) := by
    rw [torusOrdered_value_coordinate]
    rfl
  have he := cellDerivative_multiplicative_interpolation j
    (truncateTorusHk (by decide : 1 ≤ 2) U)
    (derivativeTorusHk (K := 1) (fun _ : Fin 1 => j) U) hz
  have hn : ‖cellDerivativeCLM j (derivativeTorusHk (K := 1) (fun _ : Fin 1 => j) U)‖ ≤ ‖U‖ := by
    let Z : TorusHk 1 ℂ := derivativeTorusHk (K := 1) (fun _ : Fin 1 => j) U
    have hl : ‖Z.val (⟨⟨1, by decide⟩, fun _ => j⟩ : JetIndex2 1)‖ ≤ ‖Z.val‖ :=
      PiLp.norm_apply_le Z.val ⟨⟨1, by decide⟩, fun _ => j⟩
    exact hl.trans (derivativeTorusHk_norm_le (K := 1) (fun _ : Fin 1 => j) U)
  apply he.trans
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Window-only coefficients give the principal time actions for every actual H1 derivative slice. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_planeIntervalActions_memLp (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ z, ‖v t z‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hCell : IsCellMetric G)
    (u : ℝ → PlaneHk Set.univ 1 E)
    (hu : MemLp u 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeIntervalTransport a b hab v hvc M hvb t
      (planeH1GradientOperator (u t))) 2 (volume.restrict (Set.Icc a b)) ∧
    MemLp (fun t => cellMetricIntervalDiffusion a b hab G hGc hCell t
      (planeH1GradientOperator (u t))) 2 (volume.restrict (Set.Icc a b)) := by
  apply planeScalarActions_memLp
    (planeIntervalCoefficient a b hab v) (planeIntervalCoefficient a b hab G)
    (planeIntervalVelocity_continuous a b hab v hvc)
    (planeIntervalMetric_continuous a b hab G hGc)
  · intro k
    exact (measurable_pi_apply k).comp (planeIntervalCoefficient_measurable a b hab v hvm)
  · intro k j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp
      (planeIntervalCoefficient_measurable a b hab G hGm))
  · exact hu

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! All normalized metric polynomial jets have the uniform insertion price g times zeta. -/

theorem geometryTaylor_positive_jet_budget (K J : ℕ) (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → ℝ) (ϖ ρ δ ζ g : ℝ),
      0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ r, 1 ≤ r → r ≤ K → ‖iteratedFDeriv ℝ r f 0‖ ≤ M r * g * δ ^ r) →
      ∀ j ≤ J, ∀ z : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (taylorSlow 1 K f 0) z‖ ≤
          C * g * ζ * polynomialMomentRoot ϖ z ^ K := by
  have hh (r : ℕ) := geometricHomogeneousPolynomial_jet_budget r J
  choose C hC hb using hh
  let price := ∑ r ∈ Finset.Icc 1 K, C r * ((r.factorial : ℝ))⁻¹ * M r
  refine ⟨price, Finset.sum_nonneg (fun r _ =>
    mul_nonneg (mul_nonneg (hC r) (by positivity)) (hM r)), ?_⟩
  intro f ϖ ρ δ ζ g hϖ hρ hscale hζ hζ1 hg hδ hf j hj z
  let p := fun r (z : Vec 2) => iteratedFDeriv ℝ r f 0 (fun _ => z)
  have hp (r : ℕ) : ContDiff ℝ (j : ℕ) (p r) := by
    simpa only [one_smul] using Weighted.multilinear_diagonal_contDiff j
      (fun _ => iteratedFDeriv ℝ r f 0) contDiff_const 1
  have he : taylorSlow 1 K f 0 =
      ∑ r ∈ Finset.Icc 1 K, ((r.factorial : ℝ))⁻¹ • p r := by
    funext z
    simp only [taylorSlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, p]
  have hterm (r : ℕ) : ContDiffAt ℝ (j : ℕ) (((r.factorial : ℝ))⁻¹ • p r) z := by
    rw [show (((r.factorial : ℝ))⁻¹ • p r) =
      (fun y => ((r.factorial : ℝ))⁻¹ • p r y) by funext y; rfl]
    exact (hp r).contDiffAt.const_smul _
  rw [he, iteratedFDeriv_sum_apply (fun r _ => hterm r)]
  calc
    _ ≤ ρ ^ j * ∑ r ∈ Finset.Icc 1 K,
        ‖iteratedFDeriv ℝ j (((r.factorial : ℝ))⁻¹ • p r) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hρ j)
    _ ≤ ∑ r ∈ Finset.Icc 1 K,
        C r * ((r.factorial : ℝ))⁻¹ * M r * g * ζ * polynomialMomentRoot ϖ z ^ K := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hrK := Finset.mem_Icc.mp hr
      rw [iteratedFDeriv_const_smul_apply (hp r).contDiffAt, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      have hpoly := hb r (iteratedFDeriv ℝ r f 0) ϖ ρ δ ζ (M r) g hϖ hρ hscale hζ (hM r) hg hδ
        (hf r hrK.1 hrK.2) j hj z
      have hs := smallRatio_degree_le hζ hζ1 (polynomialMomentRoot_one_le ϖ z)
        (mul_nonneg hζ (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z))) le_rfl hrK.1 hrK.2
      rw [mul_pow] at hs
      have ht := mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (hC r) (hM r)) hg)
      have hb' := mul_le_mul_of_nonneg_left (hpoly.trans (by simpa only [mul_assoc] using ht))
        (by positivity : 0 ≤ ((r.factorial : ℝ))⁻¹)
      convert hb' using 1 <;> ring
    _ = _ := by dsimp only [price]; rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Measurable bounded drift suffices for spatial integrability of the actual forced scalar equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarRawRhs_integrable_measurable (K : ℕ)
    (v : Vec 2 → Vec 2) (hvm : ∀ i, Measurable (fun x => v x i))
    (M : ℝ) (hvb : ∀ i x, ‖v x i‖ ≤ M)
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (w : PlaneHk Set.univ (K + 1) E)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (φ : PlaneHk Set.univ 1 E) :
    Integrable (planeScalarRawRhs K v (fun _ => G) w F φ) volume := by
  let u := truncatePlaneHk (E := E) (show 1 ≤ K + 1 by omega) w
  let du := planeH1GradientOperator (E := E) u
  let dz := planeH1GradientOperator (E := E) φ
  let z := planeHkValueOperator (E := E) 1 φ
  let q := planeFluxValueOperator (E := E) K F
  have hi : Integrable (fun x =>
      -(∑ i : Fin 2, v x i * inner ℝ (du i x) (z x)) -
        (∑ i : Fin 2, inner ℝ (du i x) (dz i x)) -
        (∑ i : Fin 2, ((∑ j : Fin 2, (G - 1) i j * inner ℝ (du j x) (dz i x)) +
          inner ℝ (q i x) (dz i x)))) volume := by
    exact ((integrable_finsetSum Finset.univ (fun i _ =>
      (L2.integrable_inner (du i) z).bdd_mul (hvm i).aestronglyMeasurable
        (Filter.Eventually.of_forall (hvb i)))).neg.sub
      (integrable_finsetSum Finset.univ (fun i _ => L2.integrable_inner (du i) (dz i)))).sub
      (integrable_finsetSum Finset.univ (fun i _ =>
        (integrable_finsetSum Finset.univ (fun j _ =>
          (L2.integrable_inner (du j) (dz i)).const_mul ((G - 1) i j))).add
          (L2.integrable_inner (q i) (dz i))))
  have hw : ∀ᵐ x ∂volume, ∀ i : Fin 2, du i x =
      w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hφ : ∀ᵐ x ∂volume, ∀ i : Fin 2, dz i x =
      φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hF : ∀ᵐ x ∂volume, ∀ i : Fin 2, q i x = F.toFunction.jet (valueIndex2 K) x i :=
    ae_all_iff.mpr (fun i => planeFluxValueOperator_ae K F i)
  apply hi.congr
  filter_upwards [hw, hφ, hF, univToPlane_ae (φ.val (valueIndex2 1)),
    planeZeroJetRepresentative_ae (E := E) K (valueIndex2 K)] with x hwx hφx hFx hz hzero
  dsimp only [z]
  simp only [planeScalarRawRhs, hzero, inner_zero_left, add_zero,
    inner_add_left, sum_inner, real_inner_smul_left, planeHkValueOperator_apply, hz]
  simp_rw [hwx, hφx, hFx]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! A convergent scalar normalization preserves smooth literal graph series. -/

theorem fibreSeriesFun_summable_norm_of_geometric_jets
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (t : ℝ)
    (A : ℝ) (hA : 0 ≤ A) (C : ℕ → ℝ)
    (hb : ∀ j p x, ‖iteratedFDeriv ℝ j (a p t) x‖ ≤ C j * A ^ (p.1 + p.2))
    (ξ : Fin 2 → ℂ) (hξ : A * ‖ξ‖ < 1) (x : Vec 2) :
    Summable (fun p => ‖fibreMonomial ξ p * a p t x‖) := by
  have hs := (bivariate_geometric_summable (A * ‖ξ‖)
    (mul_nonneg hA (norm_nonneg ξ)) hξ).mul_left (C 0)
  apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) _ hs
  intro p
  have hv : ‖a p t x‖ ≤ C 0 * A ^ (p.1 + p.2) := by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 p x
  rw [norm_mul]
  calc
    _ ≤ ‖fibreMonomial ξ p‖ * (C 0 * A ^ (p.1 + p.2)) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ ≤ ‖ξ‖ ^ (p.1 + p.2) * (C 0 * A ^ (p.1 + p.2)) :=
      mul_le_mul_of_nonneg_right (fibreMonomial_norm_le_pi ξ p)
        ((norm_nonneg _).trans hv)
    _ = C 0 * (A * ‖ξ‖) ^ (p.1 + p.2) := by rw [mul_pow]; ring

theorem fibreRowCoefficients_series_contDiff_of_geometric_jets
    (k : ℕ × ℕ → ℝ → ℂ) (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (t : ℝ)
    (ha : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (a p t))
    (A : ℝ) (hA : 0 ≤ A) (C : ℕ → ℝ)
    (hb : ∀ j p x, ‖iteratedFDeriv ℝ j (a p t) x‖ ≤ C j * A ^ (p.1 + p.2))
    (ξ : Fin 2 → ℂ) (hξ : A * ‖ξ‖ < 1)
    (hk : Summable (fun p => ‖fibreMonomial ξ p * k p t‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun (fibreRowCoefficients k a) ξ t) := by
  have he : fibreSeriesFun (fibreRowCoefficients k a) ξ t =
      fun x => fibreSeriesC k ξ t * (1 + fibreSeriesFun a ξ t x) := by
    funext x
    exact fibreRowCoefficients_series_pointwise k a ξ t x hk
      (fibreSeriesFun_summable_norm_of_geometric_jets a t A hA C hb ξ hξ x)
  rw [he]
  exact contDiff_const.mul (contDiff_const.add
    (fibreSeriesFun_contDiff_of_geometric_jets a t ha A hA C hb ξ hξ))

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Genuine uniformly bounded native witnesses produce one smooth family preserving its zero value. -/

theorem torusHigher_native_smooth_zero_choice (q : ℕ)
    (g : (Fin 2 → ℂ) → ComplexCellL2) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hg0 : g 0 = 0)
    (hex : ∀ y ∈ ball 0 R, ∃ U : TorusHk q ℂ, torusHkValueCLM U = g y ∧ ‖U‖ ≤ M) :
    ∃ F : (Fin 2 → ℂ) → TorusHk q ℂ,
      (∀ y ∈ ball 0 R, torusHkValueCLM (F y) = g y ∧ ‖F y‖ ≤ M) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) F (ball 0 R) ∧ F 0 = 0 := by
  obtain ⟨F, hF, _⟩ := torusHigher_native_line_choice q g (ball 0 R) hg M hex
  refine ⟨F, hF, torusHigher_native_frequency_contDiffOn q g F 0 R M hM hg hF, ?_⟩
  apply torusHigherComplexValueCLM_injective q
  change torusHkValueCLM (F 0) = torusHkValueCLM (0 : TorusHk q ℂ)
  rw [(hF 0 (mem_ball_self hR)).1, hg0, map_zero]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
open AVRegularity.Analysis.Convolution AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords

/-! Actual measurable torus multiplication agrees with the committed cell multiplier. -/

local instance scalarTorusCellMultiplierBridgeMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusToCell_measurable_multiplier
    (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b) (C : ℝ) (hC : 0 ≤ C)
    (hbC : ∀ z, ‖b z‖ ≤ C) (u : ScalarTorusL2) :
    scalarTorusToCell (measurableTorusSymbolMultiplication b hb C hbC u) =
      cellCoefficientCLM (fun x => b (torusQuotient x))
        ((hb.comp measurePreserving_torusQuotient_cell.measurable).aestronglyMeasurable.restrict)
        C hC (fun x => hbC (torusQuotient x)) (scalarTorusToCell u) := by
  have hm := scalarTorusQuotient_measurePreserving.quasiMeasurePreserving.ae
    (L2Multiplier.operator_ae b (measurableTorusSymbol_memLp_top b hb C hbC) u)
  apply Lp.ext
  filter_upwards [scalarTorusToCell_ae (measurableTorusSymbolMultiplication b hb C hbC u),
    hm, scalarTorusToCell_ae u,
    cellCoefficientCLM_ae (fun x => b (torusQuotient x))
      ((hb.comp measurePreserving_torusQuotient_cell.measurable).aestronglyMeasurable.restrict)
      C hC (fun x => hbC (torusQuotient x)) (scalarTorusToCell u)]
    with x hx hmθ hu hc
  change measurableTorusSymbolMultiplication b hb C hbC u (torusQuotient x) =
    b (torusQuotient x) * u (torusQuotient x) at hmθ
  rw [hx, hmθ, hc, hu]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Changing a constant phase preserves native higher correction states with an explicit cost. -/

theorem torusHigherConstant_scalar (K : ℕ) (c : ℂ) :
    torusHigherScalarCLM K c (torusHigherConstant K 1) = torusHigherConstant K c := by
  apply TorusHk.ext_value
  change torusHkValueCLM (torusHigherScalarCLM K c (torusHigherConstant K 1)) =
    torusHkValueCLM (torusHigherConstant K c)
  rw [torusHigherScalarCLM_value, torusHigherConstant_value, torusHigherConstant_value]
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae c (cellConstantCLM 1), cellConstantCLM_ae 1,
    cellConstantCLM_ae c] with x hs h1 hc
  rw [hs, h1, hc, mul_one]

theorem torusHigherConstant_norm_le (K : ℕ) (c : ℂ) :
    ‖torusHigherConstant K c‖ ≤
      ‖c‖ * (1 + ‖torusHigherScalarCLM K Complex.I‖) * ‖torusHigherConstant K 1‖ := by
  rw [← torusHigherConstant_scalar]
  exact ((torusHigherScalarCLM K c).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (torusHigherScalarCLM_norm_le K c ‖c‖ le_rfl)
      (norm_nonneg _))

theorem torusHigherCorrection_phase_change_norm_le (K : ℕ) (σ : ℂ) (w : TorusHk K ℂ) :
    ‖torusHigherScalarCLM K σ w + torusHigherConstant K (σ - 1)‖ ≤
      (1 + ‖torusHigherScalarCLM K Complex.I‖) *
        (‖σ‖ * ‖w‖ + ‖σ - 1‖ * ‖torusHigherConstant K 1‖) := by
  have hs := ((torusHigherScalarCLM K σ).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (torusHigherScalarCLM_norm_le K σ ‖σ‖ le_rfl)
      (norm_nonneg w))
  exact ((norm_add_le _ _).trans (add_le_add hs (torusHigherConstant_norm_le K (σ - 1)))).trans_eq
    (by ring)

theorem torusHigherCorrection_phase_change_value (K : ℕ) (σ γ : ℂ)
    (u : ComplexCellL2) (w : TorusHk K ℂ)
    (hw : torusHkValueCLM w = γ • u - cellConstantCLM 1) :
    torusHkValueCLM (torusHigherScalarCLM K σ w + torusHigherConstant K (σ - 1)) =
      (σ * γ) • u - cellConstantCLM 1 := by
  rw [map_add, torusHigherScalarCLM_value, torusHigherConstant_value, hw]
  change σ • (γ • u - cellConstantCLM 1) + cellConstantCLM (σ - 1) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul σ (γ • u - cellConstantCLM 1),
    Lp.coeFn_smul γ u, Lp.coeFn_sub (γ • u) (cellConstantCLM 1),
    Lp.coeFn_add (σ • (γ • u - cellConstantCLM 1)) (cellConstantCLM (σ - 1)),
    cellConstantCLM_ae (σ - 1), cellConstantCLM_ae 1,
    Lp.coeFn_sub ((σ * γ) • u) (cellConstantCLM 1), Lp.coeFn_smul (σ * γ) u]
    with x hs hg hsub ha hc h1 hr hm
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hs hg hsub ha hr hm
  rw [ha, hs, hsub, hg, hc, h1, hr, hm, h1]
  change σ * (γ * u x - 1) + (σ - 1) = (σ * γ) * u x - 1
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact ambient weak-jet coordinates of every complex Fourier mode. -/

local instance cellComplexFourierModeCoordinatesMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

def cellComplexFourierModeCarrier (n : Fin 2 → ℤ) : CellComplexH1 :=
  cellComplexH1RealEquiv.symm (cellComplexFourierModeH1 n)

theorem cellComplexFourierModeCarrier_coordinate (n : Fin 2 → ℤ) (a : JetIndex2 1) :
    (cellComplexFourierModeCarrier n).val a =
      if h : a.1.val = 0 then scalarTorusToCell (mFourierLp 2 n) else
        ((2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 ⟨0, by omega⟩) : ℂ)) •
          scalarTorusToCell (mFourierLp 2 n) := by
  have hjet := torusJetToL2_ae (cellComplexFourierJet n)
    (cellComplexFourierJet_hasPeriodicWeakJet n).2.1 a
  change (cellComplexFourierModeCarrier n).val a =ᵐ[volume.restrict AVenhance.unitCube]
    cellComplexFourierJet n a at hjet
  have hval : scalarTorusToCell (mFourierLp 2 n) =ᵐ[volume.restrict AVenhance.unitCube]
      cellComplexFourierMode n := by
    rw [scalarTorusToCell_mode]
    exact (cellComplexFourierMode_memLp n).coeFn_toLp
  split_ifs with h
  · apply Lp.ext
    have he : cellComplexFourierJet n a = cellComplexFourierMode n := by
      funext x
      simp only [cellComplexFourierJet, dite_eq_left h]
    rw [he] at hjet
    exact hjet.trans hval.symm
  · apply Lp.ext
    have hs := Lp.coeFn_smul
      ((2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 ⟨0, by omega⟩) : ℂ))
      (scalarTorusToCell (mFourierLp 2 n))
    filter_upwards [hjet, hval, hs] with x hx hv hsx
    simpa only [cellComplexFourierJet, dite_eq_right h, hsx, hv, Pi.smul_apply,
      smul_eq_mul] using hx

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open scoped Topology Pointwise
namespace AVRegularity.CycleWords

/-! Compactly supported native data admit smooth Sobolev approximants with a common compact support. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem exists_compact_smooth_planeHk_approximation {K : ℕ} (U : PlaneHk Set.univ K E)
    (A : Set (Vec 2)) (hA : IsCompact A)
    (hu : ∀ᵐ x ∂volume, x ∉ A → planeValue U x = 0) :
    ∃ UN : ℕ → PlaneHk Set.univ K E, ∃ fN : ℕ → Vec 2 → E,
      Tendsto UN atTop (𝓝 U) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fN n)) ∧
      (∀ n, HasCompactSupport (fN n)) ∧
      (∀ n, planeValue (UN n) =ᵐ[volume] fN n) ∧
      (∀ n, Function.support (fN n) ⊆ A + Metric.closedBall (0 : Vec 2) 2) := by
  let φ : ContDiffBump (0 : Vec 2) := ⟨1, 2, by norm_num, by norm_num⟩
  let κ : Vec 2 → ℝ := φ.normed volume
  have hc : HasCompactSupport κ := φ.hasCompactSupport_normed
  have hd : ContDiff ℝ (⊤ : ℕ∞) κ := φ.contDiff_normed
  have hm : ∫ z, κ z = 1 := φ.integral_normed
  let c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hcn (n : ℕ) : c n ≠ 0 := by dsimp [c]; positivity
  let R (n : ℕ) : Vec 2 ≃L[ℝ] Vec 2 :=
    Units.mk0 (c n) (hcn n) • ContinuousLinearEquiv.refl ℝ (Vec 2)
  have hz (z : Vec 2) : Tendsto (fun n => R n z) atTop (𝓝 0) := by
    change Tendsto (fun n => c n • z) atTop (𝓝 0)
    simpa only [c, one_div, zero_smul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const z
  let f := univToPlane (U.val (valueIndex2 K))
  have hf : ∀ᵐ x ∂volume, x ∉ A → f x = 0 := by
    have hv : f =ᵐ[volume] planeValue U := planeValueLp_ae U
    filter_upwards [hv, hu] with x hx hu'
    intro hout
    rw [hx, hu' hout]
  let UN n := planeSmoothing (K := K) (R n) κ hc hd f
  let fN n : Vec 2 → E := fun x => ∫ z, κ z • f (x - R n z)
  have hs (n : ℕ) : R n '' tsupport κ ⊆ Metric.closedBall (0 : Vec 2) 2 := by
    rintro y ⟨z, hz', rfl⟩
    have hzn : ‖z‖ ≤ 2 := by
      rw [show tsupport κ = Metric.closedBall (0 : Vec 2) 2 from φ.tsupport_normed_eq] at hz'
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz'
    have hc0 : 0 ≤ c n := by dsimp [c]; positivity
    have hc1 : c n ≤ 1 := inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
    change ‖c n • z - 0‖ ≤ 2
    rw [sub_zero, norm_smul, Real.norm_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_right hc1 (norm_nonneg z)).trans (by simpa using hzn)
  refine ⟨UN, fN, tendsto_planeSmoothing R hz hc hd hm U, ?_, ?_, ?_, ?_⟩
  · intro n
    exact contDiff_literalAverage (R n) hc hd ((Lp.memLp f).locallyIntegrable (by norm_num))
  · intro n
    exact literalAverage_hasCompactSupport (R n) κ hc f A hA hf
  · intro n
    have ha := averagingOperator_plane_literal_ae (R n)
      (hd.continuous.integrable_of_hasCompactSupport hc) f
    have hv := planeToUniv_ae (averagingOperator (R n).toLinearEquiv.toAddHom
      (R n).continuous κ (hd.continuous.integrable_of_hasCompactSupport hc) f)
    change ((UN n).val (valueIndex2 K) : Vec 2 → E) =ᵐ[volume] fN n
    rw [planeSmoothing_value]
    exact hv.trans ha
  · intro n x hx
    by_contra hout
    have hlarge : x ∉ A + R n '' tsupport κ := fun hh => hout
      ((Set.add_subset_add (Set.Subset.refl A) (hs n)) hh)
    exact hx (literalAverage_eq_zero_of_outside_support (R n) κ f A hf x hlarge)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords

/-! Scalar coordinate tests recover the exact native Hilbert-valued scalar weak RHS. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem realFiberScalarTestPair (e u : E) (a : ℝ) :
    inner ℝ u (a • e) = inner ℝ (inner ℝ e u) a := by
  rw [real_inner_smul_right, Real.inner_apply, real_inner_comm u e]
  ring

omit [FiniteDimensional ℝ E] in
theorem planeScalarCoordinateRawRhs (K : ℕ) (e : E)
    (v : Vec 2 → Vec 2) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : PlaneHk Set.univ (K + 1) E) (φ : PlaneHk Set.univ 1 ℝ) :
    planeScalarRawRhsZeroFlux K v G
      (mapPlaneHk (InnerProductSpace.toDual ℝ E e) w) φ =ᵐ[volume]
      planeScalarRawRhsZeroFlux K v G w
        (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ) := by
  have hc : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      (mapPlaneHk (InnerProductSpace.toDual ℝ E e) w).toFunction.jet
        ⟨⟨1, by omega⟩, fun _ => i⟩ x =
      inner ℝ e (w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x) :=
    ae_all_iff.mpr (fun i => planeHkMapRawReadout _ w _)
  have hi : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ).toFunction.jet
        ⟨⟨1, by omega⟩, fun _ => i⟩ x =
      φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x • e :=
    ae_all_iff.mpr (fun i => planeHkMapRawReadout _ φ _)
  filter_upwards [hc, hi,
    planeHkMapRawReadout ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ (valueIndex2 1)]
    with x hcx hix hvx
  change (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ).toFunction.jet
    (valueIndex2 1) x = φ.toFunction.jet (valueIndex2 1) x • e at hvx
  simp only [planeScalarRawRhsZeroFlux, hvx]
  simp_rw [hcx, hix, realFiberScalarTestPair, inner_sum,
    real_inner_smul_right, Real.inner_apply, smul_eq_mul]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Fixed temporal tests for a bounded measurable bilinear form on the native H1 carrier. -/

def cellBoundedFormTest
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (t : ℝ) (z : TorusHk 1 ℂ) : TorusHk 1 ℂ :=
  (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm ((B t).flip z)

theorem cellBoundedFormTest_pairing
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    inner ℝ u (cellBoundedFormTest B t z) = B t u z := by
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

theorem cellBoundedFormTest_norm_le
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t u, ‖B t u‖ ≤ M * ‖u‖)
    (t : ℝ) (z : TorusHk 1 ℂ) : ‖cellBoundedFormTest B t z‖ ≤ M * ‖z‖ := by
  unfold cellBoundedFormTest
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg z))
  intro u
  exact ((B t u).le_opNorm z).trans
    ((mul_le_mul_of_nonneg_right
      (hb t u)
      (norm_nonneg z)).trans_eq (by ring))

theorem cellBoundedFormTest_memLp (a b : ℝ)
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (hm : ∀ u z, AEStronglyMeasurable (fun t => B t u z) (volume.restrict (Icc a b)))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t u, ‖B t u‖ ≤ M * ‖u‖) (z : TorusHk 1 ℂ) :
    MemLp (fun t => cellBoundedFormTest B t z) 2 (volume.restrict (Icc a b)) := by
  apply (memLp_const (M * ‖z‖)).of_le
  · apply cellH1_aestronglyMeasurable_of_pairings
    intro u
    simpa only [real_inner_comm, cellBoundedFormTest_pairing] using hm u z
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM (norm_nonneg z))]
      exact cellBoundedFormTest_norm_le B M hM hb t z)

def cellBoundedFormIntegralCLM (a b s t : ℝ)
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (hm : ∀ u z, AEStronglyMeasurable (fun t => B t u z) (volume.restrict (Icc a b)))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t u, ‖B t u‖ ≤ M * ‖u‖) (z : TorusHk 1 ℂ) :
    CellBochnerH1 a b →L[ℝ] ℝ :=
  cellTimeTestIntegralCLM a b s t (fun r => cellBoundedFormTest B r z)
    (cellBoundedFormTest_memLp a b B hm M hM hb z)

theorem cellBoundedFormIntegralCLM_apply {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (hm : ∀ u z, AEStronglyMeasurable (fun t => B t u z) (volume.restrict (Icc a b)))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t u, ‖B t u‖ ≤ M * ‖u‖)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) (z : TorusHk 1 ℂ) :
    cellBoundedFormIntegralCLM a b s t B hm M hM hb z (hu.toLp u) =
      ∫ r in s..t, B r (u r) z := by
  rw [cellBoundedFormIntegralCLM, cellTimeTestIntegralCLM_apply hs ht hst]
  simp only [cellBoundedFormTest_pairing]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact native weak derivative of every complex Fourier mode. -/

local instance cellComplexFourierModeDerivativeMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem cellComplexFourierModeH1_derivative (n : Fin 2 → ℤ) (i : Fin 2) :
    cellDerivativeCLM i (cellComplexFourierModeH1 n) =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) •
        scalarTorusToCell (mFourierLp 2 n) := by
  change (cellComplexFourierModeCarrier n).val ⟨⟨1, by decide⟩, fun _ => i⟩ = _
  rw [cellComplexFourierModeCarrier_coordinate]
  simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The nonlinear graph forcing depends only on each spatial value class. -/

theorem fibreGraphSource_value_congr (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (ξ : Fin 2 → ℂ) (r s : ℝ → Vec 2 → ℂ)
    (he : ∀ t, r t =ᵐ[volume.restrict AVenhance.unitCube] s t) (t : ℝ) :
    fibreGraphSource η v ξ r t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreGraphSource η v ξ s t := by
  have hmean0 : cellMean (fun y => -Complex.I *
      (((Real.sqrt η : ℂ) * ∑ k, (v t y k : ℂ) * ξ k) * (1 + r t y))) =
      cellMean (fun y => -Complex.I *
      (((Real.sqrt η : ℂ) * ∑ k, (v t y k : ℂ) * ξ k) * (1 + s t y))) := by
    unfold cellMean
    apply integral_congr_ae
    filter_upwards [he t] with x hx
    rw [hx]
  have hmean1 : cellMean (fun y => ((Real.sqrt η : ℂ) *
      ∑ k, (v t y k : ℂ) * ξ k) * r t y) =
      cellMean (fun y => ((Real.sqrt η : ℂ) * ∑ k, (v t y k : ℂ) * ξ k) * s t y) := by
    unfold cellMean
    apply integral_congr_ae
    filter_upwards [he t] with x hx
    rw [hx]
  filter_upwards [he t] with x hx
  simp only [fibreGraphSource, cellQ0, hx, hmean0, hmean1]

theorem fibreGraphFlux_value_congr (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (ξ : Fin 2 → ℂ) (r s : ℝ → Vec 2 → ℂ)
    (he : ∀ t, r t =ᵐ[volume.restrict AVenhance.unitCube] s t) (t : ℝ) :
    fibreGraphFlux η G ξ r t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreGraphFlux η G ξ s t := by
  filter_upwards [he t] with x hx
  simp only [fibreGraphFlux, hx]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords

/-! Fiber coordinates commute with the literal divergence forcing in the scalar plane equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeFiberFluxCoordinate (e : E) :
    PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (InnerProductSpace.toDual ℝ E e).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem planeFiberFluxCoordinate_apply (e : E) (q : PiLp 2 (fun _ : Fin 2 => E))
    (i : Fin 2) : planeFiberFluxCoordinate e q i = inner ℝ e (q i) := rfl

theorem planeScalarCoordinateForcedRawRhs (K : ℕ) (e : E)
    (v : Vec 2 → Vec 2) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : PlaneHk Set.univ (K + 1) E)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (φ : PlaneHk Set.univ 1 ℝ) :
    planeScalarRawRhs K v G (mapPlaneHk (InnerProductSpace.toDual ℝ E e) w)
        (mapPlaneHk (planeFiberFluxCoordinate e) F) φ =ᵐ[volume]
      planeScalarRawRhs K v G w
        F (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ) := by
  have hi : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ).toFunction.jet
        ⟨⟨1, by omega⟩, fun _ => i⟩ x =
      φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x • e :=
    ae_all_iff.mpr (fun i => planeHkMapRawReadout _ φ _)
  filter_upwards [planeScalarCoordinateRawRhs K e v G w φ, hi,
    planeHkMapRawReadout (planeFiberFluxCoordinate e) F (valueIndex2 K),
    planeZeroJetRepresentative_ae (E := ℝ) K (valueIndex2 K),
    planeZeroJetRepresentative_ae (E := E) K (valueIndex2 K)]
    with x hz hix hFx hzr hzE
  change (mapPlaneHk (planeFiberFluxCoordinate e) F).toFunction.jet (valueIndex2 K) x =
    planeFiberFluxCoordinate e (F.toFunction.jet (valueIndex2 K) x) at hFx
  have hs : ∀ (W : PlaneHk Set.univ (K + 1) E)
      (Φ : PlaneHk Set.univ 1 E),
      planeScalarRawRhs K v G W F Φ x =
        planeScalarRawRhsZeroFlux K v G W Φ x -
          ∑ i : Fin 2, inner ℝ (F.toFunction.jet (valueIndex2 K) x i)
            (Φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x) := by
    intro W Φ
    simp only [planeScalarRawRhs, planeScalarRawRhsZeroFlux, hzE, inner_zero_left,
      inner_add_left, Finset.sum_add_distrib, add_zero]
    ring
  rw [hs]
  have hsR : planeScalarRawRhs K v G (mapPlaneHk (InnerProductSpace.toDual ℝ E e) w)
      (mapPlaneHk (planeFiberFluxCoordinate e) F) φ x =
      planeScalarRawRhsZeroFlux K v G (mapPlaneHk (InnerProductSpace.toDual ℝ E e) w) φ x -
        ∑ i : Fin 2, inner ℝ (inner ℝ e (F.toFunction.jet (valueIndex2 K) x i))
          (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x) := by
    simp only [planeScalarRawRhs, planeScalarRawRhsZeroFlux, hzr, inner_zero_left,
      inner_add_left, Finset.sum_add_distrib, add_zero, hFx, planeFiberFluxCoordinate_apply]
    ring
  rw [hsR, hz]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hix, realFiberScalarTestPair]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The integrated bounded form depends continuously on its spatial test. -/

variable {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (hm : ∀ u z, AEStronglyMeasurable (fun t => B t u z) (volume.restrict (Icc a b)))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t u, ‖B t u‖ ≤ M * ‖u‖)

include hs ht hst hm M hM hb

theorem cellBoundedFormIntegralCLM_apply_class (z : TorusHk 1 ℂ) (U : CellBochnerH1 a b) :
    cellBoundedFormIntegralCLM a b s t B hm M hM hb z U =
      ∫ r in s..t, B r (U r) z := by
  simpa only [Lp.toLp_coeFn] using
    cellBoundedFormIntegralCLM_apply hs ht hst B hm M hM hb U (Lp.memLp U) z

theorem cellBoundedForm_pairing_intervalIntegrable
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) (z : TorusHk 1 ℂ) :
    IntervalIntegrable (fun r => B r (u r) z) volume s t := by
  simpa only [cellBoundedFormTest_pairing] using cellTime_inner_intervalIntegrable hs ht hst
    u (fun r => cellBoundedFormTest B r z) hu (cellBoundedFormTest_memLp a b B hm M hM hb z)

def cellBoundedFormIntegralTestLinearMap :
    TorusHk 1 ℂ →ₗ[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) where
  toFun z := cellBoundedFormIntegralCLM a b s t B hm M hM hb z
  map_add' z w := by
    ext U
    simp only [add_apply, cellBoundedFormIntegralCLM_apply_class hs ht hst]
    have he : (fun r => B r (U r) (z + w)) = fun r => B r (U r) z + B r (U r) w := by
      funext r
      exact (B r (U r)).map_add z w
    rw [he]
    exact intervalIntegral.integral_add
      (cellBoundedForm_pairing_intervalIntegrable hs ht hst B hm M hM hb U (Lp.memLp U) z)
      (cellBoundedForm_pairing_intervalIntegrable hs ht hst B hm M hM hb U (Lp.memLp U) w)
  map_smul' r z := by
    ext U
    simp only [smul_apply, cellBoundedFormIntegralCLM_apply_class hs ht hst]
    simp_rw [map_smul, smul_eq_mul]
    exact intervalIntegral.integral_const_mul r _

def cellBoundedFormIntegralTestCLM (hab : a ≤ b) :
    TorusHk 1 ℂ →L[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) := by
  let L := cellBoundedFormIntegralTestLinearMap hs ht hst B hm M hM hb
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := TorusHk 1 ℂ)
    (F := CellBochnerH1 a b →L[ℝ] ℝ) (σ := RingHom.id ℝ) L ((b - a + 1) * M) ?_
  intro z
  have h := cellTimeTestIntegralCLM_norm_le hab s t
    (fun r => cellBoundedFormTest B r z) (cellBoundedFormTest_memLp a b B hm M hM hb z)
    (M * ‖z‖) (mul_nonneg hM (norm_nonneg z))
    (fun r => cellBoundedFormTest_norm_le B M hM hb r z)
  change ‖cellBoundedFormIntegralCLM a b s t B hm M hM hb z‖ ≤
    ((b - a + 1) * M) * ‖z‖
  exact h.trans_eq (by ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords

/-! The actual periodic drift symbol reproduces the native cell drift multiplier. -/

local instance cellDriftSymbolMultiplierBridgeMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusToCell_drift_multiplier (A : CellCoefficients) (hv : IsCellDrift A.v)
    (V : ℝ) (hb : ∀ t x, ∑ i, A.v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hC : ∀ t i z, ‖cellDriftTorusSymbol A.v t i z‖ ≤ C)
    (t : ℝ) (i : Fin 2) (u : ScalarTorusL2) :
    scalarTorusToCell (measurableTorusSymbolMultiplication
      (cellDriftTorusSymbol A.v t i) (cellDriftTorusSymbol_measurable A.v hv t i)
      C (hC t i) u) = cellDriftEntryCLM A V hv.1 hb t i (scalarTorusToCell u) := by
  have hm := scalarTorusQuotient_measurePreserving.quasiMeasurePreserving.ae
    (L2Multiplier.operator_ae (cellDriftTorusSymbol A.v t i)
      (measurableTorusSymbol_memLp_top _ (cellDriftTorusSymbol_measurable A.v hv t i) C
        (hC t i)) u)
  apply Lp.ext
  filter_upwards [scalarTorusToCell_ae (measurableTorusSymbolMultiplication
      (cellDriftTorusSymbol A.v t i) (cellDriftTorusSymbol_measurable A.v hv t i) C (hC t i) u),
    hm, scalarTorusToCell_ae u, cellDriftEntryCLM_ae A V hv.1 hb t i (scalarTorusToCell u)]
    with x hx hm' hu hd
  change measurableTorusSymbolMultiplication (cellDriftTorusSymbol A.v t i)
      (cellDriftTorusSymbol_measurable A.v hv t i) C (hC t i) u (torusQuotient x) =
    cellDriftTorusSymbol A.v t i (torusQuotient x) * u (torusQuotient x) at hm'
  rw [hx, hm', cellDriftTorusSymbol_plane A.v hv t i x, hd, hu]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! A genuine L2 Fourier derivative relation gives membership in the closed cell H1 graph. -/

local instance cellH1FourierCriterionMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def scalarCellFirstJet (u : ScalarTorusL2) (d : Fin 2 → ScalarTorusL2) :
    JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ :=
  WithLp.toLp 2 (fun a : JetIndex2 1 => if h : a.1.val = 0 then scalarTorusToCell u else
    scalarTorusToCell (d (a.2 ⟨0, by omega⟩)))

theorem scalarCellFirstJet_fourier_hasSum (u : ScalarTorusL2) (d : Fin 2 → ScalarTorusL2)
    (hd : ∀ i n, mFourierCoeff (d i) n =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) * mFourierCoeff u n) :
    HasSum (fun n : Fin 2 → ℤ => mFourierCoeff u n •
      (cellComplexFourierModeCarrier n).val) (scalarCellFirstJet u d) := by
  let e := PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : JetIndex2 1 => ComplexCellL2)
  have hpi : HasSum (fun n : Fin 2 → ℤ => fun a : JetIndex2 1 =>
      (mFourierCoeff u n • (cellComplexFourierModeCarrier n).val) a)
      (fun a => scalarCellFirstJet u d a) := by
    apply Pi.hasSum.mpr
    intro a
    simp only [PiLp.smul_apply, cellComplexFourierModeCarrier_coordinate]
    change HasSum (fun n => mFourierCoeff u n •
      (if h : a.1.val = 0 then scalarTorusToCell (mFourierLp 2 n) else
        ((2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 ⟨0, by omega⟩) : ℂ)) •
          scalarTorusToCell (mFourierLp 2 n)))
      (if h : a.1.val = 0 then scalarTorusToCell u else
        scalarTorusToCell (d (a.2 ⟨0, by omega⟩)))
    split_ifs with h
    · exact scalarTorusToCell_fourier_series u
    · have hs := scalarTorusToCell_fourier_series (d (a.2 ⟨0, by omega⟩))
      apply hs.congr_fun
      intro n
      rw [hd, smul_smul]
      congr 1
      ring
  have h := hpi.mapL e.symm.toContinuousLinearMap
  convert h using 1
  · funext n
    apply PiLp.ext
    intro a
    rfl
  · apply PiLp.ext
    intro a
    rfl

theorem scalarCellFirstJet_mem_H1 (u : ScalarTorusL2) (d : Fin 2 → ScalarTorusL2)
    (hd : ∀ i n, mFourierCoeff (d i) n =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) * mFourierCoeff u n) :
    scalarCellFirstJet u d ∈ cellComplexH1Submodule := by
  apply cellComplexH1Submodule_isClosed.mem_of_tendsto
    (scalarCellFirstJet_fourier_hasSum u d hd)
  apply Filter.Eventually.of_forall
  intro s
  exact cellComplexH1Submodule.sum_mem fun n _ =>
    cellComplexH1Submodule.smul_mem (mFourierCoeff u n)
      (cellComplexFourierModeCarrier n).property

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! The positive degree metric polynomial has a measurable native coefficient
and retains the small metric insertion factor on its time window. -/

def metricTaylorTimeCoefficient (K : ℕ) (f : ℝ → Vec 2 → ℝ)
    (a b : ℝ) (t : ℝ) (z : Vec 2) : ℝ :=
  if t ∈ Set.Icc a b then taylorSlow 1 K (f t) 0 z else 0

theorem metricTaylor_polynomial_contDiff (lo K N : ℕ) (f : Vec 2 → ℝ) :
    ContDiff ℝ (N : ℕ) (taylorSlow lo K f 0) := by
  classical
  have he : taylorSlow lo K f 0 = fun z =>
      ∑ r ∈ Finset.Icc lo K, ((r.factorial : ℝ))⁻¹ •
        iteratedFDeriv ℝ r f 0 (fun _ => z) := by
    funext z
    simp only [taylorSlow, smul_eq_mul]
  rw [he]
  apply ContDiff.sum
  intro r _
  simpa only [one_smul] using (Weighted.multilinear_diagonal_contDiff N
    (fun _ => iteratedFDeriv ℝ r f 0) contDiff_const 1).const_smul (((r.factorial : ℝ))⁻¹)

theorem metricTaylor_time_coefficient_budget (K N : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → Vec 2 → ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X, Measurable (fun t => f t X)) →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (f t)) →
      0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ K →
        ‖iteratedFDeriv ℝ r (f t) 0‖ ≤ M r * g * δ ^ r) →
      (∀ z, Measurable (fun t => metricTaylorTimeCoefficient K f a b t z)) ∧
      (∀ t, ContDiff ℝ (N : ℕ) (metricTaylorTimeCoefficient K f a b t)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ N, ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (metricTaylorTimeCoefficient K f a b t) z‖ ≤
          C * g * ζ * polynomialMomentRoot ϖ z ^ K) := by
  obtain ⟨C, hC, hb⟩ := geometryTaylor_positive_jet_budget K N M hM
  refine ⟨C, hC, ?_⟩
  intro f a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet
  refine ⟨?_, ?_, ?_⟩
  · intro z
    convert Weighted.taylorSlow_time_window_measurable (Set.Icc a b) measurableSet_Icc
      1 K (fun t X _ => f t X) (fun X _ => hm X)
      (fun t ht _ => hf t ht) 0 1 z using 1
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp only [metricTaylorTimeCoefficient, ite_eq_left ht, one_smul]
    · simp only [metricTaylorTimeCoefficient, ite_eq_right ht]
  · intro t
    by_cases ht : t ∈ Set.Icc a b
    · have he : metricTaylorTimeCoefficient K f a b t = taylorSlow 1 K (f t) 0 := by
        funext z
        simp only [metricTaylorTimeCoefficient, ite_eq_left ht]
      rw [he]
      exact metricTaylor_polynomial_contDiff 1 K N (f t)
    · have he : metricTaylorTimeCoefficient K f a b t = fun _ => (0 : ℝ) := by
        funext z
        simp only [metricTaylorTimeCoefficient, ite_eq_right ht]
      rw [he]
      exact contDiff_const
  · filter_upwards [hjet, ae_restrict_mem measurableSet_Icc] with t ht htI
    have he : metricTaylorTimeCoefficient K f a b t = taylorSlow 1 K (f t) 0 := by
      funext z
      simp only [metricTaylorTimeCoefficient, ite_eq_left htI]
    rw [he]
    exact hb (f t) ϖ ρ δ ζ g hϖ hρ hscale hζ hζ1 hg hδ ht

end AVRegularity.CycleWords
end
end
