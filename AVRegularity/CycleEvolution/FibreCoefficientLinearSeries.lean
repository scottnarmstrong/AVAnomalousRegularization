-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
public import AVRegularity.CycleEvolution.CellMeanProjection
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! The constant-one H¹ test and its exact value and derivative classes. -/

/-- A named real test keeps its periodicity proof and representative construction stable. -/
def cellH1RealOne : TorusHkFunction 1 ℝ :=
  cellSmoothScalarH1 (fun _ => 1) contDiff_const (fun _ _ => rfl)

/-- The complex constant-one test as a genuine periodic H¹ element. -/
def cellH1One : TorusHk 1 ℂ := mapTorusHk Complex.ofRealCLM cellH1RealOne.toHk

/-- The value of the constant test is the constant-one L² class. -/
theorem cellH1One_value : torusHkValueCLM cellH1One = cellConstantCLM 1 := by
  apply Lp.ext
  have hm := mapTorusHk_jet_ae Complex.ofRealCLM cellH1RealOne.toHk (valueIndex2 1)
  have hr := torusJetToL2_ae cellH1RealOne.jet cellH1RealOne.hasPeriodicWeakJet.2.1 (valueIndex2 1)
  filter_upwards [hm, hr, cellConstantCLM_ae 1] with x hx hq hc
  change torusHkValueCLM cellH1One x = _ at hx
  change cellH1RealOne.toHk.val (valueIndex2 1) x = cellH1RealOne.jet (valueIndex2 1) x at hq
  rw [hx, hq, hc]
  rfl

/-- The derivatives of the constant test are zero L² classes. -/
theorem cellH1One_derivative (j : Fin 2) : cellDerivativeCLM j cellH1One = 0 := by
  apply Lp.ext
  let a : JetIndex2 1 := ⟨⟨1, by decide⟩, fun _ => j⟩
  have hm := mapTorusHk_jet_ae Complex.ofRealCLM cellH1RealOne.toHk a
  have hr := torusJetToL2_ae cellH1RealOne.jet cellH1RealOne.hasPeriodicWeakJet.2.1 a
  filter_upwards [hm, hr, Lp.coeFn_zero (E := ℂ) (p := 2)
    (μ := volume.restrict AVenhance.unitCube)] with x hx hq hz
  change cellDerivativeCLM j cellH1One x = _ at hx
  change cellH1RealOne.toHk.val a x = cellH1RealOne.jet a x at hq
  rw [hx, hq, hz]
  simp only [cellH1RealOne, cellSmoothScalarH1, cellSmoothScalarJet, a, smoothLiftWord,
    AVenhance.Infra.Classical.classicalWordDerivative, AVenhance.spaceGrad, fderiv_const_apply,
    zero_apply, map_zero, Pi.zero_apply]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! The frequency coupling inherits the actual zero spatial mean of the drift. -/

local instance fibreDriftCouplingMeanZeroProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem fibreDriftCoupling_mean_zero (η : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (ξ : Fin 2 → ℂ) (t : ℝ) : cellMean (fibreDriftCoupling η v ξ t) = 0 := by
  obtain ⟨V, hV⟩ := hv.2.1
  have hi (j : Fin 2) : Integrable (fun x => (v t x j : ℂ))
      (volume.restrict AVenhance.unitCube) := by
    have hmeas : Measurable (fun x => (v t x j : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((measurable_pi_apply j).comp (hv.1.comp (measurable_const.prodMk measurable_id)))
    have hp : MemLp (fun x => (v t x j : ℂ)) 2 (volume.restrict AVenhance.unitCube) :=
      MemLp.of_bound hmeas.aestronglyMeasurable |V| (Filter.Eventually.of_forall (fun x => by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hV t x j))
    exact hp.integrable (by norm_num)
  unfold cellMean fibreDriftCoupling
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => (hi j).mul_const (ξ j))]
  simp only [integral_mul_const]
  change (Real.sqrt η : ℂ) * (∑ j : Fin 2, cellMean (fun x => (v t x j : ℂ)) * ξ j) = 0
  simp only [hm, zero_mul, Finset.sum_const_zero, mul_zero]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniform weighted cell L2 coefficient bounds control the literal monomial series at every time. -/

theorem cellL2Norm_const_complex_mul (c : ℂ) (f : Vec 2 → ℂ) :
    cellL2Norm (fun x => c * f x) = ‖c‖ₑ * cellL2Norm f := by
  change eLpNorm (c • f) 2 _ = _
  exact eLpNorm_const_smul c f 2 _

theorem fibreL2Series_norm_sum_le (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (R : ℝ)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ R) (t : ℝ) :
    (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * a p t x)) ≤
      ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, cellL2Norm (a p s) := by
  apply ENNReal.tsum_le_tsum
  intro p
  rw [cellL2Norm_const_complex_mul, ← ofReal_norm]
  exact mul_le_mul' (fibreMonomial_weight_le R ξ hξ p)
    (le_iSup (fun s => cellL2Norm (a p s)) t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Uniform weighted bounds for the overlap coefficients used to normalize the dual row. -/

def fibreMeanConvolution (f g : ℕ × ℕ → ℝ → Vec 2 → ℂ) : ℕ × ℕ → ℝ → ℂ :=
  fun p t => ∑ a ∈ fibreCoefficientPairs p,
    cellMean (fun x => f a t x * g (fibreCoefficientComplement p a) t x)

theorem fibreMeanConvolution_uniform_le (f g : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (hf : ∀ p t, MemLp (f p t) 2 (volume.restrict AVenhance.unitCube))
    (hg : ∀ p t, MemLp (g p t) 2 (volume.restrict AVenhance.unitCube)) (p : ℕ × ℕ) :
    (⨆ t, ‖fibreMeanConvolution f g p t‖ₑ) ≤
      ∑ a ∈ fibreCoefficientPairs p, (⨆ t, cellL2Norm (f a t)) *
        ⨆ t, cellL2Norm (g (fibreCoefficientComplement p a) t) := by
  apply iSup_le
  intro t
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply (cellL2_product_lintegral_le _ _ _ (hf a t).aestronglyMeasurable
    (hg (fibreCoefficientComplement p a) t).aestronglyMeasurable).trans
  exact mul_le_mul' (le_iSup (fun s => cellL2Norm (f a s)) t)
    (le_iSup (fun s => cellL2Norm (g (fibreCoefficientComplement p a) s)) t)

theorem fibreMeanConvolution_weighted_le (f g : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (hf : ∀ p t, MemLp (f p t) 2 (volume.restrict AVenhance.unitCube))
    (hg : ∀ p t, MemLp (g p t) 2 (volume.restrict AVenhance.unitCube)) (ρ : ℝ≥0∞) :
    (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖fibreMeanConvolution f g p t‖ₑ) ≤
      (∑' p, fibreCoefficientWeight ρ p * ⨆ t, cellL2Norm (f p t)) *
        ∑' p, fibreCoefficientWeight ρ p * ⨆ t, cellL2Norm (g p t) := by
  rw [← fibreCoefficient_weighted_convolution_total]
  exact ENNReal.tsum_le_tsum (fun p =>
    mul_le_mul' le_rfl (fibreMeanConvolution_uniform_le f g hf hg p))

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The zero constant coefficient turns absolute weighted energy into a linear frequency bound. -/

/-- A zero constant coefficient supplies the first-order gain in the monomial energy series. -/
theorem fibreMonomial_linear_energy_le (R : ℝ) (hR : 0 < R) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ R) (E : ℕ × ℕ → ℝ≥0∞) (hzero : E 0 = 0) :
    (∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * E p) ≤
      ENNReal.ofReal (fibreNorm ξ / R) * ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro p
  by_cases hp : p = 0
  · rw [hp, hzero]
    simp
  · have ho : 0 < p.1 + p.2 := by
      by_contra h
      have hz : p = 0 := by apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega
      exact hp hz
    exact (mul_le_mul' (fibreMonomial_linear_weight_le R hR ξ hξ ho) le_rfl).trans_eq
      (mul_assoc _ _ _)

/-! Radius gains for arbitrary vanishing order, used for the quadratic fibre symbol. -/

theorem power_radius_order_le {x R : ℝ} (hx : 0 ≤ x) (hR : 0 < R)
    (hxr : x ≤ R) {m n : ℕ} (hmn : m ≤ n) :
    x ^ n ≤ (x / R) ^ m * R ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  calc
    x ^ (m + k) = x ^ m * x ^ k := pow_add x m k
    _ ≤ x ^ m * R ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxr k) (pow_nonneg hx m)
    _ = (x / R) ^ m * R ^ (m + k) := by
      rw [div_pow, pow_add]
      field_simp

theorem fibreCoefficient_weight_order_radius_gain {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hR : 0 < R) (hρR : ρ ≤ R) {m : ℕ} {p : ℕ × ℕ} (hp : m ≤ p.1 + p.2) :
    fibreCoefficientWeight (ENNReal.ofReal ρ) p ≤
      ENNReal.ofReal ((ρ / R) ^ m) * fibreCoefficientWeight (ENNReal.ofReal R) p := by
  unfold fibreCoefficientWeight
  rw [← ENNReal.ofReal_pow hρ, ← ENNReal.ofReal_pow hR.le,
    ← ENNReal.ofReal_mul (pow_nonneg (div_nonneg hρ hR.le) m)]
  exact ENNReal.ofReal_le_ofReal (power_radius_order_le hρ hR hρR hp)

theorem fibreCoefficient_weighted_order_radius_gain {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hR : 0 < R) (hρR : ρ ≤ R) (m : ℕ) (E : ℕ × ℕ → ℝ≥0∞)
    (hz : ∀ p, p.1 + p.2 < m → E p = 0) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p * E p) ≤
      ENNReal.ofReal ((ρ / R) ^ m) *
        ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro p
  by_cases hp : m ≤ p.1 + p.2
  · exact (mul_le_mul' (fibreCoefficient_weight_order_radius_gain hρ hR hρR hp) le_rfl).trans_eq
      (mul_assoc _ _ _)
  · rw [hz p (Nat.lt_of_not_ge hp)]
    simp

end AVRegularity.CycleEvolution
end

section
open Homogenization
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Coordinate frequencies and their literal scaled-drift coefficients. -/

/-- The coordinate unit frequency used in the two-variable coefficient recursion. -/
def fibreCoordinateFrequency (j : Fin 2) : Fin 2 → ℂ := Pi.single j 1

/-- Each coordinate frequency has exactly unit fibre norm. -/
theorem fibreCoordinateFrequency_norm (j : Fin 2) :
    fibreNorm (fibreCoordinateFrequency j) = 1 := by
  rw [fibreNorm_eq_piLp_norm]
  change ‖(PiLp.single 2 j (1 : ℂ) : PiLp 2 (fun _ : Fin 2 => ℂ))‖ = 1
  rw [PiLp.norm_single]
  simp

/-- Coupling to a coordinate frequency extracts the actual corresponding scaled velocity component. -/
theorem fibreCoordinateFrequency_coupling (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (j : Fin 2) (t : ℝ) (x : Vec 2) :
    fibreDriftCoupling η v (fibreCoordinateFrequency j) t x =
      (Real.sqrt η : ℂ) * (v t x j : ℂ) := by
  simp [fibreDriftCoupling, fibreCoordinateFrequency, Pi.single_apply]

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual convergence of literal monomial-weighted quadratic convolution coefficients. -/

/-- Absolute convergence of both input monomial series proves convergence of their literal coefficient convolution. -/
theorem fibreMonomial_convolution_summable (ξ : Fin 2 → ℂ) (f g : ℕ × ℕ → ℂ)
    (hf : Summable (fun p => ‖fibreMonomial ξ p * f p‖))
    (hg : Summable (fun p => ‖fibreMonomial ξ p * g p‖)) :
    Summable (fun p => fibreMonomial ξ p *
      ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a)) := by
  have hs := (fibreCoefficient_convolution_hasSum
    (fun p => fibreMonomial ξ p * f p) (fun p => fibreMonomial ξ p * g p) hf hg).summable
  apply hs.congr
  intro p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← fibreMonomial_convolution ξ ha]
  ring

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Active coordinate shifts preserve convergence of literal monomial coefficient series. -/

/-- Every active predecessor series gains one coordinate frequency and remains summable. -/
theorem fibreMonomial_shift_summable (ξ : Fin 2 → ℂ) (j : Fin 2) (f : ℕ × ℕ → ℂ)
    (hs : Summable (fun p => fibreMonomial ξ p * f p)) :
    Summable (fun p => if j ∈ fibreCoefficientDirections p then
      fibreMonomial ξ p * f (fibreCoefficientPrevious p j) else 0) := by
  have hh := fibreCoefficient_shift_summable j
    (fun p => ξ j * (fibreMonomial ξ p * f p)) (hs.mul_left (ξ j))
  apply hh.congr
  intro p
  split_ifs with hp
  · have hm : fibreMonomial ξ p = fibreMonomial ξ (fibreCoefficientPrevious p j) * ξ j := by
      calc
        _ = fibreMonomial ξ (fibreCoefficientPrevious p j + cellJetDirection j) :=
          congrArg (fibreMonomial ξ) (fibreCoefficientPrevious_recover hp).symm
        _ = _ := by rw [fibreMonomial_add, fibreMonomial_direction]
    rw [hm]
    ring
  · rfl

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! A uniform extended-real coefficient majorant supplies genuine Banach-valued analyticity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem fibreUniformMajorant_weighted_summable (a : ℕ × ℕ → ℝ → E) (R : ℝ≥0)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ s, ‖a p s‖ₑ) < ⊤)
    (t : ℝ) : Summable (fun p => ‖a p t‖ * (R : ℝ) ^ (p.1 + p.2)) := by
  let f : ℕ × ℕ → ℝ := fun p => ‖a p t‖ * (R : ℝ) ^ (p.1 + p.2)
  have hf p : 0 ≤ f p := mul_nonneg (norm_nonneg _) (pow_nonneg R.coe_nonneg _)
  have hb : (∑' p, ‖f p‖ₑ) < ⊤ := by
    apply (ENNReal.tsum_le_tsum (fun p => ?_)).trans_lt ha
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf p)]
    simp only [f, ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.ofReal_pow R.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [mul_comm]
    exact mul_le_mul' le_rfl (by rw [ofReal_norm]; exact le_iSup (fun s => ‖a p s‖ₑ) t)
  have hs := tsum_enorm_ne_top_iff_summable_norm.mp hb.ne
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hs

theorem fibreUniformMajorant_analyticOnNhd (a : ℕ × ℕ → ℝ → E) (R : ℝ≥0)
    (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ s, ‖a p s‖ₑ) < ⊤)
    (t : ℝ) : AnalyticOnNhd ℂ (fun ξ => ∑' p, fibreMonomial ξ p • a p t)
      (Metric.ball 0 (R : ℝ)) :=
  fibreBivariateSum_analyticOnNhd (fun p => a p t) R hR
    (fibreUniformMajorant_weighted_summable a R ha t)

end AVRegularity.CycleEvolution
end

section
open Homogenization
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Coordinate expansion of the literal scaled drift coupling. -/

/-- The coordinate couplings recover the actual arbitrary-frequency drift multiplier. -/
theorem fibreDriftCoupling_coordinates (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2) :
    (∑ j : Fin 2, fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * ξ j) =
      fibreDriftCoupling η v ξ t x := by
  simp_rw [fibreCoordinateFrequency_coupling]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  rfl

end AVRegularity.CycleEvolution
end

section
open Homogenization MeasureTheory
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! All-frequency homogeneous cell L2 bounds from geometric coefficient estimates. -/

theorem fibreHomogeneous_cellL2_le_of_geometric (a : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (K A : ℝ)
    (ha : ∀ p t, cellL2Norm (a p t) ≤ ENNReal.ofReal (K * A ^ (p.1 + p.2)))
    (n : ℕ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellL2Norm (fibreHomogeneous a ξ n t) ≤ ENNReal.ofReal (K * (2 * A) ^ n * fibreNorm ξ ^ n) := by
  let S : Finset (ℕ × ℕ) := Finset.HasAntidiagonal.antidiagonal n
  let f := fun p x => fibreMonomial ξ p * a p t x
  have he : fibreHomogeneous a ξ n t = ∑ p ∈ S, f p := by
    funext x
    simp only [fibreHomogeneous, S, f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  have hsum := eLpNorm_sum_le (μ := volume.restrict AVenhance.unitCube)
    (f := f) (s := S) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply hsum.trans
  have hp p (hpn : p ∈ S) : cellL2Norm (f p) ≤ ENNReal.ofReal (K * A ^ n * fibreNorm ξ ^ n) := by
    have ho : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn
    rw [cellL2Norm_const_complex_mul]
    have hm : ‖fibreMonomial ξ p‖ₑ ≤ ENNReal.ofReal (fibreNorm ξ ^ n) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by simpa only [ho] using fibreMonomial_norm_le ξ p)
    have hcoef : cellL2Norm (a p t) ≤ ENNReal.ofReal (K * A ^ n) := by
      simpa only [ho] using ha p t
    apply (mul_le_mul' hm hcoef).trans_eq
    rw [← ENNReal.ofReal_mul (pow_nonneg (fibreNorm_nonneg ξ) n)]
    congr 1
    ring
  apply (Finset.sum_le_sum hp).trans
  rw [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]
  have hn : ((n + 1 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt ((show n < 2 ^ n from Nat.lt_two_pow_self))
  apply (mul_le_mul' hn le_rfl).trans_eq
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  congr 1
  rw [mul_pow]
  ring

end AVRegularity.CycleEvolution
end

section
open Homogenization
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! The literal finite-rectangle cell-pairing coefficients sum to the pairing of both L2 series. -/

theorem fibreMean_cauchy_product (f g : ℕ × ℕ → Vec 2 → ℂ)
    (hf : (∑' p, cellL2Norm (f p)) < ⊤) (hg : (∑' p, cellL2Norm (g p)) < ⊤) :
    (∑' p, ∑ a ∈ fibreCoefficientPairs p,
      cellMean (fun x => f a x * g (fibreCoefficientComplement p a) x)) =
      cellMean (fun x => (∑' p, f p x) * ∑' p, g p x) := by
  let H := fun q : (ℕ × ℕ) × (ℕ × ℕ) => cellMean (fun x => f q.1 x * g q.2 x)
  have hH : Summable H := (cellMean_double_series_summable_norm f g hf hg).of_norm
  have hsum := hH.hasSum.tsum_fiberwise (fun q => q.1 + q.2)
  have he (p : ℕ × ℕ) :
      (∑' q : {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p}, H q.1) =
        ∑ a ∈ fibreCoefficientPairs p,
          cellMean (fun x => f a x * g (fibreCoefficientComplement p a) x) := by
    rw [← (fibreCoefficientConvolutionFibreEquiv p).symm.tsum_eq (fun q => H q.1)]
    simp only [H, fibreCoefficientConvolutionFibreEquiv_symm_fst,
      fibreCoefficientConvolutionFibreEquiv_symm_snd]
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun a =>
      cellMean (fun x => f a x * g (fibreCoefficientComplement p a) x)) (fibreCoefficientPairs p)
  calc
    _ = ∑' p, ∑' q : {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p}, H q.1 :=
      tsum_congr (fun p => (he p).symm)
    _ = ∑' q, H q := hsum.tsum_eq
    _ = ∑' a, ∑' b, cellMean (fun x => f a x * g b x) := hH.tsum_prod
    _ = _ := (cellMean_tsum_mul_tsum f g hf hg).symm

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Exact decomposition of a scalar symbol into its quadratic polynomial and higher Taylor coefficients. -/

def fibreScalarHighCoefficients (a : ℕ × ℕ → ℝ → ℂ) : ℕ × ℕ → ℝ → ℂ :=
  fun p t => if p.1 + p.2 < 3 then 0 else a p t

def fibreScalarQuadraticValue (a : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) : ℂ :=
  a (2, 0) t * ξ 0 ^ 2 + a (1, 1) t * ξ 0 * ξ 1 + a (0, 2) t * ξ 1 ^ 2

theorem fibreScalarHighCoefficients_majorant_le (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ t, ‖fibreScalarHighCoefficients a p t‖ₑ) ≤
      ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ t, ‖a p t‖ₑ := by
  apply ENNReal.tsum_le_tsum
  intro p
  apply mul_le_mul' le_rfl
  apply iSup_mono
  intro t
  dsimp only [fibreScalarHighCoefficients]
  split_ifs
  · simp only [enorm_zero]; exact bot_le
  · exact le_rfl

theorem fibreScalarSeries_quadratic_split (a : ℕ × ℕ → ℝ → ℂ)
    (hz : ∀ p, p.1 + p.2 ≤ 1 → ∀ t, a p t = 0)
    (ξ : Fin 2 → ℂ) (t : ℝ) (hs : Summable (fun p => fibreMonomial ξ p * a p t)) :
    fibreSeriesC a ξ t = fibreScalarQuadraticValue a ξ t +
      fibreSeriesC (fibreScalarHighCoefficients a) ξ t := by
  classical
  have h20 := fibreMonomial_delta_hasSum ξ (2, 0) (a (2, 0) t)
  have h11 := fibreMonomial_delta_hasSum ξ (1, 1) (a (1, 1) t)
  have h02 := fibreMonomial_delta_hasSum ξ (0, 2) (a (0, 2) t)
  have hlo := (h20.add h11).add h02
  have hterm (p : ℕ × ℕ) : fibreMonomial ξ p * fibreScalarHighCoefficients a p t =
      fibreMonomial ξ p * a p t -
      ((fibreMonomial ξ p * (if p = (2, 0) then a (2, 0) t else 0) +
        fibreMonomial ξ p * (if p = (1, 1) then a (1, 1) t else 0)) +
        fibreMonomial ξ p * (if p = (0, 2) then a (0, 2) t else 0)) := by
    by_cases hp20 : p = (2, 0)
    · subst p; simp [fibreScalarHighCoefficients]
    by_cases hp11 : p = (1, 1)
    · subst p; simp [fibreScalarHighCoefficients]
    by_cases hp02 : p = (0, 2)
    · subst p; simp [fibreScalarHighCoefficients]
    have hdeg : p.1 + p.2 < 3 → p.1 + p.2 ≤ 1 := by
      have hnot : p.1 + p.2 ≠ 2 := by
        intro hh
        have he : p = (2, 0) ∨ p = (1, 1) ∨ p = (0, 2) := by
          rcases p with ⟨p, q⟩
          simp only [Prod.mk.injEq] at *
          omega
        rcases he with h | h | h <;> contradiction
      omega
    simp only [fibreScalarHighCoefficients, hp20, hp11, hp02, ite_false, mul_zero,
      add_zero, sub_zero]
    split_ifs with hh
    · rw [hz p (hdeg hh) t, mul_zero]
    · rfl
  have hhi := (hs.hasSum.sub hlo).congr_fun (fun p => hterm p)
  have hq : (fibreMonomial ξ (2, 0) * a (2, 0) t + fibreMonomial ξ (1, 1) * a (1, 1) t) +
      fibreMonomial ξ (0, 2) * a (0, 2) t = fibreScalarQuadraticValue a ξ t := by
    simp only [fibreMonomial, pow_zero, pow_one, mul_one, one_mul, fibreScalarQuadraticValue]
    ring
  change (∑' p, fibreMonomial ξ p * a p t) = fibreScalarQuadraticValue a ξ t +
    ∑' p, fibreMonomial ξ p * fibreScalarHighCoefficients a p t
  rw [hhi.tsum_eq, hq]
  ring

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Exact constant-plus-linear coordinate forcing in a convergent Taylor series. -/

/-- The constant and predecessor coefficient terms sum to the literal affine coordinate multiplier. -/
theorem fibreTaylor_affine_series (ξ b : Fin 2 → ℂ) (f : ℕ × ℕ → ℂ)
    (hs : Summable (fun p => fibreMonomial ξ p * f p)) :
    (∑' p, fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * ((if p = cellJetDirection j then 1 else 0) + f (fibreCoefficientPrevious p j))) =
      (∑ j : Fin 2, b j * ξ j) * (1 + ∑' p, fibreMonomial ξ p * f p) := by
  let S := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * f (fibreCoefficientPrevious p j) else 0
  let C := fun (j : Fin 2) (p : ℕ × ℕ) => if p = cellJetDirection j then b j * ξ j else 0
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * (b j * ((if p = cellJetDirection j then 1 else 0) + f (fibreCoefficientPrevious p j))) else 0
  have hunit j : j ∈ fibreCoefficientDirections (cellJetDirection j) := by
    simpa only [zero_add] using fibreCoefficientDirections_add (0 : ℕ × ℕ) j
  have he j p : A j p = C j p + b j * S j p := by
    by_cases hj : j ∈ fibreCoefficientDirections p
    · by_cases hp : p = cellJetDirection j
      · subst p
        simp only [A, C, S, ite_eq_left (hunit j), ite_eq_left rfl, ite_true, fibreMonomial_direction]
        ring
      · simp only [A, C, S, ite_eq_left hj, ite_eq_right hp, zero_add]
        ring
    · have hp : p ≠ cellJetDirection j := fun h => hj (h ▸ hunit j)
      simp only [A, C, S, ite_eq_right hj, ite_eq_right hp, mul_zero, add_zero]
  have hS j : Summable (S j) := fibreMonomial_shift_summable ξ j f hs
  have hC j : Summable (C j) := (hasSum_ite_eq (cellJetDirection j) (b j * ξ j)).summable
  have hA j : Summable (A j) := by
    have hfun : A j = C j + (fun p => b j * S j p) := funext (he j)
    rw [hfun]
    exact (hC j).add ((hS j).mul_left (b j))
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * ((if p = cellJetDirection j then 1 else 0) + f (fibreCoefficientPrevious p j))) =
      (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact (ite_eq_left hj).symm
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ite_eq_right hj)
  have hsum j : (∑' p, A j p) = b j * ξ j + b j * (ξ j * ∑' p, fibreMonomial ξ p * f p) := by
    have hfun : A j = C j + (fun p => b j * S j p) := funext (he j)
    rw [hfun]
    change (∑' p, (C j p + b j * S j p)) = _
    rw [(hC j).tsum_add ((hS j).mul_left (b j)), tsum_mul_left]
    have hc : (∑' p, C j p) = b j * ξ j := tsum_ite_eq _ _
    have hssum : (∑' p, S j p) = ξ j * ∑' p, fibreMonomial ξ p * f p :=
      fibreMonomial_shift_tsum ξ j f
    rw [hc, hssum]
  rw [htotal, Summable.tsum_finsetSum (fun j _ => hA j)]
  simp_rw [hsum]
  simp only [Fin.sum_univ_two]
  ring

/-! Coordinate-weighted predecessor series for the literal Taylor flux. -/

/-- The literal coordinate predecessor sum is multiplication by the coordinate frequency polynomial. -/
theorem fibreTaylor_coordinate_series (ξ b : Fin 2 → ℂ) (f : Fin 2 → ℕ × ℕ → ℂ)
    (hs : ∀ j, Summable (fun p => fibreMonomial ξ p * f j p)) :
    (∑' p, fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) =
      ∑ j : Fin 2, b j * ξ j * ∑' p, fibreMonomial ξ p * f j p := by
  let S := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * f j (fibreCoefficientPrevious p j) else 0
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => b j * S j p
  have hS j : Summable (S j) := fibreMonomial_shift_summable ξ j (f j) (hs j)
  have hA j : Summable (A j) := (hS j).mul_left (b j)
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) = (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [A, S]
        rw [ite_eq_left hj]
        ring
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
        dsimp [A, S]
        rw [ite_eq_right hj, mul_zero])
  have hsum j : (∑' p, A j p) = b j * (ξ j * ∑' p, fibreMonomial ξ p * f j p) := by
    change (∑' p, b j * S j p) = _
    rw [tsum_mul_left]
    congr 1
    exact fibreMonomial_shift_tsum ξ j (f j)
  rw [htotal, Summable.tsum_finsetSum (fun j _ => hA j)]
  simp_rw [hsum]
  simp only [Fin.sum_univ_two]
  ring

/-! Coordinate-weighted predecessor series for the literal Taylor flux. -/

/-- The literal coordinate predecessor sum is multiplication by the coordinate frequency polynomial. -/
theorem fibreTaylor_coordinate_summable (ξ b : Fin 2 → ℂ) (f : Fin 2 → ℕ × ℕ → ℂ)
    (hs : ∀ j, Summable (fun p => fibreMonomial ξ p * f j p)) :
    Summable (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) := by
  let S := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * f j (fibreCoefficientPrevious p j) else 0
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => b j * S j p
  have hS j : Summable (S j) := fibreMonomial_shift_summable ξ j (f j) (hs j)
  have hA j : Summable (A j) := (hS j).mul_left (b j)
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) = (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [A, S]
        rw [ite_eq_left hj]
        ring
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
        dsimp [A, S]
        rw [ite_eq_right hj, mul_zero])
  rw [htotal]
  simpa only [Fin.sum_univ_two] using (hA 0).add (hA 1)

/-! Coordinate-weighted predecessor series for the literal Taylor flux. -/

/-- The literal coordinate predecessor sum is multiplication by the coordinate frequency polynomial. -/
theorem fibreTaylor_linear_series (ξ b : Fin 2 → ℂ) (f : ℕ × ℕ → ℂ)
    (hs : Summable (fun p => fibreMonomial ξ p * f p)) :
    (∑' p, fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f (fibreCoefficientPrevious p j)) =
      (∑ j : Fin 2, b j * ξ j) * ∑' p, fibreMonomial ξ p * f p := by
  let S := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * f (fibreCoefficientPrevious p j) else 0
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => b j * S j p
  have hS j : Summable (S j) := fibreMonomial_shift_summable ξ j f hs
  have hA j : Summable (A j) := (hS j).mul_left (b j)
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f (fibreCoefficientPrevious p j)) = (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [A, S]
        rw [ite_eq_left hj]
        ring
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
        dsimp [A, S]
        rw [ite_eq_right hj, mul_zero])
  have hsum j : (∑' p, A j p) = b j * (ξ j * ∑' p, fibreMonomial ξ p * f p) := by
    change (∑' p, b j * S j p) = _
    rw [tsum_mul_left]
    congr 1
    exact fibreMonomial_shift_tsum ξ j f
  rw [htotal, Summable.tsum_finsetSum (fun j _ => hA j)]
  simp_rw [hsum]
  simp only [Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute uniformly local series converge pointwise almost everywhere on the full time-space product. -/

/-- A summable uniformly local majorant gives joint almost-everywhere absolute pointwise convergence. -/
theorem cellUlSeries_summable_norm_ae {J E : Type*} [Countable J]
    [NormedAddCommGroup E] [CompleteSpace E]
    (f : J → ℝ → Vec 2 → E)
    (hf : ∀ j, AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hs : (∑' j, cellUlNorm Set.univ (f j)) < ⊤) :
    ∀ᵐ p ∂((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)),
      Summable (fun j => ‖f j p.1 p.2‖) := by
  simp only [Measure.restrict_univ]
  apply cellProduct_ae_of_integer_windows (volume.restrict AVenhance.unitCube)
  intro n
  exact (cellLpSeries_memLp_bound _ (fun j => Function.uncurry (f j))
    (cellUlSeries_interval_eLpNorm_tsum_lt_top f hf hs (n : ℝ) ((n : ℝ) + 1))).2.2

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! The integrated scalar symbol coefficients retain an analytic majorant on every finite interval. -/

theorem fibreUniformMajorant_integrated_le (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (M : ENNReal) (ha : ∀ p, AEStronglyMeasurable (a p) volume)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ M)
    (s t : ℝ) (hst : s ≤ t) :
    (∑' p, fibreCoefficientWeight (R : ENNReal) p * ‖∫ τ in s..t, a p τ‖ₑ) ≤
      M * ENNReal.ofReal (t - s) := by
  simp_rw [intervalIntegral.integral_of_le hst]
  have h := integral_coefficient_majorant (volume.restrict (Ioc s t)) a
    (fibreCoefficientWeight (R : ENNReal)) M
    (fun p => (ha p).mono_measure Measure.restrict_le_self)
    (fun τ => (ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl
      (le_iSup (fun u => ‖a p u‖ₑ) τ))).trans hb)
  simpa only [Measure.restrict_apply_univ, Real.volume_Ioc] using h

end AVRegularity.CycleEvolution
end

section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniform scalar coefficient budgets give analytic L-infinity-valued symbol families. -/

theorem fibreLpTopSeries_weighted_summable (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (hm : ∀ p, MemLp (a p) ⊤ volume) :
    Summable (fun p => ‖(hm p).toLp (a p)‖ * (R : ℝ) ^ (p.1 + p.2)) := by
  have hbudget : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ‖(hm p).toLp (a p)‖ₑ) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl
      (lpTopClass_enorm_le_iSup volume (a p) (hm p)))).trans_lt ha
  exact fibreUniformMajorant_weighted_summable
    (fun p (_ : ℝ) => (hm p).toLp (a p)) R
    (by simpa only [iSup_const] using hbudget) 0

theorem fibreLpTopSeries_analyticOnNhd (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (hm : ∀ p, MemLp (a p) ⊤ volume) :
    AnalyticOnNhd ℂ (fun ξ : Fin 2 → ℂ => ∑' p, fibreMonomial ξ p • (hm p).toLp (a p))
      (Metric.ball 0 (R : ℝ)) :=
  fibreBivariateSum_analyticOnNhd (fun p => (hm p).toLp (a p)) R hR
    (fibreLpTopSeries_weighted_summable a R ha hm)

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Scalar series with a vanishing initial jet gain the corresponding frequency order. -/

theorem fibreScalarSeries_order_enorm_le (a : ℕ × ℕ → ℝ → ℂ) (R K : ℝ)
    (hR : 0 < R) (m : ℕ) (hz : ∀ p, p.1 + p.2 < m → ∀ t, a p t = 0)
    (ha : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, ‖a p s‖ₑ) ≤
      ENNReal.ofReal K) (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ R) (t : ℝ) :
    ‖fibreSeriesC a ξ t‖ₑ ≤ ENNReal.ofReal ((fibreNorm ξ / R) ^ m) * ENNReal.ofReal K := by
  have hzero : ∀ p, p.1 + p.2 < m → (⨆ s, ‖a p s‖ₑ) = 0 := by
    intro p hp
    simp only [hz p hp, enorm_zero, iSup_const]
  have hg := fibreCoefficient_weighted_order_radius_gain (fibreNorm_nonneg ξ) hR hξ m
    (fun p => ⨆ s, ‖a p s‖ₑ) hzero
  exact (enorm_tsum_le_tsum_enorm (f := fun p => fibreMonomial ξ p * a p t)).trans
    ((fibreScalarSeries_enorm_sum_le a (fibreNorm ξ) ξ le_rfl t).trans
      (hg.trans (mul_le_mul' le_rfl ha)))

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal triangular Taylor forcing of the nonlinear fibre graph equation. -/

/-- One coordinate contribution to the scalar constant and linear Taylor forcing. -/
def fibreCoefficientLinearTerm (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (j : Fin 2) : ℝ → Vec 2 → ℂ :=
  fun t x => -Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
    ((if p = cellJetDirection j then 1 else 0) + cellValue D t x)

/-- The constant and linear drift terms of a Taylor coefficient before projection. -/
def fibreCoefficientLinearSource (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) : ℝ → Vec 2 → ℂ :=
  fun t x => ∑ j ∈ fibreCoefficientDirections p,
    fibreCoefficientLinearTerm η v (D (fibreCoefficientPrevious p j)) p j t x

/-- One coordinate contribution of two lower states to the quadratic Taylor forcing. -/
def fibreCoefficientQuadraticTerm (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D E : ℝ → RawJet2 1 ℂ) (j : Fin 2) : ℝ → Vec 2 → ℂ :=
  fun t x => Complex.I * cellValue D t x *
    cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue E t y)

/-- The literal coefficient of the quadratic mean multiplier before projection. -/
def fibreCoefficientQuadraticSource (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) : ℝ → Vec 2 → ℂ :=
  fun t x => ∑ j ∈ fibreCoefficientDirections p,
    ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
      fibreCoefficientQuadraticTerm η v (D a)
        (D (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) j t x

/-- The complete literal scalar Taylor forcing before mean-free projection. -/
def fibreCoefficientSource (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) : ℝ → Vec 2 → ℂ :=
  fibreCoefficientLinearSource η v D p + fibreCoefficientQuadraticSource η v D p

/-- The complete literal vector Taylor forcing. -/
def fibreCoefficientFlux (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun t x => ∑ j ∈ fibreCoefficientDirections p,
    fibreGraphFlux η G (fibreCoordinateFrequency j)
      (cellValue (D (fibreCoefficientPrevious p j))) t x

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! The analytic integrated coefficient sum equals the literal phase integral. -/

theorem fibreUniformMajorant_integral_series (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (M : ENNReal) (hM : M < ⊤) (ha : ∀ p, AEStronglyMeasurable (a p) volume)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ M)
    (s t : ℝ) (hst : s ≤ t) (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) :
    (∫ τ in s..t, fibreSeriesC a ξ τ) =
      ∑' p, fibreMonomial ξ p * ∫ τ in s..t, a p τ := by
  let μ := volume.restrict (Ioc s t)
  let f : (ℕ × ℕ) → ℝ → ℂ := fun p τ => fibreMonomial ξ p * a p τ
  have hf p : AEStronglyMeasurable (f p) μ :=
    aestronglyMeasurable_const.mul ((ha p).mono_measure Measure.restrict_le_self)
  have hmon p : ENNReal.ofReal ‖fibreMonomial ξ p‖ ≤ fibreCoefficientWeight (R : ENNReal) p := by
    rw [fibreCoefficientWeight, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow R.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    exact (fibreMonomial_norm_le_pi ξ p).trans (pow_le_pow_left₀ (norm_nonneg _) hξ _)
  have hpoint τ : (∑' p, ‖f p τ‖ₑ) ≤ M := by
    have hterm p : ‖f p τ‖ₑ ≤
        fibreCoefficientWeight (R : ENNReal) p * ⨆ u, ‖a p u‖ₑ := by
      change ‖fibreMonomial ξ p * a p τ‖ₑ ≤ _
      rw [enorm_mul, ← ofReal_norm (fibreMonomial ξ p)]
      exact mul_le_mul' (hmon p) (le_iSup (fun u => ‖a p u‖ₑ) τ)
    exact (ENNReal.tsum_le_tsum hterm).trans hb
  have hfinite : (∑' p, ∫⁻ τ, ‖f p τ‖ₑ ∂μ) < ⊤ := by
    rw [← lintegral_tsum (fun p => (hf p).enorm)]
    apply (lintegral_mono hpoint).trans_lt
    rw [lintegral_const]
    apply ENNReal.mul_lt_top hM
    simp only [μ, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  simp_rw [intervalIntegral.integral_of_le hst]
  change (∫ τ, ∑' p, f p τ ∂μ) = _
  rw [integral_tsum hf hfinite.ne]
  apply tsum_congr
  intro p
  exact integral_const_mul (fibreMonomial ξ p) (a p)

theorem fibreUniformMajorant_phase_hasFPowerSeriesOnBall (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (hR : 0 < R) (M : ENNReal) (hM : M < ⊤)
    (ha : ∀ p, AEStronglyMeasurable (a p) volume)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ M)
    (s t : ℝ) (hst : s ≤ t) :
    HasFPowerSeriesOnBall (fun ξ => ∫ τ in s..t, fibreSeriesC a ξ τ)
      (fibreFormalSeries (fun p => ∫ τ in s..t, a p τ)) 0 (R : ENNReal) := by
  have hfinite := (fibreUniformMajorant_integrated_le a R M ha hb s t hst).trans_lt
    (ENNReal.mul_lt_top hM ENNReal.ofReal_lt_top)
  have hs := fibreUniformMajorant_weighted_summable
    (fun p (_ : ℝ) => ∫ τ in s..t, a p τ) R
    (by simpa only [iSup_const] using hfinite) 0
  apply (fibreBivariateSum_hasFPowerSeriesOnBall (fun p => ∫ τ in s..t, a p τ) R hR hs).congr
  intro ξ hξ
  rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hξ
  simpa only [smul_eq_mul] using
    (fibreUniformMajorant_integral_series a R M hM ha hb s t hst ξ hξ.le).symm

theorem fibreUniformMajorant_phase_analyticOnNhd (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (hR : 0 < R) (M : ENNReal) (hM : M < ⊤)
    (ha : ∀ p, AEStronglyMeasurable (a p) volume)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ M)
    (s t : ℝ) (hst : s ≤ t) :
    AnalyticOnNhd ℂ (fun ξ => ∫ τ in s..t, fibreSeriesC a ξ τ)
      (Metric.ball 0 (R : ℝ)) := by
  simpa only [Metric.eball_coe] using
    (fibreUniformMajorant_phase_hasFPowerSeriesOnBall a R hR M hM ha hb s t hst).analyticOnNhd

end AVRegularity.CycleEvolution
end

section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! The analytic L-infinity-valued symbol sum has the literal scalar series as its representative. -/

theorem fibreLpTopSeries_ae (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (hm : ∀ p, MemLp (a p) ⊤ volume) (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) :
    (⇑(∑' p, fibreMonomial ξ p • (hm p).toLp (a p)) : ℝ → ℂ) =ᵐ[volume]
      fibreSeriesC a ξ := by
  let c := fun p => (hm p).toLp (a p)
  let z := fun p => fibreMonomial ξ p • c p
  have hs := fibreLpTopSeries_weighted_summable a R ha hm
  have hnorm : Summable (fun p => ‖z p‖) := by
    apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro p
    change ‖fibreMonomial ξ p • c p‖ ≤ _
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      ((fibreMonomial_norm_le_pi ξ p).trans (pow_le_pow_left₀ (norm_nonneg _) hξ _))
      (norm_nonneg _)
  have hfinite : (∑' p, ‖z p‖ₑ) ≠ ⊤ := tsum_enorm_ne_top_iff_summable_norm.mpr hnorm
  have hall : ∀ᵐ t ∂volume, ∀ p, z p t = fibreMonomial ξ p * a p t := by
    apply ae_all_iff.mpr
    intro p
    filter_upwards [Lp.coeFn_smul (fibreMonomial ξ p) (c p), (hm p).coeFn_toLp] with t hz hc
    change (fibreMonomial ξ p • c p) t = _
    rw [hz]
    change fibreMonomial ξ p * c p t = _
    rw [hc]
  filter_upwards [Lp.coeFn_tsum hfinite, hall] with t ht hp
  exact ht.trans (tsum_congr (fun p => hp p))

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Actual convergent reciprocal series from the proved triangular coefficient equation. -/

theorem fibreScalarInverseCoefficient_series_mul (d : ℕ × ℕ → ℂ) (hd : d 0 = 0)
    (ξ : Fin 2 → ℂ)
    (hs : Summable (fun p => ‖fibreMonomial ξ p * d p‖))
    (hk : Summable (fun p => ‖fibreMonomial ξ p * fibreScalarInverseCoefficient d p‖)) :
    (1 + ∑' p, fibreMonomial ξ p * d p) *
      (∑' p, fibreMonomial ξ p * fibreScalarInverseCoefficient d p) = 1 := by
  let k := fibreScalarInverseCoefficient d
  let c := fun p => ∑ a ∈ fibreCoefficientPairs p, d a * k (fibreCoefficientComplement p a)
  have hc : Summable (fun p => fibreMonomial ξ p * c p) :=
    fibreMonomial_convolution_summable ξ d k hs hk
  have hprod := fibreMonomial_cauchy_product ξ d k hs hk
  have he (p : ℕ × ℕ) :
      fibreMonomial ξ p * k p + fibreMonomial ξ p * c p =
      fibreMonomial ξ p * (if p = 0 then 1 else 0) := by
    rw [← mul_add]
    exact congrArg (fun z => fibreMonomial ξ p * z) (fibreScalarInverseCoefficient_equation d hd p)
  have hz : (∑' p, fibreMonomial ξ p * (if p = 0 then (1 : ℂ) else 0)) = 1 := by
    simp [fibreMonomial]
  calc
    _ = (∑' p, fibreMonomial ξ p * k p) +
        (∑' p, fibreMonomial ξ p * d p) * ∑' p, fibreMonomial ξ p * k p := by ring
    _ = (∑' p, fibreMonomial ξ p * k p) + ∑' p, fibreMonomial ξ p * c p := by rw [hprod]
    _ = ∑' p, (fibreMonomial ξ p * k p + fibreMonomial ξ p * c p) :=
      (hk.of_norm.tsum_add hc).symm
    _ = ∑' p, fibreMonomial ξ p * (if p = 0 then 1 else 0) := tsum_congr he
    _ = 1 := hz

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal lower-order congruence for the triangular fibre coefficient forcing. -/

/-- The linear source depends only on strictly lower-order coefficients. -/
theorem fibreCoefficientLinearSource_congr_lower (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D E : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ)
    (he : ∀ a : ℕ × ℕ, a.1 + a.2 < p.1 + p.2 → D a = E a) :
    fibreCoefficientLinearSource η v D p = fibreCoefficientLinearSource η v E p := by
  funext t x
  unfold fibreCoefficientLinearSource
  apply Finset.sum_congr rfl
  intro j hj
  have ho := fibreCoefficientPrevious_order hj
  rw [he (fibreCoefficientPrevious p j) (by omega)]

/-- The quadratic source depends only on strictly lower-order coefficients. -/
theorem fibreCoefficientQuadraticSource_congr_lower (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D E : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ)
    (he : ∀ a : ℕ × ℕ, a.1 + a.2 < p.1 + p.2 → D a = E a) :
    fibreCoefficientQuadraticSource η v D p = fibreCoefficientQuadraticSource η v E p := by
  funext t x
  unfold fibreCoefficientQuadraticSource
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  have ho := fibreCoefficientPairs_lower_orders hj ha
  rw [he a ho.1, he (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) ho.2]

/-- The entire scalar source is triangular in the literal raw coefficients. -/
theorem fibreCoefficientSource_congr_lower (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D E : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ)
    (he : ∀ a : ℕ × ℕ, a.1 + a.2 < p.1 + p.2 → D a = E a) :
    fibreCoefficientSource η v D p = fibreCoefficientSource η v E p := by
  unfold fibreCoefficientSource
  rw [fibreCoefficientLinearSource_congr_lower η v D E p he,
    fibreCoefficientQuadraticSource_congr_lower η v D E p he]

/-- The entire vector source is triangular in the literal raw coefficients. -/
theorem fibreCoefficientFlux_congr_lower (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (D E : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ)
    (he : ∀ a : ℕ × ℕ, a.1 + a.2 < p.1 + p.2 → D a = E a) :
    fibreCoefficientFlux η G D p = fibreCoefficientFlux η G E p := by
  funext t x
  unfold fibreCoefficientFlux
  apply Finset.sum_congr rfl
  intro j hj
  have ho := fibreCoefficientPrevious_order hj
  rw [he (fibreCoefficientPrevious p j) (by omega)]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The zero-order fibre correction coefficient has exactly zero forcing. -/

/-- There is no frequency direction at order zero. -/
theorem fibreCoefficientDirections_zero : fibreCoefficientDirections 0 = ∅ := by
  ext j
  simp [fibreCoefficientDirections]

/-- The complete scalar forcing at order zero vanishes for every coefficient family. -/
theorem fibreCoefficientSource_zero (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) : fibreCoefficientSource η v D 0 = 0 := by
  funext t x
  simp [fibreCoefficientSource, fibreCoefficientLinearSource, fibreCoefficientQuadraticSource,
    fibreCoefficientDirections_zero]

/-- The complete vector forcing at order zero vanishes for every coefficient family. -/
theorem fibreCoefficientFlux_zero (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) : fibreCoefficientFlux η G D 0 = 0 := by
  funext t x
  simp [fibreCoefficientFlux, fibreCoefficientDirections_zero]

end AVRegularity.CycleEvolution
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Degenerate finite intervals retain arbitrary L² initial traces. -/

/-- On a singleton interval the constant L² trace and zero spatial slice satisfy every weak time equation. -/
theorem cellSingleton_weak_curve (a : ℝ) (initial : ComplexCellL2)
    (g : ℝ → TorusHk 1 ℂ) :
    CellWeakHilbertCurve a a (fun _ => initial) (fun _ => 0) g := by
  have hm : volume.restrict (Icc a a) = 0 := by simp
  refine ⟨continuousOn_const, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact memLp_measure_zero
  · rw [hm]
    exact memLp_measure_zero
  · rw [hm]
    simp
  · intro s hs t ht _ z
    have hs' : s = a := le_antisymm hs.2 hs.1
    have ht' : t = a := le_antisymm ht.2 ht.1
    subst s t
    simp

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Lower-order coefficient reality gives the actual scalar linear forcing reality. -/

theorem fibreCoefficientLinearTerm_reality (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (j : Fin 2)
    (hj : j ∈ fibreCoefficientDirections p) (t : ℝ)
    (hD : (fun x => star (cellValue D t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign (fibreCoefficientPrevious p j) * cellValue D t x)) :
    (fun x => star (fibreCoefficientLinearTerm η v D p j t x)) =ᵐ[
      volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * fibreCoefficientLinearTerm η v D p j t x) := by
  let δ : ℂ := if p = cellJetDirection j then 1 else 0
  have hs := fibreRealitySign_previous hj
  have hd : fibreRealitySign p * δ = -δ := by
    dsimp only [δ]
    split_ifs with he
    · rw [he, fibreRealitySign_direction]
      ring
    · ring
  have hδ : star δ = δ := by dsimp only [δ]; split_ifs <;> simp
  filter_upwards [hD] with x hx
  have hb : star (fibreDriftCoupling η v (fibreCoordinateFrequency j) t x) =
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t x := by
    rw [fibreCoordinateFrequency_coupling]
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  change star (-Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
    (δ + cellValue D t x)) = fibreRealitySign p *
    (-Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * (δ + cellValue D t x))
  rw [star_mul, star_mul, star_neg, show star Complex.I = -Complex.I from Complex.conj_I, hb,
    star_add, hδ, hx]
  rw [hs] at hd ⊢
  linear_combination (Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x) * hd

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Identification of the literal summed linear coefficient forcing. -/

/-- Pointwise convergence identifies the linear coefficient forcing with the actual graph multiplier. -/
theorem fibreCoefficientLinearSource_series (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2)
    (hs : Summable (fun p => fibreMonomial ξ p * cellValue (r p) t x)) :
    (∑' p, fibreMonomial ξ p * fibreCoefficientLinearSource η v r p t x) =
      -Complex.I * fibreDriftCoupling η v ξ t x *
        (1 + ∑' p, fibreMonomial ξ p * cellValue (r p) t x) := by
  have hh := fibreTaylor_affine_series ξ
    (fun j => -Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x)
    (fun p => cellValue (r p) t x) hs
  have hc : (∑ j : Fin 2,
      (-Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x) * ξ j) =
      -Complex.I * fibreDriftCoupling η v ξ t x := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, fibreDriftCoupling_coordinates]
  rw [hc] at hh
  exact hh

end AVRegularity.CycleEvolution
end
end
