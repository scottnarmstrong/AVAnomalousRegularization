-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.TimeEnergy
public import AVRegularity.CycleEvolution.CellSliceL2Integrability
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Fixed H1 cell tests and their bounded coefficient multipliers are product L2 fields. -/

/-- Every spatial H1 test component is product L2 on a finite time set. -/
theorem cellTest_component_product_memLp (I : Set ℝ) [IsFiniteMeasure (volume.restrict I)]
    (ψ : TorusHkFunction 1 ℂ) (a : JetIndex2 1) :
    MemLp (fun p : ℝ × Vec 2 => ψ.jet a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
  (ψ.hasPeriodicWeakJet.2.1 a).comp_snd (volume.restrict I)

/-- Metric coefficients times any H1 test component are product L2 on finite time sets. -/
theorem cellTest_metric_product_memLp (I : Set ℝ) [IsFiniteMeasure (volume.restrict I)]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (ψ : TorusHkFunction 1 ℂ) (a : JetIndex2 1) (j k : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 => (G p.1 p.2 j k : ℂ) * ψ.jet a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  have hm : Measurable (fun p : ℝ × Vec 2 => (G p.1 p.2 j k : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hG.1))
  apply cellL2_bounded_multiplier_memLp _ _ _ 2 hm.aestronglyMeasurable _
    (cellTest_component_product_memLp I ψ a)
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG p.1 p.2 j k)

/-- Bounded drift coefficients times any H1 test component are product L2 on finite time sets. -/
theorem cellTest_drift_product_memLp (I : Set ℝ) [IsFiniteMeasure (volume.restrict I)]
    (v : ℝ → Vec 2 → Vec 2) (hm : Measurable (Function.uncurry v))
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ψ : TorusHkFunction 1 ℂ) (a : JetIndex2 1) (j : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 => (v p.1 p.2 j : ℂ) * ψ.jet a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  have hv : Measurable (fun p : ℝ × Vec 2 => (v p.1 p.2 j : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp hm)
  apply cellL2_bounded_multiplier_memLp _ _ _ |V| hv.aestronglyMeasurable _
    (cellTest_component_product_memLp I ψ a)
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hb p.1 p.2 j)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleEvolution

/-! An unfrozen strong-time cell interface with almost-everywhere spatial H¹ slices.
This is a helper interface, not a replacement for the main predicates.
In particular its strong L² time derivative is more regular than an H⁻¹ derivative. -/

abbrev CellHilbert := Lp ℂ 2 (volume.restrict AVenhance.unitCube)

/-- Cell regularity with continuous L² traces at every time and genuine spatial jets
only almost everywhere in time. No spatial derivative is required at the initial trace. -/
structure CellStrongTimeH1 (a b : ℝ) (D : ℝ → RawJet2 1 ℂ)
    (u du : ℝ → CellHilbert) : Prop where
  time : StrongTimeRegularity a b u du
  derivative_L2 : MemLp du 2 (volume.restrict (uIcc a b))
  spatial : ∀ᵐ t ∂volume.restrict (uIcc a b), HasPeriodicOrderedWeakJet (D t)
  trace : ∀ t ∈ uIcc a b,
    cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] u t
  gradient_L2 : ∫⁻ t in uIcc a b, cellL2Norm (cellGradient (D t)) ^ 2 < ⊤

/-- The energy identity for the strong-time cell subclass follows from Hilbert calculus. -/
theorem CellStrongTimeH1.energy_increment {a b : ℝ} {D : ℝ → RawJet2 1 ℂ}
    {u du : ℝ → CellHilbert} (h : CellStrongTimeH1 a b D u du) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 =
      ∫ t in a..b, 2 * ∫ x in AVenhance.unitCube, inner ℝ (u t x) (du t x) := by
  rw [h.time.energy_increment]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [L2.inner_def]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Complex scalar bounds in the uniformly local cell norm. -/

/-- Complex scalar multiplication obeys the exact uniformly local operator bound. -/
theorem cellUlNorm_complex_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (I : Set ℝ) (r : ℂ)
    (f : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm I (r • f) ≤ ‖r‖ₑ * cellUlNorm I f := by
  apply iSup_le
  intro a
  have hm : (volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
      (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict I).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl
  have hf' := hf.mono_measure hm
  rw [cellUl_window_eq_product I (r • f) a (hf'.const_smul r)]
  change eLpNorm (r • Function.uncurry f) 2 _ ≤ _
  rw [eLpNorm_const_smul, ← cellUl_window_eq_product I f a hf']
  gcongr
  exact le_iSup (fun b : ℝ => (∫⁻ t in Set.Icc b (b + 1) ∩ I,
    cellL2Norm (f t) ^ 2) ^ (1 / 2 : ℝ)) a

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! A sharp square-root length loss when restricting uniformly local energy. -/

theorem cellUl_finite_interval_squared_le {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E) {a b : ℝ} (hab : a ≤ b) :
    (∫⁻ t in Set.Icc a b ∩ I, cellL2Norm (f t) ^ 2) ≤
      ENNReal.ofReal (b - a + 1) * cellUlNorm I f ^ 2 := by
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hceil : b ≤ a + (Nat.ceil (b - a) : ℝ) := by
    have h := Nat.le_ceil (b - a)
    linarith
  have hbound : (Nat.ceil (b - a) : ℝ) ≤ b - a + 1 := (Nat.ceil_lt_add_one hd).le
  calc
    _ ≤ ∫⁻ t in Set.Icc a (a + (Nat.ceil (b - a) : ℝ)) ∩ I, cellL2Norm (f t) ^ 2 :=
      lintegral_mono_set (Set.inter_subset_inter_left I (Set.Icc_subset_Icc le_rfl hceil))
    _ ≤ (Nat.ceil (b - a) : ℝ≥0∞) * cellUlNorm I f ^ 2 :=
      cellUl_integer_interval_sq_le I f a _
    _ ≤ ENNReal.ofReal (b - a + 1) * cellUlNorm I f ^ 2 := by
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hbound

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Actual product L² membership of uniformly local sources on bounded time intervals. -/

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Uniformly local source bounds give product L² membership on every bounded interval in the domain. -/
theorem cellUl_memLp_product_interval (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hm : Measurable (Function.uncurry f)) (hf : cellUlNorm I f < ⊤)
    (a b : ℝ) (hI : Icc a b ⊆ I) :
    MemLp (Function.uncurry f) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have he := cellUl_interval_integral_lt_top I f hf a b
  rw [inter_eq_left.mpr hI] at he
  exact cellSource_memLp_product (Icc a b) f hm he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.CycleEvolution

/-! Addition of norm-convergent uniformly local fields and finite sums. -/

/-- Jointly almost measurable source families preserve norm convergence under addition. -/
theorem cellUlNorm_add_tendsto {P E : Type*} [NormedAddCommGroup E]
    (l : Filter P) (f g : P → ℝ → Vec 2 → E) (f0 g0 : ℝ → Vec 2 → E)
    (hfm : ∀ p, AEStronglyMeasurable (Function.uncurry (f p))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hgm : ∀ p, AEStronglyMeasurable (Function.uncurry (g p))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf0m : AEStronglyMeasurable (Function.uncurry f0)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hg0m : AEStronglyMeasurable (Function.uncurry g0)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : Tendsto (fun p => cellUlNorm Set.univ (f p - f0)) l (𝓝 0))
    (hg : Tendsto (fun p => cellUlNorm Set.univ (g p - g0)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm Set.univ ((f p + g p) - (f0 + g0))) l (𝓝 0) := by
  have hb (p : P) : cellUlNorm Set.univ ((f p + g p) - (f0 + g0)) ≤
      cellUlNorm Set.univ (f p - f0) + cellUlNorm Set.univ (g p - g0) := by
    have he : f p + g p - (f0 + g0) = (f p - f0) + (g p - g0) := by abel
    rw [he]
    exact cellUlNorm_add Set.univ _ _ ((hfm p).sub hf0m) ((hgm p).sub hg0m)
  have hl : Tendsto (fun p => cellUlNorm Set.univ (f p - f0) +
      cellUlNorm Set.univ (g p - g0)) l (𝓝 0) := by
    simpa only [zero_add] using hf.add hg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le) hb

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Abstract scalar identities for the literal sqrt-contrast Bloch shift. -/

theorem fibreBloch_metric_quadratic (η : ℝ) (hη : 0 ≤ η)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ) :
    (∑ j : Fin 2, ∑ k : Fin 2, (G j k : ℂ) * ((Real.sqrt η : ℂ) * ξ j) *
      ((Real.sqrt η : ℂ) * ξ k)) = (η : ℂ) * fibreQuad G ξ := by
  have hs : (Real.sqrt η : ℂ) ^ 2 = (η : ℂ) := by exact_mod_cast Real.sq_sqrt hη
  calc
    _ = (Real.sqrt η : ℂ) ^ 2 * fibreQuad G ξ := by
      simp only [fibreQuad, Fin.sum_univ_two]
      ring
    _ = _ := by rw [hs]

theorem fibreBloch_drift_coupling (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2) :
    (∑ j : Fin 2, ((Real.sqrt η : ℂ) * ξ j) * (v t x j : ℂ)) =
      fibreDriftCoupling η v ξ t x := by
  simp only [fibreDriftCoupling, Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! The finite-rectangle coefficient convolution has an actual sum, not merely a formal tsum value. -/

/-- Absolute input summability proves actual convergence of the literal two-variable Cauchy coefficients. -/
theorem fibreCoefficient_convolution_hasSum (f g : ℕ × ℕ → ℂ)
    (hf : Summable (fun p => ‖f p‖)) (hg : Summable (fun p => ‖g p‖)) :
    HasSum (fun p => ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a))
      ((∑' p, f p) * ∑' p, g p) := by
  let H := fun q : (ℕ × ℕ) × (ℕ × ℕ) => f q.1 * g q.2
  have hH : Summable H := summable_mul_of_summable_norm hf hg
  have hsum := hH.hasSum.tsum_fiberwise (fun q => q.1 + q.2)
  have he (p : ℕ × ℕ) :
      (∑' q : {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p}, H q.1) =
        ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a) := by
    rw [← (fibreCoefficientConvolutionFibreEquiv p).symm.tsum_eq (fun q => H q.1)]
    simp only [H, fibreCoefficientConvolutionFibreEquiv_symm_fst,
      fibreCoefficientConvolutionFibreEquiv_symm_snd]
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun a => f a * g (fibreCoefficientComplement p a)) (fibreCoefficientPairs p)
  rw [← tsum_mul_tsum_of_summable_norm hf hg] at hsum
  exact hsum.congr_fun (fun p => (he p).symm)

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Exact nonnegative weighted totals for the literal two-variable coefficient convolution. -/

theorem fibreCoefficient_convolution_total (f g : ℕ × ℕ → ℝ≥0∞) :
    (∑' p, ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a)) =
      (∑' p, f p) * ∑' p, g p := by
  let H := fun q : (ℕ × ℕ) × (ℕ × ℕ) => f q.1 * g q.2
  have he (p : ℕ × ℕ) :
      (∑' q : {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p}, H q.1) =
        ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a) := by
    rw [← (fibreCoefficientConvolutionFibreEquiv p).symm.tsum_eq (fun q => H q.1)]
    simp only [H, fibreCoefficientConvolutionFibreEquiv_symm_fst,
      fibreCoefficientConvolutionFibreEquiv_symm_snd]
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun a => f a * g (fibreCoefficientComplement p a))
      (fibreCoefficientPairs p)
  calc
    _ = ∑' p, ∑' q : {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p}, H q.1 :=
      tsum_congr (fun p => (he p).symm)
    _ = ∑' q, H q := ENNReal.tsum_fiberwise _ _
    _ = (∑' p, f p) * ∑' p, g p := by
      dsimp only [H]
      rw [ENNReal.tsum_prod']
      simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

theorem fibreCoefficient_weighted_convolution_total (ρ : ℝ≥0∞)
    (f g : ℕ × ℕ → ℝ≥0∞) :
    (∑' p, fibreCoefficientWeight ρ p *
      ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a)) =
      (∑' p, fibreCoefficientWeight ρ p * f p) *
        ∑' p, fibreCoefficientWeight ρ p * g p := by
  rw [← fibreCoefficient_convolution_total]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [fibreCoefficientWeight_convolution ρ ha]
  ring

/-! Finite uniform norms of the actual reciprocal coefficients follow by triangular induction. -/

theorem fibreScalarInverseCoefficient_uniform_lt_top (d : ℕ × ℕ → ℝ → ℂ)
    (hd : ∀ p, (⨆ t, ‖d p t‖ₑ) < ⊤) (p : ℕ × ℕ) :
    (⨆ t, ‖fibreScalarInverseCoefficient (fun a => d a t) p‖ₑ) < ⊤ := by
  classical
  have hn : ∀ n, ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      (⨆ t, ‖fibreScalarInverseCoefficient (fun a => d a t) p‖ₑ) < ⊤ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      apply (fibreScalarInverseCoefficient_uniform_recurrence d p).trans_lt
      by_cases hp0 : p = 0
      · simp [hp0]
      · rw [ite_eq_right hp0]
        apply ENNReal.sum_lt_top.mpr
        intro a ha
        have hmem := Finset.mem_filter.mp ha
        have horder := fibreCoefficientComplement_order_lt hmem.1 hmem.2
        apply ENNReal.mul_lt_top (hd a)
        exact ih _ (horder.trans_eq hp) _ rfl
  exact hn _ p rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Restricting the observation interval decreases the literal fibre X norm. -/

theorem fibreXNorm_mono {I J : Set ℝ} (hIJ : I ⊆ J)
    (θ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ) : fibreXNorm θ I D ≤ fibreXNorm θ J D := by
  unfold fibreXNorm
  apply add_le_add
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact le_iSup_of_le t (le_iSup_of_le (hIJ ht) le_rfl)
  · exact ENNReal.rpow_le_rpow (lintegral_mono_set hIJ) (by norm_num : (0 : ℝ) ≤ 1 / 2)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Pointwise trace bounds already contained in the literal cell energy seminorm. -/

/-- Every time trace is bounded by the all-time literal energy norm. -/
theorem cellValue_cellL2Norm_le_energy (D : ℝ → RawJet2 1 ℂ) (t : ℝ) :
    cellL2Norm (cellValue D t) ≤ cellEnergyNorm Set.univ D := by
  have hv : cellL2Norm (cellValue D t) ≤
      ⨆ s ∈ (Set.univ : Set ℝ), cellL2Norm (cellValue D s) :=
    le_iSup_of_le t (le_iSup_of_le (Set.mem_univ t) le_rfl)
  exact hv.trans (le_add_right (le_refl _))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute L1 summability controls the series of actual integrals. -/

/-- The integral sequence of an absolutely L1-summable family is summable. -/
theorem cellL1Series_integrals_summable {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f : J → X → ℂ) (hs : (∑' j, eLpNorm (f j) 1 μ) < ⊤) :
    Summable (fun j => ∫ x, f j x ∂μ) := by
  have hf j : MemLp (f j) 1 μ := (ENNReal.le_tsum j).trans_lt hs
  have hb j : ‖∫ x, f j x ∂μ‖ₑ ≤ eLpNorm (f j) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf j).aestronglyMeasurable]
    exact enorm_integral_le_lintegral_enorm _
  exact Summable.of_enorm ((ENNReal.tsum_le_tsum hb).trans_lt hs).ne

end AVRegularity.CycleEvolution
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Pairing two literal absolutely L2-convergent cell series term by term. -/

theorem cellMean_tsum_mul_tsum {J K : Type*} [Countable J] [Countable K]
    (f : J → Vec 2 → ℂ) (g : K → Vec 2 → ℂ)
    (hf : (∑' j, cellL2Norm (f j)) < ⊤) (hg : (∑' k, cellL2Norm (g k)) < ⊤) :
    cellMean (fun x => (∑' j, f j x) * ∑' k, g k x) =
      ∑' j, ∑' k, cellMean (fun x => f j x * g k x) := by
  have hgm := (cellL2Series_memLp_bound g hg).1
  have ho := cellMean_product_tsum (fun x => ∑' k, g k x) hgm f hf
  have ho' : cellMean (fun x => (∑' j, f j x) * ∑' k, g k x) =
      ∑' j, cellMean (fun x => f j x * ∑' k, g k x) := by
    simpa only [mul_comm] using ho
  apply ho'.trans
  apply tsum_congr
  intro j
  have hj : MemLp (f j) 2 (volume.restrict AVenhance.unitCube) :=
    (ENNReal.le_tsum j).trans_lt hf
  exact cellMean_product_tsum (f j) hj g hg

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Polarization turns the literal near-identity quadratic bound into entrywise bounds. -/

theorem cellMetric_near_identity_entry_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {g : ℝ} (hg : IsMetricNearIdentity G g) (t : ℝ) (z : Vec 2) (i j : Fin 2) :
    |(G t z - 1) i j| ≤ g := by
  have h0 := hg t z ![1, 0]
  have h1 := hg t z ![0, 1]
  have hp := hg t z ![1, 1]
  have hm := hg t z ![1, -1]
  have hs : G t z 1 0 = G t z 0 1 := (hG.2.2.1 t z).apply 0 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, zero_pow (by decide : 2 ≠ 0), one_mul, zero_mul, mul_one,
    mul_zero, add_zero, zero_add] at h0 h1 hp hm
  have h00 : |G t z 0 0 - 1| ≤ g := by simpa using h0
  have h11 : |G t z 1 1 - 1| ≤ g := by simpa using h1
  simp only [Matrix.sub_apply, Matrix.one_apply, Fin.isValue, ↓reduceIte, hs] at hp hm
  norm_num at hp hm
  have h01 : |G t z 0 1| ≤ g := abs_le.mpr ⟨by
    have hpl := (abs_le.mp hp).1
    have hmu := (abs_le.mp hm).2
    linarith, by
    have hpu := (abs_le.mp hp).2
    have hml := (abs_le.mp hm).1
    linarith⟩
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using h01
  · simpa [hs] using h01
  · simpa using h11

/-! A universal pointwise energy-production inequality for the exact complex cell equation. -/

/-- Real energy production at a point, testing the bilinear weak equation against conjugate u. -/
def cellPointwiseProduction (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ)
    (θ : Fin 2 → ℂ) (κ src u : ℂ) (F p : Fin 2 → ℂ) : ℝ :=
  -cellMetricPairing A (p + cellBlochShift θ u)
    (p + cellBlochShift (fun i => star (θ i)) u)
  - cellDriftPairing v (p + cellBlochShift θ u) u
  + (κ * u * star u).re + (src * star u).re
  - cellFluxPairing F (p + cellBlochShift (fun i => star (θ i)) u)

/-- Explicit universal constants control the energy production and retain gradient coercivity. -/
theorem cellPointwiseProduction_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (x : Vec 2) (v : Fin 2 → ℝ) (θ : Fin 2 → ℂ)
    (κ src u : ℂ) (F p : Fin 2 → ℂ) (V k : ℝ)
    (hv : ∀ j, |v j| ≤ |V|) (hκ : ‖κ‖ ≤ k) :
    2 * cellPointwiseProduction (G t x) v θ κ src u F p +
      (1 / 2) * ∑ j, ‖p j‖ ^ 2 ≤
      300 * (1 + ∑ j, ‖θ j‖ ^ 2 + V ^ 2 + k) * ‖u‖ ^ 2 +
        ‖src‖ ^ 2 + 9 * ∑ j, ‖F j‖ ^ 2 := by
  have hdiff := cellDiffusion_pointwise_garding hG t x θ p u
  have hdp := cellDriftPairing_young v p u V hv
  have hdb := cellDriftPairing_bloch v θ u V hv
  have hpot := cellPotential_re_le κ u k hκ
  have hsrc := cellScalarSource_young src u
  have hfp := cellFluxPairing_young F p
  have hfb := cellFluxPairing_bloch F (fun i => star (θ i)) u
  simp only [norm_star] at hfb
  have hdn := neg_le_abs (cellDriftPairing v p u)
  have hdan := neg_le_abs (cellDriftPairing v (cellBlochShift θ u) u)
  have hfn := neg_le_abs (cellFluxPairing F p)
  have hfan := neg_le_abs (cellFluxPairing F (cellBlochShift (fun i => star (θ i)) u))
  have hk : 0 ≤ k := (norm_nonneg κ).trans hκ
  have hθ : 0 ≤ ∑ j : Fin 2, ‖θ j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoef : (266 * (∑ j : Fin 2, ‖θ j‖ ^ 2) + 18 * V ^ 2 + 2 * k + 1) * ‖u‖ ^ 2 ≤
      300 * (1 + ∑ j : Fin 2, ‖θ j‖ ^ 2 + V ^ 2 + k) * ‖u‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [sq_nonneg V]
  simp only [cellPointwiseProduction, cellDriftPairing_add, cellFluxPairing_add]
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! A small three-source triangle estimate for complex scalar graph forcing. -/

/-- The three-source decomposition retains the sum of its actual uniformly local bounds. -/
theorem cellUlNorm_add_two_I_smul_le (I : Set ℝ) (p q r : ℝ → Vec 2 → ℂ)
    (hp : AEStronglyMeasurable (Function.uncurry p)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hq : AEStronglyMeasurable (Function.uncurry q)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hr : AEStronglyMeasurable (Function.uncurry r)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm I ((p + Complex.I • q) + Complex.I • r) ≤
      (cellUlNorm I p + cellUlNorm I q) + cellUlNorm I r := by
  have hqm : AEStronglyMeasurable (Function.uncurry (Complex.I • q))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
    aestronglyMeasurable_const.mul hq
  have hrm : AEStronglyMeasurable (Function.uncurry (Complex.I • r))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
    aestronglyMeasurable_const.mul hr
  have hi : ‖Complex.I‖ₑ = 1 := by simp [enorm_eq_nnnorm]
  have hqb := cellUlNorm_complex_smul I Complex.I q hq
  have hrb := cellUlNorm_complex_smul I Complex.I r hr
  rw [hi, one_mul] at hqb hrb
  calc
    _ ≤ cellUlNorm I (p + Complex.I • q) + cellUlNorm I (Complex.I • r) :=
      cellUlNorm_add I (p + Complex.I • q) (Complex.I • r) (hp.add hqm) hrm
    _ ≤ (cellUlNorm I p + cellUlNorm I (Complex.I • q)) +
        cellUlNorm I (Complex.I • r) :=
      add_le_add (cellUlNorm_add I p (Complex.I • q) hp hqm) le_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl hqb) hrb

end AVRegularity.CycleEvolution
end

section
open Homogenization
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Contrast-uniform vector source estimates for the literal fibre graph flux. -/

/-- The frequency finite-array Hilbert norm agrees with the literal fibre norm. -/
theorem fibreNorm_eq_piLp_norm (ξ : Fin 2 → ℂ) :
    fibreNorm ξ = ‖WithLp.toLp 2 ξ‖ := by
  have hf : fibreNorm ξ ^ 2 = ∑ i, ‖ξ i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖ξ i‖))
  have hp := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℂ) (WithLp.toLp 2 ξ)
  nlinarith [fibreNorm_nonneg ξ, norm_nonneg (WithLp.toLp 2 ξ)]

/-- The literal graph flux is scalar multiplication of the metric action on the frequency. -/
theorem fibreGraphFlux_eq_metricVector (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ)
    (r : ℝ → Vec 2 → ℂ) (t : ℝ) (x : Vec 2) :
    fibreGraphFlux η G ξ r t x =
      (2 * Complex.I * (Real.sqrt η : ℂ) * r t x) •
        cellMetricFluxVector (G t) (WithLp.toLp 2 ξ) := by
  apply PiLp.ext
  intro k
  simp only [fibreGraphFlux, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
    cellMetricFluxVector]
  ring

/-- The fibre graph vector source has size controlled independently of the contrast. -/
theorem fibreGraphFlux_norm_le (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ t i j, |G t i j| ≤ 2)
    (ξ : Fin 2 → ℂ) (r : ℝ → Vec 2 → ℂ) (t : ℝ) (x : Vec 2) :
    ‖fibreGraphFlux η G ξ r t x‖ ≤ 8 * fibreNorm ξ * ‖r t x‖ := by
  rw [fibreGraphFlux_eq_metricVector, norm_smul]
  have hroot : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη
  have hscalar : ‖2 * Complex.I * (Real.sqrt η : ℂ) * r t x‖ ≤ 2 * ‖r t x‖ := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg η)]
    norm_num
    gcongr
    linarith
  have hvec : ‖cellMetricFluxVector (G t) (WithLp.toLp 2 ξ)‖ ≤ 2 * 2 * fibreNorm ξ := by
    rw [fibreNorm_eq_piLp_norm]
    exact cellMetricFluxVector_norm_le (G t) 2 (by norm_num) (hG t) (WithLp.toLp 2 ξ)
  calc
    _ ≤ (2 * ‖r t x‖) * (2 * 2 * fibreNorm ξ) := by gcongr
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Joint measurability of literal countable raw cell series. -/

/-- Literal complex series of jointly measurable raw jets remain jointly measurable. -/
theorem cellJetSeries_aestronglyMeasurable {J : Type*} [Countable J]
    (I : Set ℝ) (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D j p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) (a : JetIndex2 1) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => ∑' j, D j p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  exact (AEMeasurable.tsum (fun j => (hD j a).aemeasurable)).aestronglyMeasurable

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Restricting raw energy solutions preserves every clause of the public solution predicate. -/

/-- A cell solution restricts to any interval contained in its original time domain. -/
theorem cellSolution_restrict {I J : Set ℝ} (hJI : J ⊆ I) (hJ : J.OrdConnected)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution I C src F D) : IsCellSolution J C src F D := by
  have hm : volume.restrict J ≤ volume.restrict I := Measure.restrict_mono hJI le_rfl
  refine ⟨hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ae_mono hm h.2.1
  · intro t ht
    exact h.2.2.1 t (hJI ht)
  · intro a
    exact (h.2.2.2.1 a).mono_measure (Measure.prod_mono hm le_rfl)
  · intro t ht
    exact (h.2.2.2.2.1 t (hJI ht)).mono_left (nhdsWithin_mono t hJI)
  · intro a ha b hb
    exact h.2.2.2.2.2.1 a (hJI ha) b (hJI hb)
  · intro s hs t ht hst ψ
    exact h.2.2.2.2.2.2 s (hJI hs) t (hJI ht) hst ψ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Uniformly local almost measurable forcing is genuinely L² on finite intervals. -/

/-- The measurable-representative construction extends finite-window membership to almost measurable fields. -/
theorem cellUl_memLp_product_interval_ae {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm I f < ⊤) (a b : ℝ) (hI : Icc a b ⊆ I) :
    MemLp (Function.uncurry f) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  obtain ⟨g, hgm, he, hn⟩ := cellUl_measurable_representative I f hm
  have hg := cellUl_memLp_product_interval I g hgm (hn ▸ hf) a b hI
  have hm' : (volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict I).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono hI le_rfl) le_rfl
  have he' : Function.uncurry f =ᵐ[(volume.restrict (Icc a b)).prod
      (volume.restrict AVenhance.unitCube)] Function.uncurry g := ae_mono hm' he
  exact hg.ae_eq he'.symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Summable joint L2 series have summable spatial L2 norms at almost every time. -/

/-- Fubini and unit-window Cauchy--Schwarz give summable literal spatial L2 norms. -/
theorem cellSliceL2Series_ae {J E : Type*} [Countable J] [NormedAddCommGroup E]
    (f : J → ℝ → Vec 2 → E) (a : ℝ)
    (hf : ∀ j, AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict (Set.Icc a (a + 1))).prod
        (volume.restrict AVenhance.unitCube)))
    (hs : (∑' j, eLpNorm (Function.uncurry (f j)) 2
      ((volume.restrict (Set.Icc a (a + 1))).prod
        (volume.restrict AVenhance.unitCube))) < ⊤) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a (a + 1)),
      (∑' j, cellL2Norm (f j t)) < ⊤ := by
  have hm := fun j => cellSliceL2Norm_aemeasurable (Set.Icc a (a + 1)) (f j) (hf j)
  apply ae_lt_top' (AEMeasurable.tsum hm)
  have hb : (∫⁻ t in Set.Icc a (a + 1), ∑' j, cellL2Norm (f j t)) < ⊤ := by
    rw [lintegral_tsum hm]
    exact (ENNReal.tsum_le_tsum (fun j =>
      cellSliceL2Norm_lintegral_le_product (f j) a (hf j))).trans_lt hs
  exact hb.ne

/-- Bounds on the countable unit-window cover give all-time almost-everywhere slice summability. -/
theorem cellSliceL2Series_allTime_ae {J E : Type*} [Countable J] [NormedAddCommGroup E]
    (f : J → ℝ → Vec 2 → E)
    (hf : ∀ (n : ℤ) j, AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict (Set.Icc (n : ℝ) ((n : ℝ) + 1))).prod
        (volume.restrict AVenhance.unitCube)))
    (hs : ∀ n : ℤ, (∑' j, eLpNorm (Function.uncurry (f j)) 2
      ((volume.restrict (Set.Icc (n : ℝ) ((n : ℝ) + 1))).prod
        (volume.restrict AVenhance.unitCube))) < ⊤) :
    ∀ᵐ t ∂volume, (∑' j, cellL2Norm (f j t)) < ⊤ := by
  exact cellTime_ae_of_integer_windows _ (fun n => cellSliceL2Series_ae f n (hf n) (hs n))

/-! A quantitative product L2 bound on arbitrary finite time intervals. -/

/-- Covering a finite interval by `n` unit windows gives a uniform product L2 operator bound. -/
theorem cellUl_interval_eLpNorm_le {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (a b : ℝ) (n : ℕ) (hn : b ≤ a + n) :
    eLpNorm (Function.uncurry f) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)) ≤
      (n : ℝ≥0∞) * cellUlNorm Set.univ f := by
  have hm : (volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono (Set.subset_univ _) le_rfl) le_rfl
  have hcover : Set.Icc a b ⊆ Set.Icc a (a + n) := Set.Icc_subset_Icc le_rfl hn
  have hsq : eLpNorm (Function.uncurry f) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)) ^ 2 ≤
      ((n : ℝ≥0∞) * cellUlNorm Set.univ f) ^ 2 := by
    rw [cellProduct_eLpNorm_sq _ _ (hf.mono_measure hm)]
    have hh := cellUl_integer_interval_sq_le Set.univ f a n
    simp only [Set.inter_univ] at hh
    calc
      _ ≤ ∫⁻ τ in Set.Icc a (a + n), cellL2Norm (f τ) ^ 2 := lintegral_mono_set hcover
      _ ≤ (n : ℝ≥0∞) * cellUlNorm Set.univ f ^ 2 := hh
      _ ≤ (n : ℝ≥0∞) ^ 2 * cellUlNorm Set.univ f ^ 2 := by
        apply mul_le_mul' _ le_rfl
        have hn2 : n ≤ n ^ 2 := by simpa only [pow_two] using Nat.le_mul_self n
        exact_mod_cast hn2
      _ = _ := (mul_pow _ _ _).symm
  have hb := ennreal_half_power_le_of_sq_le hsq
  simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (2 : ℕ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one] using hb

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Exact coordinate frequency shifts of literal coefficient series. -/

/-- Active predecessor summation is exactly ordinary index summation after a coordinate shift. -/
theorem fibreCoefficient_shift_tsum {E : Type*} [NormedAddCommGroup E]
    (j : Fin 2) (f : ℕ × ℕ → E) :
    (∑' p, if j ∈ fibreCoefficientDirections p then f (fibreCoefficientPrevious p j) else 0) = ∑' p, f p := by
  let g := fun p : ℕ × ℕ => p + cellJetDirection j
  let a := fun p => if j ∈ fibreCoefficientDirections p then f (fibreCoefficientPrevious p j) else 0
  have hr : Function.support a ⊆ Set.range g := by
    intro p hp
    have hj : j ∈ fibreCoefficientDirections p := by
      by_contra hh
      exact hp (by simp only [a, ite_eq_right hh])
    exact ⟨fibreCoefficientPrevious p j, fibreCoefficientPrevious_recover hj⟩
  have he := (fibreCoefficient_add_direction_injective j).tsum_eq hr
  have hfg p : a (g p) = f p := by
    simp only [a, g, ite_eq_left (fibreCoefficientDirections_add p j), fibreCoefficientPrevious_add]
  exact he.symm.trans (tsum_congr hfg)

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Weighted coefficient bounds imply absolute summability of literal monomials. -/

/-- Every literal monomial is controlled by its geometric weight within the radius. -/
theorem fibreMonomial_weight_le (R : ℝ) (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ R)
    (p : ℕ × ℕ) :
    ENNReal.ofReal ‖fibreMonomial ξ p‖ ≤ fibreCoefficientWeight (ENNReal.ofReal R) p := by
  have hR : 0 ≤ R := (fibreNorm_nonneg ξ).trans hξ
  calc
    _ ≤ ENNReal.ofReal (fibreNorm ξ ^ (p.1 + p.2)) :=
      ENNReal.ofReal_le_ofReal (fibreMonomial_norm_le ξ p)
    _ ≤ ENNReal.ofReal (R ^ (p.1 + p.2)) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξ _)
    _ = _ := by rw [ENNReal.ofReal_pow hR]; rfl

/-- The actual monomial energy sum is bounded by the total weighted coefficient energy. -/
theorem fibreMonomial_weighted_energy_le (R : ℝ) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ R) (E : ℕ × ℕ → ℝ≥0∞) :
    (∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * E p) ≤
      ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p := by
  exact ENNReal.tsum_le_tsum (fun p => mul_le_mul' (fibreMonomial_weight_le R ξ hξ p) le_rfl)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute uniformly local series remain absolutely L2 summable on every finite interval. -/

/-- Summable uniformly local L2 norms imply summable product L2 norms on each finite interval. -/
theorem cellUlSeries_interval_eLpNorm_tsum_lt_top {J E : Type*} [Countable J]
    [NormedAddCommGroup E]
    (f : J → ℝ → Vec 2 → E)
    (hf : ∀ j, AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hs : (∑' j, cellUlNorm Set.univ (f j)) < ⊤) (a b : ℝ) :
    (∑' j, eLpNorm (Function.uncurry (f j)) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (b - a)
  have hb : b ≤ a + n := by linarith
  calc
    _ ≤ ∑' j, (n : ℝ≥0∞) * cellUlNorm Set.univ (f j) :=
      ENNReal.tsum_le_tsum (fun j => cellUl_interval_eLpNorm_le (f j) (hf j) a b n hb)
    _ = (n : ℝ≥0∞) * ∑' j, cellUlNorm Set.univ (f j) := ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hs

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Active predecessor shifts preserve actual summability of coefficient series. -/

/-- Reindexing through an active coordinate predecessor preserves summability. -/
theorem fibreCoefficient_shift_summable {E : Type*} [NormedAddCommGroup E]
    (j : Fin 2) (f : ℕ × ℕ → E) (hs : Summable f) :
    Summable (fun p => if j ∈ fibreCoefficientDirections p then f (fibreCoefficientPrevious p j) else 0) := by
  let g := fun p : ℕ × ℕ => p + cellJetDirection j
  let a := fun p => if j ∈ fibreCoefficientDirections p then f (fibreCoefficientPrevious p j) else 0
  have hz p (hp : p ∉ Set.range g) : a p = 0 := by
    by_cases hj : j ∈ fibreCoefficientDirections p
    · exact (hp ⟨fibreCoefficientPrevious p j, fibreCoefficientPrevious_recover hj⟩).elim
    · exact ite_eq_right hj
  apply ((fibreCoefficient_add_direction_injective j).summable_iff hz).mp
  have he : a ∘ g = f := by
    funext p
    simp only [Function.comp_def, a, g, ite_eq_left (fibreCoefficientDirections_add p j),
      fibreCoefficientPrevious_add]
  rw [he]
  exact hs

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal monomial weighting respects the absolutely convergent two-variable Cauchy product. -/

/-- Convolution indices multiply to the literal output monomial. -/
theorem fibreMonomial_convolution (ξ : Fin 2 → ℂ) {p a : ℕ × ℕ}
    (ha : a ∈ fibreCoefficientPairs p) :
    fibreMonomial ξ a * fibreMonomial ξ (fibreCoefficientComplement p a) = fibreMonomial ξ p := by
  rw [← fibreMonomial_add, fibreCoefficientPairs_recover ha]

/-- Absolutely summable monomial series have the literal finite-rectangle Taylor product. -/
theorem fibreMonomial_cauchy_product (ξ : Fin 2 → ℂ) (f g : ℕ × ℕ → ℂ)
    (hf : Summable (fun p => ‖fibreMonomial ξ p * f p‖))
    (hg : Summable (fun p => ‖fibreMonomial ξ p * g p‖)) :
    ((∑' p, fibreMonomial ξ p * f p) * ∑' p, fibreMonomial ξ p * g p) =
      ∑' p, fibreMonomial ξ p * ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a) := by
  rw [fibreCoefficient_cauchy_product _ _ hf hg]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← fibreMonomial_convolution ξ ha]
  ring

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Positive-order monomials gain a linear factor inside the coefficient radius. -/

/-- Positive powers inside a positive radius gain one linear frequency factor. -/
theorem positive_power_radius_le {x R : ℝ} (hx : 0 ≤ x) (hR : 0 < R)
    (hxr : x ≤ R) {n : ℕ} (hn : 0 < n) : x ^ n ≤ (x / R) * R ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, pow_succ]
  calc
    _ ≤ R ^ m * x := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxr m) hx
    _ = _ := by field_simp

/-- Every positive-order literal monomial gains one frequency factor against its coefficient weight. -/
theorem fibreMonomial_linear_weight_le (R : ℝ) (hR : 0 < R) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ R) {p : ℕ × ℕ} (hp : 0 < p.1 + p.2) :
    ENNReal.ofReal ‖fibreMonomial ξ p‖ ≤ ENNReal.ofReal (fibreNorm ξ / R) *
      fibreCoefficientWeight (ENNReal.ofReal R) p := by
  calc
    _ ≤ ENNReal.ofReal ((fibreNorm ξ / R) * R ^ (p.1 + p.2)) :=
      ENNReal.ofReal_le_ofReal ((fibreMonomial_norm_le ξ p).trans
        (positive_power_radius_le (fibreNorm_nonneg ξ) hR hξ hp))
    _ = _ := by
      rw [ENNReal.ofReal_mul (div_nonneg (fibreNorm_nonneg ξ) hR.le),
        ENNReal.ofReal_pow hR.le]
      rfl

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Literal monomial series identify coordinate frequency shifts exactly. -/

/-- The monomial for one coordinate direction is that coordinate frequency. -/
theorem fibreMonomial_direction (ξ : Fin 2 → ℂ) (j : Fin 2) :
    fibreMonomial ξ (cellJetDirection j) = ξ j := by
  fin_cases j <;> simp [fibreMonomial, cellJetDirection]

/-- An active predecessor coefficient series contributes exactly one coordinate frequency factor. -/
theorem fibreMonomial_shift_tsum (ξ : Fin 2 → ℂ) (j : Fin 2) (f : ℕ × ℕ → ℂ) :
    (∑' p, if j ∈ fibreCoefficientDirections p then
      fibreMonomial ξ p * f (fibreCoefficientPrevious p j) else 0) =
      ξ j * ∑' p, fibreMonomial ξ p * f p := by
  have he p : (if j ∈ fibreCoefficientDirections p then
      fibreMonomial ξ p * f (fibreCoefficientPrevious p j) else 0) =
      (if j ∈ fibreCoefficientDirections p then
        ξ j * (fibreMonomial ξ (fibreCoefficientPrevious p j) * f (fibreCoefficientPrevious p j)) else 0) := by
    split_ifs with hp
    · have hm : fibreMonomial ξ p =
          fibreMonomial ξ (fibreCoefficientPrevious p j) * ξ j := by
        calc
          _ = fibreMonomial ξ (fibreCoefficientPrevious p j + cellJetDirection j) :=
            congrArg (fibreMonomial ξ) (fibreCoefficientPrevious_recover hp).symm
          _ = _ := by rw [fibreMonomial_add, fibreMonomial_direction]
      rw [hm]
      ring
    · rfl
  rw [tsum_congr he]
  exact (fibreCoefficient_shift_tsum j (fun p => ξ j * (fibreMonomial ξ p * f p))).trans
    tsum_mul_left

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniform scalar Taylor majorants give actual absolute convergence on each time trace. -/

theorem fibreScalarSeries_enorm_sum_le (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ R) (t : ℝ) :
    (∑' p, ‖fibreMonomial ξ p * a p t‖ₑ) ≤
      ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, ‖a p s‖ₑ := by
  apply ENNReal.tsum_le_tsum
  intro p
  rw [enorm_mul, ← ofReal_norm]
  exact mul_le_mul' (fibreMonomial_weight_le R ξ hξ p)
    (le_iSup (fun s => ‖a p s‖ₑ) t)

theorem fibreScalarSeries_summable_norm (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ)
    (ha : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, ‖a p s‖ₑ) < ⊤)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ R) (t : ℝ) :
    Summable (fun p => ‖fibreMonomial ξ p * a p t‖) :=
  tsum_enorm_ne_top_iff_summable_norm.mp ((fibreScalarSeries_enorm_sum_le a R ξ hξ t).trans_lt ha).ne

/-! A smaller geometric coefficient radius gains its radius ratio when the constant vanishes. -/

theorem fibreCoefficient_weight_radius_gain {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hR : 0 < R) (hρR : ρ ≤ R) {p : ℕ × ℕ} (hp : 0 < p.1 + p.2) :
    fibreCoefficientWeight (ENNReal.ofReal ρ) p ≤
      ENNReal.ofReal (ρ / R) * fibreCoefficientWeight (ENNReal.ofReal R) p := by
  unfold fibreCoefficientWeight
  rw [← ENNReal.ofReal_pow hρ, ← ENNReal.ofReal_pow hR.le,
    ← ENNReal.ofReal_mul (div_nonneg hρ hR.le)]
  exact ENNReal.ofReal_le_ofReal (positive_power_radius_le hρ hR hρR hp)

theorem fibreCoefficient_weighted_radius_gain {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hR : 0 < R) (hρR : ρ ≤ R) (E : ℕ × ℕ → ℝ≥0∞) (hz : E 0 = 0) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p * E p) ≤
      ENNReal.ofReal (ρ / R) *
        ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro p
  by_cases hp : p = 0
  · rw [hp, hz]
    simp
  · have ho : 0 < p.1 + p.2 := by
      by_contra h
      have he : p = 0 := by
        apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega
      exact hp he
    exact (mul_le_mul' (fibreCoefficient_weight_radius_gain hρ hR hρR ho) le_rfl).trans_eq
      (mul_assoc _ _ _)

end AVRegularity.CycleEvolution
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Complex scalar algebra of the literal cell energy seminorm. -/

/-- Raw gradient fields respect complex scaling. -/
theorem cellGradient_complex_smul (z : ℂ) (D : RawJet2 1 ℂ) :
    cellGradient (z • D) = z • cellGradient D := by rfl

/-- Complex scaling has the expected bound in the public energy norm. -/
theorem cellEnergyNorm_complex_smul (I : Set ℝ) (r : ℂ) (D : ℝ → RawJet2 1 ℂ)
    (hD : AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellEnergyNorm I (r • D) ≤ ‖r‖ₑ * cellEnergyNorm I D := by
  have hv : (⨆ t ∈ I, cellL2Norm (cellValue (r • D) t)) ≤
      ‖r‖ₑ * (⨆ t ∈ I, cellL2Norm (cellValue D t)) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    change eLpNorm (r • cellValue D t) 2 _ ≤ _
    rw [eLpNorm_const_smul]
    gcongr
    exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  have hg : cellUlNorm I (fun t => cellGradient ((r • D) t)) ≤
      ‖r‖ₑ * cellUlNorm I (fun t => cellGradient (D t)) :=
    cellUlNorm_complex_smul I r (fun t => cellGradient (D t)) hD
  unfold cellEnergyNorm
  rw [mul_add]
  exact add_le_add hv hg

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Literal Taylor coefficients after simultaneous reversal of time and frequency. -/

def fibreReverseValueCoefficients (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) :
    ℕ × ℕ → ℝ → Vec 2 → ℂ :=
  fun p t x => (-1 : ℂ) ^ (p.1 + p.2) * cellValue (r p) (-t) x

theorem fibreReverseValueCoefficients_norm (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (p : ℕ × ℕ) (t : ℝ) :
    cellL2Norm (fibreReverseValueCoefficients r p t) = cellL2Norm (cellValue (r p) (-t)) := by
  change eLpNorm ((-1 : ℂ) ^ (p.1 + p.2) • cellValue (r p) (-t)) 2 _ = _
  rw [eLpNorm_const_smul]
  simp [enorm_pow, cellL2Norm]

theorem fibreReverseValueCoefficients_uniform_le (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (p : ℕ × ℕ) :
    (⨆ t, cellL2Norm (fibreReverseValueCoefficients r p t)) ≤ cellEnergyNorm Set.univ (r p) := by
  apply iSup_le
  intro t
  rw [fibreReverseValueCoefficients_norm]
  exact cellValue_cellL2Norm_le_energy (r p) (-t)

theorem fibreReverseValueCoefficients_mean_zero (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hm : ∀ p t, cellMean (cellValue (r p) t) = 0) :
    ∀ p t, cellMean (fibreReverseValueCoefficients r p t) = 0 := by
  intro p t
  unfold fibreReverseValueCoefficients cellMean
  rw [integral_const_mul]
  change (-1 : ℂ) ^ (p.1 + p.2) * cellMean (cellValue (r p) (-t)) = 0
  rw [hm, mul_zero]

theorem fibreReverseValueCoefficients_weighted_le (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 < R) (hρR : ρ ≤ R)
    (hz : cellEnergyNorm Set.univ (r 0) = 0)
    (hmajor : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p *
      cellEnergyNorm Set.univ (r p)) ≤ 1) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p *
      ⨆ t, cellL2Norm (fibreReverseValueCoefficients r p t)) ≤ ENNReal.ofReal (ρ / R) := by
  calc
    _ ≤ ∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p * cellEnergyNorm Set.univ (r p) :=
      ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl (fibreReverseValueCoefficients_uniform_le r p))
    _ ≤ ENNReal.ofReal (ρ / R) *
        ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * cellEnergyNorm Set.univ (r p) :=
      fibreCoefficient_weighted_radius_gain hρ hR hρR _ hz
    _ ≤ ENNReal.ofReal (ρ / R) * 1 := mul_le_mul' le_rfl hmajor
    _ = _ := mul_one _

end AVRegularity.CycleEvolution
end
end
