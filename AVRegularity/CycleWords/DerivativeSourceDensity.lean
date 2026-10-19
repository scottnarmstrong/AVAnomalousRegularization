-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellFiniteEnergyNativeIncrement
public import AVRegularity.Weighted.WeightedMultiplicationTermTime
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Bounded weights preserve finite literal lower-integral forcing budgets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bounded_raw_factorial_energy_norm_upper {K : ℕ}
    (ρ : ℝ) (q : Vec 2 → ℝ) (hq : Continuous q) (B : ℝ) (hB : 0 ≤ B)
    (hq0 : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ B) (U : PlaneHk Set.univ K E) :
    ENNReal.ofReal (rawWeightedFactorialEnergy ρ q U.toFunction.jet) ≤
      ENNReal.ofReal (B * factorialWeightMax ρ K) * ENNReal.ofReal (‖U‖ ^ 2) := by
  have hh := storedChartFactorialEnergy_le_scaled ρ q (fun _ => 1) hB
    (fun x => by simpa only [mul_one] using hqb x) U
  rw [storedChartFactorialEnergy_eq_ofReal ρ q hq
      (fun x => by rw [abs_of_nonneg (hq0 x)]; exact hqb x) hq0,
    storedChartFactorialEnergy_eq_ofReal ρ (fun _ => 1) continuous_const
      (B := 1) (fun _ => by norm_num) (fun _ => by norm_num),
    rawWeightedFactorialEnergy_one] at hh
  have hu := ENNReal.ofReal_le_ofReal (factorialNormSq_upper ρ U.val)
  change ENNReal.ofReal (factorialNormSq ρ U.val) ≤
    ENNReal.ofReal (factorialWeightMax ρ K * ‖U‖ ^ 2) at hu
  calc
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (factorialWeightMax ρ K * ‖U‖ ^ 2) :=
      hh.trans (mul_le_mul le_rfl hu zero_le zero_le)
    _ = _ := by rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_mul' (sq_nonneg _), mul_assoc]

theorem bounded_raw_factorial_lower_integral_finite {K : ℕ}
    (ρ : ℝ) (q : ℝ → Vec 2 → ℝ) (hq : ∀ t, Continuous (q t))
    (B : ℝ) (hB : 0 ≤ B) (hq0 : ∀ t x, 0 ≤ q t x) (hqb : ∀ t x, q t x ≤ B)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E)
    (hU : (∫⁻ t, ENNReal.ofReal (‖U t‖ ^ 2) ∂μ) < ⊤) :
    (∫⁻ t, ENNReal.ofReal (rawWeightedFactorialEnergy ρ (q t) (U t).toFunction.jet) ∂μ) < ⊤ := by
  have hb := lintegral_mono (μ := μ) (fun t => bounded_raw_factorial_energy_norm_upper
    ρ (q t) (hq t) B hB (hq0 t) (hqb t) (U t))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU)

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! Coverage, quiet buffers and physical orientations of the genuine buffered block regions. The
quiet times are the trimmed quiet times: a time that is not trimmed-quiet lies within
`2τ/3 + τ/24 = 17τ/24 < 3τ/4` of an odd slot, hence in that slot's region; a buffer time in the
annulus `3τ/4 ≤ |t - kτ| ≤ τ` is at distance at least `17τ/24` from every odd slot. -/

/-- A cell time with nonzero drift is within `2τ/3` of an odd slot. -/
theorem interior_drift_nonzero_slot {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (hL : 0 < ocEll q Λ m ν ^ 2) {s : ℝ} (z : Vec 2)
    (hz : ocCellDrift α q Λ ζ m ν y₀ s z ≠ 0) :
    ∃ n : ℤ, |s - (2 * (n : ℝ) + 1) * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)| <
      2 / 3 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
  obtain ⟨k, hk, hp⟩ := ocCellDrift_nonzero_has_active_pulse ν s y₀ z hz
  obtain ⟨n, hkn⟩ := hk
  have hkr : (k : ℝ) = 2 * (n : ℝ) + 1 := by
    have he : k = 2 * n + 1 := by omega
    exact_mod_cast he
  obtain ⟨hlo, hhi⟩ := CycleReference.pulse_nonzero_center_distance hΛ hζ hp
  have hl := div_lt_div_of_pos_right hlo hL
  have hh := div_lt_div_of_pos_right hhi hL
  rw [sub_div, mul_div_assoc, mul_div_assoc,
    mul_div_cancel_left₀ _ hL.ne', hkr] at hl
  rw [mul_div_cancel_left₀ _ hL.ne', add_div, mul_div_assoc, mul_div_assoc, hkr] at hh
  exact ⟨n, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

/-- A cell time at distance at least `17τ/24` from every odd slot is trimmed-quiet. -/
theorem interior_trimmed_of_far {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (hL : 0 < ocEll q Λ m ν ^ 2) {t : ℝ}
    (hfar : ∀ n : ℤ, 17 / 24 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) ≤
      |t - (2 * (n : ℝ) + 1) * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)|) :
    t ∈ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
      (ocCellDrift α q Λ ζ m ν y₀) := by
  intro s hs z
  by_contra hz
  obtain ⟨n, hn⟩ := interior_drift_nonzero_slot hΛ hζ ν y₀ hL z hz
  have hts : |t - s| ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 / 24 :=
    abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have htri := abs_sub_le t s ((2 * (n : ℝ) + 1) * (ocTau α q Λ m / ocEll q Λ m ν ^ 2))
  linarith [hfar n]

/-- A time of the annulus `3τ/4 ≤ |t - (2n+1)τ| ≤ τ` is at distance at least `17τ/24` from every
odd slot. -/
theorem interior_far_of_annulus {τ t : ℝ} (hτ : 0 < τ) (n : ℤ)
    (hlo : 3 / 4 * τ ≤ |t - (2 * (n : ℝ) + 1) * τ|) (hhi : |t - (2 * (n : ℝ) + 1) * τ| ≤ τ) :
    ∀ k : ℤ, 17 / 24 * τ ≤ |t - (2 * (k : ℝ) + 1) * τ| := by
  intro k
  by_cases hk : k = n
  · subst hk
    linarith
  · have hd : (1 : ℝ) ≤ |(k : ℝ) - n| := by
      have h := Int.one_le_abs (sub_ne_zero.mpr hk)
      exact_mod_cast h
    have h2 : |(2 * (k : ℝ) + 1) * τ - (2 * (n : ℝ) + 1) * τ| = 2 * (|(k : ℝ) - n| * τ) := by
      rw [show (2 * (k : ℝ) + 1) * τ - (2 * (n : ℝ) + 1) * τ = 2 * (((k : ℝ) - n) * τ) by ring,
        abs_mul, abs_mul, abs_of_pos hτ, abs_two]
    have h3 := abs_sub_le ((2 * (k : ℝ) + 1) * τ) t ((2 * (n : ℝ) + 1) * τ)
    rw [abs_sub_comm ((2 * (k : ℝ) + 1) * τ) t] at h3
    have h4 := mul_le_mul_of_nonneg_right hd hτ.le
    linarith

/-- A time within `3τ/4` of the odd slot `2n+1` lies in that slot's clipped region. -/
theorem interiorPulseRegion_contains_near {τ a b t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Set.Icc a b) (n : ℤ)
    (hnear : (2 * (n : ℝ) + 1) * τ - 3 / 4 * τ ≤ t ∧ t ≤ (2 * (n : ℝ) + 1) * τ + 3 / 4 * τ) :
    n ∈ interiorPulseIndices τ a b ∧
      t ∈ Set.Icc (interiorPulseRegionLo τ a n) (interiorPulseRegionHi τ b n) := by
  refine ⟨(interiorPulseIndices_mem_iff hτ n).mpr ⟨?_, ?_⟩, ?_⟩
  · linarith [ht.1, hnear.2]
  · linarith [ht.2, hnear.1]
  · exact ⟨max_le ht.1 hnear.1, le_min ht.2 hnear.2⟩

/-- Ends drift-free with the margins `τ/24` and `7τ/24` are trimmed-quiet for the margin `τ/4`. -/
theorem interior_trimmed_ends {τ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    (h : ∀ t ∈ Set.Icc (a - τ / 24) (a + 7 * τ / 24) ∪ Set.Icc (b - 7 * τ / 24) (b + τ / 24),
      ∀ z, v t z = 0) :
    Set.Icc a (a + τ / 4) ∪ Set.Icc (b - τ / 4) b ⊆ interiorTrimmedQuiet τ v := by
  rintro t (ht | ht) s hs z
  · exact h s (Or.inl ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩) z
  · exact h s (Or.inr ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩) z

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
  (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
  (hL : 0 < ocEll q Λ m ν ^ 2) (a b D : ℝ)
  (marks : Fin 2 → Finset ℝ)
  (hleft : Set.Ico a (a + D) ⊆ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (ocCellDrift α q Λ ζ m ν y₀))
  (hright : Set.Ioc (b - D) b ⊆ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (ocCellDrift α q Λ ζ m ν y₀))

include hΛ hζ hL hleft hright in
theorem interiorBufferedActualRegions_cover :
    let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
      (ocCellDrift α q Λ ζ m ν y₀) marks
    ∀ t ∈ Set.Icc a b, t ∈ reg.quiet ∨ ∃ p, t ∈ Set.Icc (reg.lo p) (reg.hi p) := by
  classical
  dsimp only
  intro t ht
  by_cases hq : t ∈ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
      (ocCellDrift α q Λ ζ m ν y₀)
  · exact Or.inl hq
  · have hq' := hq
    simp only [interiorTrimmedQuiet, Set.mem_ofPred_eq, not_forall] at hq'
    obtain ⟨s, hs, z, hz⟩ := hq'
    obtain ⟨n, hsn⟩ := interior_drift_nonzero_slot hΛ hζ ν y₀ hL z hz
    have hτ : 0 < ocTau α q Λ m / ocEll q Λ m ν ^ 2 :=
      div_pos (AVRegularity.Construction.Stream.ocTau_pos hΛ) hL
    have hsn' := abs_lt.mp hsn
    obtain ⟨hn, hwide⟩ := interiorPulseRegion_contains_near hτ ht n
      ⟨by linarith [hs.2, hsn'.1], by linarith [hs.1, hsn'.2]⟩
    obtain ⟨hn', hclip⟩ := interiorActivePulseRegion_contains _ a b D
      (ocCellDrift α q Λ ζ m ν y₀) hleft hright hn ht hwide hq
    let s' := interiorActivePulseIndices (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
      (ocCellDrift α q Λ ζ m ν y₀)
    let p : Fin s'.card := s'.equivFin ⟨n, hn'⟩
    have hp : interiorActivePulseRegionIndex (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
        (ocCellDrift α q Λ ζ m ν y₀) p = n := by
      simp only [interiorActivePulseRegionIndex, p, s', Equiv.symm_apply_apply]
    right
    refine ⟨p, ?_⟩
    change t ∈ Set.Icc
      (interiorBufferedPulseLo (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a D
        (interiorActivePulseRegionIndex _ a b (ocCellDrift α q Λ ζ m ν y₀) p))
      (interiorBufferedPulseHi (ocTau α q Λ m / ocEll q Λ m ν ^ 2) b D
        (interiorActivePulseRegionIndex _ a b (ocCellDrift α q Λ ζ m ν y₀) p))
    rw [hp]
    exact hclip

include hΛ hζ hL hleft hright in
theorem interiorBufferedActualRegions_quiet_buffers
    (hD : D ≤ (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4) :
    let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
      (ocCellDrift α q Λ ζ m ν y₀) marks
    ∀ p, Set.Ico (reg.lo p - reg.buffer) (reg.lo p) ⊆ reg.quiet ∧
      Set.Ioc (reg.hi p) (reg.hi p + reg.buffer) ⊆ reg.quiet := by
  dsimp only
  intro p
  have hτ : 0 < ocTau α q Λ m / ocEll q Λ m ν ^ 2 :=
    div_pos (AVRegularity.Construction.Stream.ocTau_pos hΛ) hL
  constructor
  · intro t ht
    rcases interiorBufferedPulse_left_buffer hτ hD
      (interiorActivePulseRegionIndex _ a b (ocCellDrift α q Λ ζ m ν y₀) p) ht with he | he
    · exact hleft he
    · exact interior_trimmed_of_far hΛ hζ ν y₀ hL (interior_far_of_annulus hτ _ he.1 he.2)
  · intro t ht
    rcases interiorBufferedPulse_right_buffer hτ hD
      (interiorActivePulseRegionIndex _ a b (ocCellDrift α q Λ ζ m ν y₀) p) ht with he | he
    · exact hright he
    · exact interior_trimmed_of_far hΛ hζ ν y₀ hL (interior_far_of_annulus hτ _ he.1 he.2)

include hL in
theorem interiorBufferedActualRegions_orientations :
    let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
      (ocCellDrift α q Λ ζ m ν y₀) marks
    ∀ p, ∃ k : ℤ, Odd k ∧
      (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
        |ocEll q Λ m ν ^ 2 * t - (k : ℝ) * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
      reg.orient p = (if k % 4 = 3 then 0 else 1) := by
  dsimp only
  intro p
  let n := interiorActivePulseRegionIndex (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
    (ocCellDrift α q Λ ζ m ν y₀) p
  refine ⟨2 * n + 1, ⟨n, by ring⟩, ?_, rfl⟩
  intro t ht
  have hs := scaled_pulse_window hL (interiorBufferedPulse_window _ a b D n ht)
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hs

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Single-pulse extensions inherit the actual drift's spatial cosine and jet prices. -/

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}

theorem interiorSinglePulseDrift_component_cosine (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (t : ℝ) (i : Fin 2) :
    ∃ j : Fin 2, ∃ phase A : ℝ,
      |A| ≤ |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| ∧
      (fun z => interiorSinglePulseDrift α q Λ ζ m ν y₀ k t z i) =
        fun z => A * CycleDamping.cellCosine j phase z := by
  rcases interiorSinglePulseDrift_eq_actual_or_zero hΛ hζ ν y₀ hk t with he | he
  · rw [he]
    exact constructed_spatial_component_cosine hΛ hζ ν y₀ t i
  · refine ⟨0, 0, 0, ?_, ?_⟩
    · simpa only [abs_zero] using abs_nonneg (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)
    · funext z
      simp only [he, Pi.zero_apply, zero_mul]

theorem interiorSinglePulseDrift_component_jet_bound (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (t : ℝ) (i : Fin 2) (n : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun x => interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x i) z‖ ≤
      |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| * (2 * Real.pi) ^ n := by
  obtain ⟨j, phase, A, hA, he⟩ :=
    interiorSinglePulseDrift_component_cosine hΛ hζ ν y₀ hk t i
  rw [he]
  exact (cellCosine_scalar_jet_bound j phase A n z).trans
    (mul_le_mul_of_nonneg_right hA (by positivity))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Actual plane value and gradient reconstructed from cell H1 frequency readouts. -/

def cellFrequencyPlaneValue (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    Lp ℂ 2 (volume : Measure (Vec 2)) :=
  (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
    (centeredCellBlochValueField u)

def cellFrequencyPlaneGradient (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    Lp ℂ 2 (volume : Measure (Vec 2)) :=
  (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
    (centeredCellBlochGradientField u i)

theorem centeredCellBlochH1Reconstruct_native_gradient
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    univToPlane ((centeredCellBlochH1Reconstruct u).val ⟨⟨1, by decide⟩, fun _ => i⟩) =
      cellFrequencyPlaneGradient u i := by
  rw [centeredCellBlochH1Reconstruct, planeBlochReconstructH1_gradient,
    cellFrequencyPlaneGradient, planeCellBlochUnitary_symm_apply]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The quadratic native cell source represents the literal raw graph forcing. -/

theorem cellNonlinearSourceClass_ae
    (b : Vec 2 → ℂ) (hb : AEStronglyMeasurable b (volume.restrict AVenhance.unitCube))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, ‖b x‖ ≤ B)
    (u : ComplexCellL2) (ρ : Vec 2 → ℂ)
    (hρ : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] ρ) :
    let M := cellCoefficientCLM b hb B hB hbound
    (cellQ0CLM (cellScalarCLM (-Complex.I) (M (cellConstantCLM 1 + u))) +
      cellScalarCLM (Complex.I * cellMeanCLM (M u)) u : ComplexCellL2) =ᵐ[
        volume.restrict AVenhance.unitCube]
      fun x => cellQ0 (fun y => -Complex.I * (b y * (1 + ρ y))) x +
        Complex.I * ρ x * cellMean (fun y => b y * ρ y) := by
  let M := cellCoefficientCLM b hb B hB hbound
  let A := cellScalarCLM (-Complex.I) (M (cellConstantCLM 1 + u))
  have hMu : (M u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => b x * ρ x := by
    filter_upwards [cellCoefficientCLM_ae b hb B hB hbound u, hρ] with x hx hux
    exact hx.trans (congrArg (b x * ·) hux)
  have hm : cellMeanCLM (M u) = cellMean (fun x => b x * ρ x) := by
    rw [cellMeanCLM_apply]
    exact integral_congr_ae hMu
  have hA : (A : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => -Complex.I * (b x * (1 + ρ x)) := by
    filter_upwards [cellScalarCLM_ae (-Complex.I) (M (cellConstantCLM 1 + u)),
      cellCoefficientCLM_ae b hb B hB hbound (cellConstantCLM 1 + u),
      Lp.coeFn_add (cellConstantCLM 1) u, cellConstantCLM_ae 1, hρ]
      with x hs hc ha h1 hu
    dsimp only [A, M]
    rw [hs, hc, ha, Pi.add_apply, h1, hu]
  have hma : cellMean A = cellMean (fun x => -Complex.I * (b x * (1 + ρ x))) :=
    integral_congr_ae hA
  have hQ : (cellQ0CLM A : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => cellQ0 (fun y => -Complex.I * (b y * (1 + ρ y))) x := by
    filter_upwards [cellQ0CLM_ae A, hA] with x hx hax
    rw [hx]
    simp only [cellQ0, hax, hma]
  filter_upwards [Lp.coeFn_add (cellQ0CLM A)
    (cellScalarCLM (Complex.I * cellMeanCLM (M u)) u), hQ,
    cellScalarCLM_ae (Complex.I * cellMeanCLM (M u)) u, hρ] with x ha hq hs hu
  change (cellQ0CLM A + cellScalarCLM (Complex.I * cellMeanCLM (M u)) u) x = _
  rw [ha, Pi.add_apply, hq, hs, hu, hm]
  congr 1
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual plane H1 reconstruction as a bounded real linear operator. -/

local instance centeredCellBlochH1LpSeminormed :
    SeminormedAddCommGroup (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :=
  (inferInstance : NormedAddCommGroup (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure)).toSeminormedAddCommGroup

local instance centeredCellBlochH1PlaneSeminormed : SeminormedAddCommGroup (PlaneHk Set.univ 1 ℂ) :=
  (inferInstance : NormedAddCommGroup (PlaneHk Set.univ 1 ℂ)).toSeminormedAddCommGroup

local instance centeredCellBlochH1LpAdd :
    AddCommMonoid (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :=
  (inferInstance : NormedAddCommGroup (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure)).toAddCommMonoid

local instance centeredCellBlochH1PlaneAdd : AddCommMonoid (PlaneHk Set.univ 1 ℂ) :=
  (inferInstance : NormedAddCommGroup (PlaneHk Set.univ 1 ℂ)).toAddCommMonoid

local instance centeredCellBlochH1PlaneTopology : TopologicalSpace (PlaneHk Set.univ 1 ℂ) :=
  (inferInstance : PseudoMetricSpace (PlaneHk Set.univ 1 ℂ)).toUniformSpace.toTopologicalSpace

local instance centeredCellBlochH1LpModule :
    Module ℝ (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :=
  (inferInstance : NormedSpace ℝ (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure)).toModule

local instance centeredCellBlochH1PlaneModule : Module ℝ (PlaneHk Set.univ 1 ℂ) :=
  (inferInstance : NormedSpace ℝ (PlaneHk Set.univ 1 ℂ)).toModule

def centeredCellBlochH1LinearMap :
    Lp CellComplexH1 2 centeredPlaneFrequencyMeasure →ₗ[ℝ] PlaneHk Set.univ 1 ℂ where
  toFun := centeredCellBlochH1Reconstruct
  map_add' := centeredCellBlochH1Reconstruct_add
  map_smul' := centeredCellBlochH1Reconstruct_smul

def centeredCellBlochH1Operator :
    Lp CellComplexH1 2 centeredPlaneFrequencyMeasure →L[ℝ] PlaneHk Set.univ 1 ℂ :=
  centeredCellBlochH1LinearMap.mkContinuous centeredCellBlochH1Bound
    centeredCellBlochH1Reconstruct_norm_le

theorem centeredCellBlochH1Operator_apply
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    centeredCellBlochH1Operator u = centeredCellBlochH1Reconstruct u := rfl

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! An extracted derivative source has the literal prefix-concatenated stored words. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem derivativeSourceOperator_word_readout {K L r : ℕ} (hKL : K + r ≤ L + 1)
    (I : DerivativeWord2 r) (U : PlaneHk Set.univ (L + 1) E)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder (Weighted.derivativeSourceOperator hKL I U) j w =
      planeJetOrder U (r + j) (Fin.append I w) := by
  rw [planeJetOrder_eq_stored hj,
    planeJetOrder_eq_stored (by omega : r + j ≤ L + 1)]
  rfl

theorem sourceWordAppend_injective {r j : ℕ} (I : DerivativeWord2 r) :
    Function.Injective (fun w : DerivativeWord2 j => Fin.append I w) := by
  intro w v h
  funext i
  have hh := congrFun h (Fin.natAdd r i)
  simpa only [Fin.append_right] using hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite family forcing norms imply literal component lower-integral bounds. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryFluxNorm_lower_component_finite (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kslot : ι → ℕ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r a b : ℝ) (hr : 0 < r)
    (F : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (he : geometryFluxNorm π Kslot n ϖ zc r a b F ≠ ⊤) (i : ι) :
    (∫⁻ t in Set.Icc a b, ENNReal.ofReal (‖F i t‖ ^ 2)) < ⊤ := by
  have htotal : (∫⁻ t in Set.Icc a b, ∑ x, ENNReal.ofReal ((π x)⁻¹) *
      weightedFactorialNormSq n ϖ zc r (Kslot x) (F x t)) ≠ ⊤ := by
    intro hh
    apply he
    unfold geometryFluxNorm
    rw [hh]
    simp
  have hmul : ENNReal.ofReal ((π i)⁻¹) *
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (F i t)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top htotal
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro t
    exact Finset.single_le_sum
      (f := fun x => ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq n ϖ zc r (Kslot x) (F x t))
      (fun _ _ => by positivity) (Finset.mem_univ i)
  have hi : (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (F i t)) ≠ ⊤ := by
    intro hh
    apply hmul
    rw [hh, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hπ i))).ne'
  exact weightedSobolev_lower_norm_integral_finite n ϖ zc r hr
    (volume.restrict (Set.Icc a b)) (F i) hi

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedWords_clipped_compact_energy_growth {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hcurve : ∀ α : JetIndex2 K, PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) :
    let q := fun t x => clipWeight B (C.W m t x)
    let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := planeIntervalDiffusion a b hab G
      (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
    let u := fun α t => planeJetReadoutOperator K α (U t)
    let slice := fun α t => planeWordH1SliceOperator K α (W t)
    let L := fun α t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice α t))
    let R := fun α t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice α t))
    ∃ P : ℝ → ℝ,
      AVRegularity.CycleEvolution.StrongTimeRegularity a b
        (fun t => ∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, χ x ^ 2 * q t x * ‖u α t x‖ ^ 2)) P ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        P t + (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, χ x ^ 2 * q t x * ‖(WithLp.toLp 2
            (fun k => planeH1GradientOperator (slice α t) k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) ≤
        18 * C.lam m * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, χ x ^ 2 * q t x * ‖u α t x‖ ^ 2)) +
        8 * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, q t x * ‖(WithLp.toLp 2 (fun k => L α t k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) +
        (4096 * η ^ 2 + 16 * Mv * η) * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, q t x * ‖u α t x‖ ^ 2)) +
        2 * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, χ x ^ 2 * q t x * (‖R α t x‖ * ‖u α t x‖)))) := by
  dsimp only
  apply finite_weighted_strong_growth a b (fun α : JetIndex2 K => factorialWeight ρ α.1.val)
    (fun α => factorialWeight_nonneg ρ α.1.val)
  intro α
  exact storedWord_clipped_compact_energy_growth a b hab v hv hdiv Mv hMv hvb G hG g hg4
    hGnear hGs t₀ S ϖ zc N m Cw C hm ha hb U H W Q α (hcurve α)
    χ hχ hsχ hχ0 hχ1 η hη hdχ B hB

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The actual unscaled transport entry acts on every reserved native carrier. -/

 def constructedDriftEntryNativeCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (i : Fin 2) (t : ℝ) : TorusHk K ℂ →L[ℝ] TorusHk K ℂ :=
  KernelEnergy.torusMultiplierCLM (constructedDriftEntryCoefficient α q Λ m ζ ν y₀ i t)
    (constructedDriftEntryCoefficient_contDiff hΛ hζ ν y₀ i t K)
    (constructedDriftEntryCoefficient_periodic α q Λ m ζ ν y₀ hv i t)
    (fun l => constructedDriftEntryJetPrice α q Λ m ν l.val)
    (fun l x => constructedDriftEntryCoefficient_array_bound hΛ hζ ν y₀ i t l.val x)
    1 (by norm_num)

 def constructedDriftEntryNativePrice (α q : ℝ) (Λ m : ℕ) (ν : ℝ) (K : ℕ) : ℝ :=
  (∑ l : Fin (K + 1), factorialRootWeight 1 l.val *
      constructedDriftEntryJetPrice α q Λ m ν l.val) *
    Real.sqrt (factorialWeightMax 1 K) / Real.sqrt (factorialWeightMin 1 K)

 theorem constructedDriftEntryNativeCLM_norm_bound (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    ‖constructedDriftEntryNativeCLM K hΛ hζ ν y₀ hv i t U‖ ≤
      constructedDriftEntryNativePrice α q Λ m ν K * ‖U‖ :=
  KernelEnergy.torusMultiplier_norm_bound _ _ _ _ _ 1 (by norm_num) U

 theorem constructedDriftEntryNativeCLM_value (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    torusHkValueCLM (constructedDriftEntryNativeCLM K hΛ hζ ν y₀ hv i t U) =
      cellDriftEntryCLM ⟨0, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩ V hv.1 hb t i
        (torusHkValueCLM U) := by
  apply Lp.ext
  have hl := torusMulCoefficient_value_ae U
    (constructedDriftEntryCoefficient α q Λ m ζ ν y₀ i t)
    (constructedDriftEntryCoefficient_contDiff hΛ hζ ν y₀ i t K)
    (constructedDriftEntryCoefficient_periodic α q Λ m ζ ν y₀ hv i t)
    (fun l x => constructedDriftEntryCoefficient_array_bound hΛ hζ ν y₀ i t l.val x)
  have hr := cellDriftEntryCLM_ae ⟨0, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩ V hv.1 hb t i
    (torusHkValueCLM U)
  filter_upwards [hl, hr] with x hl hr
  exact hl.trans hr.symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Positive derivative sources pay exactly the factorial reserve against weighted dissipation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem derivativeSourceOperator_weightedFactorialNormSq_le {K L r : ℕ}
    (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (U : PlaneHk Set.univ (L + 1) E) :
    weightedFactorialNormSq n ϖ zc ρ K (Weighted.derivativeSourceOperator hKL I U) ≤
      ENNReal.ofReal ((derivativeReserveFactor ρ K (r - 1)) ^ 2) *
        weightedGradFactorialNormSq n ϖ zc ρ L U := by
  let G := fun j : ℕ => ∫⁻ z, ENNReal.ofReal
    ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
      ∑ w : DerivativeWord2 (j + 1), ‖planeJetOrder U (j + 1) w z‖ ^ 2)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      ENNReal.ofReal (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2) *
        (∫⁻ z, ENNReal.ofReal
          ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
            ∑ w : DerivativeWord2 j,
              ‖planeJetOrder (Weighted.derivativeSourceOperator hKL I U) j w z‖ ^ 2)) ≤
      ENNReal.ofReal ((derivativeReserveFactor ρ K (r - 1)) ^ 2) *
        (ENNReal.ofReal (ρ ^ (2 * (j + (r - 1))) / ((j + (r - 1)).factorial : ℝ) ^ 2) *
          G (j + (r - 1))) := by
    have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hi : (∫⁻ z, ENNReal.ofReal
        ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
          ∑ w : DerivativeWord2 j,
            ‖planeJetOrder (Weighted.derivativeSourceOperator hKL I U) j w z‖ ^ 2)) ≤ G (j + (r - 1)) := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp_rw [derivativeSourceOperator_word_readout hKL I U j hjK]
      have hh := sum_comp_le_sum_nonneg (fun w : DerivativeWord2 j => Fin.append I w)
        (sourceWordAppend_injective I)
        (fun w : DerivativeWord2 (r + j) => ‖planeJetOrder U (r + j) w z‖ ^ 2)
        (fun w => sq_nonneg _)
      have he : r + j = j + (r - 1) + 1 := by omega
      conv_rhs => rw [← he]
      exact hh
    have hw := ENNReal.ofReal_le_ofReal (factorialWeight_reserve_le ρ hρ hjK (r - 1))
    rw [ENNReal.ofReal_mul (sq_nonneg _)] at hw
    exact (mul_le_mul' hw hi).trans_eq (mul_assoc _ _ _)
  unfold weightedFactorialNormSq
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal ((derivativeReserveFactor ρ K (r - 1)) ^ 2) *
        (ENNReal.ofReal (ρ ^ (2 * (j + (r - 1))) / ((j + (r - 1)).factorial : ℝ) ^ 2) * G (j + (r - 1))) :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((derivativeReserveFactor ρ K (r - 1)) ^ 2) *
        ∑ j ∈ Finset.range (K + 1),
          ENNReal.ofReal (ρ ^ (2 * (j + (r - 1))) / ((j + (r - 1)).factorial : ℝ) ^ 2) * G (j + (r - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_right _ _
      change (∑ j ∈ Finset.range (K + 1),
        (fun q => ENNReal.ofReal (ρ ^ (2 * q) / (q.factorial : ℝ) ^ 2) * G q) (j + (r - 1))) ≤
        ∑ j ∈ Finset.range (L + 1), ENNReal.ofReal (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2) * G j
      have hsum := Finset.sum_image (s := Finset.range (K + 1))
        (g := fun j : ℕ => j + (r - 1))
        (f := fun q => ENNReal.ofReal (ρ ^ (2 * q) / (q.factorial : ℝ) ^ 2) * G q)
        (by intro a _ b _ hab; exact Nat.add_right_cancel hab)
      rw [← hsum]
      apply Finset.sum_le_sum_of_subset
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_range.mpr
      have := Finset.mem_range.mp hk
      omega

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! Actual single-pulse extensions indexed by the constructed buffered regions. -/

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}

def interiorOrientationExtensions (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν : ℝ) (y₀ : Vec 2) (a b : ℝ)
    (p : Fin (interiorActivePulseIndices (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
      (ocCellDrift α q Λ ζ m ν y₀)).card) : ℝ → Vec 2 → Vec 2 :=
  interiorSinglePulseDrift α q Λ ζ m ν y₀
    (2 * interiorActivePulseRegionIndex (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
      (ocCellDrift α q Λ ζ m ν y₀) p + 1)

theorem interiorOrientationExtensions_shear (ν : ℝ) (y₀ : Vec 2) (a b D : ℝ)
    (marks : Fin 2 → Finset ℝ) :
    let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
      (ocCellDrift α q Λ ζ m ν y₀) marks
    ∀ p, ∃ V : ℝ → ℝ → ℝ, ∀ t z,
      interiorOrientationExtensions α q Λ ζ m ν y₀ a b p t z =
        V t (z (reg.orient p).rev) • basisVec (reg.orient p) := by
  dsimp only
  intro p
  exact interiorSinglePulseDrift_shear α q Λ ζ m ν y₀ ⟨_, by ring⟩

theorem interiorOrientationExtensions_drift (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (a b : ℝ) (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (hw : ∀ t z, Real.sqrt η * Real.sqrt
      (∑ i, ocCellDrift α q Λ ζ m ν y₀ t z i ^ 2) ≤ Cw) :
    ∀ p, IsCellDrift (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p) ∧
      (∀ t (i : Fin 2), cellMean
        (fun z => (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p t z i : ℂ)) = 0) ∧
      ∀ t z, Real.sqrt η * Real.sqrt
        (∑ i, interiorOrientationExtensions α q Λ ζ m ν y₀ a b p t z i ^ 2) ≤ Cw := by
  intro p
  have hk : Odd (2 * interiorActivePulseRegionIndex
      (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b (ocCellDrift α q Λ ζ m ν y₀) p + 1) :=
    ⟨_, by ring⟩
  exact ⟨interiorSinglePulseDrift_isCellDrift hΛ hζ ν y₀ hk hv,
    fun t i => interiorSinglePulseDrift_mean_zero hΛ ν y₀ hk t i,
    interiorSinglePulseDrift_scaled_bound hΛ hζ ν y₀ hk η Cw hCw hw⟩

theorem interiorOrientationExtensions_agree (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hL : 0 < ocEll q Λ m ν ^ 2) (a b D : ℝ)
    (marks : Fin 2 → Finset ℝ)
    (hD : D ≤ (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4)
    (hleft : ∀ t ∈ Set.Ico a (a + D), ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0)
    (hright : ∀ t ∈ Set.Ioc (b - D) b, ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) :
    let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
      (ocCellDrift α q Λ ζ m ν y₀) marks
    ∀ p, ∀ t ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer), ∀ z,
      interiorOrientationExtensions α q Λ ζ m ν y₀ a b p t z =
        ocCellDrift α q Λ ζ m ν y₀ t z := by
  dsimp only
  intro p t ht z
  exact interiorSinglePulseDrift_buffered_agrees hΛ hζ ν y₀ hL a b D hD hleft hright
    (interiorActivePulseRegionIndex _ a b (ocCellDrift α q Λ ζ m ν y₀) p) ht z

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Native L² classes of the literal nonlinear graph source and flux, with exact projection identities. -/

def cellFibreDriftCouplingCLM (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) : ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  cellCoefficientCLM (fibreDriftCoupling η v ξ t)
    (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t)
    (Cw * fibreNorm ξ) (mul_nonneg hCw (fibreNorm_nonneg ξ))
    (fibreDriftCoupling_norm_le η Cw v hw ξ t)

def cellFibreGraphSourceClass (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) : ComplexCellL2 :=
  let M := cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
  cellQ0CLM (cellScalarCLM (-Complex.I) (M (cellConstantCLM 1 + u))) +
    cellScalarCLM (Complex.I * cellMeanCLM (M u)) u

def cellFibreGraphFluxClass (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) (k : Fin 2) : ComplexCellL2 :=
  cellScalarCLM (2 * Complex.I * (Real.sqrt η : ℂ) * (∑ j, (G t k j : ℂ) * ξ j)) u

theorem cellFibreGraphSourceClass_ae (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) (ρ : ℝ → Vec 2 → ℂ)
    (hρ : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] ρ t) :
    (cellFibreGraphSourceClass η Cw hCw hv hw ξ t u : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] fibreGraphSource η v ξ ρ t := by
  have he := cellNonlinearSourceClass_ae (fibreDriftCoupling η v ξ t)
      (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t)
      (Cw * fibreNorm ξ) (mul_nonneg hCw (fibreNorm_nonneg ξ))
      (fibreDriftCoupling_norm_le η Cw v hw ξ t) u (ρ t) hρ
  filter_upwards [he] with x hx
  exact hx

theorem cellFibreGraphFluxClass_ae (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) (ρ : ℝ → Vec 2 → ℂ)
    (hρ : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] ρ t) (k : Fin 2) :
    (cellFibreGraphFluxClass η G ξ t u k : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => fibreGraphFlux η G ξ ρ t x k := by
  filter_upwards [cellScalarCLM_ae
    (2 * Complex.I * (Real.sqrt η : ℂ) * (∑ j, (G t k j : ℂ) * ξ j)) u, hρ]
    with x hx hu
  exact hx.trans (congrArg
    ((2 * Complex.I * (Real.sqrt η : ℂ) * (∑ j, (G t k j : ℂ) * ξ j)) * ·) hu)

/-! The literal sum of shifted drift multipliers equals the bounded normalized coupling multiplier. -/

theorem cellScaledDriftMultiplier_sum (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (C : CellCoefficients) (hCv : C.v = v) (V : ℝ)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) :
    (∑ j : Fin 2, cellDriftEntryCLM C V (hCv ▸ hv.1) hb t j
      (cellScalarCLM (Complex.I * ((Real.sqrt η : ℂ) * ξ j)) u)) =
    cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u) := by
  have hentry (j : Fin 2) :
      (cellDriftEntryCLM C V (hCv ▸ hv.1) hb t j
        (cellScalarCLM (Complex.I * ((Real.sqrt η : ℂ) * ξ j)) u) : Vec 2 → ℂ) =ᵐ[
          volume.restrict AVenhance.unitCube]
        fun x => (v t x j : ℂ) * (Complex.I * ((Real.sqrt η : ℂ) * ξ j) * u x) := by
    filter_upwards [cellDriftEntryCLM_ae C V (hCv ▸ hv.1) hb t j
      (cellScalarCLM (Complex.I * ((Real.sqrt η : ℂ) * ξ j)) u),
      cellScalarCLM_ae (Complex.I * ((Real.sqrt η : ℂ) * ξ j)) u] with x hd hs
    rw [hd, hs, hCv]
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun j : Fin 2 => cellDriftEntryCLM C V (hCv ▸ hv.1) hb t j
        (cellScalarCLM (Complex.I * ((Real.sqrt η : ℂ) * ξ j)) u)),
    ae_all_iff.mpr hentry,
    cellScalarCLM_ae Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u),
    cellCoefficientCLM_ae (fibreDriftCoupling η v ξ t)
      (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t) (Cw * fibreNorm ξ)
      (mul_nonneg hCw (fibreNorm_nonneg ξ)) (fibreDriftCoupling_norm_le η Cw v hw ξ t) u]
    with x hs he hi hc
  rw [hs, hi]
  change (∑ j : Fin 2, cellDriftEntryCLM C V (hCv ▸ hv.1) hb t j
      (cellScalarCLM (Complex.I * ((Real.sqrt η : ℂ) * ξ j)) u) x) =
    Complex.I * cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u x
  simp_rw [he]
  change cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u x =
    fibreDriftCoupling η v ξ t x * u x at hc
  rw [hc]
  simp only [fibreDriftCoupling, Fin.sum_univ_two]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Unscaled single-pulse coefficients retain the actual transport jet prices. -/

 def interiorPulseDriftEntryCoefficient (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ)
    (ν : ℝ) (y₀ : Vec 2) (k : ℤ) (i : Fin 2) (t : ℝ) (x : Vec 2) : ℂ →L[ℝ] ℂ :=
  realScalarMultiplierMap (interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x i)

 def interiorPulseDriftEntryJetPrice (α q : ℝ) (Λ m : ℕ) (ν : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (DerivativeWord2 n) : ℝ) * ‖realScalarMultiplierMap‖ *
    (|2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| * (2 * Real.pi) ^ n)

 theorem interiorPulseDriftEntryCoefficient_contDiff
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (i : Fin 2) (t : ℝ) (n : ℕ) :
    ContDiff ℝ (n : ℕ) (interiorPulseDriftEntryCoefficient α q Λ m ζ ν y₀ k i t) := by
  have hv : ContDiff ℝ (n : ℕ) (interiorSinglePulseDrift α q Λ ζ m ν y₀ k t) := (interiorSinglePulseDrift_contDiff ν y₀ hk t).of_le (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  exact realScalarMultiplierMap.contDiff.comp ((contDiff_apply ℝ ℝ i).comp hv)

 theorem interiorPulseDriftEntryCoefficient_periodic
    (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ) (y₀ : Vec 2) (k : ℤ)
    (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k)) (i : Fin 2) (t : ℝ) :
    IsZ2Periodic (interiorPulseDriftEntryCoefficient α q Λ m ζ ν y₀ k i t) := by
  intro k x
  unfold interiorPulseDriftEntryCoefficient
  rw [hv.2.2.1 t k x]

 theorem interiorPulseDriftEntryCoefficient_array_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (i : Fin 2) (t : ℝ) (n : ℕ) (x : Vec 2) :
    ‖coefficientDerivativeArray (interiorPulseDriftEntryCoefficient α q Λ m ζ ν y₀ k i t) n x‖ ≤
      interiorPulseDriftEntryJetPrice α q Λ m ν n := by
  have hv : ContDiff ℝ (n : ℕ) (fun x => interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x i) := by
    simpa only [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp
      ((interiorSinglePulseDrift_contDiff ν y₀ hk t).of_le (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)))
  have hb := realScalarMultiplier_jet_array_bound _ n hv x
  exact hb.trans (mul_le_mul_of_nonneg_left
    (interiorSinglePulseDrift_component_jet_bound hΛ hζ ν y₀ hk t i n x) (by positivity))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every genuine real plane H1 test has an actual cell H1 frequency realization. -/

def planeRealH1TestGradient (φ : PlaneHk Set.univ 1 ℝ) (i : Fin 2) :
    Lp ℝ 2 (volume : Measure (Vec 2)) :=
  univToPlane (φ.val ⟨⟨1, by decide⟩, fun _ => i⟩)

theorem planeRealH1Test_weakDerivative (φ : PlaneHk Set.univ 1 ℝ) (i : Fin 2) :
    HasWeakPartialDerivOn Set.univ i (planeHkValueOperator 1 φ) (planeRealH1TestGradient φ i) := by
  let w : Fin 0 → Fin 2 := fun j => Fin.elim0 j
  have hl : lowerIndex2 (0 : Fin 1) w = valueIndex2 1 := rfl
  have hn : nextIndex2 (0 : Fin 1) w i = ⟨⟨1, by decide⟩, fun _ => i⟩ := by
    rfl
  have hw : HasWeakPartialDerivOn Set.univ i (φ.val (valueIndex2 1))
      (φ.val ⟨⟨1, by decide⟩, fun _ => i⟩) := by
    simpa only [PlaneHk.toFunction, planeJetRepresentative, Real.inner_apply, one_mul, hl, hn]
      using φ.toFunction.hasWeakJet (0 : Fin 1) w i 1
  apply hasWeakPartialDerivOn_congr_ae _ _ hw
  · simpa only [Measure.restrict_univ, planeHkValueOperator_apply] using
      (univToPlane_ae (φ.val (valueIndex2 1))).symm
  · simpa only [Measure.restrict_univ, planeRealH1TestGradient] using
      (univToPlane_ae (φ.val ⟨⟨1, by decide⟩, fun _ => i⟩)).symm

def planeRealH1BlochTest (φ : PlaneHk Set.univ 1 ℝ) :
    Lp CellComplexH1 2 centeredPlaneFrequencyMeasure :=
  centeredPlaneBlochRealH1Field (planeHkValueOperator 1 φ) (planeRealH1TestGradient φ)
    (planeRealH1Test_weakDerivative φ)

theorem planeRealH1BlochTest_value (φ : PlaneHk Set.univ 1 ℝ) :
    cellFrequencyPlaneValue (planeRealH1BlochTest φ) =
      ofRealL2 volume (planeHkValueOperator 1 φ) := by
  unfold cellFrequencyPlaneValue planeRealH1BlochTest
  rw [centeredPlaneBlochRealH1Field_value]
  exact (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm_apply_apply _

theorem planeRealH1BlochTest_gradient (φ : PlaneHk Set.univ 1 ℝ) (i : Fin 2) :
    cellFrequencyPlaneGradient (planeRealH1BlochTest φ) i =
      ofRealL2 volume (planeRealH1TestGradient φ i) := by
  unfold cellFrequencyPlaneGradient planeRealH1BlochTest
  rw [centeredPlaneBlochRealH1Field_gradient]
  exact (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm_apply_apply _

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The positive word reserve is paid pointwise by the full factorial gradient density. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeGradFactorialDensity {L : ℕ} (ρ : ℝ) (U : PlaneHk Set.univ (L + 1) E)
    (z : Vec 2) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), factorialWeight ρ j *
    ∑ w : DerivativeWord2 (j + 1), ‖planeJetOrder U (j + 1) w z‖ ^ 2

theorem planeGradFactorialDensity_nonneg {L : ℕ} (ρ : ℝ)
    (U : PlaneHk Set.univ (L + 1) E) (z : Vec 2) : 0 ≤ planeGradFactorialDensity ρ U z :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (factorialWeight_nonneg _ _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem planeFactorialDensity_orders_eq {K : ℕ} (ρ : ℝ)
    (U : PlaneHk Set.univ K E) (z : Vec 2) :
    planeFactorialDensity ρ U z = ∑ j ∈ Finset.range (K + 1), factorialWeight ρ j *
      ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w z‖ ^ 2 := by
  unfold planeFactorialDensity
  rw [Fintype.sum_sigma]
  simp_rw [← Finset.mul_sum]
  exact Fin.sum_univ_eq_sum_range (fun j => factorialWeight ρ j *
    ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w z‖ ^ 2) (K + 1)

theorem derivativeSourceOperator_density_le {K L r : ℕ}
    (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (ρ : ℝ) (hρ : 0 < ρ) (U : PlaneHk Set.univ (L + 1) E) (z : Vec 2) :
    planeFactorialDensity ρ (Weighted.derivativeSourceOperator hKL I U) z ≤
      (derivativeReserveFactor ρ K (r - 1)) ^ 2 * planeGradFactorialDensity ρ U z := by
  let G := fun j : ℕ => ∑ w : DerivativeWord2 (j + 1), ‖planeJetOrder U (j + 1) w z‖ ^ 2
  have hG (j : ℕ) : 0 ≤ G j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      factorialWeight ρ j * ∑ w : DerivativeWord2 j,
        ‖planeJetOrder (Weighted.derivativeSourceOperator hKL I U) j w z‖ ^ 2 ≤
      (derivativeReserveFactor ρ K (r - 1)) ^ 2 *
        (factorialWeight ρ (j + (r - 1)) * G (j + (r - 1))) := by
    have hjK := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hw : (∑ w : DerivativeWord2 j,
        ‖planeJetOrder (Weighted.derivativeSourceOperator hKL I U) j w z‖ ^ 2) ≤ G (j + (r - 1)) := by
      simp_rw [derivativeSourceOperator_word_readout hKL I U j hjK]
      have hh := sum_comp_le_sum_nonneg (fun w : DerivativeWord2 j => Fin.append I w)
        (sourceWordAppend_injective I)
        (fun w : DerivativeWord2 (r + j) => ‖planeJetOrder U (r + j) w z‖ ^ 2)
        (fun _ => sq_nonneg _)
      have he : r + j = j + (r - 1) + 1 := by omega
      dsimp only [G]
      conv_rhs => rw [← he]
      exact hh
    have hh := mul_le_mul (factorialWeight_reserve_le ρ hρ hjK (r - 1)) hw
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (factorialWeight_nonneg _ _))
    simpa only [mul_assoc, factorialWeight] using hh
  rw [planeFactorialDensity_orders_eq]
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), (derivativeReserveFactor ρ K (r - 1)) ^ 2 *
        (factorialWeight ρ (j + (r - 1)) * G (j + (r - 1))) := Finset.sum_le_sum ht
    _ = (derivativeReserveFactor ρ K (r - 1)) ^ 2 *
        ∑ j ∈ Finset.range (K + 1), factorialWeight ρ (j + (r - 1)) * G (j + (r - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      dsimp only [planeGradFactorialDensity]
      have hs := Finset.sum_image (s := Finset.range (K + 1))
        (g := fun j : ℕ => j + (r - 1)) (f := fun j => factorialWeight ρ j * G j)
        (by intro a _ b _ hab; exact Nat.add_right_cancel hab)
      rw [← hs]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        have := Finset.mem_range.mp hk
        apply Finset.mem_range.mpr
        omega
      · intro j _ _
        exact mul_nonneg (factorialWeight_nonneg _ _) (hG j)

end AVRegularity.CycleWords
end
