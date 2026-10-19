-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleDamping.BandHighDecay
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
public import AVRegularity.CycleDamping.Graph.FibreCoefficientGraph
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.ChartTestTransport
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Exact normalized reference tensor, expressed using the public raw-jet bridge matrix. -/

/-- Any raw realization of the normalized reference trace has bridge tensor exactly `J/B`. -/
theorem reference_bridge_exact {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (y₀ : Vec 2) (t : ℝ) (χ : Fin 2 → ℝ → RawJet2 1 ℂ)
    (hχ : ∀ j, cellValue (χ j) t =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => (cellReferenceValue α q Λ ζ m ν B y₀ t z j : ℂ)) (i j : Fin 2) :
    fibreBridgeMatrix (ν / B) (fun _ => 1) (ocCellDrift α q Λ ζ m ν y₀) χ t i j =
      ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B : ℝ) : ℂ) := by
  have hm (i j : Fin 2) :
      cellMean (fun z => ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z i : ℝ) : ℂ) *
        cellValue (χ j) t z) =
      ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B -
        (ν / B) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ) := by
    have hf := cell_reference_flux (α := α) (q := q) (m := m) hΛ hζ hν hB y₀ t i j
    have he : (∫ z in AVenhance.unitCube,
        (Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z i) *
          cellReferenceValue α q Λ ζ m ν B y₀ t z j) =
        ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B -
          (ν / B) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by linarith only [hf]
    calc
      _ = ∫ z in AVenhance.unitCube,
          (((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z i) *
            cellReferenceValue α q Λ ζ m ν B y₀ t z j : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hχ j] with z hz
        simp only [hz, Complex.ofReal_mul]
      _ = _ := by rw [integral_complex_ofReal, he]
  have hsym : ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) j i =
      ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j := by
    have hd := CycleReference.refFlux_diagonal (α := α) (q := q) (m := m)
      hΛ hζ hν (t := ocEll q Λ m ν ^ 2 * t)
    fin_cases i <;> fin_cases j <;> norm_num [hd.1, hd.2]
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℝ) j i =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by simp only [Matrix.one_apply, eq_comm]
  unfold fibreBridgeMatrix
  rw [hm i j, hm j i, hsym, hone]
  push_cast
  ring

/-! Actual admissible-window quadratic coercivity of the corrector bridge. -/

theorem bridge_quadratic_admissible_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B Θ θ ta T : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hΘ : 0 ≤ Θ)
    (hI : IsOCAdmissibleInterval α q Λ ζ m ν B Θ θ ta T)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ) (x : Vec 2) (δ : ℝ) (hδ : 0 ≤ δ)
    (hint : IntervalIntegrable (fun t => -(∑ i, ∑ j,
      (x i : ℂ) * fibreBridgeMatrix (ν / B) G v χ t i j * (x j : ℂ))) volume
        (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2))
    (herr : ∀ t i j, ‖fibreBridgeMatrix (ν / B) G v χ t i j -
      ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B : ℝ) : ℂ)‖ ≤ δ) :
    (∫ t in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
      -(∑ i, ∑ j, (x i : ℂ) * fibreBridgeMatrix (ν / B) G v χ t i j * (x j : ℂ))).re ≤
      -((1 - Real.exp (-2)) / 288 - 2 * δ) *
        (T / ocEll q Λ m ν ^ 2) * vecDot x x := by
  let J : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t i j => ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B
  have he (t : ℝ) : vecDot x ((J t).mulVec x) =
      vecDot x ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t)).mulVec x) / B := by
    simp only [J, vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hj : IntervalIntegrable (fun t => vecDot x ((J t).mulVec x)) volume
      (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) := by
    simpa only [he] using normalized_refFlux_quadratic_intervalIntegrable hΛ hζ hν B x
      (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2)
  have hlen : 0 < ocEll q Λ m ν ^ 2 := by
    rw [CycleReference.ocEll_sq_eq hν]
    have hp := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    positivity
  have hT := mul_nonneg (hΘ.trans hI.2.1) hlen.le
  rw [div_mul_cancel₀ _ hlen.ne'] at hT
  have ht : ta / ocEll q Λ m ν ^ 2 ≤ (ta + T) / ocEll q Λ m ν ^ 2 := by
    apply div_le_div_of_nonneg_right _ hlen.le
    linarith only [hT]
  have hd : (ta + T) / ocEll q Λ m ν ^ 2 - ta / ocEll q Λ m ν ^ 2 =
      T / ocEll q Λ m ν ^ 2 := by ring
  have hc := admissible_cell_flux_coercivity hΛ hν hB hI x
  simp_rw [← he] at hc
  have hh := quadratic_integral_of_entry_error
    (fun t => fibreBridgeMatrix (ν / B) G v χ t) J x
    (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2)
    ((1 - Real.exp (-2)) / 288) δ ht hδ hint hj
    (fun t _ i j => herr t i j) (by simpa only [hd] using hc)
  simpa only [hd] using hh

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Existence of the actual all-time correctors of the constructed weighted drift. -/

theorem constructed_correctors {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ : Vec 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) :
    ∃ χ : Fin 2 → ℝ → RawJet2 1 ℂ,
      ∀ j, IsCellInverseValue ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
        (fun t => cellQ0 (fun x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
          ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) (χ j) := by
  classical
  have hv := ocCellDrift_isCellDrift (α := α) (q := q) (m := m) hΛ hζ ν y₀
  have hz : cellUlNorm Set.univ (fun (_ : ℝ) (_ : Vec 2) =>
      (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) < ⊤ := by
    simp [cellUlNorm, cellL2Norm]
  have hh (j : Fin 2) : ∃ D : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
        (fun t => cellQ0 (fun x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
          ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) D := by
    have hm := (cellForcing_joint_continuous (α := α) (q := q) (m := m) hΛ hζ ν (ocMeanFlux α q Λ ζ m ν) y₀ j).measurable
    have hf := (cellForcing_ul_uniform_bound hΛ hζ hν hr y₀ j).trans_lt ENNReal.ofReal_lt_top
    obtain ⟨D, hD, _, _⟩ := cellAllTimeInverse_exists_unique hG hv
      (fun t x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
        ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)) (fun _ _ => 0)
      hm measurable_const hf hz
    exact ⟨D, hD⟩
  choose χ hχ using hh
  exact ⟨χ, hχ⟩

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! The genuine identity-metric inverse differs from the reference by the switching source budget. -/

theorem identity_inverse_reference_error {α q : ℝ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, 1 ≤ Λ → ∀ m : ℕ, ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m → ∀ y₀ : Vec 2, ∀ j : Fin 2,
      ∀ χ : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨fun _ _ => 1, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
        (fun t => cellQ0 (fun x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
          ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) χ →
      cellEnergyNorm Set.univ
        (cellReferenceJet α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ j - χ) ≤
      ENNReal.ofReal (C * (ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)))) := by
  obtain ⟨C, hC, hb⟩ := cellSwitchResidual_ul_bound (α := α) (q := q) hζ
  refine ⟨13 * C, mul_pos (by norm_num) hC, ?_⟩
  intro Λ hΛ m ν hν hr y₀ j χ hχ
  let B := ocMeanFlux α q Λ ζ m ν
  let f : ℝ → Vec 2 → ℂ := fun t x => ((Real.sqrt (ν / B) *
    ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)
  let e : ℝ → Vec 2 → ℂ := fun t x => ((cellSwitchResidual α q Λ ζ m ν B y₀ t x j : ℝ) : ℂ)
  let g := f + e
  have hc : Continuous (Function.uncurry f) := cellForcing_joint_continuous hΛ hζ ν B y₀ j
  have he : Continuous (Function.uncurry e) := Complex.continuous_ofReal.comp
    (cellSwitchResidual_component_continuous hΛ hζ hν B y₀ j)
  have hgm : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
    simpa only [g, Function.uncurry_def, Pi.add_def] using hc.aestronglyMeasurable.add he.aestronglyMeasurable
  have hf : cellUlNorm Set.univ f < ⊤ := cellForcing_ul_finite hΛ hζ ν B y₀ j
  have heb : cellUlNorm Set.univ e ≤ ENNReal.ofReal (C *
      (ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)))) :=
    hb Λ hΛ m ν hν hr y₀ j
  have hef := heb.trans_lt ENNReal.ofReal_lt_top
  have hg : cellUlNorm Set.univ g < ⊤ :=
    (CycleEvolution.cellUlNorm_add Set.univ f e hc.aestronglyMeasurable he.aestronglyMeasurable).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hf, hef⟩)
  have hE : IsCellInverseValue ⟨fun _ _ => 1, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
      (fun t => cellQ0 (g t)) (fun _ _ => 0)
      (cellReferenceJet α q Λ ζ m ν B y₀ j) := by
    have heq : (fun t => cellQ0 (g t)) = fun t x =>
        ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
          cellSwitchResidual α q Λ ζ m ν B y₀ t x j : ℝ) : ℂ) := by
      funext t
      have hg' : g t = fun x => ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
        cellSwitchResidual α q Λ ζ m ν B y₀ t x j : ℝ) : ℂ) := by
        funext x
        exact (Complex.ofReal_add _ _).symm
      rw [hg', cellReferenceSource_q0 hΛ hζ hν]
    rw [heq]
    exact cellReferenceJet_isCellInverse hΛ hζ hν hr y₀ j
  have hz : cellUlNorm Set.univ (fun (_ : ℝ) (_ : Vec 2) => (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) = 0 := by
    simp [cellUlNorm, cellL2Norm]
  have ht := CycleEvolution.cellInverse_parameter_bound identity_isCellMetric identity_isCellMetric
    (ocCellDrift_isCellDrift hΛ hζ ν y₀) f g (fun _ _ => 0) (fun _ _ => 0) χ
    (cellReferenceJet α q Λ ζ m ν B y₀ j) hc.aestronglyMeasurable hgm
    aestronglyMeasurable_const aestronglyMeasurable_const hf hg
    (by rw [hz]; exact ENNReal.zero_lt_top) (by rw [hz]; exact ENNReal.zero_lt_top) hχ hE
  have hgf : g - f = e := by dsimp [g]; abel
  rw [hgf] at ht
  have hz0 : cellUlNorm Set.univ (0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) = 0 := by
    simpa only [Pi.zero_def] using hz
  have hmz : cellMetricSupNorm (0 : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    simp [cellMetricSupNorm]
  simp only [sub_self, hmz, hz0, mul_zero, zero_mul, add_zero] at ht
  apply ht.trans
  calc
    _ ≤ ENNReal.ofReal 13 * ENNReal.ofReal (C * (ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)))) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 13)]
      congr 1
      ring

/-! The actual metric corrector has a uniform energy distance from the reference corrector. -/

theorem corrector_reference_energy_error {α q : ℝ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, 1 ≤ Λ → ∀ m : ℕ, ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m → ∀ y₀ : Vec 2,
      ∀ G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ, IsCellMetric G →
      ∀ g : ℝ, 0 ≤ g → IsMetricNearIdentity G g → ∀ j : Fin 2,
      ∀ χ : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨G, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
        (fun t => cellQ0 (fun x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
          ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) χ →
      cellEnergyNorm Set.univ
        (cellReferenceJet α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ j - χ) ≤
      ENNReal.ofReal (C * (g + ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)))) := by
  obtain ⟨Cs, hCs, hsw⟩ := identity_inverse_reference_error (α := α) (q := q) hζ
  let W := 2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96))
  let C := 338 * W + Cs + 1
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Λ hΛ m ν hν hr y₀ G hG g hg hnear j χ hχ
  let B := ocMeanFlux α q Λ ζ m ν
  let f : ℝ → Vec 2 → ℂ := fun t x => ((Real.sqrt (ν / B) *
    ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)
  let d := ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
    Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2))
  have hd : 0 ≤ d := by
    have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    dsimp [d]; positivity
  have hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) :=
    (cellForcing_joint_continuous (α := α) (q := q) (m := m) hΛ hζ ν B y₀ j).aestronglyMeasurable
  have hfb : cellUlNorm Set.univ f ≤ ENNReal.ofReal W := cellForcing_ul_uniform_bound hΛ hζ hν hr y₀ j
  have hf := hfb.trans_lt ENNReal.ofReal_lt_top
  have hz : cellUlNorm Set.univ (fun (_ : ℝ) (_ : Vec 2) =>
      (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) < ⊤ := by
    simp [cellUlNorm, cellL2Norm]
  obtain ⟨I, hI, _⟩ := CycleEvolution.cellAllTimeInverse_exists_bound_ae identity_isCellMetric
    (ocCellDrift_isCellDrift hΛ hζ ν y₀) f (fun _ _ => 0) hfm aestronglyMeasurable_const hf hz
  have hm := metric_inverse_difference_bound hG hnear (ocCellDrift_isCellDrift hΛ hζ ν y₀)
    f hfm hf χ I hχ hI
  have hmb : cellEnergyNorm Set.univ (I - χ) ≤ ENNReal.ofReal (338 * W * g) := by
    apply hm.trans
    calc
      _ ≤ ENNReal.ofReal 13 * (2 * ENNReal.ofReal g *
          (ENNReal.ofReal 13 * ENNReal.ofReal W)) := by gcongr
      _ = _ := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 13),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 13)]
        congr 1
        ring
  have hs : cellEnergyNorm Set.univ (cellReferenceJet α q Λ ζ m ν B y₀ j - I) ≤
      ENNReal.ofReal (Cs * d) := hsw Λ hΛ m ν hν hr y₀ j I hI
  have hR := cellReferenceJet_isCellInverse hΛ hζ hν hr y₀ j
  have ht := CycleEvolution.cellEnergyNorm_sub_triangle Set.univ
    (cellReferenceJet α q Λ ζ m ν B y₀ j) I χ
    hR.1.2.2.2.1 hI.1.2.2.2.1 hχ.1.2.2.2.1
  apply (ht.trans (add_le_add hs hmb)).trans
  rw [← ENNReal.ofReal_add (mul_nonneg hCs.le hd) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    Cs * d + 338 * W * g ≤ C * d + C * g := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ hd
        dsimp [C]; linarith only [hW]
      · apply mul_le_mul_of_nonneg_right _ hg
        dsimp [C]; linarith only [hCs]
    _ = C * (g + d) := by ring

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! The actual constructed bridge tensor differs from J/B by O(g + d_sw). -/

theorem constructed_bridge_error {α q : ℝ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, 1 ≤ Λ → ∀ m : ℕ, ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m → ∀ y₀ : Vec 2,
      ∀ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ, IsCellMetric (fun t _ => G t) →
      ∀ g : ℝ, 0 ≤ g → IsMetricNearIdentity (fun t _ => G t) g →
      ∀ χ : Fin 2 → ℝ → RawJet2 1 ℂ,
      (∀ j, IsCellInverseValue ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
        (fun t => cellQ0 (fun x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
          ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) (χ j)) →
      ∀ t : ℝ, ∀ i j : Fin 2,
      ‖fibreBridgeMatrix (ν / ocMeanFlux α q Λ ζ m ν) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j -
        ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j /
          ocMeanFlux α q Λ ζ m ν : ℝ) : ℂ)‖ ≤
      C * (g + ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2))) := by
  obtain ⟨Ce, hCe, he⟩ := corrector_reference_energy_error (α := α) (q := q) hζ
  let W := 2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨1 + W * Ce, by positivity, ?_⟩
  intro Λ hΛ m ν hν hr y₀ G hG g hg hnear χ hχ t i j
  let B := ocMeanFlux α q Λ ζ m ν
  let d := ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
    Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2))
  have hνB : ν ≤ B := CycleReference.meanFlux_ge_input hΛ hζ hν
  have hB : 0 < B := hν.trans_le hνB
  have hd : 0 ≤ d := by
    have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    dsimp [d]; positivity
  let Ψ : Fin 2 → ℝ → RawJet2 1 ℂ := fun k => cellReferenceJet α q Λ ζ m ν B y₀ k
  have hE (k : Fin 2) : cellL2Norm (cellValue (Ψ k) t - cellValue (χ k) t) ≤
      ENNReal.ofReal (Ce * (g + d)) :=
    (CycleEvolution.cellValue_cellL2Norm_le_energy (Ψ k - χ k) t).trans
      (he Λ hΛ m ν hν hr y₀ (fun t _ => G t) hG g hg hnear k (χ k) (hχ k))
  have hvm (k : Fin 2) : Measurable (fun x => ((Real.sqrt (ν / B) *
      ocCellDrift α q Λ ζ m ν y₀ t x k : ℝ) : ℂ)) :=
    ((cellForcing_joint_continuous hΛ hζ ν B y₀ k).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hv (k : Fin 2) (x : Vec 2) : ‖((Real.sqrt (ν / B) *
      ocCellDrift α q Λ ζ m ν y₀ t x k : ℝ) : ℂ)‖ ≤ W := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact cellForcing_component_uniform_bound hΛ hζ hν hr y₀ x t k
  have hb := bridge_entry_difference_bound (ν / B) g W (Ce * (g + d))
    (div_nonneg hν.le hB.le) ((div_le_one hB).mpr hνB) hg hW (by positivity)
    G (ocCellDrift α q Λ ζ m ν y₀) χ Ψ t
    (fun a b => metric_entry_error hG hnear t 0 a b) hvm hv
    (fun k => ((hχ k).1.2.2.1 t (Set.mem_univ t)).1)
    (fun k => cellReferenceJet_value_memLp hΛ ν B t y₀ k) hE i j
  have hJ := reference_bridge_exact hΛ hζ hν hB y₀ t Ψ
    (fun k => Filter.Eventually.of_forall (fun x => cellReferenceJet_value α q Λ ζ m ν B y₀ k t x)) i j
  rw [hJ] at hb
  apply hb.trans
  calc
    g + W * (Ce * (g + d)) ≤ (g + d) + W * (Ce * (g + d)) :=
      add_le_add (show g ≤ g + d from le_add_of_nonneg_right hd) le_rfl
    _ = (1 + W * Ce) * (g + d) := by ring

end AVRegularity.CycleDamping
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Uniform bridge error with exactly the band-chain parameters. -/

theorem bandChain_bridge_error {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
      ∀ y₀ : Vec 2, ∀ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      IsCellMetric (fun t _ => G t) → ∀ g : ℝ, 0 ≤ g →
      IsMetricNearIdentity (fun t _ => G t) g →
      ∀ χ : Fin 2 → ℝ → RawJet2 1 ℂ,
      (∀ j, IsCellInverseValue ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
        (fun t => cellQ0 (fun x => ((Real.sqrt (ν / B) *
          ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) (χ j)) →
      ∀ t : ℝ, ∀ i j : Fin 2,
      ‖fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j -
        ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B : ℝ) : ℂ)‖ ≤
      C * (g + ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2))) := by
  obtain ⟨L, hL, hr⟩ := bandChain_relaxation_large hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  obtain ⟨C, hC, hb⟩ := constructed_bridge_error (α := α) (q := q) hζ
  refine ⟨L, hL, C, hC, ?_⟩
  intro Λ hΛ M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG g hg hnear χ hχ t i j
  have hΛ1 : 1 ≤ Λ := by omega
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hB : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hκ.2 m (by omega) hmM, hνeq]
  rw [hB] at hχ ⊢
  exact hb Λ hΛ1 m ν hν (hνeq ▸ hr Λ hΛ M κ hκ m hm hmM)
    y₀ G hG g hg hnear χ hχ t i j

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Uniform integrated quadratic damping for the actual constructed band-chain correctors. -/

theorem bandChain_quadratic_damping {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
      ∀ y₀ : Vec 2, ∀ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      IsCellMetric (fun t _ => G t) → ∀ g : ℝ, 0 ≤ g → g ≤ g₀ →
      IsMetricNearIdentity (fun t _ => G t) g →
      ∀ χ : Fin 2 → ℝ → RawJet2 1 ℂ,
      (∀ j, IsCellInverseValue ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
        (fun t => cellQ0 (fun x => ((Real.sqrt (ν / B) *
          ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) (χ j)) →
      ∀ Θ θ ta T : ℝ, 0 ≤ Θ → IsOCAdmissibleInterval α q Λ ζ m ν B Θ θ ta T →
      ∀ x : Vec 2,
      (∫ t in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
        -(∑ i, ∑ j, (x i : ℂ) *
          fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j * (x j : ℂ))).re ≤
        -(3 * ((1 - Real.exp (-2)) / 288) / 4) *
          (T / ocEll q Λ m ν ^ 2) * vecDot x x := by
  obtain ⟨L, hL, C, hC, hb⟩ := bandChain_bridge_error hα₀ hα₁ hs₀ hs₁ hq hζ
  let c := (1 - Real.exp (-2)) / 288
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))) (by norm_num)
  let g₀ := c / (16 * C)
  have hg₀ : 0 < g₀ := div_pos hc (mul_pos (by norm_num) hC)
  obtain ⟨K, hK, hk⟩ := bandChain_memory_ratio_small hα₀ hα₁ hs₀ hs₁ hq hζ g₀ hg₀
  obtain ⟨R, hR, hr⟩ := bandChain_relaxation_large hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  refine ⟨max L (max K R), hL.trans (le_max_left _ _), g₀, hg₀, ?_⟩
  intro Λ hΛ M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG g hg hgg hnear χ hχ Θ θ ta T hΘ hI x
  have hΛL := (le_max_left L (max K R)).trans hΛ
  have hΛK := (le_max_left K R).trans ((le_max_right L (max K R)).trans hΛ)
  have hΛR := (le_max_right K R).trans ((le_max_right L (max K R)).trans hΛ)
  have hΛ1 : 1 ≤ Λ := by omega
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hB : 0 < B := hBeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ (by omega)
  have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hκ.2 m (by omega) hmM, hνeq]
  let d := ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
    Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2))
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hds : d ≤ g₀ := (switch_error_le_memory_ratio (q := q) (m := m) (ν := ν) hΛ1).trans
    (hνeq ▸ hk Λ hΛK M κ hκ m hm hmM)
  have hδ : C * (g + d) ≤ c / 8 := by
    have he := mul_le_mul_of_nonneg_left (add_le_add hgg hds) hC.le
    have hh : C * (g₀ + g₀) = c / 8 := by dsimp only [g₀]; field_simp; ring
    exact he.trans_eq hh
  have hrel : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m := hνeq ▸ hr Λ hΛR M κ hκ m hm hmM
  let W := 2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96))
  have hwm (j : Fin 2) : Measurable (fun p : ℝ × Vec 2 =>
      ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ p.1 p.2 j : ℝ) : ℂ)) :=
    (cellForcing_joint_continuous hΛ1 hζ ν B y₀ j).measurable
  have hw (t : ℝ) (z : Vec 2) (j : Fin 2) :
      ‖((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z j : ℝ) : ℂ)‖ ≤ W := by
    rw [Complex.norm_real, Real.norm_eq_abs, hBmean]
    exact cellForcing_component_uniform_bound hΛ1 hζ hν hrel y₀ z t j
  have hi := bridge_quadratic_intervalIntegrable (ν / B) W (by dsimp only [W]; positivity)
    hG _ hwm hw χ hχ (fun j => (x j : ℂ))
    (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2)
  have hquad := bridge_quadratic_admissible_bound hΛ1 hζ hν hB hΘ hI G
    (ocCellDrift α q Λ ζ m ν y₀) χ x (C * (g + d)) (by positivity) hi
    (fun t i j => hb Λ hΛL M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG g hg hnear χ hχ t i j)
  have hS : 0 ≤ T / ocEll q Λ m ν ^ 2 := hΘ.trans hI.2.1
  have hx : 0 ≤ vecDot x x := by
    simp only [vecDot, Fin.sum_univ_two]
    nlinarith only [sq_nonneg (x 0), sq_nonneg (x 1)]
  have hbudget := mul_le_mul_of_nonneg_right hδ (mul_nonneg hS hx)
  dsimp only [c] at hbudget
  nlinarith only [hquad, hbudget]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! The actual canonical degree-two symbol has uniform admissible-interval damping. -/

theorem bandChain_canonical_quadratic_damping {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
        (hG : IsCellMetric (fun t _ => G t)),
      0 ≤ g → g ≤ g₀ → IsMetricNearIdentity (fun t _ => G t) g →
      ∀ Cw : ℝ, ∀ hη : ν / B ≤ 1,
      ∀ hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀),
      ∀ hw : ∀ t x, Real.sqrt (ν / B) *
        Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw,
      ∀ Θ θ ta T : ℝ, 0 ≤ Θ → IsOCAdmissibleInterval α q Λ ζ m ν B Θ θ ta T →
      ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) →
      (∫ t in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
        fibreHomogeneous (canonicalSymbol (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
          (fibreCoefficientFamily (ν / B) Cw hη G hG hv hw)) ξ 2 t).re ≤
        -(3 * ((1 - Real.exp (-2)) / 288) / 4) *
          (T / ocEll q Λ m ν ^ 2) * fibreNorm ξ ^ 2 := by
  obtain ⟨Λ₀, hΛ₀, g₀, hg₀, hquad⟩ := bandChain_quadratic_damping hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, g₀, hg₀, ?_⟩
  intro Λ hΛ M κ hκ m hm hmM ν B hνeq hBeq y₀ G g hG hg hgg hnear Cw hη hv hw Θ θ ta T hΘ hadm ξ hξ
  let r := fibreCoefficientFamily (ν / B) Cw hη G hG hv hw
  let χ := canonicalCorrector r
  have hχ (j : Fin 2) := canonicalCorrector_isInverse (ν / B) Cw hη G hG hv hw j
  have he := hquad Λ hΛ M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG g hg hgg hnear
    χ hχ Θ θ ta T hΘ hadm (fun i => (ξ i).re)
  have hid : (fun t => fibreHomogeneous (canonicalSymbol (ν / B) G
      (ocCellDrift α q Λ ζ m ν y₀) r) ξ 2 t) =
      fun t => -(∑ i, ∑ j, ((ξ i).re : ℂ) *
        fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j * ((ξ j).re : ℂ)) := by
    funext t
    rw [canonicalSymbol_quadratic_bridge (ν / B) Cw hη G hG hv hw χ hχ ξ t]
    congr 1
    exact congrArg (fun z : Fin 2 → ℂ => ∑ i, ∑ j,
      z i * fibreBridgeMatrix (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) χ t i j * z j)
      (real_frequency_eq ξ hξ)
  rw [hid, real_frequency_norm_sq ξ hξ]
  exact he

/-! A genuine canonical graph for the constructed pulse drift, with its bridge identity. -/

def constructedGraphBudget : ℝ :=
  Real.sqrt 2 * (2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)))

theorem constructedGraphBudget_pos : 0 < constructedGraphBudget := by
  have he : 1 - Real.exp (-2) > 0 := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  unfold constructedGraphBudget
  positivity

def constructedGraphRadius : ℝ := fibreCoefficientMajorantRadius constructedGraphBudget

def constructedGraphBound : ℝ := Graph.fibreCoefficientGraphBound constructedGraphBudget

theorem constructedGraphRadius_pos : 0 < constructedGraphRadius :=
  fibreCoefficientMajorantRadius_pos constructedGraphBudget_pos.le

theorem constructedGraphBound_pos : 0 < constructedGraphBound := by
  unfold constructedGraphBound Graph.fibreCoefficientGraphBound
  have hR := constructedGraphRadius_pos
  change 0 < 2 * constructedGraphRadius⁻¹ + (6 * constructedGraphBudget + 24) + 2
  have hW := constructedGraphBudget_pos
  positivity

theorem constructed_canonical_graph {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ : Vec 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) :
    ∃ (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ),
      IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G (ocCellDrift α q Λ ζ m ν y₀)
        constructedGraphRadius constructedGraphBound r lam ∧
      (∀ p, AEStronglyMeasurable (lam p) volume) ∧
      ∀ χ : Fin 2 → ℝ → RawJet2 1 ℂ,
        (∀ j, IsCellInverseValue ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
          (fun t => cellQ0 (fun x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
            ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ))) (fun _ _ => 0) (χ j)) →
        ∀ ξ t, fibreHomogeneous lam ξ 2 t =
          -(∑ i, ∑ j, ξ i * fibreBridgeMatrix (ν / ocMeanFlux α q Λ ζ m ν) G
            (ocCellDrift α q Λ ζ m ν y₀) χ t i j * ξ j) := by
  let B := ocMeanFlux α q Λ ζ m ν
  have hB : 0 < B := hν.trans_le (CycleReference.meanFlux_ge_input hΛ hζ hν)
  have hη : ν / B ≤ 1 := (div_le_one hB).mpr (CycleReference.meanFlux_ge_input hΛ hζ hν)
  have hv := ocCellDrift_isCellDrift (α := α) (q := q) (m := m) hΛ hζ ν y₀
  have hw : ∀ t x, Real.sqrt (ν / B) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ constructedGraphBudget :=
    fun t x => ocCellDrift_weighted_uniform_bound hΛ hζ hν hr y₀ x t
  let r := fibreCoefficientFamily (ν / B) constructedGraphBudget hη G hG hv hw
  let lam := canonicalSymbol (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) r
  refine ⟨r, lam, ?_, ?_, ?_⟩
  · exact Graph.fibreCoefficientFamily_isFibreGraph (ν / B) constructedGraphBudget
      (div_pos hν hB).le hη constructedGraphBudget_pos.le G hG hv hw
  · intro p
    exact canonicalSymbol_aestronglyMeasurable _ _ hη G hG hv hw p
  · intro χ hχ ξ t
    exact canonicalSymbol_quadratic_bridge _ _ hη G hG hv hw χ hχ ξ t

end AVRegularity.CycleDamping
end
