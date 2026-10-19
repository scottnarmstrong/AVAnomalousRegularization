-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.Multiset
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
import AVRegularity.External.FourierCarrierParseval
public import AVRegularity.CycleWords.MixedWords.Discard.BlochBridge
import AVRegularity.CycleWords.MixedWords.Discard.Combine
import AVRegularity.CycleWords.MixedWords.Discard.Letter
import AVenhance.Infra.Section5.AnalyticBridge.Sobolev
import AVRegularity.CycleWords.MixedWords.B1WRepresentation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Combinatorics.SimpleGraph.Basic

section
section
/-! # The marks kernel

At a real frequency of the zone with `|θ| ≥ ξ_lo √η`, the high-band decay by marks of the scalar
package makes `κ(r, s) = 2^{-n(r,s)}`, `n` the number of complete marks of the orientation chosen by
`high_marks` inside `[r, s]`, an `L²` decay kernel of the homogeneous fibre equation: the
package's raw solutions are the Hilbert curves (`cellWeakHilbert_exists_raw_solution`), `contraction`
gives monotonicity of the norm and `high_marks` the halving across a mark. The loss
constants are `A = 2^{2 N}`, `N = ⌊1/θ_s⌋ + 1`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

/-- A homogeneous Hilbert curve at the real shift `θ` is a raw solution of the fibre equation at
`ξ = θ/√η` with the same traces. -/
theorem curve_to_raw {η : ℝ} (hη : 0 < η) {a b : ℝ} (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice t) 0 0)) :
    ∃ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc a b) (fibreCoefficients η G v (planeFibreFrequency η θ) (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D ∧
      ∀ t, cellL2Norm (cellValue D t) = ENNReal.ofReal ‖u t‖ := by
  have hC : fibreCoefficients η G v (planeFibreFrequency η θ) (fun _ => 0) =
      (⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ : CellCoefficients) := by
    have := fibreShift_eq hη θ
    unfold fibreCoefficients
    congr 1
    funext t; simp
  rw [hC]
  obtain ⟨D, hD, hae⟩ := cellWeakHilbert_exists_raw_solution
    (⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ : CellCoefficients) hG V hv.1 hb
    (fun _ _ => 0) (fun _ _ => 0) MemLp.zero MemLp.zero u slice (by
      simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
        show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using h)
  exact ⟨D, hD, fun t => cellL2Norm_eq_of_class _ _ (hae t)⟩


theorem one_le_A (θs : ℝ) : (1 : ℝ) ≤ 2 ^ (2 * shrinkLossConst θs) :=
  one_le_pow₀ (by norm_num)

theorem two_le_A (θs : ℝ) : (2 : ℝ) ≤ 2 ^ (2 * shrinkLossConst θs) := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by unfold shrinkLossConst; omega)

theorem half_pow_le {n : ℕ} {x : ℝ} (h : x ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ Real.exp (-(x * Real.log 2)) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : (1 / 2 : ℝ) ^ n = Real.exp (-((n : ℝ) * Real.log 2)) := by
    rw [one_div, ← Real.exp_log (by positivity : (0 : ℝ) < (2⁻¹) ^ n), Real.log_pow, Real.log_inv]
    ring_nf
  rw [this]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The marks kernel. -/
theorem marksKernel : MarksKernelStatement := by
  intro K
  classical
  set c : ℝ := if 0 < K.cadm ∧ 0 < K.θs then K.cadm * Real.log 2 / K.θs else 1 with hc
  refine ⟨2 ^ (2 * shrinkLossConst K.θs), c, one_le_A _, ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hc]
    split_ifs with h
    · exact div_pos (mul_pos h.1 h2) h.2
    · exact one_pos
  intro η t₀ S ϖ G v reg pkg hG hv V hb hη0 hη1 hS θ hθ hθlo
  obtain ⟨_, hξlo, _, _, _, hθs, hcadm, -⟩ := pkg.consts_pos
  have hcval : c = K.cadm * Real.log 2 / K.θs := by simp [hc, hcadm, hθs]
  set ξ : Fin 2 → ℂ := planeFibreFrequency η θ with hξ
  have hξim : ∀ i, (ξ i).im = 0 := fun i => planeFibreFrequency_im η θ i
  have hsq : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη0
  have hnorm : K.ξlo ≤ fibreNorm ξ := by
    rw [hξ, fibreNorm_planeFibreFrequency_eq_div hη0, le_div_iff₀ hsq]
    exact hθlo
  have hcube : ∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η := by
    intro i
    refine ⟨hξim i, ?_⟩
    simp only [hξ, planeFibreFrequency, Complex.ofReal_re, abs_div, abs_of_pos hsq]
    exact div_le_div_of_nonneg_right (hθ i) hsq.le
  obtain ⟨j, hj⟩ := pkg.high_marks ξ hcube hnorm
  have hsep := pkg.marks_sep j
  refine ⟨geometricMarkKernel (reg.marks j) K.θs, ⟨Ker_pos _ _, Ker_le_one _ _,
    Ker_self _ hθs, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r s t _ _ _ _
    exact (Ker_mul_le (reg.marks j) hsep).trans
      (mul_le_mul_of_nonneg_right (two_le_A _) (Ker_pos _ _ _ _).le)
  · intro r s t _ _ hst _
    exact (Ker_anti (reg.marks j) K.θs hst).trans
      (le_mul_of_one_le_left (Ker_pos _ _ _ _).le (one_le_A _))
  · intro r r' t' t _ _ h2 _ _ h5 _
    exact Ker_shrink (reg.marks j) hθs hsep h2 h5
  · intro r s hr hrs hs u slice hu
    -- the norm of the curve
    have hnormraw : ∀ x y, r ≤ x → y ≤ s → x ≤ y →
        ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution (Icc x y)
          (fibreCoefficients η G v ξ (fun _ => 0)) (fun _ _ => 0) (fun _ _ => 0) D ∧
          ∀ t, cellL2Norm (cellValue D t) = ENNReal.ofReal ‖u t‖ := by
      intro x y hx hy _
      exact curve_to_raw hη0 G hG hv V hb θ
        (hu.mono (Icc_subset_Icc hx hy))
    refine decay_marks (reg.marks j) hθs hsep (r₀ := r) (s₀ := s) (fun t => ‖u t‖) ?_ ?_
      le_rfl hrs le_rfl
    · intro x y hx hxy hy
      obtain ⟨D, hD, hn⟩ := hnormraw x y hx hy hxy
      have := pkg.contraction ξ hξim x y (by linarith) hxy (by linarith) D hD
      rw [hn, hn] at this
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp this
    · intro m hm hrm hms
      obtain ⟨D, hD, hn⟩ := hnormraw m (m + K.θs) hrm hms (by linarith)
      have := hj m hm D hD
      rw [hn, hn, ← ENNReal.ofReal_mul (by norm_num)] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
  · have hcount : Count (reg.marks j) K.θs t₀ (t₀ + S) = (reg.marks j).card := by
      unfold Count
      rw [Finset.filter_true_of_mem]
      intro m hm
      have := pkg.marks_in j m hm
      exact ⟨this.1, this.2⟩
    have hge := pkg.marks_count j
    calc geometricMarkKernel (reg.marks j) K.θs t₀ (t₀ + S)
        = (1 / 2 : ℝ) ^ (reg.marks j).card := by unfold geometricMarkKernel; rw [hcount]
      _ ≤ Real.exp (-(K.cadm * S / K.θs * Real.log 2)) := half_pow_le hge
      _ = Real.exp (-c * S) := by rw [hcval]; congr 1; ring
      _ ≤ 2 ^ (2 * shrinkLossConst K.θs) * Real.exp (-c * S) :=
        le_mul_of_one_le_left (Real.exp_pos _).le (one_le_A _)

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the tested source of a stage against a smooth test, and its extension to `H^1`

* `term'`: the scale ratio form of one term of the stage expansion.
* `smooth_source`: for a smooth periodic representative of an `H^1` test `z`, the cell source
  of a stage `i` of order `k` is the sum over the earlier stages of the scale ratio times the
  pairing of the stage value with the test transform (the facts of `b1w_stage_representation`
  without the transposed family).
* Two continuous functionals of `H^1` that agree on a sequence of smooth functions converging to
  `z` agree at `z`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

section Source

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The scale ratio form of one term of the stage expansion. -/
theorem term' (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (r : ℝ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (i i' : B1WIndex ι h Nw m Ks)
    (φ : Vec 2 → ℂ) (Xv : Vec 2 → ℂ)
    (hX : Xv =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
      b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y) :
    b1wScale F.π F.ϖ F.ηg F.letters i *
        ∫ y in AVenhance.unitCube, b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y =
      b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
        ∫ y in AVenhance.unitCube, Xv y * b1wTestTransform F θ i i' r φ y := by
  set c := b1wScale F.π F.ϖ F.ηg F.letters (Nw := Nw) (m := m) (Ks := Ks) with hc
  have hWT : (∫ y in AVenhance.unitCube, Xv y * b1wTestTransform F θ i i' r φ y) =
      c i' * ∫ y in AVenhance.unitCube, b1wStageVal F θ i' r y *
        b1wTestTransform F θ i i' r φ y := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hX] with y hy
    rw [hy]
    ring
  rw [hWT]
  unfold b1wScaleRatio
  by_cases hci : c i' = 0
  · by_cases hl : i'.1 ≤ i.1
    · have h0 : c i = 0 := b1wScale_eq_zero_of_le F.π F.ηg F.letters hπ hϖ i i' hl hci
      rw [← hc, h0, hci]
      simp
    · push Not at hl
      have hT0 : b1wTestTransform F θ i i' r φ = 0 :=
        b1wTestTransform_zero_of_level F θ i i' (ne_of_gt hl)
          (fun l hl' => by
            have h1 := hl'.1
            have h2 := hl'.2
            have : i'.1 < i.1 := by
              rw [h1, h2]
              exact Fin.castSucc_lt_succ
            exact absurd hl (not_lt.2 this.le)) r _
      rw [hT0]
      simp
  · rw [← hc]
    field_simp

/-- **The cell source of a stage against a smooth test**, in terms of the earlier stage values. -/
theorem smooth_source (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (θ : Vec 2) (r : ℝ) (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ)
    (Xv : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (hX : ∀ i', b1wSt i' < k → (Xv i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hFl : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (dmax : ℕ)
    (hExp : ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ (dmax + 1) φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      ∀ i', ¬ b1wSt i' < k → ∀ φ, b1wTestTransform F θ i i' r φ = 0)
    {i : B1WIndex ι h Nw m Ks} (hi : i ∈ stageSet b1wSt k) (z : TorusHk 1 ℂ) (ψ : Vec 2 → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hper : AVenhance.IsZ2Periodic ψ)
    (hzψ : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] ψ) :
    cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) z =
      ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
        b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          ∫ y in AVenhance.unitCube, (Xv i' : Vec 2 → ℂ) y *
            b1wTestTransform F θ i i' r (fun y => star (ψ y)) y := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hsψ : ContDiff ℝ (dmax + 1) (fun y => star (ψ y)) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp (hψ.of_le (by exact_mod_cast le_top))
  have hsper : AVenhance.IsZ2Periodic (fun y => star (ψ y)) := fun n x => by
    simp only [hper n x]
  rw [cellComplexSource_eq_testedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r _ (S i) (Fl i)
    (hS i hi) (hFl i hi) z ψ hψ1 hzψ, hExp i _ hsψ hsper, Finset.mul_sum]
  rw [sum_eq_sum_stages b1wSt k _ fun i' hi' => ?_]
  · refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr rfl fun i' hi' => ?_
    have hst : b1wSt i' < k := (Finset.mem_filter.1 hi').2 ▸ Finset.mem_range.1 hk'
    exact term' F θ r hπ hϖ i i' _ _ (hX i' hst)
  · rw [hearly i hi i' hi']
    simp

end Source

end AVRegularity.CycleWords.Discard
end
end

section
/-! # Parseval for a real `H^K` element, summed over words of length `≤ k`

For `g : TorusHk K ℝ` and `k ≤ K`:
`∑_n ∑_{a ≤ k} |2πn|^{2a} |ĝ(n)|² ≤ ‖g‖²` (as a `HasSum` with a bounded sum). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs

local instance BandRealMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance BandRealIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace AVRegularity.CycleWords.Discard

/-- The exact frequency square of the sum over the words of length `a`. -/
theorem word_sq_sum (K : ℕ) (g : TorusHk K ℝ) (a : ℕ) (ha : a ≤ K)
    (n : Fin 2 → ℤ) :
    ∑ w : DerivativeWord2 a, ‖realJetFourier K g ⟨⟨a, by omega⟩, w⟩ n‖ ^ 2 =
      (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a *
        ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 := by
  have hterm : ∀ w : DerivativeWord2 a,
      ‖realJetFourier K g ⟨⟨a, by omega⟩, w⟩ n‖ ^ 2 =
        (∏ j : Fin a, (2 * Real.pi * ((n (w j) : ℤ) : ℝ)) ^ 2) *
          ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 := by
    intro w
    have h2 : ((2 * Real.pi) ^ a) ^ 2 = ((2 * Real.pi) ^ 2) ^ a := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [realJetFourier_word_norm K g a ha w n, mul_pow, mul_pow, h2, ← Finset.prod_pow]
    have : ∀ j : Fin a, (2 * Real.pi * ((n (w j) : ℤ) : ℝ)) ^ 2 =
        (2 * Real.pi) ^ 2 * |((n (w j) : ℤ) : ℝ)| ^ 2 := by
      intro j; rw [mul_pow, sq_abs]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  congr 1
  have hh := Fintype.prod_sum
    (fun (_ : Fin a) (i : Fin 2) => (2 * Real.pi * (n i : ℝ)) ^ 2)
  simpa only [Finset.prod_const, Finset.card_fin] using hh.symm

/-- Parseval for the value and the jets of order `≤ k`, as a `HasSum` over the frequencies. -/
theorem real_hasSum (K k : ℕ) (hk : k ≤ K) (g : TorusHk K ℝ) :
    ∃ S : ℝ, S ≤ ‖g‖ ^ 2 ∧ HasSum (fun n : Fin 2 → ℤ =>
      ∑ a ∈ Finset.range (k + 1),
        (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a *
          ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2) S := by
  let F : JetIndex2 K → (Fin 2 → ℤ) → ℝ := fun j n =>
    if j.1.val ≤ k then ‖UnitAddTorus.mFourierCoeff
      (AVRegularity.External.torusJetComponentL2 g j) n‖ ^ 2 else 0
  let A : JetIndex2 K → ℝ := fun j => if j.1.val ≤ k then ‖g.val j‖ ^ 2 else 0
  have hsum := AVenhance.Infra.Torus.FourierCalculus.hasSum_finset_sum Finset.univ F A
    (fun j _ => by
      by_cases hj : j.1.val ≤ k
      · simpa only [F, A, hj, ite_true] using AVRegularity.External.torusJetComponentParseval g j
      · simpa only [F, A, hj, ite_false] using hasSum_zero)
  refine ⟨∑ j : JetIndex2 K, A j, ?_, ?_⟩
  · have hnorm : ‖g‖ ^ 2 = ∑ j : JetIndex2 K, ‖g.val j‖ ^ 2 := by
      have := PiLp.norm_sq_eq_of_L2 (fun _ : JetIndex2 K => ComponentL2
        (volume.restrict AVenhance.unitCube) ℝ) g.val
      exact this
    rw [hnorm]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j.1.val ≤ k
    · simp [A, hj]
    · simp [A, hj]
  · refine (hsum.congr_fun ?_)
    intro n
    change _ = ∑ j : JetIndex2 K, F j n
    rw [Fintype.sum_sigma]
    have hword : ∀ a : Fin (K + 1), ∑ w : DerivativeWord2 a.val, F ⟨a, w⟩ n =
        if a.val ≤ k then (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a.val *
          ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 else 0 := by
      intro a
      by_cases ha : a.val ≤ k
      · simp only [F, ha, ite_true]
        rw [← word_sq_sum K g a.val (by omega) n]
        apply Finset.sum_congr rfl
        intro w _
        simp only [realJetFourier, UnitAddTorus.mFourierBasis_repr]
        rfl
      · simp [F, ha]
    simp_rw [hword]
    rw [Fin.sum_univ_eq_sum_range (fun a => if a ≤ k then
      (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a *
        ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 else 0) (K + 1)]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega

/-- The shifted weighted Fourier sum of the value of a real `H^K` element. -/
theorem real_band (K k : ℕ) (hk : k ≤ K) (g : TorusHk K ℝ) (θ : Vec 2)
    (hθ : ∀ i, |θ i| ≤ Real.pi) :
    Summable (fun n : Fin 2 → ℤ =>
      (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2) ^ k *
        ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2) ∧
    ∑' n : Fin 2 → ℤ, (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2) ^ k *
        ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 ≤
      ((1 + 4 * Real.pi ^ 2) * 2) ^ k * ‖g‖ ^ 2 := by
  obtain ⟨S, hS, hsum⟩ := real_hasSum K k hk g
  have hle : ∀ n : Fin 2 → ℤ,
      (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2) ^ k *
        ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 ≤
      ((1 + 4 * Real.pi ^ 2) * 2) ^ k * ∑ a ∈ Finset.range (k + 1),
        (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a *
          ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 := by
    intro n
    rw [← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weight_le'' k n θ hθ) (sq_nonneg _)
  have hnn : ∀ n : Fin 2 → ℤ, 0 ≤ (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2) ^ k *
        ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 := fun n => by
    have : 0 ≤ ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    positivity
  have hsm : Summable (fun n : Fin 2 → ℤ =>
      ((1 + 4 * Real.pi ^ 2) * 2) ^ k * ∑ a ∈ Finset.range (k + 1),
        (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a *
          ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2) :=
    (hsum.mul_left _).summable
  have hs := Summable.of_nonneg_of_le hnn hle hsm
  refine ⟨hs, ?_⟩
  calc _ ≤ ∑' n : Fin 2 → ℤ, ((1 + 4 * Real.pi ^ 2) * 2) ^ k * ∑ a ∈ Finset.range (k + 1),
        (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a *
          ‖realJetFourier K g (valueIndex2 K) n‖ ^ 2 := hs.tsum_le_tsum hle hsm
    _ = ((1 + 4 * Real.pi ^ 2) * 2) ^ k * S := by rw [tsum_mul_left, hsum.tsum_eq]
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (by positivity)

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the dual of the weighted `ℓ²` norm on the cell modes

Testing a family of `L²` functions against finite sums of unit modes `quietHsMode` of `H^j`: the
weighted sum `∑_n ‖Ŵ(n)‖² / ‖e_n‖²_{H^j}` is at most `M²` when every test is bounded by `M` times
the `H^j` norm (`dual_tsum`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

local instance ModesMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem mode_value (s : ℕ) (n : Fin 2 → ℤ) (c : ℂ) :
    torusHkValueCLM (quietHsMode s n c) = c • scalarTorusToCell (UnitAddTorus.mFourierLp 2 n) := by
  have := quietHsMode_coordinate s n c (valueIndex2 s)
  rw [quietHsSymbol_value, mul_one] at this
  exact this

theorem torus_norm_sq {Λ : Finset (Fin 2 → ℤ)} (c : (Fin 2 → ℤ) → ℂ) :
    ‖∑ n ∈ Λ, c n • (UnitAddTorus.mFourierLp 2 n : ScalarTorusL2)‖ ^ 2 = ∑ n ∈ Λ, ‖c n‖ ^ 2 := by
  have h := (UnitAddTorus.orthonormal_mFourier (d := Fin 2)).inner_sum c c Λ
  have h2 := @inner_self_eq_norm_sq_to_K ℂ ScalarTorusL2 _ _ _
    (∑ n ∈ Λ, c n • (UnitAddTorus.mFourierLp 2 n : ScalarTorusL2))
  have h3 : ∑ n ∈ Λ, (starRingEnd ℂ) (c n) * c n = ((∑ n ∈ Λ, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp_rw [Complex.conj_mul']
  have h4 := h2.symm.trans (h.trans h3)
  have h5 : ((‖∑ n ∈ Λ, c n • (UnitAddTorus.mFourierLp 2 n : ScalarTorusL2)‖ ^ 2 : ℝ) : ℂ) = ((∑ n ∈ Λ, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h3, ← h]; push_cast; exact h2.symm
  exact Complex.ofReal_injective h5

/-- The squared `H^s` norm of the unit mode `e_n`. -/
def ModeNorm (s : ℕ) (n : Fin 2 → ℤ) : ℝ := ∑ a : JetIndex2 s, ‖quietHsSymbol n a‖ ^ 2

theorem hk_coord (s : ℕ) (Λ : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ) (a : JetIndex2 s) :
    (∑ n ∈ Λ, quietHsMode s n (c n)).val a =
      scalarTorusToCell (∑ n ∈ Λ, (c n * quietHsSymbol n a) • (UnitAddTorus.mFourierLp 2 n : ScalarTorusL2)) := by
  have h1 : (∑ n ∈ Λ, quietHsMode s n (c n)).val a = ∑ n ∈ Λ, (quietHsMode s n (c n)).val a := by
    simp
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [quietHsMode_coordinate, scalarTorusToCell_complex_smul]

theorem hk_norm_sq (s : ℕ) (Λ : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ) :
    ‖∑ n ∈ Λ, quietHsMode s n (c n)‖ ^ 2 = ∑ n ∈ Λ, ‖c n‖ ^ 2 * ModeNorm s n := by
  have h0 : ‖∑ n ∈ Λ, quietHsMode s n (c n)‖ ^ 2 =
      ∑ a : JetIndex2 s, ‖(∑ n ∈ Λ, quietHsMode s n (c n)).val a‖ ^ 2 := by
    change ‖(∑ n ∈ Λ, quietHsMode s n (c n)).val‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2]
  rw [h0]
  simp_rw [hk_coord, scalarTorusToCell.norm_map, torus_norm_sq, norm_mul, mul_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ModeNorm, Finset.mul_sum]

theorem star_mode (n : Fin 2 → ℤ) (x : Vec 2) :
    star (cellComplexFourierMode n x) =
      Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ)))) := by
  have : cellComplexFourierMode n x =
      Complex.exp (2 * Real.pi * Complex.I * ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ))) := by
    simp [cellComplexFourierMode, cellComplexFourierPhase, seamDotPairing_apply, vecDot,
      Fin.sum_univ_two]
  rw [this, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, map_add, map_ofNat]

theorem pair_mode (W : ComplexCellL2) (c : ℂ) (n : Fin 2 → ℤ) :
    cellComplexPair W (c • scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)) =
      star c * cellFourierCoeff (W : Vec 2 → ℂ) n := by
  rw [scalarTorusToCell_mode]
  unfold cellComplexPair cellFourierCoeff
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c ((cellComplexFourierMode_memLp n).toLp (cellComplexFourierMode n)),
    (cellComplexFourierMode_memLp n).coeFn_toLp] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, star_mul, star_mode]
  ring

/-- The wavevector budget `1 + (2π)²|n|²`. -/
def Budget (n : Fin 2 → ℤ) : ℝ := 1 + 4 * Real.pi ^ 2 * ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2)

theorem Budget_pos (n : Fin 2 → ℤ) : 1 ≤ Budget n := by
  unfold Budget
  have := Real.pi_pos
  nlinarith [sq_nonneg (n 0 : ℝ), sq_nonneg (n 1 : ℝ), sq_nonneg Real.pi,
    mul_nonneg (sq_nonneg Real.pi) (add_nonneg (sq_nonneg (n 0 : ℝ)) (sq_nonneg (n 1 : ℝ)))]

theorem symbol_sq_le {s : ℕ} (n : Fin 2 → ℤ) (a : JetIndex2 s) :
    ‖quietHsSymbol n a‖ ^ 2 ≤ Budget n ^ s := by
  unfold quietHsSymbol
  rw [norm_prod, ← Finset.prod_pow]
  have h1 : ∀ l : Fin a.1.val, ‖(2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 l) : ℂ)‖ ^ 2 ≤
      Budget n := by
    intro l
    have : ‖(2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 l) : ℂ)‖ ^ 2 =
        4 * Real.pi ^ 2 * ((n (a.2 l) : ℝ)) ^ 2 := by
      rw [norm_mul, mul_pow]
      have : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        simp
      rw [this]
      have h2 : ‖(n (a.2 l) : ℂ)‖ ^ 2 = ((n (a.2 l) : ℝ)) ^ 2 := by
        rw [show ((n (a.2 l) : ℤ) : ℂ) = (((n (a.2 l) : ℤ) : ℝ) : ℂ) by simp, Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
      rw [h2]; ring
    rw [this]
    unfold Budget
    have hp : 0 ≤ 4 * Real.pi ^ 2 := by positivity
    have hj : ∀ j : Fin 2, ((n j : ℝ)) ^ 2 ≤ (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 := by
      intro j
      fin_cases j <;> simp <;> nlinarith [sq_nonneg (n 0 : ℝ), sq_nonneg (n 1 : ℝ)]
    have := hj (a.2 l)
    nlinarith [mul_le_mul_of_nonneg_left this hp]
  calc ∏ l : Fin a.1.val, ‖(2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 l) : ℂ)‖ ^ 2
      ≤ ∏ _l : Fin a.1.val, Budget n :=
        Finset.prod_le_prod₀ (fun l _ => sq_nonneg _) (fun l _ => h1 l)
    _ = Budget n ^ a.1.val := by simp
    _ ≤ Budget n ^ s := pow_le_pow_right₀ (Budget_pos n) (by have := a.1.isLt; omega)

theorem ModeNorm_le (s : ℕ) (n : Fin 2 → ℤ) :
    ModeNorm s n ≤ Fintype.card (JetIndex2 s) * Budget n ^ s := by
  unfold ModeNorm
  calc ∑ a : JetIndex2 s, ‖quietHsSymbol n a‖ ^ 2 ≤ ∑ _a : JetIndex2 s, Budget n ^ s :=
        Finset.sum_le_sum fun a _ => symbol_sq_le n a
    _ = _ := by simp

theorem one_le_s167ModeNorm (s : ℕ) (n : Fin 2 → ℤ) : 1 ≤ ModeNorm s n := by
  unfold ModeNorm
  calc (1 : ℝ) = ‖quietHsSymbol n (valueIndex2 s)‖ ^ 2 := by
        rw [quietHsSymbol_value]; simp
    _ ≤ _ := Finset.single_le_sum (f := fun a : JetIndex2 s => ‖quietHsSymbol n a‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ _)

theorem Budget_le {θ : Vec 2} (hθ : θ ∈ freqCube) (n : Fin 2 → ℤ) :
    Budget n ≤ (1 + 4 * Real.pi ^ 2) * (1 + quietYSq θ n) := by
  have hj : ∀ j : Fin 2, (2 * Real.pi * (n j : ℝ)) ^ 2 ≤ 2 * quietFourierFrequency θ n j ^ 2 +
      2 * Real.pi ^ 2 := by
    intro j
    have h1 : 2 * Real.pi * (n j : ℝ) = quietFourierFrequency θ n j - θ j := by
      simp [quietFourierFrequency]
    have h2 : θ j ^ 2 ≤ Real.pi ^ 2 := by
      have := hθ j
      exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
    rw [h1]; nlinarith [sq_nonneg (quietFourierFrequency θ n j + θ j)]
  have h0 := hj 0
  have h1 := hj 1
  unfold Budget quietYSq
  rw [Fin.sum_univ_two]
  have hp : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hy : 0 ≤ quietFourierFrequency θ n 0 ^ 2 + quietFourierFrequency θ n 1 ^ 2 := by positivity
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * Real.pi ^ 2 - 1) hy]

theorem weight_le' {θ : Vec 2} (hθ : θ ∈ freqCube) (s S : ℕ) (hS : s ≤ S) (n : Fin 2 → ℤ) :
    ((1 + quietYSq θ n) ^ S)⁻¹ ≤
      (Fintype.card (JetIndex2 s) * (1 + 4 * Real.pi ^ 2) ^ s) * (ModeNorm s n)⁻¹ := by
  have hy : 1 ≤ 1 + quietYSq θ n := by
    have : 0 ≤ quietYSq θ n := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hN : 0 < ModeNorm s n := lt_of_lt_of_le one_pos (one_le_s167ModeNorm s n)
  have hb := Budget_le hθ n
  have hb0 := Budget_pos n
  have h1 : ModeNorm s n ≤ (Fintype.card (JetIndex2 s) * (1 + 4 * Real.pi ^ 2) ^ s) *
      (1 + quietYSq θ n) ^ S := by
    calc ModeNorm s n ≤ Fintype.card (JetIndex2 s) * Budget n ^ s := ModeNorm_le s n
      _ ≤ Fintype.card (JetIndex2 s) * (((1 + 4 * Real.pi ^ 2) * (1 + quietYSq θ n)) ^ s) := by
        gcongr
      _ = (Fintype.card (JetIndex2 s) * (1 + 4 * Real.pi ^ 2) ^ s) * (1 + quietYSq θ n) ^ s := by
        rw [mul_pow]; ring
      _ ≤ _ := by gcongr
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) hN]
  linarith

theorem coeFn_sum {κ : Type*} (z : κ → ComplexCellL2) (Λ : Finset κ) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), (↑(∑ n ∈ Λ, z n) : Vec 2 → ℂ) x =
      ∑ n ∈ Λ, (z n : Vec 2 → ℂ) x := by
  classical
  induction Λ using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube)] with x hx
    simpa using hx
  | insert a Λ ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [ih, Lp.coeFn_add (z a) (∑ n ∈ Λ, z n)] with x h1 h2
    rw [h2, Pi.add_apply, h1, Finset.sum_insert ha]

theorem pair_sum {κ : Type*} (W : ComplexCellL2) (z : κ → ComplexCellL2) (Λ : Finset κ) :
    cellComplexPair W (∑ n ∈ Λ, z n) = ∑ n ∈ Λ, cellComplexPair W (z n) := by
  unfold cellComplexPair
  rw [← integral_finsetSum _ (fun n _ => cellComplex_pairing_integrable W (z n))]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_sum z Λ] with x hx
  rw [hx, star_sum, Finset.mul_sum]

theorem dual_finite {I : Type*} [Fintype I] (T : Finset I) (W : I → ComplexCellL2) (j : ℕ)
    {M : ℝ}
    (hP : ∀ ψ : I → TorusHk j ℂ,
      ‖∑ i ∈ T, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
        M * Real.sqrt (∑ i ∈ T, ‖ψ i‖ ^ 2))
    (Λ : Finset (Fin 2 → ℤ)) :
    ∑ i ∈ T, ∑ n ∈ Λ, ‖cellFourierCoeff (W i : Vec 2 → ℂ) n‖ ^ 2 * (ModeNorm j n)⁻¹ ≤ M ^ 2 := by
  set c : I → (Fin 2 → ℤ) → ℂ := fun i n => cellFourierCoeff (W i : Vec 2 → ℂ) n with hc
  set N : (Fin 2 → ℤ) → ℝ := fun n => ModeNorm j n with hN
  have hNpos : ∀ n, 0 < N n := fun n => lt_of_lt_of_le one_pos (one_le_s167ModeNorm j n)
  set ψ : I → TorusHk j ℂ := fun i => ∑ n ∈ Λ, quietHsMode j n (c i n / (N n : ℂ)) with hψ
  set X : ℝ := ∑ i ∈ T, ∑ n ∈ Λ, ‖c i n‖ ^ 2 * (N n)⁻¹ with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun n _ =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hNpos n).le)
  have hpair : ∀ i, cellComplexPair (W i) (torusHkValueCLM (ψ i)) =
      ((∑ n ∈ Λ, ‖c i n‖ ^ 2 * (N n)⁻¹ : ℝ) : ℂ) := by
    intro i
    rw [hψ]
    simp only [map_sum, mode_value]
    rw [pair_sum]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pair_mode]
    have hn : (N n : ℂ) ≠ 0 := by exact_mod_cast (hNpos n).ne'
    have : star (c i n / (N n : ℂ)) = star (c i n) / (N n : ℂ) := by
      rw [star_div₀]; simp
    have hcc : star (c i n) * cellFourierCoeff (W i : Vec 2 → ℂ) n = ((‖c i n‖ ^ 2 : ℝ) : ℂ) := by
      change star (c i n) * c i n = _
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [this, div_mul_eq_mul_div, hcc]
    push_cast
    rw [div_eq_mul_inv]
  have hnorm : ∀ i, ‖ψ i‖ ^ 2 = ∑ n ∈ Λ, ‖c i n‖ ^ 2 * (N n)⁻¹ := by
    intro i
    rw [hψ]
    simp only
    rw [hk_norm_sq]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hn0 : (N n) ≠ 0 := (hNpos n).ne'
    rw [norm_div, div_pow]
    have : ‖(N n : ℂ)‖ = N n := by
      rw [Complex.norm_real, Real.norm_of_nonneg (hNpos n).le]
    rw [this]
    change ‖c i n‖ ^ 2 / N n ^ 2 * N n = _
    field_simp
  have h1 := hP ψ
  simp only [hpair, hnorm] at h1
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (by exact hX0)] at h1
  change X ≤ M * Real.sqrt X at h1
  by_cases h0 : X = 0
  · rw [h0]; positivity
  · have hXp : 0 < X := lt_of_le_of_ne hX0 (Ne.symm h0)
    have hs : 0 < Real.sqrt X := Real.sqrt_pos.2 hXp
    have h2 : Real.sqrt X ≤ M := by
      have : Real.sqrt X * Real.sqrt X ≤ M * Real.sqrt X := by
        rw [Real.mul_self_sqrt hX0]; exact h1
      exact le_of_mul_le_mul_right this hs
    calc X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2

theorem dual_tsum {I : Type*} [Fintype I] (T : Finset I) (W : I → ComplexCellL2) (j : ℕ)
    {M : ℝ}
    (hP : ∀ ψ : I → TorusHk j ℂ,
      ‖∑ i ∈ T, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
        M * Real.sqrt (∑ i ∈ T, ‖ψ i‖ ^ 2)) :
    ∑ i ∈ T, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal (‖cellFourierCoeff (W i : Vec 2 → ℂ) n‖ ^ 2 * (ModeNorm j n)⁻¹) ≤
      ENNReal.ofReal (M ^ 2) := by
  classical
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun Λ => ?_
  have hnn : ∀ (i : I) (n : Fin 2 → ℤ),
      0 ≤ ‖cellFourierCoeff (W i : Vec 2 → ℂ) n‖ ^ 2 * (ModeNorm j n)⁻¹ := fun i n => by
    have := one_le_s167ModeNorm j n
    positivity
  rw [Finset.sum_comm]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn _ n)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun n _ => hnn i n)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact dual_finite T W j hP Λ

end AVRegularity.CycleWords.Discard
end
end
end

section
section
/-! # the forward same-level bound from the pairwise operators

`FwdSameStatement` follows from `FwdSameOpsStatement` by the Schur test (`elem_schur`) with the
fibre counts `≤ 5` of the relation `SameRel`, exactly as `sameLevelTransformBoundZone_of_ops` does
for the tests, with the roles of `i` and `i'` exchanged. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

open Classical in
theorem fwdSame_of_ops (hO : FwdSameOpsStatement.{u, v}) :
    FwdSameStatement.{u, v} := by
  intro K Nw D m d Ks ρ n
  obtain ⟨C0, hC0, hC⟩ := hO K Nw D m Ks ρ n
  refine ⟨5 * C0, by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hρ r hr k k' _hlev N hnN X
  choose A hAn hAv using fun i i' => hC g₁ F θ hρ r hr N hnN i i'
  refine ⟨fun i => if i ∈ stageSet b1wSt k then ∑ i' ∈ stageSet b1wSt k', A i i' (X i') else 0,
    ?_, ?_⟩
  · intro i hi φ hφ hper
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast; omega)
    simp only [hi, ↓reduceIte, map_sum]
    rw [int_sum _ _ _ hφ.continuous]
    exact Finset.sum_congr rfl fun i' _ => hAv i i' (X i') φ hφ1 hper
  · have hw0 : ∀ i' i : B1WIndex ι h Nw m Ks, 0 ≤ (if SameRel i i' then C0 else 0) := by
      intro i' i
      split_ifs <;> simp [hC0]
    have hcount : ∀ (S : Finset (B1WIndex ι h Nw m Ks)) (P : B1WIndex ι h Nw m Ks → Prop),
        (Finset.univ.filter P).card ≤ 5 → ∑ x ∈ S, (if P x then C0 else 0) ≤ 5 * C0 := by
      intro S P hP
      calc ∑ x ∈ S, (if P x then C0 else 0) ≤ ∑ x, (if P x then C0 else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => by
              split_ifs <;> simp [hC0]
        _ = (Finset.univ.filter P).card * C0 := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ 5 * C0 := mul_le_mul_of_nonneg_right (by exact_mod_cast hP) hC0
    have key := elem_schur (stageSet b1wSt k') (stageSet b1wSt k)
      (fun i' i => A i i' (X i')) (fun i' i => if SameRel i i' then C0 else 0) (fun i' => ‖X i'‖)
      hw0 (fun i' _ i _ => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hAn i i') (norm_nonneg _)))
      (A := 5 * C0) (B := 5 * C0)
      (fun i' _ => hcount _ (fun i => SameRel i i') (sameRel_card_left i'))
      (fun i _ => hcount _ (fun i' => SameRel i i') (sameRel_card_right i)) (by positivity)
    calc ∑ i ∈ stageSet b1wSt k, ‖(if i ∈ stageSet b1wSt k then
            ∑ i' ∈ stageSet b1wSt k', A i i' (X i') else 0)‖ ^ 2
        = ∑ i ∈ stageSet b1wSt k, ‖∑ i' ∈ stageSet b1wSt k', A i i' (X i')‖ ^ 2 :=
          Finset.sum_congr rfl fun i hi => by simp only [hi, ↓reduceIte]
      _ ≤ 5 * C0 * (5 * C0) * ∑ i' ∈ stageSet b1wSt k', ‖X i'‖ ^ 2 := key
      _ = (5 * C0) ^ 2 * ∑ i' ∈ stageSet b1wSt k', ‖X i'‖ ^ 2 := by ring

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the forward same-level operators

`fwdSameOps : FwdSameOpsStatement`. The operator is `sameOp` of the test form with the
signs of the twisted-derivative coefficients flipped (the transpose of `D_{-θ,k}` is
`-(∂_k + iθ_k)`); the norm bound is that of `sameLevelOps`, the pairing identity is
`same_pair_eq`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

theorem fwdSameOps : FwdSameOpsStatement.{u, v} := by
  classical
  intro K Nw D m Ks ρ n
  refine ⟨8 + 2 * (|cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) +
    8 * (1 + |ρ|)), by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hρ r hr N hnN i i'
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hϖpos : 0 < F.ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_self hη.le hS).trans hη1)
  obtain ⟨M, hMn, hMv⟩ := drift_mul_exists K hη hS hϖ n (F.v r) (F.piece.hvs r)
    (F.piece.hv.2.2.1 r) (fun j z => F.piece.hvj j r z)
  have hθ := hρ
  have hsum : ∀ j k, |F.G r j k + F.G r k j| ≤ 4 := fun j k =>
    metric_sum_le (F.G r) (fun ξ => F.piece.hGm.2.2.2 r 0 ξ) j k
  have hdiag : ∀ j, |F.G r j j| ≤ 2 := by
    intro j
    have := hsum j j
    rw [← two_mul, abs_mul] at this
    norm_num at this
    linarith
  have hal := sameAlive_abs_le F.ηg F.letters i
  have ha4 : ∀ k, |F.G r k 0 + F.G r 0 k| ≤ 4 := fun k => hsum k 0
  have ha5 : ∀ k, |F.G r k 1 + F.G r 1 k| ≤ 4 := fun k => hsum k 1
  refine ⟨sameOp n N hnN θ M (fun k => -(F.G r k 0 + F.G r 0 k)) (fun k => -(F.G r k 1 + F.G r 1 k))
    (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
    (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
    (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))), ?_, ?_⟩
  · have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
    by_cases hrel : SameRel i i'
    · simp only [hrel, ↓reduceIte]
      have hSnn : 0 ≤ ∑ l ∈ Finset.range (n + 1), |K.Cvj l| :=
        Finset.sum_nonneg fun l _ => abs_nonneg _
      have hBnn : 0 ≤ |cellDriftNativePrice n| *
          ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ) :=
        mul_nonneg (abs_nonneg _) (div_nonneg hSnn hϖpos.le)
      have hC0 : 0 ≤ 8 + 2 * (|cellDriftNativePrice n| *
          (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) + 8 * (1 + |ρ|)) := by positivity
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun ψ => ?_
      have hn := sameOp_norm_le n N hnN θ M (fun k => -(F.G r k 0 + F.G r 0 k))
        (fun k => -(F.G r k 1 + F.G r 1 k))
        (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
        (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
        (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)))
        _ ρ hBnn hMn (fun k => (abs_neg _).le.trans (ha4 k)) (fun k => (abs_neg _).le.trans (ha5 k)) hθ ψ
      have h123 := sameE123_abs_le (sameAlive F.ηg F.letters i) F.ϖ hal hϖpos.le hϖ1 (F.G r)
        (hdiag 0) (hdiag 1) (hsum 0 1) i i'
      have h4 : |sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0))| ≤ F.ϖ :=
        (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (1, 0)
          (1 * F.ϖ ^ (1 + 0))).trans (by simp [abs_of_pos hϖpos])
      have h5 : |sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))| ≤ F.ϖ :=
        (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (0, 1)
          (1 * F.ϖ ^ (0 + 1))).trans (by simp [abs_of_pos hϖpos])
      refine hn.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      have hkey : F.ϖ * (|cellDriftNativePrice n| *
          ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ) + 8 * (1 + ρ)) ≤
          |cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) +
            8 * (1 + |ρ|) := by
        have e : F.ϖ * (|cellDriftNativePrice n| *
            ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ)) =
            |cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) := by
          field_simp
        nlinarith [le_abs_self ρ]
      have hq : 0 ≤ |cellDriftNativePrice n| *
          ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ) + 8 * (1 + ρ) := by positivity
      have e4' := mul_le_mul_of_nonneg_right h4 hq
      have e5' := mul_le_mul_of_nonneg_right h5 hq
      nlinarith
    · simp only [hrel, ↓reduceIte]
      refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun ψ => ?_
      have hn := sameOp_norm_le n N hnN θ M (fun k => -(F.G r k 0 + F.G r 0 k))
        (fun k => -(F.G r k 1 + F.G r 1 k))
        (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
        (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
        (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)))
        _ ρ (mul_nonneg (abs_nonneg _) (div_nonneg (Finset.sum_nonneg fun l _ => abs_nonneg _)
          hϖpos.le)) hMn (fun k => (abs_neg _).le.trans (ha4 k)) (fun k => (abs_neg _).le.trans (ha5 k)) hθ ψ
      refine hn.trans (le_of_eq ?_)
      rw [sameE123_eq_zero _ _ _ i i' hrel,
        sameE_eq_zero_of_not_rel _ i i' hrel (1, 0) (by simp [sameShifts]),
        sameE_eq_zero_of_not_rel _ i i' hrel (0, 1) (by simp [sameShifts])]
      simp
  · intro X φ hφ hφp
    exact same_pair_eq F.π F.ϖ F.ηg F.letters F.piece.hπ hϖpos.ne' θ (F.G r) (F.v r)
      (fun c => (continuous_apply c).comp (F.piece.hvs r).continuous) i i' n N hnN M hMv X φ hφ hφp

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the stage test transform is diagonal on the cell modes

On a quiet time (zero drift, letter coefficients independent of the fast variable) the test
transform `b1wTestTransform` of a mode `A e_m` is a scalar multiple of the mode, the scalar being
independent of `A` and the position: `b1wTestTransform_mode`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

/-- The eigenvalue of the covariant derivative `∂_k + iθ'_k` on the mode `m`. -/
def modeEig (θ' : Vec 2) (m : Fin 2 → ℤ) (k : Fin 2) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) * (m k : ℂ) + Complex.I * (θ' k : ℂ)

theorem fibreCovDeriv_mode (θ' : Vec 2) (m : Fin 2 → ℤ) (k : Fin 2) (A : ℂ) :
    fibreCovDeriv θ' k (fun y => A * cellComplexFourierMode m y) =
      fun y => (modeEig θ' m k * A) * cellComplexFourierMode m y := by
  funext z
  unfold fibreCovDeriv
  have hd : DifferentiableAt ℝ (cellComplexFourierMode m) z :=
    ((cellComplexFourierMode_contDiff m).differentiable (by simp)).differentiableAt
  rw [fderiv_const_mul hd, smul_apply, smul_eq_mul,
    cellComplexFourierMode_directional_derivative]
  unfold modeEig
  ring

theorem fibreCovPow_mode (θ' : Vec 2) (m : Fin 2 → ℤ) (b : ℕ × ℕ) (A : ℂ) :
    fibreCovPow θ' b (fun y => A * cellComplexFourierMode m y) =
      fun y => ((modeEig θ' m 0) ^ b.1 * (modeEig θ' m 1) ^ b.2 * A) *
        cellComplexFourierMode m y := by
  unfold fibreCovPow
  have h1 : ∀ (j : ℕ) (A : ℂ), (fibreCovDeriv θ' 1)^[j] (fun y => A * cellComplexFourierMode m y) =
      fun y => ((modeEig θ' m 1) ^ j * A) * cellComplexFourierMode m y := by
    intro j
    induction j with
    | zero => intro A; simp
    | succ j ih =>
      intro A
      rw [Function.iterate_succ_apply, fibreCovDeriv_mode, ih]
      funext y; ring
  have h0 : ∀ (j : ℕ) (A : ℂ), (fibreCovDeriv θ' 0)^[j] (fun y => A * cellComplexFourierMode m y) =
      fun y => ((modeEig θ' m 0) ^ j * A) * cellComplexFourierMode m y := by
    intro j
    induction j with
    | zero => intro A; simp
    | succ j ih =>
      intro A
      rw [Function.iterate_succ_apply, fibreCovDeriv_mode, ih]
      funext y; ring
  rw [h1, h0]
  funext y; ring

theorem cellComplexFourierMode_zero (m : Fin 2 → ℤ) : cellComplexFourierMode m 0 = 1 := by
  simp [cellComplexFourierMode]

section Diag

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m' : ℕ} {Ks : Fin Nw → ℕ}

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem b1wSameTransform_mode
    (θ : Vec 2) (G : Matrix (Fin 2) (Fin 2) ℝ) (vf : Vec 2 → Vec 2) (hvf : ∀ z, vf z = 0)
    (i i' : B1WIndex ι h Nw m' Ks) (m : Fin 2 → ℤ) (A : ℂ) (z : Vec 2) :
    b1wSameTransform θ G vf i i' (fun y => A * cellComplexFourierMode m y) z =
      A * cellComplexFourierMode m z *
        b1wSameTransform θ G vf i i' (fun y => 1 * cellComplexFourierMode m y) 0 := by
  unfold b1wSameTransform
  simp only [fibreCovDeriv_mode, hvf, Pi.zero_apply, Complex.ofReal_zero, zero_mul,
    cellComplexFourierMode_zero]
  split_ifs <;> simp <;> ring

theorem fibreCovPow_coef_mode (θ' : Vec 2) (b : ℕ × ℕ) (coef : Vec 2 → ℝ) (c0 : ℝ)
    (hc : ∀ z, coef z = c0) (m : Fin 2 → ℤ) (A : ℂ) (z : Vec 2) :
    fibreCovPow θ' b (fun z' => (coef z' : ℂ) * (A * cellComplexFourierMode m z')) z =
      A * cellComplexFourierMode m z *
        fibreCovPow θ' b (fun z' => (coef z' : ℂ) * (1 * cellComplexFourierMode m z')) 0 := by
  have e1 : (fun z' => (coef z' : ℂ) * (A * cellComplexFourierMode m z')) =
      fun z' => ((c0 : ℂ) * A) * cellComplexFourierMode m z' := by
    funext z'; rw [hc z']; ring
  have e2 : (fun z' => (coef z' : ℂ) * (1 * cellComplexFourierMode m z')) =
      fun z' => ((c0 : ℂ) * 1) * cellComplexFourierMode m z' := by
    funext z'; rw [hc z']; ring
  rw [e1, e2, fibreCovPow_mode, fibreCovPow_mode]
  simp only [cellComplexFourierMode_zero]
  ring

theorem b1wLetterPart_mode {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (l : Fin Nw) (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ)
    (hfast : ∀ (v u : ι) (d : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d, ∀ α,
      ∀ X z z', γ.coeff α r X z = γ.coeff α r X z')
    (i' : B1WIndex ι h Nw m' Ks) (m : Fin 2 → ℤ) (A : ℂ) (z : Vec 2) :
    b1wLetterPart F θ l x e β₀ k r (fun y => A * cellComplexFourierMode m y) i' z =
      A * cellComplexFourierMode m z *
        b1wLetterPart F θ l x e β₀ k r (fun y => 1 * cellComplexFourierMode m y) i' 0 := by
  unfold b1wLetterPart
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun γ hγ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [mul_left_comm (A * cellComplexFourierMode m z), mul_left_comm (A * cellComplexFourierMode m z)]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_ite, mul_zero]
    split_ifs
    · have hc : ∀ z' : Vec 2, (iteratedFDeriv ℝ s (fun X => γ.coeff α r X z' k) F.X₀)
          (fun n => basisVec (ω n)) =
          (iteratedFDeriv ℝ s (fun X => γ.coeff α r X 0 k) F.X₀) (fun n => basisVec (ω n)) := by
        intro z'
        have hfun : (fun X => γ.coeff α r X z' k) = (fun X => γ.coeff α r X 0 k) := by
          funext X; rw [hfast x i'.2.1 ⟨d, hd⟩ γ hγ α X z' 0]
        rw [hfun]
      rw [fibreCovPow_coef_mode (-θ) _ (fun z' => (iteratedFDeriv ℝ s (fun X => γ.coeff α r X z' k)
        F.X₀) (fun n => basisVec (ω n))) _ hc m A z]
      ring
    · rfl
  · simp [hd]

theorem b1wLetterTransform_mode {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i i' : B1WIndex ι h Nw m' Ks) (r : ℝ)
    (hq : ∀ l, ∀ (v u : ι) (d : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d, ∀ α,
      ∀ X z z', γ.coeff α r X z = γ.coeff α r X z')
    (m : Fin 2 → ℤ) (A : ℂ) (z : Vec 2) :
    b1wLetterTransform F θ i i' r (fun y => A * cellComplexFourierMode m y) z =
      A * cellComplexFourierMode m z *
        b1wLetterTransform F θ i i' r (fun y => 1 * cellComplexFourierMode m y) 0 := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ∀ (l : Fin Nw) (x : ι) (_ : h x) (_ : ℕ × ℕ) (_ : Fin 2)
      (_ : B1WIndex ι h Nw m' Ks), ℂ, ∀ l x e β₀ k i'',
      c1 l x e β₀ k i'' = b1wLetterPart F θ l x e β₀ k r (fun y => 1 * cellComplexFourierMode m y) i'' 0 :=
    ⟨fun l x e β₀ k i'' => b1wLetterPart F θ l x e β₀ k r (fun y => 1 * cellComplexFourierMode m y) i'' 0,
      fun _ _ _ _ _ _ => rfl⟩
  have key : ∀ l x e β₀ k (i'' : B1WIndex ι h Nw m' Ks) (A : ℂ) (z : Vec 2),
      b1wLetterPart F θ l x e β₀ k r (fun y => A * cellComplexFourierMode m y) i'' z =
        A * cellComplexFourierMode m z * c1 l x e β₀ k i'' :=
    fun l x e β₀ k i'' A z => by
      rw [hc1]; exact b1wLetterPart_mode F θ l x e β₀ k r (hq l) i'' m A z
  unfold b1wLetterTransform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [fibreCovDeriv_mode, key, cellComplexFourierMode_zero]
    have hs : ∑ x : Fin 2, modeEig (-θ) m x * A * cellComplexFourierMode m z *
        c1 l i.2.1 (b1wVec i) (b1wMom i) x i' =
        A * cellComplexFourierMode m z * ∑ x : Fin 2, modeEig (-θ) m x * 1 * 1 *
          c1 l i.2.1 (b1wVec i) (b1wMom i) x i' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hs]
    ring
  · simp

theorem b1wTestTransform_mode {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i i' : B1WIndex ι h Nw m' Ks) (r : ℝ) (hv : ∀ z, F.v r z = 0)
    (hq : ∀ l, ∀ (v u : ι) (d : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d, ∀ α,
      ∀ X z z', γ.coeff α r X z = γ.coeff α r X z')
    (m : Fin 2 → ℤ) (A : ℂ) (z : Vec 2) :
    b1wTestTransform F θ i i' r (fun y => A * cellComplexFourierMode m y) z =
      A * cellComplexFourierMode m z *
        b1wTestTransform F θ i i' r (fun y => 1 * cellComplexFourierMode m y) 0 := by
  unfold b1wTestTransform
  rw [b1wSameTransform_mode θ (F.G r) (F.v r) hv i i' m A z,
    b1wLetterTransform_mode F θ i i' r hq m A z]
  ring

end Diag

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the cell Fourier coefficient of an `L²` class, and real and imaginary parts -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Analysis.Convolution

local instance BandCoeffMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance BandCoeffIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance BandCoeffIsProb :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.CycleWords.Discard

local instance BandCoeffFiniteCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simp only [Measure.restrict_apply_univ, AVRegularity.EntryWeakProofs.weak_unitCube_volume]; exact ENNReal.one_lt_top⟩

/-- The cell integral of the representative is the torus Fourier coefficient. -/
theorem cellCoeff_eq_clm (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (n : Fin 2 → ℤ) :
    cellFourierCoeff (u : Vec 2 → ℂ) n = cellFourierCoeffCLM n u := by
  rw [cellFourierCoeffCLM_apply]
  have h1 : UnitAddTorus.mFourierCoeff (cellToTorus u) n =
      UnitAddTorus.mFourierCoeff (AVenhance.Infra.Torus.periodicToTorus (u : Vec 2 → ℂ)) n := by
    unfold UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    filter_upwards [cellToTorus_ae u] with y hy
    simp only [hy]
  rw [h1, AVenhance.Infra.Section5.AnalyticBridge.Sobolev.mFourierCoeff_periodicToTorus]
  unfold AVenhance.Infra.Torus.smoothFourierCoeff cellFourierCoeff
  rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  apply integral_congr_ae
  filter_upwards with z
  rw [mul_comm]
  congr 1
  simp only [AVenhance.Infra.Torus.torusCharacter, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, AVenhance.Infra.Torus.toUnitTorus, Fin.prod_univ_two, Pi.neg_apply,
    fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The cell Fourier coefficient only depends on the almost-everywhere class. -/
theorem cellCoeff_congr {f g : Vec 2 → ℂ} (h : f =ᵐ[volume.restrict AVenhance.unitCube] g)
    (n : Fin 2 → ℤ) : cellFourierCoeff f n = cellFourierCoeff g n := by
  unfold cellFourierCoeff
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]

/-- The cell Fourier coefficient of the complexified value of a real element. -/
theorem cellCoeff_real (K : ℕ) (g : TorusHk K ℝ) (n : Fin 2 → ℤ) :
    cellFourierCoeff (fun x => ((g.val (valueIndex2 K) x : ℝ) : ℂ)) n =
      realJetFourier K g (valueIndex2 K) n := by
  rw [realJetFourier_eq_cellCoeff, ← cellCoeff_eq_clm]
  apply cellCoeff_congr
  have := ContinuousLinearMap.coeFn_compLpL (L := Complex.ofRealCLM)
    (g.val (valueIndex2 K))
  exact this.symm

/-- Real and imaginary parts split the cell Fourier coefficient. -/
theorem cellCoeff_split (f : Vec 2 → ℂ) (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (n : Fin 2 → ℤ) :
    cellFourierCoeff f n = cellFourierCoeff (fun x => (((f x).re : ℝ) : ℂ)) n +
      Complex.I * cellFourierCoeff (fun x => (((f x).im : ℝ) : ℂ)) n := by
  have hint : Integrable f (volume.restrict AVenhance.unitCube) :=
    hf.integrable one_le_two
  have hchar : AEStronglyMeasurable (fun z : Vec 2 => Complex.exp (-(2 * Real.pi * Complex.I *
      (((n 0 : ℤ) : ℂ) * (z 0 : ℂ) + ((n 1 : ℤ) : ℂ) * (z 1 : ℂ)))))
      (volume.restrict AVenhance.unitCube) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hbd : ∀ z : Vec 2, ‖Complex.exp (-(2 * Real.pi * Complex.I *
      (((n 0 : ℤ) : ℂ) * (z 0 : ℂ) + ((n 1 : ℤ) : ℂ) * (z 1 : ℂ))))‖ ≤ 1 := by
    intro z
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp
  have hre : Integrable (fun x => (((f x).re : ℝ) : ℂ)) (volume.restrict AVenhance.unitCube) :=
    (hf.re.ofReal (K := ℂ)).integrable one_le_two
  have him : Integrable (fun x => (((f x).im : ℝ) : ℂ)) (volume.restrict AVenhance.unitCube) :=
    (hf.im.ofReal (K := ℂ)).integrable one_le_two
  unfold cellFourierCoeff
  rw [← integral_const_mul, ← integral_add]
  · apply integral_congr_ae
    filter_upwards with z
    rw [← mul_assoc, ← add_mul, mul_comm Complex.I]
    congr 1
    exact (Complex.re_add_im (f z)).symm
  · exact hre.mul_bdd hchar (Filter.Eventually.of_forall hbd)
  · exact (him.mul_bdd hchar (Filter.Eventually.of_forall hbd)).const_mul _

end AVRegularity.CycleWords.Discard
end
end
end
