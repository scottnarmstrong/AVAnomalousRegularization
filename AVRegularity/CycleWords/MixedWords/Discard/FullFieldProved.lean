-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.PlainPassStage
public import AVRegularity.CycleWords.MixedWords.Discard.MarksBand
import AVRegularity.CycleWords.MixedWords.Discard.WeakContFluxTerm
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldWindowFamily
import AVRegularity.CycleWords.MixedWords.RetainedAmplitudeFactor
import AVRegularity.CycleWords.MixedWords.B1WCrudeH4
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
import Mathlib.CategoryTheory.Countable
import Mathlib.Data.Int.Star

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the weighted `ℓ²` bound of the stage modes on a frame

`quietEntrance_frame_le`: from the plain-pass inequality against all tests of the ladder, the
weighted `ℓ²` norm of the cell modes of all stages at one time. -/

universe u v

section Entrance

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The constant of the weights over the stage orders. -/
def quietEntranceConst (L : ℕ → ℕ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, (Fintype.card (JetIndex2 (L k)) * (1 + 4 * Real.pi ^ 2) ^ (L k) : ℝ)

theorem stageMode_eq_of_scaled {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (t : ℝ)
    (W : B1WIndex ι h Nw m Ks → ComplexCellL2) (hW : IsScaledStage F θ t W)
    (i : B1WIndex ι h Nw m Ks) (n : Fin 2 → ℤ) :
    stageMode F θ i n t = cellFourierCoeff (W i : Vec 2 → ℂ) n := by
  unfold stageMode cellFourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [hW i] with z hz
  rw [hz]

theorem quietEntrance_frame_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hθ : θ ∈ freqCube) (t₁ : ℝ)
    (W₀ W : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (hW₀ : IsScaledStage F θ F.a W₀) (hW : IsScaledStage F θ t₁ W)
    (L : ℕ → ℕ) (S : ℕ) (hL : ∀ k < b1wM Nw m Ks, L k ≤ S) {B : ℝ}
    (hP : ∀ (k : ℕ) (ψ : B1WIndex ι h Nw m Ks → TorusHk (L k) ℂ),
      ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
        B * Real.sqrt (∑ i, ‖W₀ i‖ ^ 2) *
          Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) :
    ∑ i : B1WIndex ι h Nw m Ks, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i n t₁‖ ^ 2) ≤
      ENNReal.ofReal (quietEntranceConst L (b1wM Nw m Ks) * B ^ 2) * stageDatumSq F m Ks θ := by
  classical
  set R := ∑ i, ‖W₀ i‖ ^ 2 with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdat : stageDatumSq F m Ks θ = ENNReal.ofReal R := by
    unfold stageDatumSq
    rw [hR, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [marksMean_ofReal_norm_sq]
    refine lintegral_congr_ae ?_
    filter_upwards [hW₀ i] with z hz
    rw [hz]
  set g : B1WIndex ι h Nw m Ks → ℝ≥0∞ := fun i => ∑' n : Fin 2 → ℤ,
    ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i n t₁‖ ^ 2) with hg
  have hsplit : ∑ i, g i = ∑ k ∈ Finset.range (b1wM Nw m Ks), ∑ i ∈ stageSet b1wSt k, g i := by
    unfold stageSet
    exact (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (b1wM Nw m Ks))
      (g := b1wSt) (fun i _ => Finset.mem_range.2 (b1wSt_lt i)) g).symm
  have hk : ∀ k ∈ Finset.range (b1wM Nw m Ks), ∑ i ∈ stageSet b1wSt k, g i ≤
      ENNReal.ofReal ((Fintype.card (JetIndex2 (L k)) * (1 + 4 * Real.pi ^ 2) ^ (L k) : ℝ) *
        (B ^ 2 * R)) := by
    intro k hkm
    have hkM := Finset.mem_range.1 hkm
    have hdual := dual_tsum (stageSet b1wSt k) W (L k) (M := B * Real.sqrt R) (hP k)
    have hM2 : (B * Real.sqrt R) ^ 2 = B ^ 2 * R := by
      rw [mul_pow, Real.sq_sqrt hR0]
    rw [hM2] at hdual
    set Cs : ℝ := (Fintype.card (JetIndex2 (L k)) * (1 + 4 * Real.pi ^ 2) ^ (L k) : ℝ) with hCs
    have hCs0 : 0 ≤ Cs := by positivity
    calc ∑ i ∈ stageSet b1wSt k, g i
        ≤ ∑ i ∈ stageSet b1wSt k, ENNReal.ofReal Cs * ∑' n : Fin 2 → ℤ,
            ENNReal.ofReal (‖cellFourierCoeff (W i : Vec 2 → ℂ) n‖ ^ 2 *
              (ModeNorm (L k) n)⁻¹) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hg]
          simp only
          rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun n => ?_
          rw [← ENNReal.ofReal_mul hCs0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [stageMode_eq_of_scaled F θ t₁ W hW i n]
          have hw := weight_le' hθ (L k) S (hL k hkM) n
          calc ((1 + quietYSq θ n) ^ S)⁻¹ * ‖cellFourierCoeff (W i : Vec 2 → ℂ) n‖ ^ 2
              ≤ (Cs * (ModeNorm (L k) n)⁻¹) * ‖cellFourierCoeff (W i : Vec 2 → ℂ) n‖ ^ 2 :=
                mul_le_mul_of_nonneg_right hw (sq_nonneg _)
            _ = _ := by ring
      _ = ENNReal.ofReal Cs * ∑ i ∈ stageSet b1wSt k, ∑' n : Fin 2 → ℤ,
            ENNReal.ofReal (‖cellFourierCoeff (W i : Vec 2 → ℂ) n‖ ^ 2 *
              (ModeNorm (L k) n)⁻¹) := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal Cs * ENNReal.ofReal (B ^ 2 * R) := by gcongr
      _ = _ := (ENNReal.ofReal_mul hCs0).symm
  rw [hdat, hsplit, ← ENNReal.ofReal_mul (by
    have : 0 ≤ quietEntranceConst L (b1wM Nw m Ks) :=
      Finset.sum_nonneg fun k _ => by positivity
    positivity)]
  calc ∑ k ∈ Finset.range (b1wM Nw m Ks), ∑ i ∈ stageSet b1wSt k, g i
      ≤ ∑ k ∈ Finset.range (b1wM Nw m Ks), ENNReal.ofReal
          ((Fintype.card (JetIndex2 (L k)) * (1 + 4 * Real.pi ^ 2) ^ (L k) : ℝ) * (B ^ 2 * R)) :=
        Finset.sum_le_sum hk
    _ = ENNReal.ofReal (quietEntranceConst L (b1wM Nw m Ks) * B ^ 2 * R) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
        congr 1
        unfold quietEntranceConst
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring

end Entrance

/-- The reserve `J_*` covers the ladder of the plain pass with `s₀ = max d + 3`. -/
theorem quietEntrance_reserve {Nw : ℕ} (m Kf : ℕ) (d Ks : Fin Nw → ℕ) :
    b1wLadderTop (Finset.univ.sup d + 3) d Ks m + Finset.univ.sup d ≤
      wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d := by
  have hsup : Finset.univ.sup d ≤ ∑ l, d l :=
    Finset.sup_le fun l hl => Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) hl
  unfold b1wLadderTop wordReserveJstar wordReserveKstar wordReserveN
  omega

/-- The plain pass with the constant kernel at the entrance of the quiet stretch. -/
theorem quietEntranceAssembly : QuietEntranceAssembly.{u, v} := by
  intro hPS hPK K
  obtain ⟨gP, hgP, hPK'⟩ := hPS K
  obtain ⟨gW, hgW, hWK⟩ := isScaledStage_exists.{u, v} K
  refine ⟨min gP gW, lt_min hgP hgW, ?_⟩
  intro Nw D m Kf d Ks pos
  obtain ⟨C, Q, hC, hPQ⟩ := hPK' Nw D m d Ks pos (Finset.univ.sup d + 3) 1 le_rfl le_rfl
  set L : ℕ → ℕ := b1wLadderAt Nw (Finset.univ.sup d + 3) d Ks with hLdef
  set Cc : ℝ := quietEntranceConst L (b1wM Nw m Ks) with hCc
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun k _ => by positivity
  refine ⟨Real.sqrt (Cc + 1) * C, Q, b1wLadderTop (Finset.univ.sup d + 3) d Ks m, ?_, ?_⟩
  · have : 0 < Real.sqrt (Cc + 1) := Real.sqrt_pos.2 (by linarith)
    positivity
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hθ t₁ ht1a ht1b
  have hJ' : b1wLadderTop (Finset.univ.sup d + 3) d Ks m + Finset.univ.sup d ≤ F.J :=
    (quietEntrance_reserve m Kf d Ks).trans hJ
  obtain ⟨V, hb⟩ := F.piece.hv.2.1
  set κ : ℝ → ℝ → ℝ := fun _ _ => 1 with hκdef
  have hκ : IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb F.a F.b 1 κ :=
    isFibreKernel_shift (b1wCoeff_eq_real F θ).symm
      (hPK F.a F.b F.G F.piece.hGm F.piece.hv V hb θ)
  obtain ⟨Wf, hWf⟩ := hWK (m := m) (Ks := Ks) (F.mono (min_le_right gP gW)) θ
  have hma : F.a ∈ Icc F.a F.b := ⟨le_rfl, F.ordered⟩
  have hmt : t₁ ∈ Icc F.a F.b := ⟨ht1a, ht1b⟩
  have hfr := quietEntrance_frame_le F θ hθ t₁ (fun i => Wf i F.a) (fun i => Wf i t₁)
    (hWf F.a hma) (hWf t₁ hmt) L (b1wLadderTop (Finset.univ.sup d + 3) d Ks m)
    (fun k hk => b1wLadderAt_le_top _ _ d Ks hk)
    (B := C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q * κ F.a t₁)
    (fun k ψ => hPQ (F.mono (min_le_left gP gW)) θ hlet hJ' hθ V hb κ hκ (fun i => Wf i F.a)
      (hWf F.a hma) t₁ hmt (fun i => Wf i t₁) (hWf t₁ hmt) k ψ)
  refine hfr.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hpe : 0 < peFactor F.η := by
    unfold peFactor
    have := F.piece.hη
    positivity
  have hτ : 0 ≤ t₁ - F.a := by linarith
  have hX : 0 ≤ C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q := by positivity
  have hκ1 : κ F.a t₁ = 1 := rfl
  rw [hκ1, mul_one]
  have hX2 : Real.sqrt (Cc + 1) * C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q =
      Real.sqrt (Cc + 1) * (C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q) := by ring
  have hsq : (Real.sqrt (Cc + 1) * (C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q)) ^ 2 =
      (Cc + 1) * (C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  rw [hX2, hsq]
  have h0 := sq_nonneg (C * peFactor F.η ^ Q * (1 + (t₁ - F.a)) ^ Q)
  have hCc' : quietEntranceConst L (b1wM Nw m Ks) = Cc := rfl
  rw [hCc']
  nlinarith

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the multiplier bound of the damping exponent and the band condition -/

/-- The damping exponent of the cell mode gives the heat multiplier. -/
theorem quietLam_exp_bound (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Vec 2) (n : Fin 2 → ℤ) {s t : ℝ} (hst : s ≤ t) :
    ‖Complex.exp (∫ r in s..t, quietLam G θ n r)‖ ≤
      Real.exp (-(quietYSq θ n / 2) * (t - s)) := by
  have h := quietFourier_multiplier_bound G hG θ n hst
  have he : Complex.exp (∫ r in s..t, quietLam G θ n r) = quietFourierMultiplier G θ n s t := by
    unfold quietFourierMultiplier
    congr 1
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [quietLam, fibreQuad]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [he]
  refine h.trans (le_of_eq ?_)
  unfold quietYSq
  congr 1
  ring

theorem vecDot_quietFourierFrequency (θ : Vec 2) (n : Fin 2 → ℤ) :
    vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) = quietYSq θ n := by
  simp [vecDot, quietYSq, sq]

universe u v

/-- The absorption of the polynomial factors by the heat decay, the sum over the modes
with `|y| ≥ π/4`, and the composition of the mode equation (through `quietTriVec_total`) and the entrance bound. -/
theorem quietAbsorbAssembly : QuietAbsorbAssembly.{u, v} := by
  intro hE hMq K
  obtain ⟨g1, hg1, hEK⟩ := hE K
  obtain ⟨g2, hg2, hMK⟩ := hMq K
  refine ⟨min g1 g2, lt_min hg1 hg2, ?_⟩
  intro Nw D m Kf d Ks pos
  obtain ⟨Cc, Qc, S, hCc, hEQ⟩ := hEK Nw D m Kf d Ks pos
  obtain ⟨B, p, hB, hBQ⟩ := hMK Nw D m Kf d Ks pos
  set Mst : ℕ := b1wM Nw m Ks with hMst
  set y0 : ℝ := (Real.pi / 4) ^ 2 with hy0
  have hy0p : 0 < y0 := by rw [hy0]; positivity
  set L : ℝ := 1 + (Mst + 1) * B with hL
  set K0 : ℝ := (Mst + 1) * L ^ (2 * (Mst + 1)) * quietAbsorbConst (Kf + 2 * p * Mst + S) with hK0
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Mst + 1) hB]
  have hK0p : 0 < K0 := by
    rw [hK0]; have := quietAbsorbConst_pos (Kf + 2 * p * Mst + S); positivity
  refine ⟨Real.sqrt K0 * Cc, y0 / 4, Mst + Qc, by positivity, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hθ Dq hDq hab hqu hv0
  set t₁ : ℝ := F.b - Dq with ht₁
  have hb : F.b = t₁ + Dq := by rw [ht₁]; ring
  have hDq0 : 0 ≤ Dq := by linarith
  have ht1b : t₁ ≤ F.b := by linarith
  have hEc := hEQ (F.mono (min_le_left g1 g2)) θ hlet hJ hθ t₁ hab ht1b
  set K1 : ℝ := K0 * (1 + Dq) ^ (2 * Mst) * Real.exp (-(y0 / 2) * Dq) with hK1
  have hK1p : 0 < K1 := by positivity
  -- the bound for one mode
  have pn : ∀ n : Fin 2 → ℤ, y0 ≤ quietYSq θ n →
      (1 + quietYSq θ n) ^ Kf * ∑ i : B1WIndex ι h Nw m Ks, ‖stageMode F θ i n F.b‖ ^ 2 ≤
        K1 * ∑ i' : B1WIndex ι h Nw m Ks, ((1 + quietYSq θ n) ^ S)⁻¹ *
          ‖stageMode F θ i' n t₁‖ ^ 2 := by
    intro n hband
    obtain ⟨τ, hop, hT0, hint, hD⟩ := hBQ (F.mono (min_le_right g1 g2)) θ hlet hJ hθ t₁ hab ht1b
      hqu hv0 n
    have hint' : ∀ t ∈ Icc t₁ (t₁ + Dq), ∀ i, IntervalIntegrable (fun r =>
        Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
          ∑ i', τ i i' r * stageMode F θ i' n r) volume t₁ t := by
      rw [← hb]; exact hint
    have hD' : ∀ i, ∀ t ∈ Icc t₁ (t₁ + Dq), stageMode F θ i n t =
        Complex.exp (∫ r in t₁..t, quietLam F.G θ n r) * stageMode F θ i n t₁ +
        ∫ r in t₁..t, Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
          ∑ i', τ i i' r * stageMode F θ i' n r := by
      rw [← hb]; intro i t ht; exact hD t ht i
    have := quietMode_scalar_bound (fun i : B1WIndex ι h Nw m Ks => b1wSt i) (Mst := Mst)
      (fun i => (b1wSt_lt i).le) hB p S Kf (y0 := y0) (yq := quietYSq θ n) (Dq := Dq) hy0p.le
      hband hDq (t₁ := t₁) (quietLam F.G θ n) (fun i t => stageMode F θ i n t) τ hop hT0
      (fun s t _ hs _ => by simpa using quietLam_exp_bound F.G F.piece.hGm θ n hs) hint' hD'
    rw [← hb] at this
    exact this
  -- the band sum
  have hq0 : ∀ n, 0 ≤ quietYSq θ n := fun n => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnn : ∀ (i : B1WIndex ι h Nw m Ks) (n : Fin 2 → ℤ),
      0 ≤ ((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i n t₁‖ ^ 2 := fun i n =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg (by linarith [hq0 n]) _)) (sq_nonneg _)
  have hpern : ∀ n : Fin 2 → ℤ, ∑ i : B1WIndex ι h Nw m Ks, (if i.1 = Fin.last Nw then
        (if y0 ≤ quietYSq θ n then ENNReal.ofReal ((1 + quietYSq θ n) ^ Kf *
          ‖stageMode F θ i n F.b‖ ^ 2) else 0) else 0) ≤
      ENNReal.ofReal K1 * ∑ i' : B1WIndex ι h Nw m Ks,
        ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i' n t₁‖ ^ 2) := by
    intro n
    by_cases hbn : y0 ≤ quietYSq θ n
    · simp only [hbn, ite_true]
      calc _ ≤ ∑ i : B1WIndex ι h Nw m Ks, ENNReal.ofReal ((1 + quietYSq θ n) ^ Kf *
            ‖stageMode F θ i n F.b‖ ^ 2) :=
            Finset.sum_le_sum fun i _ => by split_ifs <;> simp
        _ = ENNReal.ofReal ((1 + quietYSq θ n) ^ Kf *
            ∑ i : B1WIndex ι h Nw m Ks, ‖stageMode F θ i n F.b‖ ^ 2) := by
            rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ =>
              mul_nonneg (pow_nonneg (by linarith [hq0 n]) _) (sq_nonneg _)]
        _ ≤ ENNReal.ofReal (K1 * ∑ i' : B1WIndex ι h Nw m Ks,
            ((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i' n t₁‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal (pn n hbn)
        _ = _ := by
            rw [ENNReal.ofReal_mul hK1p.le, ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i n]
    · simp [hbn]
  have hband : stageTerminalBandSq F m Ks Kf (Real.pi / 4) θ ≤ ENNReal.ofReal K1 *
      ∑ i' : B1WIndex ι h Nw m Ks, ∑' n : Fin 2 → ℤ,
        ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i' n t₁‖ ^ 2) := by
    unfold stageTerminalBandSq cellBandSq
    simp only [vecDot_quietFourierFrequency]
    calc _ = ∑ i : B1WIndex ι h Nw m Ks, ∑' n : Fin 2 → ℤ, (if i.1 = Fin.last Nw then
          (if y0 ≤ quietYSq θ n then ENNReal.ofReal ((1 + quietYSq θ n) ^ Kf *
            ‖stageMode F θ i n F.b‖ ^ 2) else 0) else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i.1 = Fin.last Nw
          · simp only [hi, ite_true]; rfl
          · simp [hi]
      _ = ∑' n : Fin 2 → ℤ, ∑ i : B1WIndex ι h Nw m Ks, (if i.1 = Fin.last Nw then
          (if y0 ≤ quietYSq θ n then ENNReal.ofReal ((1 + quietYSq θ n) ^ Kf *
            ‖stageMode F θ i n F.b‖ ^ 2) else 0) else 0) :=
          (Summable.tsum_finsetSum fun i _ => ENNReal.summable).symm
      _ ≤ ∑' n : Fin 2 → ℤ, ENNReal.ofReal K1 * ∑ i' : B1WIndex ι h Nw m Ks,
            ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i' n t₁‖ ^ 2) :=
          ENNReal.tsum_le_tsum hpern
      _ = _ := by
          rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum fun i _ => ENNReal.summable]
  have hEc' : ∑ i : B1WIndex ι h Nw m Ks, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i n t₁‖ ^ 2) ≤
      ENNReal.ofReal ((Cc * peFactor F.η ^ Qc * (1 + (t₁ - F.a)) ^ Qc) ^ 2) *
        stageDatumSq F m Ks θ := hEc
  have hpe1 : 1 ≤ peFactor F.η := by
    unfold peFactor
    have : 0 ≤ (Real.sqrt F.η)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    linarith
  set P : ℝ := 1 + (F.b - F.a) with hP
  have hP1 : 1 + Dq ≤ P := by rw [hP]; linarith
  have hP2 : 1 + (t₁ - F.a) ≤ P := by rw [hP, ht₁]; linarith
  have hP0 : 0 ≤ 1 + (t₁ - F.a) := by rw [ht₁]; linarith
  have hexp : Real.exp (-(y0 / 4) * Dq) ^ 2 = Real.exp (-(y0 / 2) * Dq) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hreal : K1 * (Cc * peFactor F.η ^ Qc * (1 + (t₁ - F.a)) ^ Qc) ^ 2 ≤
      (Real.sqrt K0 * Cc * peFactor F.η ^ (Mst + Qc) * P ^ (Mst + Qc) *
        Real.exp (-(y0 / 4) * Dq)) ^ 2 := by
    have hpe0 : 0 < peFactor F.η := lt_of_lt_of_le one_pos hpe1
    have e1 : (1 + Dq) ^ (2 * Mst) ≤ P ^ (2 * Mst) := pow_le_pow_left₀ (by linarith) hP1 _
    have e2 : (1 + (t₁ - F.a)) ^ (2 * Qc) ≤ P ^ (2 * Qc) := pow_le_pow_left₀ hP0 hP2 _
    have e3 : peFactor F.η ^ (2 * Qc) ≤ peFactor F.η ^ (2 * (Mst + Qc)) :=
      pow_le_pow_right₀ hpe1 (by omega)
    have hPp : 0 ≤ P := by linarith
    have hEp := Real.exp_pos (-(y0 / 2) * Dq)
    calc K1 * (Cc * peFactor F.η ^ Qc * (1 + (t₁ - F.a)) ^ Qc) ^ 2
        = K0 * Cc ^ 2 * Real.exp (-(y0 / 2) * Dq) *
          ((1 + Dq) ^ (2 * Mst) * (peFactor F.η ^ (2 * Qc) * (1 + (t₁ - F.a)) ^ (2 * Qc))) := by
          rw [hK1]; ring
      _ ≤ K0 * Cc ^ 2 * Real.exp (-(y0 / 2) * Dq) *
          (P ^ (2 * Mst) * (peFactor F.η ^ (2 * (Mst + Qc)) * P ^ (2 * Qc))) := by
          gcongr
      _ = _ := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, hexp, Real.sq_sqrt hK0p.le]
          ring
  calc stageTerminalBandSq F m Ks Kf (Real.pi / 4) θ
      ≤ ENNReal.ofReal K1 * ∑ i' : B1WIndex ι h Nw m Ks, ∑' n : Fin 2 → ℤ,
        ENNReal.ofReal (((1 + quietYSq θ n) ^ S)⁻¹ * ‖stageMode F θ i' n t₁‖ ^ 2) := hband
    _ ≤ ENNReal.ofReal K1 * (ENNReal.ofReal ((Cc * peFactor F.η ^ Qc * (1 + (t₁ - F.a)) ^ Qc) ^ 2) *
        stageDatumSq F m Ks θ) := by gcongr
    _ = ENNReal.ofReal (K1 * (Cc * peFactor F.η ^ Qc * (1 + (t₁ - F.a)) ^ Qc) ^ 2) *
        stageDatumSq F m Ks θ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK1p.le]
    _ ≤ _ := by
        gcongr

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Discard

/-! # The fibre statements of the discard design proved so far

* `plainStage : PlainStageStatement`: `plainStage_of_adjointKernel` with the adjoint propagator bound
  (`cellAdjointKernelHs`).
* `marksBandFibre : MarksBandFibreStatement`: `marksBandFibreAssembly` with the
  plain pass and the marks kernel (`marksKernel`). -/

universe u v

/-- The plain pass. -/
theorem plainStage : PlainStageStatement.{u, v} :=
  plainStage_of_adjointKernel cellAdjointKernelHs

/-- The marks band at the fibre level. -/
theorem marksBandFibre : MarksBandFibreStatement.{u, v} :=
  marksBandFibreAssembly plainStage marksKernel

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the coupled Duhamel equation of the stage modes on a frame -/

section Assemble

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The transform families of the zone at the time `r`. -/
def QuietProv {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (d : Fin Nw → ℕ) (s₀ : ℕ) (Bz : ℝ) (r : ℝ) : Prop :=
  ∀ (k k' : ℕ), k' < k →
    ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r (fun y => star
                (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ Bz ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2

/-- The coupling of the mode `n` on the stretch `[t₁, b]`: the diagonal coefficient at the good
quiet times, `0` elsewhere. -/
def quietTauHat {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (d : Fin Nw → ℕ) (s₀ : ℕ) (Bz : ℝ) (t₁ : ℝ) (n : Fin 2 → ℤ) (r : ℝ)
    (i i' : B1WIndex ι h Nw m Ks) : ℂ := by
  classical
  exact if QuietProv (m := m) (Ks := Ks) F θ d s₀ Bz r ∧ r ∈ Icc t₁ F.b then
    quietTau F θ n r i i' else 0

theorem quietTauHat_zero {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (d : Fin Nw → ℕ) (s₀ : ℕ) (Bz : ℝ) (t₁ : ℝ) (n : Fin 2 → ℤ) (r : ℝ)
    (i i' : B1WIndex ι h Nw m Ks) (hi : ¬ b1wSt i' < b1wSt i) :
    quietTauHat F θ d s₀ Bz t₁ n r i i' = 0 := by
  unfold quietTauHat
  split_ifs
  · exact quietTau_zero F θ n r i i' hi
  · rfl

/-- **The coupled Duhamel equation of the stage modes on a quiet stretch of a frame.** -/
theorem quiet_mode_frame {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hθ : θ ∈ freqCube) (d : Fin Nw → ℕ) (s₀ : ℕ) (hs₀ : (Finset.univ.sup d) + 3 ≤ s₀)
    (hlet : ∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l)
    (hJ : Finset.univ.sup d ≤ F.J)
    (hM : ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
      ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
        (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
        MemLp (Function.uncurry src) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
        (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
        (∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
          src r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ j x e β r ∧
          Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
        IsCellSolution (Icc F.a F.b)
          (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
        ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
          planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)))
    {Bz : ℝ} (hBz : 0 ≤ Bz)
    (hprov : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), QuietProv (m := m) (Ks := Ks) F θ d s₀ Bz r)
    (t₁ : ℝ) (hat : F.a ≤ t₁) (htb : t₁ ≤ F.b) (hqu : Icc t₁ F.b ⊆ F.reg.quiet)
    (hv0 : ∀ t ∈ Icc t₁ F.b, ∀ z, F.v t z = 0) (n : Fin 2 → ℤ) :
    (∀ r (w : B1WIndex ι h Nw m Ks → ℂ),
      ∑ i, ‖∑ i', quietTauHat F θ d s₀ Bz t₁ n r i i' * w i'‖ ^ 2 ≤
        ((((b1wM Nw m Ks + 1) ^ 2 : ℝ) * (Bz * Real.sqrt (quietJetConst Nw s₀ d Ks (b1wM Nw m Ks)))) *
          (1 + quietYSq θ n) ^ (b1wLadderTop s₀ d Ks m)) ^ 2 * ∑ i', ‖w i'‖ ^ 2) ∧
    (∀ t ∈ Icc t₁ F.b, ∀ i : B1WIndex ι h Nw m Ks, IntervalIntegrable (fun r =>
      Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
        ∑ i', quietTauHat F θ d s₀ Bz t₁ n r i i' * stageMode F θ i' n r) volume t₁ t) ∧
    ∀ t ∈ Icc t₁ F.b, ∀ i : B1WIndex ι h Nw m Ks,
      stageMode F θ i n t =
        Complex.exp (∫ r in t₁..t, quietLam F.G θ n r) * stageMode F θ i n t₁ +
        ∫ r in t₁..t, Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
          ∑ i', quietTauHat F θ d s₀ Bz t₁ n r i i' * stageMode F θ i' n r := by
  classical
  refine ⟨?_, ?_⟩
  · intro r w
    unfold quietTauHat
    by_cases hr : QuietProv (m := m) (Ks := Ks) F θ d s₀ Bz r ∧ r ∈ Icc t₁ F.b
    · simp only [hr, and_self, ite_true]
      have hq : ∀ l, ∀ (v u : ι) (d' : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d', ∀ α,
          ∀ X z z', γ.coeff α r X z = γ.coeff α r X z' := fun l v u d' γ hγ α X z z' =>
        ((F.piece.hquiet l).2 v u d' γ hγ α) r (hqu hr.2) X z z'
      refine (quiet_tau_op_bound F θ hθ r (hv0 r hr.2) hq d s₀ (by omega) hBz n hr.1 w).trans
        (le_of_eq ?_)
      ring
    · simp only [hr, ite_false, zero_mul, Finset.sum_const_zero, norm_zero]
      simp
      positivity
  · obtain ⟨V, hb⟩ := F.piece.hv.2.1
    have hϖ : 0 < F.ϖ := by
      rw [F.piece.hϖ]
      exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
    obtain ⟨Dθ, src, Fl, hcur, hval, hlit, hmem, hsl, hsrcP, hFlP⟩ :=
      b1w_stage_curves_mem F m Ks θ hM V hb (b1wScale F.π F.ϖ F.ηg F.letters)
    have hord : ∀ l, (F.letters l).order ≤ F.J := fun l => by
      rw [(hlet l).1]
      exact (Finset.le_sup (f := d) (Finset.mem_univ l)).trans hJ
    have hsup : (Finset.univ.sup fun l => (F.letters l).order) = Finset.univ.sup d := by
      congr 1
      funext l
      exact (hlet l).1
    have hexp : ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
        ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ),
          ContDiff ℝ (Finset.univ.sup d + 1 : ℕ) φ → AVenhance.IsZ2Periodic φ →
          b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
            ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
              b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y := by
      filter_upwards [stageExpansion K g₁ F θ m Ks (fun l => (hlet l).2) hord letterBloch
        (amplitudeIdMoments K g₁ F)] with r hr i φ hφ hper
      refine hr i φ ?_ hper
      rw [hsup]
      exact_mod_cast hφ
    set u : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2 := fun i t =>
      cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) t) with hu
    set Sg : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2 := fun i r =>
      cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r) with hSg
    set Fg : B1WIndex ι h Nw m Ks → ℝ → Fin 2 → ComplexCellL2 := fun i r j =>
      cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
        (cellSourceSlice (fun r z => Fl i r z j) r) with hFg
    have hcurθ := fun i => cellWeakHilbertCurve_shift (b1wCoeff_eq_real F θ) (hcur i)
    have hscaled : ∀ t ∈ Icc F.a F.b, IsScaledStage F θ t (fun i => u i t) := by
      intro t ht i
      filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
        (cellRawTrace (Dθ i) t), cellRawTrace_ae (Dθ i) t (hmem i t ht), hval i t ht]
        with y h1 h2 h3
      rw [h1, h2, h3]
      rfl
    have hmode : ∀ i, ∀ t ∈ Icc F.a F.b, stageMode F θ i n t =
        cellComplexPair (u i t) (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)) := by
      intro i t ht
      rw [stageMode_eq_of_scaled F θ t (fun i => u i t) (hscaled t ht) i n]
      have := pair_mode (u i t) 1 n
      rw [one_smul, star_one, one_mul] at this
      exact this.symm
    have hab : t₁ ≤ F.b := htb
    have hSmem : ∀ i, ∀ t ∈ Icc t₁ F.b, MemLp (Sg i) 2 (volume.restrict (Icc t₁ t)) := by
      intro i t ht
      have hsub : Icc t₁ t ⊆ Icc F.a F.b := Icc_subset_Icc hat ht.2
      have h1 := cellSourceSlice_memLp (Icc t₁ t) (src i)
        ((hsrcP i).mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl))
      exact (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)).comp_memLp' h1
    have hFmem : ∀ i, ∀ t ∈ Icc t₁ F.b, ∀ j, MemLp (fun r => Fg i r j) 2
        (volume.restrict (Icc t₁ t)) := by
      intro i t ht j
      have hsub : Icc t₁ t ⊆ Icc F.a F.b := Icc_subset_Icc hat ht.2
      have h1 := cellSourceSlice_memLp (Icc t₁ t) (fun r z => Fl i r z j)
        ((hFlP i j).mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl))
      exact (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)).comp_memLp' h1
    have hDu : ∀ i, ∀ t ∈ Icc t₁ F.b, stageMode F θ i n t =
        Complex.exp (∫ r in t₁..t, quietLam F.G θ n r) * stageMode F θ i n t₁ +
        ∫ r in t₁..t, Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
          quietModeForcing θ n (Sg i r) (Fg i r) := by
      intro i t ht
      have hsub : Icc t₁ t ⊆ Icc F.a F.b := Icc_subset_Icc hat ht.2
      rw [hmode i t ⟨hat.trans ht.1, ht.2⟩, hmode i t₁ ⟨hat, htb⟩]
      exact quietFourierS_evolution ht.1 F.G F.piece.hGm F.piece.hv V hb θ (u i) _ (Sg i) (Fg i)
        (hSmem i t ht) (hFmem i t ht) ((hcurθ i).mono hsub)
        (fun r hr x => hv0 r ⟨hr.1, hr.2.trans ht.2⟩ x) n
    have hae_r : ∀ᵐ r ∂volume.restrict (Icc F.a F.b), r ∈ Icc t₁ F.b → ∀ i,
        quietModeForcing θ n (Sg i r) (Fg i r) =
          ∑ i', quietTauHat F θ d s₀ Bz t₁ n r i i' * stageMode F θ i' n r := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_all_iff.2 hlit, ae_all_iff.2 hsl,
        hexp, hprov] with r hr hl hs he hp r1 i
      have hgood := b1w_good_stage_ae F θ Dθ src Fl r (fun i => hval i r hr)
        (fun i => hmem i r hr) (fun i => ⟨(hs i).1, (hl i).1, (hs i).2, (hl i).2⟩)
      have hq : ∀ l, ∀ (v u : ι) (d' : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d', ∀ α,
          ∀ X z z', γ.coeff α r X z = γ.coeff α r X z' := fun l v u d' γ hγ α X z z' =>
        ((F.piece.hquiet l).2 v u d' γ hγ α) r (hqu r1) X z z'
      have hid := quiet_forcing_identity F θ r (hv0 r r1) hq F.piece.hπ hϖ
        (Finset.univ.sup d + 1) n i (fun i' => u i' r) (fun i => Sg i r) (fun i => Fg i r)
        hgood.1 hgood.2.1 hgood.2.2 he
        (fun i i' hn φ => stageTransformEarlier K g₁ F θ m Ks (fun l => (hlet l).2) i i' hn r φ)
      rw [hid]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← stageMode_eq_of_scaled F θ r (fun i => u i r) (hscaled r hr) i' n]
      unfold quietTauHat
      simp only [hp, r1, and_self, ↓reduceIte]
    have hae : ∀ᵐ r ∂volume, r ∈ Icc t₁ F.b → ∀ i,
        quietModeForcing θ n (Sg i r) (Fg i r) =
          ∑ i', quietTauHat F θ d s₀ Bz t₁ n r i i' * stageMode F θ i' n r := by
      filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hae_r] with r hr r1
      exact hr ⟨hat.trans r1.1, r1.2⟩ r1
    have hlam : IntervalIntegrable (quietLam F.G θ n) volume t₁ F.b := by
      have hi := fibreMetricSymbol_intervalIntegrable 1 F.G F.piece.hGm
        (fun j => (quietFourierFrequency θ n j : ℂ)) t₁ F.b
      have he : (fun t => -(1 : ℂ) * fibreQuad (F.G t)
          (fun j => (quietFourierFrequency θ n j : ℂ))) = quietLam F.G θ n := by
        funext t
        simp only [neg_one_mul, fibreQuad, quietLam]
        congr 1
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      rw [Complex.ofReal_one, he] at hi
      exact hi
    have hfint : ∀ i, IntervalIntegrable (fun r => quietModeForcing θ n (Sg i r) (Fg i r))
        volume t₁ F.b := fun i =>
      quietModeForcing_integrable hab θ n (Sg i) (Fg i) (hSmem i F.b ⟨hab, le_rfl⟩)
        (hFmem i F.b ⟨hab, le_rfl⟩)
    have hglue := quietDuhamel_glue hab (quietLam F.G θ n) hlam
      (fun i r => stageMode F θ i n r) (fun i r => quietModeForcing θ n (Sg i r) (Fg i r))
      (fun i i' r => quietTauHat F θ d s₀ Bz t₁ n r i i') hfint hDu hae
    exact ⟨hglue.1, fun t ht i => hglue.2 i t ht⟩

end Assemble

universe u v

/-- The mode-diagonal coupled Duhamel equation of the stages on the quiet stretch, from the
transform families of the zone. -/
theorem quietModeAssembly : QuietModeAssembly.{u, v} := by
  intro hZ K
  obtain ⟨g₁, hg₁, hMK⟩ := amplitudeIdFibresMeas_of_literal.{u, v} amplitudeIdentification
    amplitudeIdForcingCurves K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D m Kf d Ks pos
  obtain ⟨Bz, hBz, hprov⟩ := hZ K Nw D m d Ks pos Real.pi (Finset.univ.sup d + 3) le_rfl
  refine ⟨((b1wM Nw m Ks + 1) ^ 2 : ℝ) * (Bz * Real.sqrt (quietJetConst Nw (Finset.univ.sup d + 3)
    d Ks (b1wM Nw m Ks))), b1wLadderTop (Finset.univ.sup d + 3) d Ks m, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hθ t₁ hat htb hqu hv0 n
  have hJ' : b1wLadderTop (Finset.univ.sup d + 3) d Ks m + Finset.univ.sup d ≤ F.J :=
    (quietEntrance_reserve m Kf d Ks).trans hJ
  have hfr := quiet_mode_frame F θ hθ d (Finset.univ.sup d + 3) le_rfl
    (fun l => ⟨(hlet l).1, (hlet l).2.1⟩) (by omega) (fun j x e β => hMK F j x e θ β) hBz
    (hprov g₁ F θ hlet hJ' fun k => hθ k) t₁ hat htb hqu hv0 n
  exact ⟨fun i i' r => quietTauHat F θ d (Finset.univ.sup d + 3) Bz t₁ n r i i', hfr.1,
    fun i i' r hi => quietTauHat_zero F θ d _ Bz t₁ n r i i' hi, hfr.2.1, hfr.2.2⟩

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the constants

* `b1wPosLadder_ge`, `b1wPosLadder_le`: `K_f ≤ n_i ≤ K_f + ∑d + (m + ∑K_s)`.
* `reserve_plain_le`, `reserve_sources_le`: the fast reserve of `FullFieldFibreStatement` covers
  the plain pass (ladder base `sup d + 3`) and the source bound.
* `termConst_mono`, `termConst_le_scale`: `termConst` is monotone in `Λ` and of degree `k + 1`.
* `cellBandSq_congr`: the band norm of a cell function depends only on its class.
* `stageDatumSq_eq`: the datum is the sum of the squared `L²` norms of any representatives. -/

section
open AVRegularity.CycleWords.Assembly

universe u v

section Ladder

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

theorem b1wPosLadder_ge (Kf : ℕ) (d : Fin Nw → ℕ) (i : B1WIndex ι h Nw m Ks) :
    Kf ≤ b1wPosLadder Kf d i := by
  unfold b1wPosLadder
  omega

theorem b1wPosLadder_le (Kf : ℕ) (d : Fin Nw → ℕ) (i : B1WIndex ι h Nw m Ks) :
    b1wPosLadder Kf d i ≤ Kf + ∑ l, d l + (m + ∑ l, Ks l) := by
  unfold b1wPosLadder
  have h1 : (∑ l : Fin Nw, if i.1.val ≤ l.val then d l else 0) ≤ ∑ l, d l :=
    Finset.sum_le_sum fun l _ => by split_ifs <;> omega
  have h2 : b1wLevelMoments m Ks i.1 ≤ m + ∑ l, Ks l := by
    unfold b1wLevelMoments
    have : (∑ l : Fin Nw, if i.1.val ≤ l.val then Ks l else 0) ≤ ∑ l, Ks l :=
      Finset.sum_le_sum fun l _ => by split_ifs <;> omega
    omega
  omega

end Ladder

theorem reserve_plain_le {Nw : ℕ} (Kf m : ℕ) (d Ks : Fin Nw → ℕ) :
    b1wLadderTop (Finset.univ.sup d + 3) d Ks m + Finset.univ.sup d ≤
      wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d := by
  have hsup : Finset.univ.sup d ≤ ∑ l, d l := Finset.sup_le fun l _ =>
    Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  unfold b1wLadderTop wordReserveJstar wordReserveKstar wordReserveN
  omega

theorem reserve_sources_le {Nw : ℕ} (Kf m : ℕ) (d Ks : Fin Nw → ℕ) :
    wordReserveKstar Kf (wordReserveN m Ks) d + Finset.univ.sup d ≤
      wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d := by
  unfold wordReserveJstar
  omega

theorem termConst_mono {Λ Λ' Tτ B c : ℝ} (hΛ : 0 ≤ Λ) (hΛΛ : Λ ≤ Λ') (hT : 0 ≤ Tτ)
    (hB : 0 ≤ B) (k : ℕ) : termConst Λ Tτ B c k ≤ termConst Λ' Tτ B c k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [termConst_eq, termConst_eq]
    have hs : ∑ k' ∈ Finset.range k, termConst Λ Tτ B c k' ≤
        ∑ k' ∈ Finset.range k, termConst Λ' Tτ B c k' :=
      Finset.sum_le_sum fun k' hk' => ih k' (Finset.mem_range.1 hk')
    have h0 : 0 ≤ ∑ k' ∈ Finset.range k, termConst Λ Tτ B c k' :=
      Finset.sum_nonneg fun k' _ => termConst_nonneg hΛ hT hB k'
    exact mul_le_mul hΛΛ (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by positivity)))
      (by positivity) (hΛ.trans hΛΛ)

theorem termConst_le_scale {Λ₀ lam Tτ B c : ℝ} (hΛ : 0 ≤ Λ₀) (hl : 1 ≤ lam) (hT : 0 ≤ Tτ)
    (hB : 0 ≤ B) (k : ℕ) :
    termConst (Λ₀ * lam) Tτ B c k ≤ lam ^ (k + 1) * termConst Λ₀ Tτ B c k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [termConst_eq, termConst_eq]
    have hl0 : 0 ≤ lam := zero_le_one.trans hl
    have hs : ∑ k' ∈ Finset.range k, termConst (Λ₀ * lam) Tτ B c k' ≤
        lam ^ k * ∑ k' ∈ Finset.range k, termConst Λ₀ Tτ B c k' := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k' hk' => (ih k' (Finset.mem_range.1 hk')).trans ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl (by
        have := Finset.mem_range.1 hk'
        omega)) (termConst_nonneg hΛ hT hB k')
    have h0 : 0 ≤ ∑ k' ∈ Finset.range k, termConst Λ₀ Tτ B c k' :=
      Finset.sum_nonneg fun k' _ => termConst_nonneg hΛ hT hB k'
    have hlk : 1 ≤ lam ^ k := one_le_pow₀ hl
    have hBc : 0 ≤ B * Real.sqrt c := mul_nonneg hB (Real.sqrt_nonneg c)
    have hs0 : 0 ≤ ∑ k' ∈ Finset.range k, termConst (Λ₀ * lam) Tτ B c k' :=
      Finset.sum_nonneg fun k' _ => termConst_nonneg (mul_nonneg hΛ hl0) hT hB k'
    calc Λ₀ * lam * (Tτ + B * Real.sqrt c * ∑ k' ∈ Finset.range k,
          termConst (Λ₀ * lam) Tτ B c k')
        ≤ Λ₀ * lam * (lam ^ k * Tτ + B * Real.sqrt c *
            (lam ^ k * ∑ k' ∈ Finset.range k, termConst Λ₀ Tτ B c k')) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (mul_nonneg hΛ hl0)
          · nlinarith
          · exact mul_le_mul_of_nonneg_left hs hBc
      _ = lam ^ (k + 1) * (Λ₀ * (Tτ + B * Real.sqrt c *
            ∑ k' ∈ Finset.range k, termConst Λ₀ Tτ B c k')) := by ring

/-- The band norm of a cell function depends only on its class on the cell. -/
theorem cellBandSq_congr (k : ℕ) (ρ : ℝ) (θ : Vec 2) {f g : Vec 2 → ℂ}
    (hfg : f =ᵐ[volume.restrict AVenhance.unitCube] g) :
    cellBandSq k ρ θ f = cellBandSq k ρ θ g := by
  have hc : ∀ n, cellFourierCoeff f n = cellFourierCoeff g n := fun n => by
    unfold cellFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hfg] with z hz
    rw [hz]
  unfold cellBandSq
  simp only [hc]

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The datum is the sum of the squared norms of any `L²` representatives of the stages at `a`. -/
theorem stageDatumSq_eq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (W₀ : B1WIndex ι h Nw m Ks → ComplexCellL2) (hW₀ : IsScaledStage F θ F.a W₀) :
    stageDatumSq F m Ks θ = ENNReal.ofReal (∑ i, ‖W₀ i‖ ^ 2) := by
  unfold stageDatumSq
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [marksMean_ofReal_norm_sq]
  refine lintegral_congr_ae ?_
  filter_upwards [hW₀ i] with z hz
  rw [hz]

end Frame
end

/-! # The full-field bound at the fibre level

`fullFieldFibre_of_families : TorusHkBandBoundStatement → CellForcedHsFamilyStatement →
CellNegativeSmoothingFamilyStatement → FullFieldFibreAssembly`. It uses the plain pass, the plain kernel and the source bound `StageSourceHsStatement`; the family forms of the forced-curve and negative-smoothing bounds
replace the per-curve ones, and the band bound reads the output.

Constants. The plain pass with ladder base `sup d + 3` and `A = 1` (`C_P, Q_P`); the source bound (`B`); the
family window constants for `j_max = J_t = K_f + ∑d + (m + ∑K_s)` and `s ≤ S_t` (the ladder top)
(`C_f, Q_f`); the band constants for the orders `≤ J_t` (`C_b`). With
`Φ₀ k = termConst (C_f(1+J)^{Q_f}) ((M+1)^{J_t+S_t}) B 1 k`:
`C = √C_b (∑_{k<M} Φ₀ k) C_P + 1`, `Q = Q_f M + Q_P`, before the frame and the frequency. -/

section
open AVRegularity.CycleWords.Assembly

universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The terminal band from the stage families at the end. -/
theorem terminalBand_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (Kf : ℕ)
    (d : Fin Nw → ℕ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hband : ∀ i : B1WIndex ι h Nw m Ks, ∀ w : TorusHk (b1wPosLadder Kf d i) ℂ,
      cellBandSq Kf 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (Cb * ‖w‖ ^ 2))
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (Mn : ℝ) (hMn : 0 ≤ Mn)
    (hX : ∀ k < b1wM Nw m Ks, ∃ X : ∀ i : B1WIndex ι h Nw m Ks,
        TorusHk (b1wPosLadder Kf d i) ℂ,
      (∀ i ∈ stageSet b1wSt k, (torusHkValueCLM (X i) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i F.b) ∧
      Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖X i‖ ^ 2) ≤ T k * Mn) :
    stageTerminalBandSq F m Ks Kf 0 θ ≤
      ENNReal.ofReal (Cb * ((∑ k ∈ Finset.range (b1wM Nw m Ks), T k) * Mn) ^ 2) := by
  classical
  have hX' : ∀ k, ∃ X : ∀ i : B1WIndex ι h Nw m Ks, TorusHk (b1wPosLadder Kf d i) ℂ,
      k < b1wM Nw m Ks →
      (∀ i ∈ stageSet b1wSt k, (torusHkValueCLM (X i) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i F.b) ∧
      Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖X i‖ ^ 2) ≤ T k * Mn := by
    intro k
    by_cases hk : k < b1wM Nw m Ks
    · obtain ⟨X, h1, h2⟩ := hX k hk
      exact ⟨X, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hk⟩
  choose X hXp using hX'
  have hmem : ∀ i : B1WIndex ι h Nw m Ks, i ∈ stageSet b1wSt (b1wSt i) :=
    fun i => Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  -- every term by the band bound of its representative
  have hterm : ∀ i : B1WIndex ι h Nw m Ks,
      (if i.1 = Fin.last Nw then cellBandSq Kf 0 θ (stageScaled F θ i F.b) else 0) ≤
        ENNReal.ofReal (Cb * ‖X (b1wSt i) i‖ ^ 2) := by
    intro i
    split_ifs
    · rw [← cellBandSq_congr Kf 0 θ ((hXp (b1wSt i) (b1wSt_lt i)).1 i (hmem i))]
      exact hband i _
    · exact zero_le
  have hsum : ∑ i : B1WIndex ι h Nw m Ks, ‖X (b1wSt i) i‖ ^ 2 =
      ∑ k ∈ Finset.range (b1wM Nw m Ks), ∑ i ∈ stageSet b1wSt k, ‖X k i‖ ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (b1wM Nw m Ks))
      (g := b1wSt) (fun i _ => Finset.mem_range.2 (b1wSt_lt i))]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hk : ∀ k ∈ Finset.range (b1wM Nw m Ks),
      ∑ i ∈ stageSet b1wSt k, ‖X k i‖ ^ 2 ≤ (T k * Mn) ^ 2 := by
    intro k hk
    have h := (hXp k (Finset.mem_range.1 hk)).2
    have h0 : 0 ≤ ∑ i ∈ stageSet b1wSt k, ‖X k i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc ∑ i ∈ stageSet b1wSt k, ‖X k i‖ ^ 2
        = Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖X k i‖ ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ (T k * Mn) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  unfold stageTerminalBandSq
  calc ∑ i : B1WIndex ι h Nw m Ks,
        (if i.1 = Fin.last Nw then cellBandSq Kf 0 θ (stageScaled F θ i F.b) else 0)
      ≤ ∑ i : B1WIndex ι h Nw m Ks, ENNReal.ofReal (Cb * ‖X (b1wSt i) i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ENNReal.ofReal (Cb * ∑ i : B1WIndex ι h Nw m Ks, ‖X (b1wSt i) i‖ ^ 2) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ =>
          mul_nonneg hCb (sq_nonneg _)]
    _ ≤ ENNReal.ofReal (Cb * ((∑ k ∈ Finset.range (b1wM Nw m Ks), T k) * Mn) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hCb)
        rw [hsum]
        refine (Finset.sum_le_sum hk).trans ?_
        rw [Finset.sum_mul]
        exact fullField_sum_sq_le_sq_sum _ (fun k => T k * Mn) fun k => mul_nonneg (hT k) hMn

end Frame

/-- The final arithmetic of the constants. -/
theorem fullField_arith {Cb S₀ CP P T X A : ℝ} {Qf M QP : ℕ} (hCb : 0 ≤ Cb) (hS₀ : 0 ≤ S₀)
    (hCP : 0 ≤ CP) (hP : 1 ≤ P) (hT : 0 ≤ T) (hX : 0 ≤ X) (hA0 : 0 ≤ A)
    (hA : A ≤ S₀ * P ^ (Qf * M)) :
    Cb * (A * (CP * P ^ QP * (1 + T) ^ QP * X)) ^ 2 ≤
      ((Real.sqrt Cb * S₀ * CP + 1) * P ^ (Qf * M + QP) * (1 + T) ^ (Qf * M + QP)) ^ 2 *
        X ^ 2 := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hT1 : 1 ≤ 1 + T := by linarith
  have hsq : Cb = Real.sqrt Cb ^ 2 := (Real.sq_sqrt hCb).symm
  have hs0 : 0 ≤ Real.sqrt Cb := Real.sqrt_nonneg _
  have h1 : Real.sqrt Cb * (A * (CP * P ^ QP * (1 + T) ^ QP * X)) ≤
      (Real.sqrt Cb * S₀ * CP + 1) * P ^ (Qf * M + QP) * (1 + T) ^ (Qf * M + QP) * X := by
    have hPQ : P ^ (Qf * M + QP) = P ^ (Qf * M) * P ^ QP := pow_add _ _ _
    have hTQ : (1 + T) ^ QP ≤ (1 + T) ^ (Qf * M + QP) := pow_le_pow_right₀ hT1 (by omega)
    have hR0 : 0 ≤ CP * P ^ QP * X := by positivity
    calc Real.sqrt Cb * (A * (CP * P ^ QP * (1 + T) ^ QP * X))
        = Real.sqrt Cb * A * (CP * P ^ QP * X) * (1 + T) ^ QP := by ring
      _ ≤ Real.sqrt Cb * (S₀ * P ^ (Qf * M)) * (CP * P ^ QP * X) * (1 + T) ^ (Qf * M + QP) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hA hs0) hR0) hTQ (by positivity) (by positivity)
      _ = Real.sqrt Cb * S₀ * CP * P ^ (Qf * M + QP) * (1 + T) ^ (Qf * M + QP) * X := by
          rw [hPQ]; ring
      _ ≤ (Real.sqrt Cb * S₀ * CP + 1) * P ^ (Qf * M + QP) * (1 + T) ^ (Qf * M + QP) * X := by
          have : 0 ≤ P ^ (Qf * M + QP) * (1 + T) ^ (Qf * M + QP) * X := by positivity
          nlinarith
  have h0 : 0 ≤ Real.sqrt Cb * (A * (CP * P ^ QP * (1 + T) ^ QP * X)) := by positivity
  calc Cb * (A * (CP * P ^ QP * (1 + T) ^ QP * X)) ^ 2
      = (Real.sqrt Cb * (A * (CP * P ^ QP * (1 + T) ^ QP * X))) ^ 2 := by
        rw [mul_pow (Real.sqrt Cb), ← hsq]
    _ ≤ ((Real.sqrt Cb * S₀ * CP + 1) * P ^ (Qf * M + QP) * (1 + T) ^ (Qf * M + QP) * X) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = _ := by ring
end

/-! # `FullFieldFibreAssembly` from the family forms

`fullFieldFibre_of_families`: the band bound and the family forms of the forced-curve and negative-smoothing bounds give
`FullFieldFibreAssembly` (it uses the plain pass, the plain kernel and the source bound). See
`FullFieldAssembly.lean` for the constants. -/

section
open AVRegularity.CycleWords.Assembly

universe u v

/-- The full-field bound at the fibre level, from the family forms. -/
theorem fullFieldFibre_of_families (hBand : TorusHkBandBoundStatement)
    (hP4bF : CellForcedHsFamilyStatement.{u}) (hP4cF : CellNegativeSmoothingFamilyStatement.{u}) :
    FullFieldFibreAssembly.{u, v} := by
  intro hPS hPK _ _ _ _ _ hP4a K
  obtain ⟨gP, hgP, hPSK⟩ := hPS K
  obtain ⟨gM, hgM, hMK⟩ := amplitudeIdFibresMeas_of_literal.{u, v} amplitudeIdentification
    amplitudeIdForcingCurves K
  obtain ⟨gS, hgS, hSK⟩ := isScaledStage_exists.{u, v} K
  refine ⟨min gP (min gM gS), lt_min hgP (lt_min hgM hgS), ?_⟩
  intro Nw D m Kf d Ks pos
  obtain ⟨CP, QP, hCP, hPSs⟩ := hPSK Nw D m d Ks pos (Finset.univ.sup d + 3) 1 le_rfl le_rfl
  obtain ⟨B, hB, hP4aK⟩ := hP4a K Nw D m Kf d Ks pos
  obtain ⟨Jt, hJt⟩ : ∃ Jt : ℕ, Jt = Kf + ∑ l, d l + (m + ∑ l, Ks l) := ⟨_, rfl⟩
  obtain ⟨St, hSt⟩ : ∃ St : ℕ, St = b1wLadderTop (Finset.univ.sup d + 3) d Ks m := ⟨_, rfl⟩
  obtain ⟨Cf, Qf, hCf, hwinF⟩ := window_family_uniform.{u} hP4bF hP4cF Jt St
    (ρ := 2 * Real.pi) (by positivity)
  -- the band constants of the orders `≤ J_t`
  have hbandN : ∀ N : Fin (Jt + 1), ∃ C : ℝ, 0 ≤ C ∧ (Kf ≤ N.val →
      ∀ (w : TorusHk N.val ℂ) (θ : Vec 2), θ ∈ freqCube →
        cellBandSq Kf 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (C * ‖w‖ ^ 2)) := by
    intro N
    by_cases hN : Kf ≤ N.val
    · obtain ⟨C, hC, hb⟩ := hBand Kf N.val hN
      exact ⟨C, hC, fun _ => hb⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hN⟩
  choose CbN hCbN hbN using hbandN
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = ∑ N, CbN N := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; exact Finset.sum_nonneg fun N _ => hCbN N
  obtain ⟨Js, hJs⟩ : ∃ Js : ℝ, Js = ∑ l ∈ Finset.range (Jt + St + 2), b1wJets K l := ⟨_, rfl⟩
  have hJs0 : 0 ≤ Js := by
    rw [hJs]
    exact Finset.sum_nonneg fun l _ => le_max_right _ _
  set Mst := b1wM Nw m Ks with hMst
  set Λ₀ := Cf * (1 + Js) ^ Qf with hΛ₀
  set Tτ : ℝ := ((Mst : ℝ) + 1) ^ (Jt + St) with hTτ
  have hΛ₀0 : 0 ≤ Λ₀ := by positivity
  have hTτ0 : 0 ≤ Tτ := by positivity
  set S₀ := ∑ k ∈ Finset.range Mst, termConst Λ₀ Tτ B 1 k with hS₀
  have hS₀0 : 0 ≤ S₀ := Finset.sum_nonneg fun k _ => termConst_nonneg hΛ₀0 hTτ0 hB k
  refine ⟨Real.sqrt Cb * S₀ * CP + 1, Qf * Mst + QP, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hab hθ
  have hP := one_le_peFactor F.η
  have hP0 : 0 ≤ peFactor F.η := zero_le_one.trans hP
  have hleP : min gP (min gM gS) ≤ gP := min_le_left _ _
  have hleM : min gP (min gM gS) ≤ gM := (min_le_right _ _).trans (min_le_left _ _)
  have hleS : min gP (min gM gS) ≤ gS := (min_le_right _ _).trans (min_le_right _ _)
  -- the data at the start
  obtain ⟨W0f, hW0f⟩ := hSK (F.mono hleS) θ (m := m) (Ks := Ks)
  have hW₀ : IsScaledStage F θ F.a (fun i => W0f i F.a) :=
    (isScaledStage_mono F hleS θ F.a _).1 (hW0f F.a ⟨le_rfl, F.ordered⟩)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = Real.sqrt (∑ i, ‖W0f i F.a‖ ^ 2) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact Real.sqrt_nonneg _
  obtain ⟨V, hb⟩ := F.piece.hv.2.1
  set Mn := CP * peFactor F.η ^ QP * (1 + (F.b - F.a)) ^ QP * X with hMn
  have hT0 : 0 ≤ F.b - F.a := by linarith
  have hMn0 : 0 ≤ Mn := by positivity
  -- the plain pass at every time
  have hplain : ∀ t ∈ Icc (F.mono hleM).a (F.mono hleM).b,
      ∀ W : B1WIndex ι h Nw m Ks → ComplexCellL2, IsScaledStage (F.mono hleM) θ t W →
      ∀ (k : ℕ) (ψ : B1WIndex ι h Nw m Ks →
        TorusHk (b1wLadderAt Nw (Finset.univ.sup d + 3) d Ks k) ℂ),
        ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
          Mn * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
    intro t ht W hW k ψ
    have hk := hPSs (F.mono hleP) θ hlet ((reserve_plain_le Kf m d Ks).trans hJ) hθ V hb
      (fun _ _ => 1) (isFibreKernel_shift (b1wCoeff_eq_real (F.mono hleP) θ).symm
        (plainKernel (F.mono hleP).a (F.mono hleP).b (F.mono hleP).G
          (F.mono hleP).piece.hGm (F.mono hleP).piece.hv V hb θ))
      (fun i => W0f i F.a) ((isScaledStage_mono F hleP θ F.a _).2 hW₀) t ht W
      ((isScaledStage_mono F hleP θ t W).2 ((isScaledStage_mono F hleM θ t W).1 hW)) k ψ
    refine hk.trans ?_
    have ht1 : F.a ≤ t := ht.1
    have ht2 : t ≤ F.b := ht.2
    have hpow : (1 + (t - F.a)) ^ QP ≤ (1 + (F.b - F.a)) ^ QP :=
      pow_le_pow_left₀ (by linarith) (by linarith) QP
    have hs0 : 0 ≤ Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := Real.sqrt_nonneg _
    show CP * peFactor F.η ^ QP * (1 + (t - F.a)) ^ QP * 1 * Real.sqrt (∑ i, ‖W0f i F.a‖ ^ 2) *
        Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) ≤ Mn * _
    rw [← hX, mul_one, hMn]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) hX0) hs0
  -- the terminal pass by stage families
  have hfam := fullField_frame_family (F.mono hleM) θ hθ d (Finset.univ.sup d + 3) Kf
    (fun j x e β => hMK (F.mono hleM) j x e θ β) V hb hab Jt St
    (fun i => hJt ▸ b1wPosLadder_le Kf d i)
    (fun k hk => hSt ▸ b1wLadderAt_le_top (Finset.univ.sup d + 3) m d Ks hk) Cf Qf hCf.le
    hwinF Mn hMn0 (fun t ht => hplain t ⟨by have := (F.mono hleM).ordered; linarith [ht.1,
      show (F.mono hleM).a + 1 ≤ (F.mono hleM).b from hab], ht.2⟩) B hB
    (hP4aK _ (F.mono hleM) θ hlet ((reserve_sources_le Kf m d Ks).trans hJ) hθ)
  rw [← hJs] at hfam
  -- the band of the terminal stages
  have hband : ∀ i : B1WIndex ι h Nw m Ks, ∀ w : TorusHk (b1wPosLadder Kf d i) ℂ,
      cellBandSq Kf 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (Cb * ‖w‖ ^ 2) := by
    intro i w
    have hle : b1wPosLadder Kf d i < Jt + 1 := by
      have := b1wPosLadder_le Kf d i
      omega
    refine (hbN ⟨b1wPosLadder Kf d i, hle⟩ (b1wPosLadder_ge Kf d i) w θ hθ).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    rw [hCb]
    exact Finset.single_le_sum (f := CbN) (fun N _ => hCbN N) (Finset.mem_univ _)
  set T : ℕ → ℝ := fun k => termConst (Cf * (1 + Js / Real.sqrt F.η) ^ Qf) Tτ B 1 k with hTdef
  have hs : 0 < Real.sqrt F.η := Real.sqrt_pos.mpr F.piece.hη
  have hΛ0 : 0 ≤ Cf * (1 + Js / Real.sqrt F.η) ^ Qf := by
    have := div_nonneg hJs0 hs.le
    positivity
  have hTk0 : ∀ k, 0 ≤ T k := fun k => termConst_nonneg hΛ0 hTτ0 hB k
  have hterm := terminalBand_le F θ Kf d Cb hCb0 hband T hTk0 Mn hMn0 hfam
  -- the constants
  have hΛle : Cf * (1 + Js / Real.sqrt F.η) ^ Qf ≤ Λ₀ * peFactor F.η ^ Qf := by
    rw [hΛ₀, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (one_add_div_sqrt_le F.piece.hη hJs0) Qf) hCf.le
  have hTle : ∀ k < Mst, T k ≤ termConst Λ₀ Tτ B 1 k * peFactor F.η ^ (Qf * Mst) := by
    intro k hk
    have hPQ : 1 ≤ peFactor F.η ^ Qf := one_le_pow₀ hP
    calc T k ≤ termConst (Λ₀ * peFactor F.η ^ Qf) Tτ B 1 k :=
          termConst_mono hΛ0 hΛle hTτ0 hB k
      _ ≤ (peFactor F.η ^ Qf) ^ (k + 1) * termConst Λ₀ Tτ B 1 k :=
          termConst_le_scale hΛ₀0 hPQ hTτ0 hB k
      _ ≤ termConst Λ₀ Tτ B 1 k * peFactor F.η ^ (Qf * Mst) := by
          rw [← pow_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (by
            have := Nat.mul_le_mul_left Qf (show k + 1 ≤ Mst by omega)
            linarith)) (termConst_nonneg hΛ₀0 hTτ0 hB k)
  have hA : ∑ k ∈ Finset.range Mst, T k ≤ S₀ * peFactor F.η ^ (Qf * Mst) := by
    rw [hS₀, Finset.sum_mul]
    exact Finset.sum_le_sum fun k hk => hTle k (Finset.mem_range.1 hk)
  have harith := fullField_arith (QP := QP) hCb0 hS₀0 hCP.le hP hT0 hX0
    (Finset.sum_nonneg fun k _ => hTk0 k) hA
  rw [stageDatumSq_eq F θ _ hW₀]
  calc stageTerminalBandSq F m Ks Kf 0 θ
      ≤ ENNReal.ofReal (Cb * ((∑ k ∈ Finset.range Mst, T k) * Mn) ^ 2) := hterm
    _ ≤ ENNReal.ofReal (((Real.sqrt Cb * S₀ * CP + 1) * peFactor F.η ^ (Qf * Mst + QP) *
          (1 + (F.b - F.a)) ^ (Qf * Mst + QP)) ^ 2 * X ^ 2) :=
        ENNReal.ofReal_le_ofReal harith
    _ = ENNReal.ofReal (((Real.sqrt Cb * S₀ * CP + 1) * peFactor F.η ^ (Qf * Mst + QP) *
          (1 + (F.b - F.a)) ^ (Qf * Mst + QP)) ^ 2) *
          ENNReal.ofReal (∑ i, ‖W0f i F.a‖ ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), hX,
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
end

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords.Discard

/-! # the quiet stretch at the fibre level

`quietHighFibreAssembly : QuietHighFibreAssembly`: from the plain pass, the plain kernel and the
transform families of the zone. The three parts are `quietEntranceAssembly` (the plain pass at the
entrance, weighted `ℓ²` bound of the cell modes), `quietModeAssembly` (the mode-diagonal coupled
Duhamel equation with operator-norm coupling, uniform in the number of components) and
`quietAbsorbAssembly` (the vector triangular bound, the absorption of the polynomial factors by the
heat decay, the sum over the modes). -/

universe u v

/-- The quiet stretch at the fibre level. -/
theorem quietHighFibreAssembly : QuietHighFibreAssembly.{u, v} :=
  quietHighFibreAssembly_of_parts quietEntranceAssembly quietModeAssembly quietAbsorbAssembly

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Discard

/-! # Proved

* `fullFieldFibreAssembly : FullFieldFibreAssembly`: `fullFieldFibre_of_families` with the
  band bound and the family forms of the forced-curve and negative-smoothing bounds.
* `fullFieldFibre_of_sources`: `FullFieldFibreStatement` from `StageSourceHsStatement` alone; every other input is proved. -/

universe u v

/-- The full-field bound at the fibre level, as an assembly. -/
theorem fullFieldFibreAssembly : FullFieldFibreAssembly.{u, v} :=
  fullFieldFibre_of_families torusHkBandBound cellForcedHsFamily.{u}
    cellNegativeSmoothingFamily.{u}

/-- The full-field bound at the fibre level from the source bound alone. -/
theorem fullFieldFibre_of_sources (hP4a : StageSourceHsStatement.{u, v}) :
    FullFieldFibreStatement.{u, v} :=
  fullFieldFibreAssembly plainStage plainKernel stageFamilyZone cellKernelHs
    cellAdjointKernelHs cellForcedHs cellNegativeSmoothing hP4a

end AVRegularity.CycleWords.Discard
end
end
