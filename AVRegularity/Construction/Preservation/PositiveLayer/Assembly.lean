-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.PositiveLayer.CellFourierBounds
import AVRegularity.Construction.Preservation.PositiveLayer.DifferenceFrom
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.QuietDecay.Combine.Main
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Conversion of the quiet cell amplitudes to the literal Fourier window norm.
Infinite amplitudes are handled in ENNReal. A window shorter than one has no admissible start. The time supremum remains entrywise. -/

section
open QuietDecay CycleComparison.Lift

/-- Fixed coefficient conversion constant, independent of the component spaces and data. -/
def Orders.windowFourierConstant (o : Orders) : ℝ :=
  2 ^ o.L * (1 + 4 * Real.pi) *
    (4 * (2 ^ o.K * (2 ^ (o.K + (o.L + 3)) * 28)) * (centeredProfileJetConstant + 1)) + 1

private theorem windowFourierConstant_pos (o : Orders) : 0 < o.windowFourierConstant := by
  have := centeredProfileJetConstant_nonneg
  unfold Orders.windowFourierConstant
  positivity

private theorem decayF_later {a s t : ℝ} (hst : s ≤ t) : decayF a t ≤ decayF a s := by
  unfold decayF
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_left (sub_le_sub_right hst a) (by positivity))

variable {ι : Type} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {o : Orders} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}

/-- Each Fourier constituent is controlled by its own entry of the cell amplitude. -/
theorem positive_layer_coefficient_window_bound
    (P : Input (ι := ι) (h := h) o CG Cw Cj) {hh n m r : ℕ}
    (hhH : hh ≤ o.H) (hn1 : 1 ≤ n) (hnN : n ≤ o.N) (hm : m ≤ n) (hr : r ≤ o.K)
    (α : DerivativeWord2 m) (v u : ι) {s : ℝ} (has : P.a ≤ s) (hsb : s + 1 ≤ P.b) :
    (∑' ξ : NZMode, ENNReal.ofReal ((1 + modeLen ξ.1) ^ o.L) *
      ⨆ X, modeE ξ.1 (fun t => modeJet
        (fun Y z => liftDiff P.Cc P.Cc' hh n m α t Y z v u) ξ.1 r X) (Icc s (s + 1))) ≤
      ENNReal.ofReal o.windowFourierConstant *
        (cellAmplitude P hh n v u * decayF P.a s) := by
  classical
  let f := fun t Y z => liftDiff P.Cc P.Cc' hh n m α t Y z v u
  let B : ℝ≥0∞ := cellAmplitude P hh n v u * decayF P.a s
  have hC : 0 < o.windowFourierConstant := windowFourierConstant_pos o
  by_cases hBt : B = ⊤
  · change _ ≤ ENNReal.ofReal o.windowFourierConstant * B
    simp [hBt, not_le.mpr hC]
  have hBreal : ENNReal.ofReal B.toReal = B := ENNReal.ofReal_toReal hBt
  have hn0 : n ≠ 0 := by omega
  have hwin : Icc s (s + 1) ⊆ Icc P.a P.b := Icc_subset_Icc has hsb
  have seq := quiet_lift_diff_sequence_from P
  have hreg (t : ℝ) (ht : t ∈ Icc s (s + 1)) :
      IsBoxSmooth (o.entranceSlow + o.D + 2) o.entranceFast (f t) ∧
      ∀ X, AVenhance.IsZ2Periodic (f t X) := by
    simpa only [f, quietLiftDiff, hn0, ↓reduceIte] using
      seq.2.2.2.2.2.1 hh hhH n m α v u t (hwin ht)
  have hRD : 2 ≤ o.reserve := by
    have h1 := Nat.le_mul_of_pos_right o.D (by omega : 0 < o.H + 1)
    have h2 := Nat.le_mul_of_pos_right (o.D * (o.H + 1)) o.degree_pos
    dsimp only [Orders.reserve]
    have := o.source_order
    omega
  have hwords (t : ℝ) (ht : t ∈ Icc s (s + 1)) (X : Vec 2) (l mm : List (Fin 2))
      (hl : l.length ≤ o.K) (hmm : mm.length ≤ o.L + 5) (η : h u) (hη : ‖η‖ ≤ 1) :
      vecJ (fun X z => f t X z η) X l mm ≤ ENNReal.ofReal B.toReal := by
    rw [hBreal]
    have hw := vecJ_le_blkJ (quietLiftDiff P.Cc P.Cc') hh n t v u o.K (o.L + 5)
      hm α l mm hl hmm X η hη
    have ha := blkJ_le_ampQ (quietLiftDiff P.Cc P.Cc')
      (s := P.a) (T := P.b - P.a) (σ := t) (by simpa only [add_sub_cancel] using hwin ht)
      (K₀ := o.K) (J₀ := o.L + 4) (D := o.D) (H := o.H) (N := o.N) (hh := hh)
      hn1 hnN v u (S := o.K) (F := o.L + 5)
      (by unfold ordS; omega) (by unfold ordF; omega)
    have hw' : vecJ (fun X z => f t X z η) X l mm ≤
        cellAmplitude P hh n v u * decayF P.a t := by
      simpa only [cellAmplitude, f, quietLiftDiff, hn0, ↓reduceIte] using hw.trans ha
    exact hw'.trans (mul_le_mul_of_nonneg_left (decayF_later ht.1) zero_le)
  let : ∀ i, MeasurableSpace (h i) := fun _ => borel _
  let : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  obtain ⟨hc, hc'⟩ := positive_layer_promoted_sequences P
  have ht0 := setting_lift_all_degree_coefficient_transverse P.setting _ _ (by omega)
    P.Cc hc hh hhH n m α v u
  have ht1 := setting_lift_all_degree_coefficient_transverse
    (positive_layer_setting_restrict P.setting P.starts (P.new_le.trans (P.interval.trans P.end_le)))
    _ _ (by omega) P.Cc' hc' hh hhH n m α v u
  have htrans : IsTransverseOn P.par (Icc s (s + 1)) f := by
    intro t ht X z z'
    dsimp only [f, liftDiff]
    exact congrArg₂ (fun A B => A - B)
      (ht0 t ⟨P.starts.trans (P.new_le.trans (hwin ht).1), (hwin ht).2.trans P.end_le⟩ X z z')
      (ht1 t ⟨P.new_le.trans (hwin ht).1, (hwin ht).2.trans P.end_le⟩ X z z')
  have hW := positive_layer_wiener_bound
    (fun t ht => (hreg t ht).1) (fun t ht => (hreg t ht).2)
    (P := o.K) (L := o.L) (by dsimp only [Orders.entranceSlow]; omega)
    (by dsimp only [Orders.entranceFast]; omega)
    ENNReal.toReal_nonneg hwords P.par htrans hr
  refine (positive_layer_window_fourier_le_wiener f s o.L r).trans
    ((mul_le_mul_of_nonneg_left hW zero_le).trans ?_)
  have hconst :
      2 ^ o.L * (1 + 4 * Real.pi) *
        (4 * (2 ^ r * (2 ^ (o.K + (o.L + 3)) * (28 * B.toReal))) *
          (centeredProfileJetConstant + 1)) ≤ o.windowFourierConstant * B.toReal := by
    have hp : (2 : ℝ) ^ r ≤ 2 ^ o.K := pow_le_pow_right₀ (by norm_num) hr
    have hc0 := centeredProfileJetConstant_nonneg
    have hf0 : 0 ≤ 2 ^ o.L * (1 + 4 * Real.pi) *
        (4 * (2 ^ (o.K + (o.L + 3)) * 28) * (centeredProfileJetConstant + 1)) * B.toReal := by positivity
    calc
      _ = 2 ^ r * (2 ^ o.L * (1 + 4 * Real.pi) *
          (4 * (2 ^ (o.K + (o.L + 3)) * 28) * (centeredProfileJetConstant + 1)) * B.toReal) := by ring
      _ ≤ 2 ^ o.K * (2 ^ o.L * (1 + 4 * Real.pi) *
          (4 * (2 ^ (o.K + (o.L + 3)) * 28) * (centeredProfileJetConstant + 1)) * B.toReal) :=
        mul_le_mul_of_nonneg_right hp hf0
      _ = (o.windowFourierConstant - 1) * B.toReal := by
        unfold Orders.windowFourierConstant; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_mul (by positivity)]
  change _ ≤ ENNReal.ofReal o.windowFourierConstant * B
  calc
    _ ≤ ENNReal.ofReal (o.windowFourierConstant * B.toReal) := ENNReal.ofReal_le_ofReal hconst
    _ = _ := by rw [ENNReal.ofReal_mul hC.le, hBreal]

/-- The exact finite word and factorial count; it involves no component dimension. -/
def Orders.windowWordCount (o : Orders) : ℝ :=
  ∑ d ∈ Finset.Icc 1 o.N, ∑ _α : DerivativeWord2 d,
    ∑ j ∈ Finset.range (o.K + 1), (j.factorial : ℝ)⁻¹

/-- The Fourier window conversion in the positive-layer assembly is unconditional. -/
theorem positive_layer_cell_window_comparison (o : Orders) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) : CellWindowComparisonStatement o CG Cw Cj := by
  classical
  let Cf : ℝ := o.windowWordCount * o.windowFourierConstant + 1
  have hcount0 : 0 ≤ o.windowWordCount := by unfold Orders.windowWordCount; positivity
  have hC0 := (windowFourierConstant_pos o).le
  have hCf : 1 ≤ Cf := by dsimp only [Cf]; linarith only [mul_nonneg hcount0 hC0]
  have hcount : ENNReal.ofReal o.windowWordCount =
      ∑ d ∈ Finset.Icc 1 o.N, ∑ _α : DerivativeWord2 d,
        ∑ j ∈ Finset.range (o.K + 1), ENNReal.ofReal ((j.factorial : ℝ)⁻¹) := by
    unfold Orders.windowWordCount
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)
  refine ⟨Cf, hCf, ?_⟩
  intro ι _ h _ _ _ _ P hh hhH s has hsb
  have hdegree (n : ℕ) (hn : n ∈ Finset.Icc 1 o.N) (v u : ι) :
      degreeEntry (liftDiff P.Cc P.Cc') hh n o.K o.L (Icc s (s + 1)) none v u ≤
        (ENNReal.ofReal Cf * decayF P.a s) * cellAmplitude P hh n v u := by
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    let B := cellAmplitude P hh n v u * decayF P.a s
    have hc : ENNReal.ofReal o.windowWordCount * ENNReal.ofReal o.windowFourierConstant ≤
        ENNReal.ofReal Cf := by
      rw [← ENNReal.ofReal_mul hcount0]
      apply ENNReal.ofReal_le_ofReal
      exact le_add_of_nonneg_right zero_le_one
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 n, ∑ α : DerivativeWord2 d, ∑ j ∈ Finset.range (o.K + 1),
          ENNReal.ofReal ((j.factorial : ℝ)⁻¹) * (ENNReal.ofReal o.windowFourierConstant * B) := by
        unfold degreeEntry
        refine Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_left
          (positive_layer_coefficient_window_bound P hhH hn1 hnN (Finset.mem_Icc.mp hd).2
            (by have := Finset.mem_range.mp hj; omega) α v u has hsb) zero_le
      _ ≤ ∑ d ∈ Finset.Icc 1 o.N, ∑ _α : DerivativeWord2 d, ∑ j ∈ Finset.range (o.K + 1),
          ENNReal.ofReal ((j.factorial : ℝ)⁻¹) * (ENNReal.ofReal o.windowFourierConstant * B) :=
        Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl hnN)
      _ = ENNReal.ofReal o.windowWordCount * ENNReal.ofReal o.windowFourierConstant * B := by
        rw [hcount]
        simp_rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun j _ => ?_
        ring
      _ ≤ ENNReal.ofReal Cf * B := mul_le_mul_of_nonneg_right hc zero_le
      _ = _ := by dsimp only [B]; ring
  have hs : layerNorm P.π (liftDiff P.Cc P.Cc') hh o.N o.K o.L (Icc s (s + 1)) ≤
      ∑ n ∈ Finset.Icc 1 o.N, (ENNReal.ofReal Cf * decayF P.a s) *
        schurSums P.π (cellAmplitude P hh n) := by
    change schurSums P.π (fun v u => ∑ n ∈ Finset.Icc 1 o.N,
      degreeEntry (liftDiff P.Cc P.Cc') hh n o.K o.L (Icc s (s + 1)) none v u) ≤ _
    refine (schurSums_sum_le P.π _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    exact (schurSums_mono' P.π (hdegree n hn)).trans (schurSums_const_mul P.π _ _)
  refine hs.trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ zero_le
  unfold gradeSum
  apply Finset.sum_le_sum_of_subset
  intro n hn
  exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
end

/-! The quiet-cell amplitude recursion applied to the actual difference.
Degree zero has zero amplitude and grade zero has no source-grade term. Constants precede the component family and data.
-/

section
open QuietDecay

/-- A dimension-independent cell-amplitude recursion, without assuming finite traces. -/
theorem quiet_cell_amplitude (o : Orders) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    QuietCellAmplitudeStatement o CG Cw Cj := by
  classical
  let Csrc := srcConstU o.N o.D o.H o.K (o.L + 4) CG
  let Kc := levelK CG o.entranceSlow Csrc
  let rE := o.entranceSlow + o.N
  let χ := max 1 (envC Cj rE)
  let κ := max 1 Kc.toReal
  have hK : Kc ≤ ENNReal.ofReal κ := by
    calc Kc = ENNReal.ofReal Kc.toReal := (ENNReal.ofReal_toReal
          (show Kc ≠ ⊤ from levelK_ne_top CG o.entranceSlow Csrc)).symm
         _ ≤ ENNReal.ofReal κ := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  refine ⟨κ, χ, le_max_left _ _, le_max_left _ _, ?_⟩
  intro ι _ h _ _ _ _ P I htrace
  have hset : IsLiftSetting P.Q P.π P.a P.b P.e P.ν P.B P.ρ P.ρ P.ℓ P.dstar P.εc 1
      P.par P.V o.H o.N (o.K + o.D * (o.H + 1) * o.N)
      (0 + o.D * (o.H + 1) * o.N) ((o.L + 2) + o.D * (o.H + 1) * o.N)
      o.slowReserve o.cellFastReserve CG Cw Cj P.bb P.Θ := by
    simpa only [Orders.entranceSlow, Orders.settingFast, Orders.reserve,
      Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      positive_layer_auxiliary_setting P
  have hmax : max (0 + o.D * (o.H + 1) * o.N + 1)
      ((o.L + 2) + o.D * (o.H + 1) * o.N + 2) = o.entranceFast := by
    dsimp only [Orders.entranceFast, Orders.reserve]
    omega
  have hseq : IsLiftSequenceFrom P.Q (o.K + o.D * (o.H + 1) * o.N + o.D + 2)
      (max (0 + o.D * (o.H + 1) * o.N + 1)
        ((o.L + 2) + o.D * (o.H + 1) * o.N + 2)) P.a P.b o.N o.H
      (quietLiftDiff P.Cc P.Cc') := by
    simpa only [hmax, Orders.entranceSlow, Orders.reserve] using quiet_lift_diff_sequence_from P
  have hq : IsQuietOn P.Q.edge (fun t z => Real.sqrt P.Q.η • P.Q.v t z) (Icc P.a P.b) :=
    ⟨fun t ht z => by
      change Real.sqrt P.Q.η • P.Q.v t z = 0
      rw [P.drift_zero t ht z, smul_zero], P.independent⟩
  have hD := o.source_order
  have hqs := hset.qs_eq
  have hbig : o.N + 2 ≤ 4 * (o.H + 1) * (o.N + o.D) ^ 2 := by
    have h1 : o.N + 2 ≤ (o.N + o.D) ^ 2 := by have := o.source_order; nlinarith
    have h2 := Nat.le_mul_of_pos_left ((o.N + o.D) ^ 2)
      (by positivity : 0 < 4 * (o.H + 1))
    omega
  have hrE : rE ≤ o.slowReserve := by dsimp only [rE, Orders.entranceSlow, Orders.reserve]; rw [hqs]; omega
  have henv (v w : ι) : massW P.π v w * cellEnvelope P v w ≤
      ENNReal.ofReal χ * ENNReal.ofReal (P.bb v w) := by
    have he := massW_envB_le hset.envelope (by norm_num : (0 : ℝ) ≤ 1) le_rfl hrE v w
    change massW P.π v w * envB P.Q.edge (Icc P.a P.b) rE v w ≤ _
    refine he.trans ?_
    rw [ENNReal.ofReal_mul (envC_nonneg Cj rE)]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) zero_le
  have hrow (v : ι) : ∑ w, ENNReal.ofReal χ * ENNReal.ofReal (P.bb v w) ≤
      ENNReal.ofReal χ * ENNReal.ofReal P.Θ := by
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun u _ => hset.envelope.nonneg v u)]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hset.envelope.row_sum v)) zero_le
  have hcol (u : ι) : ∑ v, ENNReal.ofReal χ * ENNReal.ofReal (P.bb v u) ≤
      ENNReal.ofReal χ * ENNReal.ofReal P.Θ := by
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun v _ => hset.envelope.nonneg v u)]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hset.envelope.col_sum u)) zero_le
  refine ⟨hset.mass_pos, htrace, henv, henv, hrow, hcol, ?_⟩
  intro hh hhH n hn v u
  have hend : P.a + (P.b - P.a) = P.b := by ring
  by_cases hn1 : 1 ≤ n
  · have hq' : IsQuietOn P.Q.edge (fun t z => Real.sqrt P.Q.η • P.Q.v t z)
        (Icc P.a (P.a + (P.b - P.a))) := by simpa only [hend] using hq
    have hlast : P.a + (P.b - P.a) ≤ P.b := by simp
    have hrec := ampQ_rec (Csrc := Csrc) hset hseq (sub_nonneg.mpr P.interval) le_rfl hlast
      (by simpa only [hend] using P.drift_zero)
      (cellEnvelope P) ?_ (final_hzero hset hseq le_rfl hlast hq')
      (final_hreg hset hseq le_rfl hlast hq') hhH hn1 hn v u
    · change cellAmplitude P hh n v u ≤ _
      have hrec' : cellAmplitude P hh n v u ≤ Kc *
          (cellTrace P hh n v u + ∑ n' ∈ Finset.range n, cellAmplitude P hh n' v u +
            (if hh = 0 then 0 else ∑ n' ∈ Finset.range (o.N + 1),
              (∑ w, cellEnvelope P v w * cellAmplitude P (hh - 1) n' w u +
                ∑ w, cellAmplitude P (hh - 1) n' v w * cellEnvelope P w u))) := by
        simpa only [cellAmplitude, cellTrace, traceQ, hn1, hn, and_self, ↓reduceIte,
          Nat.zero_max, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.reduceAdd, Orders.entranceSlow, Orders.entranceFast, Orders.reserve,
          Csrc, Kc] using hrec
      exact hrec'.trans (mul_le_mul_of_nonneg_right hK zero_le)
    · intro g gH j hj1 hjN h01 σ hσ m hm α v u x hx X l m' hl hm'
      have hDsZ := final_hDsZ (D := o.D) (H := o.H) (k₀ := 0) (L₀ := o.L + 2) o.degree_pos
      have hS := ordS_le (K₀ := o.K) (D := o.D) (H := o.H) (hh := g) (n := j) o.degree_pos
      have hF := ordF_le (J₀ := o.L + 4) (D := o.D) (H := o.H) (hh := g) (n := j) o.degree_pos
      have hFseq := ordF_add_D_le (k₀ := 0) (L₀ := o.L + 2) o.degree_pos o.source_order gH hj1 hjN h01
      simp only [Nat.zero_max] at hFseq hm'
      have hσ' : σ ∈ Icc P.a P.b := by simpa only [hend] using hσ
      have hb := blockSrc_vecJ_le hDsZ hset hseq (Subset.rfl : Icc P.a P.b ⊆ Icc P.a P.b)
        hq gH hj1 hjN (p := ordS o.K o.D o.H o.N g j)
        (q := ordF (o.L + 4) o.D o.H o.N g j) (by omega)
        hFseq
        (by rw [hqs]; omega) α hm v u x hx hσ' X l m' hl hm'
      refine hb.trans ?_
      have he (v w : ι) : edgeEnv P.Q σ X v w (ordS o.K o.D o.H o.N g j + o.N) ≤
          cellEnvelope P v w :=
        (edgeEnv_mono P.Q σ X v w (r' := rE) (by dsimp only [rE, Orders.entranceSlow, Orders.reserve]; omega)).trans
          (by unfold edgeEnv; exact edgeSum_le_envB P.Q.edge hσ' X v w rE)
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (srcConst_le_srcConstU CG (by omega) (by omega)))
        (add_le_add le_rfl ?_)
      split_ifs with h0
      · exact le_rfl
      · exact Finset.sum_le_sum fun n' _ => add_le_add
          (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (he v w) zero_le)
          (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (he w u) zero_le)
  · have hz : cellAmplitude P hh n v u = 0 := by
      simp only [cellAmplitude, ampQ, hn1, false_and, ↓reduceIte]
    rw [hz]
    exact zero_le
end

end AVRegularity.Construction.Preservation.PositiveLayer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.PositiveLayer

/-! Assembly of the positive-layer comparison from proved ingredients.

For `H = 0` the degree-only initial-layer recursion closes; for `Θ = 0` the
diagonal entrance term is kept since natural powers have `0^0 = 1`. At `s = a` the decay factor is
one. If the interval is shorter than one the final quantification is vacuous. No dimension
or component count appears in the constants.
-/

private theorem triangular_factor_le {N H hh : ℕ} (h : hh ≤ H) {κ : ℝ} (hκ : 0 ≤ κ) :
    (1 + ENNReal.ofReal κ) ^ (N + 1) * (2 * (1 + ENNReal.ofReal κ) ^ (N + 1)) ^ hh ≤
      ENNReal.ofReal ((1 + κ) ^ (N + 1) * (2 * (1 + κ) ^ (N + 1)) ^ H) := by
  have hbase : (1 : ℝ≥0∞) ≤ 2 * (1 + ENNReal.ofReal κ) ^ (N + 1) := by
    have hpow : (1 : ℝ≥0∞) ≤ (1 + ENNReal.ofReal κ) ^ (N + 1) :=
      one_le_pow₀ (le_add_right le_rfl)
    calc 1 ≤ (1 + ENNReal.ofReal κ) ^ (N + 1) := hpow
      _ ≤ 2 * (1 + ENNReal.ofReal κ) ^ (N + 1) :=
        le_mul_of_one_le_left zero_le (by norm_num)
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase h) zero_le).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add zero_le_one hκ]
  norm_num

/-- The literal statement with the Fourier entrance conversion discharged.
The cell amplitude recursion is discharged by `quiet_cell_amplitude`, using the
actual quiet difference sequence. Triangular induction is
`QuietDecay.schur_amplitude_le`. -/
theorem comparison_lift_positive_layer_of_ingredients
    (Dm N H K L k sX sZ : ℕ) (hN : 1 ≤ N) (hD : 2 ≤ Dm)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h Dm) (π : ι → ℝ) (sOld sNew s₁ e ν B ρ E ℓ dstar εc lam : ℝ)
      (par : Fin 2) (V : ℝ → ℝ → ℝ) (bb : ι → ι → ℝ) (Θ : ℝ),
      IsLiftSetting Q π sOld s₁ e ν B ρ E ℓ dstar εc lam par V H N (K + Dm * (H + 1) * N) k
        (L + Dm * (H + 1) * N + 2) (K + Dm * (H + 1) * N + 4 * (H + 1) * (N + Dm) ^ 2)
        (max k (L + Dm * (H + 1) * N + 4) + H * Dm + 2 * N + 2 * Dm) CG Cw Cj bb Θ →
      sX ≤ K + Dm * (H + 1) * N + 4 * (H + 1) * (N + Dm) ^ 2 →
      sZ ≤ max k (L + Dm * (H + 1) * N + 4) + H * Dm + 2 * N + 2 * Dm →
      sOld ≤ sNew →
    ∀ Cc Cc' : ℕ → ℕ → LiftCoeff ι h,
      IsLiftSequence Q sX sZ sOld s₁ N H Cc → IsLiftSequence Q sX sZ sNew s₁ N H Cc' →
    ∀ a b : ℝ, sNew ≤ a → a ≤ b → b ≤ s₁ →
      (∀ t ∈ Set.Icc a b, ∀ z, Q.v t z = 0) →
      (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, IsFastIndependentOn (Set.Icc a b) (γ.coeff α)) →
    ∀ hh ≤ H, ∀ s : ℝ, a ≤ s → s + 1 ≤ b →
      layerNorm π (liftDiff Cc Cc') hh N K L (Set.Icc s (s + 1)) ≤
        ENNReal.ofReal (C * Real.exp (-(c * (s - a)))) *
          ∑ b' ∈ Finset.range (hh + 1), ENNReal.ofReal Θ ^ (hh - b') *
            entranceNorm π (liftDiff Cc Cc') b' N (K + Dm * (H + 1) * N)
              (L + Dm * (H + 1) * N + 4) a := by
  let o : Orders := ⟨Dm, N, H, K, L, k, sX, sZ, hN, hD⟩
  obtain ⟨κ, χ, hκ, hχ, hcell⟩ := quiet_cell_amplitude o CG Cw Cj
  obtain ⟨Ct, hCt, htrace⟩ := positive_layer_cell_entrance_comparison o CG Cw Cj
  obtain ⟨Cf, hCf, hwindow⟩ := positive_layer_cell_window_comparison o CG Cw Cj
  let Ctri := (1 + κ) ^ (N + 1) * (2 * (1 + κ) ^ (N + 1)) ^ H
  refine ⟨Cf * Ctri * χ ^ H * Ct, Real.pi ^ 2 / 4, by dsimp [Ctri]; positivity,
    by positivity, ?_⟩
  intro ι _ h _ _ _ _ Q π sOld sNew s₁ e ν B ρ E ℓ dstar εc lam par V bb Θ
    hset hsX hsZ hstarts Cc Cc' hseq hseq' a b ha hab hb hv hi hh hhH s has hsb
  let P : Input (ι := ι) (h := h) o CG Cw Cj :=
    ⟨Q, π, sOld, sNew, s₁, e, ν, B, ρ, E, ℓ, dstar, εc, lam, par, V, bb, Θ,
      hset, hsX, hsZ, hstarts, Cc, Cc', hseq, hseq', a, b, ha, hab, hb, hv, hi⟩
  let I : ℕ → ℝ≥0∞ := fun hh => ENNReal.ofReal Ct *
    entranceNorm π (liftDiff Cc Cc') hh N o.entranceSlow o.entranceFast a
  have R := hcell P I (fun hh hhH n => htrace P hh hhH n)
  have ht := (hwindow P hh hhH s has hsb).trans
    (mul_le_mul_of_nonneg_left (QuietDecay.schur_amplitude_le R hh hhH) zero_le)
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hχ0 : 0 ≤ χ := zero_le_one.trans hχ
  have hpχ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal χ := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hχ
  have hsum :
      (∑ b' ∈ Finset.range (hh + 1), (ENNReal.ofReal χ * ENNReal.ofReal Θ) ^ (hh - b') * I b') ≤
      ENNReal.ofReal χ ^ H * ENNReal.ofReal Ct *
        ∑ b' ∈ Finset.range (hh + 1), ENNReal.ofReal Θ ^ (hh - b') *
          entranceNorm π (liftDiff Cc Cc') b' N o.entranceSlow o.entranceFast a := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    dsimp only [I]
    rw [mul_pow]
    have hm := pow_le_pow_right₀ hpχ (show hh - b' ≤ H by omega)
    calc
      _ = ENNReal.ofReal χ ^ (hh - b') * (ENNReal.ofReal Ct *
          (ENNReal.ofReal Θ ^ (hh - b') * entranceNorm π (liftDiff Cc Cc') b' N
            o.entranceSlow o.entranceFast a)) := by ring
      _ ≤ ENNReal.ofReal χ ^ H * (ENNReal.ofReal Ct *
          (ENNReal.ofReal Θ ^ (hh - b') * entranceNorm π (liftDiff Cc Cc') b' N
            o.entranceSlow o.entranceFast a)) := mul_le_mul_of_nonneg_right hm zero_le
      _ = _ := by ring
  have htri := triangular_factor_le (N := N) hhH hκ0
  refine ht.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul htri hsum zero_le zero_le) zero_le).trans_eq ?_)
  rw [QuietDecay.decayF]
  dsimp only [Ctri] at *
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Cf * _ * χ ^ H * Ct),
    ENNReal.ofReal_mul (by positivity : 0 ≤ Cf * _ * χ ^ H),
    ENNReal.ofReal_mul (by positivity : 0 ≤ Cf * _),
    ENNReal.ofReal_mul (by positivity : 0 ≤ Cf), ENNReal.ofReal_pow hχ0]
  dsimp only [P, o, Orders.entranceSlow, Orders.entranceFast, Orders.reserve]

  ring

end AVRegularity.Construction.Preservation.PositiveLayer
end
