-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.B1WCrudeObjects
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.WeightedPlainDecayKappa
import AVRegularity.CycleWords.MixedWords.B1WWeightedMember
import AVRegularity.CycleWords.MixedWords.B1WWeightedNormFacts
public import AVRegularity.CycleWords.MixedWords.SharpLetterCommFact
import AVRegularity.CycleWords.MixedWords.B1WCrudeH4
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The output clauses of the poorly buffered instantiation

The data and the output relation hold without any hypothesis on the buffers
(`b1w_out_common`, used by the well-buffered instantiation too). For one moment
`β ∈ momentIndices m` (`b1w_poor_out`):
* the data: `c_q b1wDd(out β) ≤ C_d · datumJets` (`b1wDd_out_le`, finiteness from the
  level-0 identity);
* the error: in the poorly buffered case `1 ≤ C₀ P_e^{Q₀}(1+S)^{Q₀}(budget)`, so the crude
  `ε_s(out β)(b − a) ≤ C₂ P_e^{Q₂}(1+S)^{Q₂} b1wDd(out β)` fits `C_d P_e^Q (1+S)^Q (budget)`
  when `C₂ C₀ ≤ C_d`;
* the output relation: if `Θ_w = 0` the terminal level vanishes; otherwise the moment
  amplitude is at most `β! Θ_w ‖N₀‖` times the slow stage of `out β` at `b` (the terminal output
  relation, `q(b) = 1`), and `‖N₀‖ = e^{Re Ξ}`. -/

universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- The moment amplitude of an a.e. zero family vanishes. -/
theorem momentAmpNorm_eq_zero (π : ι → ℝ) (ϖ : ℝ) (β : ℕ × ℕ) (g : ∀ x, Vec 2 → h x)
    (θ : Vec 2) (hg : ∀ x, g x =ᵐ[volume] 0) : momentAmpNorm π ϖ β g θ = 0 := by
  have hc : ∀ x (c : Vec 2 → ℝ), (∫ y, c y • g x y) = 0 := fun x c => by
    rw [integral_congr_ae (g := fun _ => (0 : h x))]
    · exact integral_zero _ _
    · filter_upwards [hg x] with y hy
      rw [hy, Pi.zero_apply, smul_zero]
  unfold momentAmpNorm
  simp only [hc, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    ENNReal.ofReal_zero, add_zero, mul_zero, Finset.sum_const_zero]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

/-- `β! ≤ m!` on `momentIndices m`. -/
theorem factorial_le_of_mem_momentIndices {m : ℕ} {β : ℕ × ℕ} (hβ : β ∈ momentIndices m) :
    ((β.1.factorial * β.2.factorial : ℕ) : ℝ) ≤ m.factorial := by
  have hβm : β.1 + β.2 ≤ m := (Finset.mem_filter.1 hβ).2
  exact_mod_cast (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add
    _ _)).trans (Nat.factorial_le hβm)

/-- **The output clauses common to both instantiations** for one moment: the data and the output
relation (no hypothesis on the buffers). -/
theorem b1w_out_common (hL : LevelZeroDataStatement.{v}) (hZ : ZeroAmplitudeWordStatement.{u, v})
    (hTO : TerminalOutputStatement.{u, v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hmom : AmplitudeIdMoments F) (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (q : ℝ → ComplexCellL2) (hqb : q F.b = cellConstantCLM 1) (cq : ℝ) (hcq : 0 ≤ cq)
    (Cd Cout : ℝ) (hCd1 : cq ≤ Cd) (hCout : (m.factorial : ℝ) ≤ Cout)
    (fast err : ℝ) (hfast : 0 ≤ fast) (herr : 0 ≤ err) (β : ℕ × ℕ) (hβ : β ∈ momentIndices m) :
    ENNReal.ofReal (cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 (b1wOut Nw Ks β)) ≤
        ENNReal.ofReal Cd * datumJets F.π F.ϖ (β.1 + β.2 + ∑ i, Ks i) F.φ θ ∧
      momentAmpNorm F.π F.ϖ β (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ ≤
        ENNReal.ofReal (Real.exp (blockGauge F.pkg.actual.lam F.η F.a F.b θ).re * Cout *
          wordTheta F.ηg F.letters * (slowStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) q (b1wN₀ F θ)
            F.a (F.b - F.a) + fast + err)) := by
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  have hβm : β.1 + β.2 ≤ m := (Finset.mem_filter.1 hβ).2
  have hlev : b1wLevelMoments m Ks 0 = m + ∑ i, Ks i := by
    unfold b1wLevelMoments
    simp
  have hβN : β.1 + β.2 + ∑ l, Ks l ≤ b1wLevelMoments m Ks 0 := by rw [hlev]; omega
  have hfin : ∀ α ∈ momentIndices (b1wLevelMoments m Ks 0),
      blochFibreDerivNorm F.π (fun _ => 1) α F.φ θ ≠ ⊤ := fun α hα =>
    (b1w_level_zero_norms hL F m Ks θ Dθ hval hmem α hα).1
  have hout := b1wDd_out_le Ks F.π hϖ.le F.φ θ zero_le_one β hβN hfin
  rw [ENNReal.ofReal_one, one_mul] at hout
  set dJ := datumJets F.π F.ϖ (β.1 + β.2 + ∑ i, Ks i) F.φ θ with hdJ
  set bd := b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 (b1wOut Nw Ks β) with hbd
  have hbd0 : 0 ≤ bd := b1wDd_nonneg _ _ _ hϖ.le _ _ zero_le_one _
  refine ⟨?_, ?_⟩
  · -- the data
    rw [ENNReal.ofReal_mul hcq]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCd1) hout
  · -- the output relation
    have hΘw0 : 0 ≤ wordTheta F.ηg F.letters := F.piece.wordTheta_nonneg
    rcases hΘw0.eq_or_lt with h0 | hpos
    · rw [momentAmpNorm_eq_zero _ _ _ _ _ fun x => hZ K g₁ F h0.symm x F.b ⟨F.ordered, le_rfl⟩]
      exact bot_le
    have hA : 0 < b1wAmp F.ηg F.letters (Fin.last Nw) := by rw [b1wAmp_last]; exact hpos
    refine (hTO K g₁ F m Ks θ Dθ (fun i => hval i F.b ⟨F.ordered, le_rfl⟩)
      (fun i => hmem i F.b ⟨F.ordered, le_rfl⟩) hmom hA β hβ).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hN : 0 < ‖b1wN₀ F θ‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
    have hNe : ‖b1wN₀ F θ‖ = Real.exp (blockGauge F.pkg.actual.lam F.η F.a F.b θ).re := by
      unfold b1wN₀
      exact Complex.norm_exp _
    have hstage : stageNorm b1wSt (b1wOut Nw Ks β) (fun i => cellComplexPair
        (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) F.b))
        (cellConstantCLM 1)) = ‖b1wN₀ F θ‖ *
          slowStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) q (b1wN₀ F θ) F.a (F.b - F.a) := by
      unfold slowStage
      rw [show F.a + (F.b - F.a) = F.b by ring, hqb, mul_div_cancel₀ _ hN.ne']
      rfl
    rw [hstage, ← b1wAmp_last, ← hNe]
    have hsl0 : 0 ≤ slowStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) q (b1wN₀ F θ) F.a
        (F.b - F.a) := div_nonneg (stageNorm_nonneg _ _ _) (norm_nonneg _)
    have hfac := factorial_le_of_mem_momentIndices hβ
    calc ((β.1.factorial * β.2.factorial : ℕ) : ℝ) * b1wAmp F.ηg F.letters (Fin.last Nw) *
          (‖b1wN₀ F θ‖ * slowStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) q (b1wN₀ F θ) F.a
            (F.b - F.a))
        = ‖b1wN₀ F θ‖ * ((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
            b1wAmp F.ηg F.letters (Fin.last Nw) *
            slowStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) q (b1wN₀ F θ) F.a (F.b - F.a) := by
          ring
      _ ≤ ‖b1wN₀ F θ‖ * Cout * b1wAmp F.ηg F.letters (Fin.last Nw) *
            (slowStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) q (b1wN₀ F θ) F.a (F.b - F.a) +
              fast + err) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (hfac.trans hCout) hN.le) hA.le) (by linarith) hsl0 ?_
          exact mul_nonneg (mul_nonneg hN.le ((Nat.cast_nonneg _).trans (hfac.trans hCout)))
            hA.le


/-- **The output clauses of the poorly buffered instantiation** for one moment. -/
theorem b1w_poor_out (hL : LevelZeroDataStatement.{v}) (hZ : ZeroAmplitudeWordStatement.{u, v})
    (hTO : TerminalOutputStatement.{u, v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hmom : AmplitudeIdMoments F) (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (q : ℝ → ComplexCellL2) (hqb : q F.b = cellConstantCLM 1) (cq : ℝ) (hcq : 0 ≤ cq)
    (εs : ℕ → ℝ) (C₂ : ℝ) (hC₂ : 0 ≤ C₂) (Q₂ : ℕ)
    (hbud : ∀ k ≤ b1wM Nw m Ks, εs k * (F.b - F.a) ≤ C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂ *
      b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (Q₀ : ℕ) (c₀ : ℝ) (Q : ℕ) (Cd Cout cE Dq : ℝ) (hQ : Q₂ + Q₀ ≤ Q)
    (hCd1 : cq ≤ Cd) (hCd2 : C₂ * C₀ ≤ Cd) (hCout : (m.factorial : ℝ) ≤ Cout) (hcE : cE ≤ c₀)
    (hDq : 0 ≤ Dq)
    (hpoor : 1 ≤ C₀ * peFactor F.η ^ Q₀ * (1 + F.S) ^ Q₀ * ((1 + (F.reg.joins : ℝ)) *
      Real.exp (-c₀ * F.reg.buffer) + Real.exp (-c₀ * Dq)))
    (fast err : ℝ) (hfast : 0 ≤ fast) (herr : 0 ≤ err) (β : ℕ × ℕ) (hβ : β ∈ momentIndices m) :
    ENNReal.ofReal (cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 (b1wOut Nw Ks β)) ≤
        ENNReal.ofReal Cd * datumJets F.π F.ϖ (β.1 + β.2 + ∑ i, Ks i) F.φ θ ∧
      ENNReal.ofReal ((εs (b1wOut Nw Ks β) + 0) * (F.b - F.a)) ≤
        ENNReal.ofReal (Cd * peFactor F.η ^ Q * (1 + F.S) ^ Q * ((1 + (F.reg.joins : ℝ)) *
          Real.exp (-cE * F.reg.buffer) + Real.exp (-cE * Dq))) *
          datumJets F.π F.ϖ (β.1 + β.2 + ∑ i, Ks i) F.φ θ ∧
      momentAmpNorm F.π F.ϖ β (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ ≤
        ENNReal.ofReal (Real.exp (blockGauge F.pkg.actual.lam F.η F.a F.b θ).re * Cout *
          wordTheta F.ηg F.letters * (slowStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) q (b1wN₀ F θ)
            F.a (F.b - F.a) + fast + err)) := by
  obtain ⟨hdata, hampl⟩ := b1w_out_common hL hZ hTO F θ hmom Dθ hval hmem q hqb cq hcq Cd Cout
    hCd1 hCout fast err hfast herr β hβ
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  have hβm : β.1 + β.2 ≤ m := (Finset.mem_filter.1 hβ).2
  have hlev : b1wLevelMoments m Ks 0 = m + ∑ i, Ks i := by
    unfold b1wLevelMoments
    simp
  have hβN : β.1 + β.2 + ∑ l, Ks l ≤ b1wLevelMoments m Ks 0 := by rw [hlev]; omega
  have hfin : ∀ α ∈ momentIndices (b1wLevelMoments m Ks 0),
      blochFibreDerivNorm F.π (fun _ => 1) α F.φ θ ≠ ⊤ := fun α hα =>
    (b1w_level_zero_norms hL F m Ks θ Dθ hval hmem α hα).1
  have hout := b1wDd_out_le Ks F.π hϖ.le F.φ θ zero_le_one β hβN hfin
  rw [ENNReal.ofReal_one, one_mul] at hout
  set dJ := datumJets F.π F.ϖ (β.1 + β.2 + ∑ i, Ks i) F.φ θ with hdJ
  set bd := b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 (b1wOut Nw Ks β) with hbd
  refine ⟨hdata, ?_, hampl⟩
  -- the error
  have hP : 1 ≤ peFactor F.η := one_le_peFactor F.η
  have hS1 : 1 ≤ 1 + F.S := by linarith [F.piece.hS]
  have hbuf := F.pkg.buffer_nonneg
  set B₀ := (1 + (F.reg.joins : ℝ)) * Real.exp (-c₀ * F.reg.buffer) + Real.exp (-c₀ * Dq)
    with hB₀
  set BE := (1 + (F.reg.joins : ℝ)) * Real.exp (-cE * F.reg.buffer) + Real.exp (-cE * Dq)
    with hBE
  have hBB : B₀ ≤ BE := by
    have hj : 0 ≤ 1 + (F.reg.joins : ℝ) := by positivity
    refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hj)
      (Real.exp_le_exp.2 ?_)
    · exact mul_le_mul_of_nonneg_right (by linarith) hbuf
    · exact mul_le_mul_of_nonneg_right (by linarith) hDq
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hX0 : 0 ≤ C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂ :=
    mul_nonneg (mul_nonneg hC₂ (pow_nonneg (by linarith) _)) (pow_nonneg (by linarith) _)
  have hreal : C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂ ≤
      Cd * peFactor F.η ^ Q * (1 + F.S) ^ Q * BE := by
    have hC20 : 0 ≤ C₂ * C₀ := mul_nonneg hC₂ hC₀
    calc C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂
        ≤ C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂ *
            (C₀ * peFactor F.η ^ Q₀ * (1 + F.S) ^ Q₀ * B₀) := le_mul_of_one_le_right hX0 hpoor
      _ = (C₂ * C₀) * (peFactor F.η ^ (Q₂ + Q₀) * (1 + F.S) ^ (Q₂ + Q₀)) * B₀ := by ring
      _ ≤ Cd * (peFactor F.η ^ Q * (1 + F.S) ^ Q) * BE := by
          refine mul_le_mul (mul_le_mul hCd2 (mul_le_mul (pow_le_pow_right₀ hP hQ)
            (pow_le_pow_right₀ hS1 hQ) (pow_nonneg (by linarith) _)
            (pow_nonneg (by linarith) _)) (by positivity) (hC20.trans hCd2)) hBB hB₀0
            (mul_nonneg (hC20.trans hCd2) (by positivity))
      _ = Cd * peFactor F.η ^ Q * (1 + F.S) ^ Q * BE := by ring
  rw [add_zero]
  calc ENNReal.ofReal (εs (b1wOut Nw Ks β) * (F.b - F.a))
      ≤ ENNReal.ofReal (C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂ * bd) :=
        ENNReal.ofReal_le_ofReal (hbud _ (b1wOut_lt hβ).le)
    _ = ENNReal.ofReal (C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂) * ENNReal.ofReal bd :=
        ENNReal.ofReal_mul hX0
    _ ≤ ENNReal.ofReal (Cd * peFactor F.η ^ Q * (1 + F.S) ^ Q * BE) * dJ :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) hout
end Frame

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The well-buffered case: the good times with the sharp families

The good times of a frame (`b1w_good_frame`) in `[a, b]`, intersected with the full-measure set
where the sharp transform families exist (`b1w_sharp_family_provider`). Their first two
clauses are the crude families of `b1w_good_frame`. -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The good times of a well-buffered frame.** -/
theorem b1w_well_good {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (s : ℕ → ℕ) (n : ℕ) (B M₀ : ℝ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hlit : ∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      src i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ i.1 i.2.1
        (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ i.1 i.2.1
        (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r)
    (hsl : ∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
        ∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube))
    (hexp : ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hfam : ∀ᵐ r ∂volume.restrict (Icc F.a F.b), ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          B1WSharpFamily F θ r k k' (s k) (s k') ψ Φ B M₀)
    (hag : ∀ᵐ t ∂volume.restrict (Icc F.a F.b), q t = torusHkValueCLM (qs t)) :
    ∃ Good : Set ℝ, (∀ᵐ t ∂volume.restrict (Icc F.a F.b), t ∈ Good) ∧
      (∀ r ∈ Good, r ∈ Icc F.a F.b) ∧
      (∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
        src i r =ᵐ[volume.restrict AVenhance.unitCube]
          amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
        (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
        Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
          amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r) ∧
      (∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y) ∧
      (∀ r ∈ Good, ∀ (k k' : ℕ), k' < k → ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          B1WSharpFamily F θ r k k' (s k) (s k') ψ Φ B M₀) ∧
      ∀ r ∈ Good, torusHkValueCLM (qs r) = q r := by
  have hcrude : ∀ᵐ r ∂volume.restrict (Icc F.a F.b), ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (s k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 := by
    filter_upwards [hfam] with r hr k k' hk ψ
    obtain ⟨Φ, h1, h2, -⟩ := hr k k' hk ψ
    exact ⟨Φ, h1, h2⟩
  obtain ⟨Good, hGfull, hG1, hG2, -, hG4⟩ := b1w_good_frame F θ s n B src Fl q qs hlit hsl hexp
    hcrude hag
  refine ⟨(Good ∩ Icc F.a F.b) ∩ {r | ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          B1WSharpFamily F θ r k k' (s k) (s k') ψ Φ B M₀}, ?_, fun r hr => hr.1.2,
    fun r hr => hG1 r hr.1.1, fun r hr => hG2 r hr.1.1, fun r hr => hr.2,
    fun r hr => hG4 r hr.1.1⟩
  filter_upwards [hGfull, hfam, ae_restrict_mem measurableSet_Icc] with r h1 h2 h3
  exact ⟨⟨h1, h3⟩, h2⟩

end Frame
end

/-! # The weights of the word fibre facts on a frame, and the weighted adjoint families

* `b1wOmega F Λ k r` is `1` at `r = a`, and `max(1, Λ^{k+1} e^{-(3π²/8)(r − τ(r))})` elsewhere
  (`activityWeight` with the level `Λ^{k+1}`). `b1wOrient F` is the orientation of the last
  activity.
* `b1w_weighted_adj_frame`: the adjoint families of the weighted H4 (`b1w_weighted_H4`), with
  one constant for the stages `k < M`. They come from the weighted adjoint
  (`b1w_weighted_adjoint`, the weighted sharp decay) with `Λ₁ = Λ^{k+1}`:
  - `Λ₂ = 1` for the weight `1`;
  - `Λ₂ = Λ^{k'+1}`, `k' < k`, for the lower levels.
  Hypotheses: `Λ ≥ P_e^{Q'}`, and the regime at `Λ^M`. At `T = a` the datum's own split. -/

section
universe u v

/-- Finitely many positive reals have a positive lower bound. -/
theorem exists_pos_le_all (M : ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k < M, c₀ ≤ c k := by
  induction M with
  | zero => exact ⟨1, one_pos, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ M ih =>
    obtain ⟨c₀, hc₀, hle⟩ := ih
    refine ⟨min c₀ (c M), lt_min hc₀ (hc M), fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact (min_le_left _ _).trans (hle k hk)
    · exact min_le_right _ _

/-- Finitely many reals have an upper bound at least `1`. -/
theorem exists_one_le_ge_all (M : ℕ) (C : ℕ → ℝ) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ k < M, C k ≤ C₀ := by
  induction M with
  | zero => exact ⟨1, le_rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ M ih =>
    obtain ⟨C₀, hC₀, hle⟩ := ih
    refine ⟨max C₀ (C M), le_max_of_le_left hC₀, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact (hle k hk).trans (le_max_left _ _)
    · exact le_max_right _ _

/-- Finitely many naturals have an upper bound. -/
theorem exists_nat_ge_all (M : ℕ) (Q : ℕ → ℕ) : ∃ Q₀ : ℕ, ∀ k < M, Q k ≤ Q₀ :=
  ⟨∑ k ∈ Finset.range M, Q k, fun _ hk =>
    Finset.single_le_sum (f := Q) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hk)⟩

/-- The regime at `Λ^M` gives the regime at `Λ^k`, `k ≤ M`, with smaller constants. -/
theorem regime_mono_pow {Cb Cb' cb cb' Λ J P D : ℝ} {Q Q' k M : ℕ} (hCb : Cb' ≤ Cb)
    (hcb : cb ≤ cb') (hQ : Q' ≤ Q) (hΛ : 1 ≤ Λ) (hk : k ≤ M) (hJ : 0 ≤ J) (hP : 1 ≤ P)
    (hD : 0 ≤ D) (h : Cb * Λ ^ M * J * P ^ Q * Real.exp (-cb * D) ≤ 1) :
    Cb' * Λ ^ k * J * P ^ Q' * Real.exp (-cb' * D) ≤ 1 := by
  have hΛk : 0 ≤ Λ ^ k := pow_nonneg (by linarith) _
  have hPQ : 0 ≤ P ^ Q' := pow_nonneg (by linarith) _
  rcases le_total Cb' 0 with hneg | hpos
  · have : Cb' * Λ ^ k * J * P ^ Q' * Real.exp (-cb' * D) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hΛk) hJ) hPQ)
        (Real.exp_pos _).le
    linarith
  have h1 : Cb' * Λ ^ k ≤ Cb * Λ ^ M :=
    mul_le_mul hCb (pow_le_pow_right₀ hΛ hk) hΛk (hpos.trans hCb)
  have h2 : Cb' * Λ ^ k * J ≤ Cb * Λ ^ M * J := mul_le_mul_of_nonneg_right h1 hJ
  have h3 : Cb' * Λ ^ k * J * P ^ Q' ≤ Cb * Λ ^ M * J * P ^ Q :=
    mul_le_mul h2 (pow_le_pow_right₀ hP hQ) hPQ
      (mul_nonneg (mul_nonneg (hpos.trans hCb) (hΛk.trans (pow_le_pow_right₀ hΛ hk))) hJ)
  have h4 : Real.exp (-cb' * D) ≤ Real.exp (-cb * D) := Real.exp_le_exp.2 (by nlinarith)
  have h0 : 0 ≤ Cb' * Λ ^ k * J * P ^ Q' := mul_nonneg (mul_nonneg (mul_nonneg hpos hΛk) hJ) hPQ
  exact (mul_le_mul h3 h4 (Real.exp_pos _).le (h0.trans h3)).trans h

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- The weights of the word fibre facts on a frame. -/
def b1wOmega {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (Λ : ℝ) : ℕ → ℝ → ℝ :=
  fun k r => if r = F.a then 1 else
    activityWeight F.v F.t₀ (Λ ^ (k + 1)) (3 * Real.pi ^ 2 / 8) r

/-- The orientation of the last activity on a frame. -/
def b1wOrient {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : ℝ → Fin 2 :=
  activityOrient F.reg F.v F.t₀

variable {K : ScalarConstants} {g₁ : ℝ}
  (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)

theorem one_le_b1wOmega (Λ : ℝ) (k : ℕ) (r : ℝ) : 1 ≤ b1wOmega F Λ k r := by
  unfold b1wOmega
  split_ifs
  · exact le_rfl
  · exact one_le_activityWeight _ _ _ _ _

theorem b1wOmega_a (Λ : ℝ) (k : ℕ) : b1wOmega F Λ k F.a = 1 := by
  unfold b1wOmega
  simp

theorem b1wOmega_of_ne (Λ : ℝ) (k : ℕ) {r : ℝ} (hr : r ≠ F.a) :
    b1wOmega F Λ k r = activityWeight F.v F.t₀ (Λ ^ (k + 1)) (3 * Real.pi ^ 2 / 8) r := by
  unfold b1wOmega
  simp [hr]

end Frame

/-- **The weighted adjoint families on a frame.** -/
theorem b1w_weighted_adj_frame (hR : CellDriftRegularityStatement)
    (hW : WeightedSharpDecayStatement) (K : ScalarConstants) (Nw m : ℕ) (Ks : Fin Nw → ℕ)
    (s : ℕ → ℕ) {ρ : ℝ} (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hρ0 : 0 ≤ ρ) :
    ∃ (Cd Cb cb : ℝ) (Q Q' : ℕ), 1 ≤ Cd ∧ 0 < cb ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
      ∀ (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (Λ : ℝ), 1 ≤ Λ →
      peFactor F.η ^ Q' ≤ Λ →
      Cb * Λ ^ b1wM Nw m Ks * (1 + (F.reg.joins : ℝ)) * peFactor F.η ^ Q *
        Real.exp (-cb * F.reg.buffer) ≤ 1 →
      ∀ k < b1wM Nw m Ks, ∀ T ∈ Icc F.a F.b, ∀ ψ : ComplexCellL2,
        b1wAdm s (b1wRow F θ) k T ψ →
        ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
          CellWeakHilbertCurve F.a T Ψv Ψs (fun r =>
            -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
              (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
          Ψv T = ψ ∧
          (∀ r ∈ Icc F.a T, b1wAdm s (b1wRow F θ) k r (Ψv r)) ∧
          ∀ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ →
            cellTransverseProjection (b1wOrient F T) (torusHkValueCLM UT) =
              torusHkValueCLM UT →
          ∀ r ∈ Icc F.a T, ∀ ω ∈ {ω : ℝ | ω = 1 ∨ ∃ k' < k, b1wOmega F Λ k' r = ω},
            ∃ VT VN : TorusHk (s k) ℂ, torusHkValueCLM (VT + VN) = Ψv r ∧
              cellTransverseProjection (b1wOrient F r) (torusHkValueCLM VT) =
                torusHkValueCLM VT ∧
              ‖VT‖ + ω * ‖VN‖ ≤ Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
                (‖UT‖ + b1wOmega F Λ k T * ‖UN‖) := by
  choose Ck Cbk cbk Qk Q'k hCk hcbk hadj using fun k =>
    b1w_weighted_adjoint hR hW K s k hρ hρlo hρ0
  set M := b1wM Nw m Ks with hM
  obtain ⟨Cd, hCd1, hCd⟩ := exists_one_le_ge_all M Ck
  obtain ⟨Cb, -, hCb⟩ := exists_one_le_ge_all M Cbk
  obtain ⟨cb, hcb0, hcb⟩ := exists_pos_le_all M cbk hcbk
  obtain ⟨Q, hQ⟩ := exists_nat_ge_all M Qk
  obtain ⟨Q', hQ'⟩ := exists_nat_ge_all M Q'k
  refine ⟨Cd, Cb, cb, Q, Q', hCd1, hcb0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ D F θ hθ V hb Λ hΛ1 hΛ hreg k hk T hT ψ hψ
  have H := b1w_transverseLocalHyp F θ hρ hρlo hθ
  have hP := one_le_peFactor F.η
  have hJ : (0 : ℝ) ≤ 1 + (F.reg.joins : ℝ) := by positivity
  have hD := F.pkg.buffer_nonneg
  obtain ⟨Ψv, Ψs, h1, h2, h3, h4⟩ := hadj k F.η F.t₀ F.Sw F.ϖ F.G F.v F.g F.reg F.pkg
    F.piece.hη F.piece.hvs F.piece.hvj F.piece.hg0 F.piece.hg F.piece.hGn
    (planeFibreFrequency F.η θ) H hθ V hb F.left hT.1 (hT.2.trans F.right) ψ hψ
  refine ⟨Ψv, Ψs, h1, h2, h3, fun UT UN hU hUT r hr ω hω => ?_⟩
  have hexp0 : 0 ≤ Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) := (Real.exp_pos _).le
  by_cases hTa : T = F.a
  · -- at `T = a`, the datum's own split
    have hra : r = F.a := le_antisymm (hr.2.trans hTa.le) hr.1
    have hω1 : ω = 1 := by
      rcases hω with hω | ⟨k', -, hω⟩
      · exact hω
      · rw [← hω, hra, b1wOmega_a]
    have hrT : r = T := hra.trans hTa.symm
    subst hrT
    refine ⟨UT, UN, by rw [hU, h2], hUT, ?_⟩
    rw [hω1, sub_self, mul_zero, Real.exp_zero, mul_one, hTa, b1wOmega_a, one_mul]
    exact le_mul_of_one_le_left (add_nonneg (norm_nonneg _) (norm_nonneg _)) hCd1
  -- `T > a`: the two-level decay with `Λ₁ = Λ^{k+1}`
  have hΩT : b1wOmega F Λ k T = activityWeight F.v F.t₀ (Λ ^ (k + 1)) (3 * Real.pi ^ 2 / 8) T :=
    b1wOmega_of_ne F Λ k hTa
  have hk1 : k + 1 ≤ M := hk
  have hregk : Cbk k * Λ ^ (k + 1) * (1 + (F.reg.joins : ℝ)) * peFactor F.η ^ Qk k *
      Real.exp (-cbk k * F.reg.buffer) ≤ 1 :=
    regime_mono_pow (hCb k hk) (hcb k hk) (hQ k hk) hΛ1 hk1 hJ hP hD hreg
  have hPk : peFactor F.η ^ Q'k k ≤ Λ := (pow_le_pow_right₀ hP (hQ' k hk)).trans hΛ
  -- the decay with a lower level `Λ₂`
  have hlow : ∀ Λ₂ : ℝ, 1 ≤ Λ₂ → Λ₂ * Λ ≤ Λ ^ (k + 1) →
      ∃ VT VN : TorusHk (s k) ℂ, torusHkValueCLM (VT + VN) = Ψv r ∧
        cellTransverseProjection (b1wOrient F r) (torusHkValueCLM VT) = torusHkValueCLM VT ∧
        ‖VT‖ + activityWeight F.v F.t₀ Λ₂ (3 * Real.pi ^ 2 / 8) r * ‖VN‖ ≤
          Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * (‖UT‖ + b1wOmega F Λ k T * ‖UN‖) := by
    intro Λ₂ hΛ₂ hΛ₂Λ
    have hdrop : Λ₂ * peFactor F.η ^ Q'k k ≤ Λ ^ (k + 1) :=
      (mul_le_mul_of_nonneg_left hPk (by linarith)).trans hΛ₂Λ
    obtain ⟨VT, VN, hV, hVT, hVn⟩ := h4 UT UN hU hUT (Λ ^ (k + 1)) Λ₂ hΛ₂ hdrop hregk r hr
    refine ⟨VT, VN, hV, hVT, hVn.trans ?_⟩
    rw [← hΩT]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCd k hk) hexp0)
      (add_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans (one_le_b1wOmega F Λ k T))
        (norm_nonneg _)))
  -- the weight `1`, from `Λ₂ = 1`
  have hone : ∃ VT VN : TorusHk (s k) ℂ, torusHkValueCLM (VT + VN) = Ψv r ∧
      cellTransverseProjection (b1wOrient F r) (torusHkValueCLM VT) = torusHkValueCLM VT ∧
      ‖VT‖ + 1 * ‖VN‖ ≤
        Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * (‖UT‖ + b1wOmega F Λ k T * ‖UN‖) := by
    obtain ⟨VT, VN, hV, hVT, hVn⟩ := hlow 1 le_rfl
      (by rw [one_mul]; exact le_self_pow₀ hΛ1 (Nat.succ_ne_zero k))
    refine ⟨VT, VN, hV, hVT, le_trans ?_ hVn⟩
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (one_le_activityWeight _ _ _ _ _)
      (norm_nonneg _))
  rcases hω with hω | ⟨k', hk', hω⟩
  · rw [hω]
    exact hone
  · by_cases hra : r = F.a
    · rw [← hω, hra, b1wOmega_a]
      rw [hra] at hone
      exact hone
    · rw [← hω, b1wOmega_of_ne F Λ k' hra]
      refine hlow (Λ ^ (k' + 1)) (one_le_pow₀ hΛ1) ?_
      rw [← pow_succ]
      exact pow_le_pow_right₀ hΛ1 (by omega)
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The poorly buffered instantiation on one frame

With the objects of the crude pass (`b1w_crude_objects`), a poorly buffered frame satisfies the
conclusion of the word fibre facts (`b1w_poor_frame`, as `WordFibreFactsAt` with the frame's datum
jets and terminal amplitudes): the stage curves with the forcing off the good times, the slow test,
the gauge, the trivial class `Adm = {0}` with `ν = ‖·‖` (`b1w_trivial_H3s`, `b1w_trivial_H4`),
`ζ = 0`, `ε_s` the crude source bound, `ε_f = 0`, `D = c_q b1wDd`, `D_p = 0`, and the output clauses
of `b1w_poor_out`. -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The poorly buffered instantiation of the word fibre facts on one frame.** -/
theorem b1w_poor_frame (hL : LevelZeroDataStatement.{v}) (hZ : ZeroAmplitudeWordStatement.{u, v})
    (hTO : TerminalOutputStatement.{u, v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hθ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ)
    (hmom : AmplitudeIdMoments F) (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (Good : Set ℝ)
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ) (εs : ℕ → ℝ)
    (hW : ∀ i, CellWeakHilbertCurve F.a F.b (b1wW F Dθ i) (b1wWs F Dθ i) (fun t =>
      cellDualDerivative (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb t (b1wWs F Dθ i t)
        (b1wSr F src Good i t) (b1wFl F Fl Good i t)))
    (hq : CellWeakHilbertCurve F.a F.b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
        (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) t (qs t) 0 0))
    (hqb : q F.b = cellConstantCLM 1)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (cq : ℝ) (hcq : 0 ≤ cq)
    (hD0 : ∀ k, slowStage b1wSt k (b1wW F Dθ) q (b1wN₀ F θ) F.a 0 ≤
      cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
    (hεm : Monotone εs) (hε0 : ∀ k, 0 ≤ εs k)
    (hsrc : ∀ r ∈ Icc F.a F.b, ∀ k < b1wM Nw m Ks, ∀ β : B1WIndex ι h Nw m Ks → ℂ,
      ‖∑ i ∈ stageSet b1wSt k, β i * cellComplexSource (b1wCoeff F θ).θ
          (b1wSr F src Good i r) (b1wFl F Fl Good i r) (qs r)‖ ≤
        ‖b1wN₀ F θ‖ * εs k * stageNorm b1wSt k β)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂) (Q₂ : ℕ)
    (hbud : ∀ k ≤ b1wM Nw m Ks, εs k * (F.b - F.a) ≤ C₂ * peFactor F.η ^ Q₂ * (1 + F.S) ^ Q₂ *
      b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (Q₀ : ℕ) (c₀ : ℝ) (Q : ℕ) (Cz Cd Cout Θ Cf cE Dq : ℝ)
    (hQ : Q₂ + Q₀ ≤ Q) (hCz : 0 ≤ Cz)
    (hCd1 : cq ≤ Cd) (hCd2 : C₂ * C₀ ≤ Cd) (hCout : (m.factorial : ℝ) ≤ Cout) (hΘ : 0 ≤ Θ)
    (hCf : 0 ≤ Cf) (hcE : cE ≤ c₀) (hDq : 0 ≤ Dq)
    (hpoor : 1 ≤ C₀ * peFactor F.η ^ Q₀ * (1 + F.S) ^ Q₀ * ((1 + (F.reg.joins : ℝ)) *
      Real.exp (-c₀ * F.reg.buffer) + Real.exp (-c₀ * Dq))) :
    WordFibreFactsAt K m Ks (b1wM Nw m Ks) (b1wOut Nw Ks) Q Cz Cd Cout Θ Cf cE F.letters F.η F.S
      F.ηg F.t₀ F.Sw F.ϖ F.a F.b Dq F.G F.v F.reg F.pkg (fun n => datumJets F.π F.ϖ n F.φ θ)
      (fun β => momentAmpNorm F.π F.ϖ β (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ) θ := by
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  have hbd0 : ∀ k, 0 ≤ b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k :=
    b1wDd_nonneg _ _ _ hϖ.le _ _ zero_le_one
  have hbdm : Monotone (b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1) :=
    b1wDd_mono _ _ _ hϖ.le _ _ zero_le_one
  have hΓ := b1wGamma_pos F.pkg.actual.lam F.η F.a θ
  have hT0 : 0 ≤ F.b - F.a := sub_nonneg.2 F.ordered
  have H3s := b1w_trivial_H3s b1wSt (b1wM Nw m Ks) (b1wCoeff F θ) (b1wW F Dθ)
    (b1wSr F src Good) (b1wFl F Fl Good) q qs (b1wN₀ F θ) (b1wGamma F.pkg.actual.lam F.η F.a θ)
    Θ 0 εs F.a F.b hΘ le_rfl hΓ hsrc
  have H4 := b1w_trivial_H4 b1wSt (b1wM Nw m Ks) (b1wCoeff F θ) F.piece.hGm V F.piece.hv hb
    (b1wW F Dθ) (b1wSr F src Good) (b1wFl F Fl Good) q (b1wN₀ F θ)
    (b1wGamma F.pkg.actual.lam F.η F.a θ) Θ 0 Cf (fun _ => 0) F.a F.b hΘ le_rfl hCf hΓ
    (fun _ => le_rfl)
  have hfast0 : ∀ k t, fastStage b1wSt k (b1wW F Dθ) (fun _ _ ψ => ψ = 0) (fun _ _ ψ => ‖ψ‖)
      (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a t = 0 := fun k t => by
    unfold fastStage
    rw [fastRaw_trivial, mul_zero]
  refine ⟨B1WIndex ι h Nw m Ks, inferInstance, b1wSt, b1wCoeff F θ, F.piece.hGm, V, F.piece.hv,
    hb, b1wW F Dθ, b1wWs F Dθ, b1wSr F src Good, b1wFl F Fl Good, q, qs, b1wN₀ F θ,
    b1wGamma F.pkg.actual.lam F.η F.a θ, fun _ _ ψ => ψ = 0, fun _ _ ψ => ‖ψ‖, 0, εs,
    fun _ => 0, fun k => cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k, fun _ => 0,
    hW, hq, Complex.exp_ne_zero _, hΓ, b1w_gauge_growth F θ hρ hρlo hθ,
    fun _ _ c ψ hψ => by rw [hψ]; exact map_zero _,
    fun _ _ c ψ => by simp only [cellScalarCLM_smul, norm_smul], fun _ _ ψ _ => le_rfl, le_rfl,
    zero_le_one, by rw [zero_pow two_ne_zero, zero_mul]; positivity, hεm, monotone_const, hε0,
    fun _ => le_rfl, fun k k' hk => mul_le_mul_of_nonneg_left (hbdm hk) hcq, monotone_const,
    fun k => mul_nonneg hcq (hbd0 k), fun _ => le_rfl,
    fun k => by rw [zero_mul]; exact mul_nonneg hcq (hbd0 k), fun k _ => hD0 k,
    fun k _ => by rw [hfast0, mul_zero], H3s, H4, fun β hβ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := b1w_poor_out hL hZ hTO F θ hmom Dθ hval hmem q hqb cq hcq εs C₂ hC₂ Q₂
    hbud C₀ hC₀ Q₀ c₀ Q Cd Cout cE Dq hQ hCd1 hCd2 hCout hcE hDq hpoor
    (fastStage b1wSt (b1wOut Nw Ks β) (b1wW F Dθ) (fun _ _ ψ => ψ = 0) (fun _ _ ψ => ‖ψ‖)
      (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a (F.b - F.a))
    ((εs (b1wOut Nw Ks β) + 0) * (F.b - F.a)) (by rw [hfast0])
    (mul_nonneg (by linarith [hε0 (b1wOut Nw Ks β)]) hT0) β hβ
  exact ⟨h1, by rw [ENNReal.ofReal_zero]; exact bot_le, h2, h3⟩

end Frame
end

/-! # The poorly buffered half of the word fibre facts

For a buffering threshold `(Q₀, c₀)`, every word piece with
`1 ≤ P_e^{Q₀}(1+S)^{Q₀}((1+B_p)e^{-c₀·buffer} + e^{-c₀ D_q})` satisfies the conclusion of the word
fibre facts (`WordFibreFactsAt`), with `M = b1wM`, `out = b1wOut` and any constants above explicit
thresholds: `Q ≥ Q₀ + Q₁`, `C_d ≥ C₁`, `C_out ≥ m!`, `c_E ≤ c₀`, and `C_z, Θ, C_f ≥ 0`. The frame is
the capped frame of the piece (`b1wCappedFrame`, a compactly supported representative of the
datum by `planeDatum_rep`). The frame's datum jets and terminal amplitudes are those of the piece:
the representative agrees a.e. (`datumJets_congr_ae`), and the truncation does not change the
values (`planeValue_truncate`). -/

section
universe u v

/-- `d_max ≤ ∑ d`. -/
theorem sup_le_sum_nat {Nw : ℕ} (d : Fin Nw → ℕ) : Finset.univ.sup d ≤ ∑ l, d l :=
  Finset.sup_le fun l _ => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The weighted H3s at every time

The hypothesis `H3s` of the abstract fibre word `afw_bound` for the weighted test norm
`ν k r = b1wNuW s Ω e k r`, with `ζ = min 1 (|ξ| + S^{-1/2})` and `ε_s = 0`.
* At a good time the decomposition is exact (`b1w_weighted_H3s_at`). The slow test `q(r)` has
  the representatives `Uq r k = Eq(r)·1 + Dd r k` at every stage. Their weighted defects are
  hypotheses (`hΩw`, `hΩq`), discharged by the instantiation.
* Off the good times there is no forcing (`b1w_weighted_H3s_zero_forcing`). -/

universe u v

/-- **Weighted H3s with zero forcing**: the coefficients and the remainders `0`. -/
theorem b1w_weighted_H3s_zero_forcing {I : Type*} [Fintype I] (st : I → ℕ) (s : ℕ → ℕ)
    (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2) (tr : ℝ → ComplexCellL2) (r : ℝ)
    (hΩ0 : ∀ k', 0 ≤ Ω k' r) (k : ℕ) (θc : Fin 2 → ℂ) (W : I → ComplexCellL2)
    (q : ComplexCellL2) (qs : TorusHk 1 ℂ) (Θ ζ X : ℝ) (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ) (hX : 0 ≤ X)
    (N₀ : ℂ) (β : I → ℂ) :
    ∃ (κ : I → ℂ) (φ : I → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet st k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤ Θ * ζ ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', b1wNuW s Ω e k' r (φ i') ^ 2) ≤
        Θ * ζ * X * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource θc 0 (fun _ => 0) qs -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i'))‖ ≤
        ‖N₀‖ * 0 * stageNorm st k β := by
  have hν : ∀ k', b1wNuW s Ω e k' r 0 = 0 := fun k' => le_antisymm
    ((b1wNuW_le_mul s Ω e k' r (hΩ0 k') 0 (map_zero _)).trans_eq (by rw [norm_zero, mul_zero]))
    (b1wNuW_nonneg s Ω e k' r (hΩ0 k') 0)
  have hβ := stageNorm_nonneg st k β
  refine ⟨0, 0, fun k' _ i' _ => ⟨⟨0, map_zero _⟩, cellComplexPair_zero_right _⟩,
    fun k' _ => ?_, fun k' _ => ?_, ?_⟩
  · have h0 : stageNorm st k' (0 : I → ℂ) = 0 := by
      unfold stageNorm
      simp
    rw [h0]
    positivity
  · simp only [Pi.zero_apply, hν, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  · simp only [cellComplexSource_zero, mul_zero, Finset.sum_const_zero, Pi.zero_apply, zero_mul,
      cellComplexPair_zero_right, add_zero, sub_zero, norm_zero, le_refl]

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The weighted H3s at every time.** -/
theorem b1w_weighted_H3s {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (hη : 0 < F.η) (s : ℕ → ℕ) (n : ℕ)
    (hn : ∀ k, n + 3 ≤ s k)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (Good : Set ℝ)
    (hGsrc : ∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
      src i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
      (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r)
    (hGexp : ∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ (i i' : B1WIndex ι h Nw m Ks), ¬ b1wSt i' < b1wSt i →
      ∀ (r : ℝ) (φ : Vec 2 → ℂ), b1wTestTransform F θ i i' r φ = 0)
    (B M₀ : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ r ∈ Good, ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          B1WSharpFamily F θ r k k' (s k) (s k') ψ Φ B M₀)
    (tr q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hGq : ∀ r ∈ Good, torusHkValueCLM (qs r) = q r) (E : ℝ → ℂ)
    (hE : ∀ r ∈ Icc F.a F.b, cellComplexPair (tr r + cellConstantCLM 1) (q r) = E r)
    (hE0 : ∀ r, E r ≠ 0)
    (htr : ∀ r ∈ Good, ‖tr r‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ))
    (cE Cw : ℝ) (hcE : 0 ≤ cE) (hCw : 0 ≤ Cw) (M : ℕ)
    (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2) (hΩ0 : ∀ k r, 0 ≤ Ω k r)
    (Uq : ℝ → ∀ k', TorusHk (s k') ℂ) (Eq : ℝ → ℂ) (Dd : ℝ → ∀ k', TorusHk (s k') ℂ)
    (hUq : ∀ r ∈ Good, ∀ k' < M, torusHkValueCLM (Uq r k') = q r)
    (hUqn : ∀ r ∈ Good, ∀ k' < M, ‖Uq r k'‖ ≤ Cw * ‖E r‖)
    (hUd : ∀ r ∈ Good, ∀ k' < M, Uq r k' = torusHigherConstant (s k') (Eq r) + Dd r k')
    (hDd : ∀ r ∈ Good, ∀ k' < M,
      ‖Dd r k'‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖Eq r‖)
    (hEq : ∀ r ∈ Good, ‖Eq r‖ ≤ cE * ‖E r‖)
    (hwin : ∀ r ∈ Good, ∀ k' < M, 1 < Ω k' r →
      ∃ p, IsLeastWindow F.reg p r ∧ F.reg.orient p = e r)
    (hΩw : ∀ r ∈ Good, ∀ k < M, ∀ k' < k, 1 < Ω k' r →
      ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
        (∀ U, torusHkValueCLM (P U) = cellTransverseProjection (e r) (torusHkValueCLM U)) →
        Ω k' r * ‖Uq r k - P (Uq r k)‖ ≤
          min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) * ‖E r‖)
    (hΩq : ∀ r ∈ Good, ∀ k' < M, 1 < Ω k' r →
      ∀ P : TorusHk (s k') ℂ →L[ℝ] TorusHk (s k') ℂ,
        (∀ U, torusHkValueCLM (P U) = cellTransverseProjection (e r) (torusHkValueCLM U)) →
        Ω k' r * ‖Uq r k' - P (Uq r k')‖ ≤ ‖E r‖)
    (N₀ : ℂ) (Γ : ℝ → ℝ) (hNΓ : ∀ r ∈ Icc F.a F.b, ‖N₀‖ * Γ r = ‖E r‖) (Θ : ℝ)
    (hΘ : b1wWeightedΘ B cE Cw ≤ Θ) :
    ∀ r ∈ Icc F.a F.b, ∀ k < M, ∀ β : B1WIndex ι h Nw m Ks → ℂ,
      ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤
        Θ * min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ^ 2 *
          stageNorm b1wSt k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNuW s Ω e k' r (φ i') ^ 2) ≤
        Θ * min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) *
          (‖N₀‖ * Γ r) * stageNorm b1wSt k β) ∧
      ‖∑ i ∈ stageSet b1wSt k, β i * cellComplexSource
          (fun j => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ j)
          (Good.indicator (fun t =>
            cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) t)) r)
          (Good.indicator (fun t j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
            (cellSourceSlice (fun r z => Fl i r z j) t)) r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
              (cellRawTrace (Dθ i') r)) (q r) +
            cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
              (cellRawTrace (Dθ i') r)) (φ i'))‖ ≤
        ‖N₀‖ * 0 * stageNorm b1wSt k β := by
  intro r hr k hk β
  have hΘw0 : 0 ≤ b1wWeightedΘ B cE Cw := by unfold b1wWeightedΘ; positivity
  have hΘ0 : 0 ≤ Θ := hΘw0.trans hΘ
  have hX : 0 ≤ ‖N₀‖ * Γ r := by rw [hNΓ r hr]; exact norm_nonneg _
  have hζ0 : 0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
    le_min zero_le_one (add_nonneg (fibreNorm_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _)))
  have hβ0 := stageNorm_nonneg b1wSt k β
  by_cases hg : r ∈ Good
  swap
  · -- no forcing off the good times
    simp only [Set.indicator_of_notMem hg]
    exact b1w_weighted_H3s_zero_forcing b1wSt s Ω e tr r (fun k' => hΩ0 k' r) k _ _ (q r)
      (qs r) _ _ _ hΘ0 hζ0 hX N₀ β
  -- a good time
  simp only [Set.indicator_of_mem hg]
  rw [fibreShift_eq hη θ]
  obtain ⟨hS', hF', hW'⟩ := b1w_good_stage_ae F θ Dθ src Fl r (fun i => hval i r hr)
    (fun i => hmem i r hr) (hGsrc r hg)
  obtain ⟨PN, hPN, -⟩ := transverseHsProjection (e r) (s k)
  choose Pw hPw hPwn using fun k' => transverseHsProjection (e r) (s k')
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_weighted_H3s_at F θ r k hπ hϖ s n (s k) (hn k)
    (fun i' => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i') (cellRawTrace (Dθ i') r))
    (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
    (fun i j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z j) r))
    (q r) (qs r) (Uq r k) (hUq r hg k hk) (hGq r hg)
    (fun i _ => hS' i) (fun i _ j => hF' i j) (fun i _ => hGexp r hg i)
    (fun i hi i' hi' => hearly i i' (by rw [(Finset.mem_filter.1 hi).2]; exact hi') r)
    hW' B M₀ (fun ψ k' hk' => hprov r hg k k' hk' ψ) hB tr Ω e (fun k' => hΩ0 k' r)
    (Eq r) (Dd r k) (hUd r hg k hk) (hDd r hg k hk) (htr r hg) (E r) (hE r hr) (hE0 r)
    cE Cw hcE hCw (hEq r hg) (Uq r) (fun k' hk' => hUq r hg k' (hk'.trans hk))
    (fun k' hk' => hUqn r hg k' (hk'.trans hk)) PN hPN Pw hPw hPwn
    (fun k' hk' => hwin r hg k' (hk'.trans hk))
    (fun k' hk' hΩ => hΩw r hg k hk k' hk' hΩ PN hPN)
    (fun k' hk' hΩ => hΩq r hg k' (hk'.trans hk) hΩ (Pw k') (hPw k')) N₀ (Γ r)
    (hNΓ r hr) β
  refine ⟨κ, φ, h1, fun k' hk' => (h2 k' hk').trans ?_, fun k' hk' => (h3 k' hk').trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΘ (by positivity)) hβ0
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΘ hζ0) hX) hβ0
  · rw [h4, sub_self, norm_zero, mul_zero, zero_mul]

end Frame

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the block statement `SlBlockStmt`

`slBlockStmt : SlBlockStmt`.  The constant is `8 * gamCfin D n |ρ| M0 Sm`; the gain family and the
zero family are assembled from `br_gain`, `br_zero` by `block_gen`, and the two are put
together into `SlBlockSplit`. -/

universe u v

theorem gamCfin_nonneg (D n M0 S : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ gamCfin D n ρ M0 S := by
  unfold gamCfin gamPr
  have h1 := gamCc_nonneg D M0 S
  have h3 : 0 ≤ ∑ K ∈ Finset.range (n + D + 1), |cellDriftNativePrice K| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  positivity

theorem scal {G T rel cw : ℝ} (hG : 0 ≤ G) (hT : 0 ≤ T) (hrel : 0 ≤ rel) (hcw : 0 ≤ cw) :
    T * (4 * G * rel * cw) ≤ 8 * G * T * (rel * cw) := by
  have : 0 ≤ G * T * (rel * cw) := mul_nonneg (mul_nonneg hG hT) (mul_nonneg hrel hcw)
  nlinarith

open Classical in
/-- **The block statement.** -/
theorem slBlockStmt : SlBlockStmt.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  have hC0 : 0 ≤ 8 * gamCfin D n |ρ| (m + ∑ l, Ks l) (Finset.univ.sup Ks) := by
    have := gamCfin_nonneg D n (m + ∑ l, Ks l) (Finset.univ.sup Ks) (abs_nonneg ρ)
    positivity
  refine ⟨8 * gamCfin D n |ρ| (m + ∑ l, Ks l) (Finset.univ.sup Ks), hC0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hϖpos : 0 < F.ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_self hη.le hS).trans hη1)
  have hθt : ∀ k, |θ k| ≤ fibreNorm (planeFibreFrequency F.η θ) :=
    fun k => theta_abs_le hη hη1 θ le_rfl k
  have hgood : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
      ∀ l, LetterGood (F.letters l) (Icc F.a F.b) F.J r := by
    have h1 : ∀ᵐ r ∂(volume : Measure ℝ), ∀ l, r ∈ Icc F.a F.b →
        LetterGood (F.letters l) (Icc F.a F.b) F.J r :=
      ae_all_iff.2 fun l => letterGood_ae F.π F.piece.hπ (F.letters l) (Icc F.a F.b) F.J F.H
        (F.piece.hlet l)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h1] with r hr hrI l using hr l hrI
  filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with r hg hr
  intro l x x' β β' hβ hβ'
  set M0 := m + ∑ l, Ks l with hM0
  set Sm := Finset.univ.sup Ks with hSm
  set Dmax := Finset.univ.sup d with hDmax
  set t := fibreNorm (planeFibreFrequency F.η θ) with ht
  set ζ := min 1 (t + (Real.sqrt F.S)⁻¹) with hζ
  have hρ0 : 0 ≤ |ρ| := abs_nonneg ρ
  obtain ⟨hϖ0', hϖζ⟩ := sl80_varpi F θ
  obtain ⟨hζ0, htζ⟩ := sl80_zeta F θ ρ hρ
  have hζ1 : ζ ≤ 1 := min_le_left _ _
  have ht0 : 0 ≤ t := fibreNorm_nonneg _
  have htρ : t ≤ |ρ| := hρ.trans (le_abs_self ρ)
  have hord : (F.letters l).order ≤ Dmax := by
    rw [(hlet l).1]; exact Finset.le_sup (f := d) (Finset.mem_univ l)
  have hslow : (F.letters l).slow ≤ Sm := by
    rw [(hlet l).2.1]; exact Finset.le_sup (f := Ks) (Finset.mem_univ l)
  have hL1 : n + (F.letters l).order ≤ n + d l := by rw [(hlet l).1]
  have hNmin : (F.letters l).order + 3 ≤ d l + 3 := by rw [(hlet l).1]
  have hJ' : n + Dmax ≤ F.J := hJ
  set kc := ‖torusHigherConstant (n + d l) 1‖ with hkc
  set Af := admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x)
    (l.castSucc, x') with hAf
  set G := gamCfin D n |ρ| M0 Sm with hG
  have hG0 : 0 ≤ G := gamCfin_nonneg D n M0 Sm hρ0
  have hrel0 : 0 ≤ (if LetterMomRel Sm (Dmax + 1) β β' then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hcw0 := letterCompWeight_nonneg (F.piece.hlet l) x x'
  have hgain := block_gen true F.π F.letters l F.a F.b F.J F.H (F.piece.hlet l) F.ϖ F.ηg θ |ρ| hρ0
    F.X₀ r Af n (n + d l) (d l + 3) Dmax M0 Sm hord hslow x x' β β' F.ϖ F.ϖ (F.ϖ * kc)
    (ζ ^ 2 * kc) hϖpos.le hϖpos.le (by positivity) (by positivity)
    (fun hθpos w hw dd hd γ hγ => by
      have := br_gain F.π F.letters l F.a F.b F.J F.H (F.piece.hlet l) r hr (hg l) F.piece.hπ
        F.ϖ F.ηg hϖpos hϖ1 F.piece.hηg F.piece.hηg1 θ |ρ| hρ0 ζ t hϖζ hζ1 ht0 htρ htζ hθt F.X₀ n
        (n + d l) (d l + 3) Dmax M0 Sm hord hslow hJ' hL1 hNmin x x' β β' hβ hβ'
        hθpos w hw dd hd γ hγ
      exact brq_mono this (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
        (le_of_eq (by ring)))
  have hzero := block_gen false F.π F.letters l F.a F.b F.J F.H (F.piece.hlet l) F.ϖ F.ηg θ |ρ| hρ0
    F.X₀ r Af n (n + d l) (d l + 3) Dmax M0 Sm hord hslow x x' β β' 1 t (t * kc)
    (ζ ^ 2 * kc) zero_le_one ht0 (by positivity) (by positivity)
    (fun hθpos w hw dd hd γ hγ => by
      have := br_zero F.π F.letters l F.a F.b F.J F.H (F.piece.hlet l) r hr (hg l) F.piece.hπ
        F.ϖ F.ηg hϖpos hϖ1 F.piece.hηg F.piece.hηg1 θ |ρ| hρ0 ζ t hϖζ hζ1 ht0 htρ htζ hθt F.X₀ n
        (n + d l) (d l + 3) Dmax M0 Sm hord hslow hJ' hL1 hNmin x x' β β' hβ hβ'
        hθpos w hw dd hd γ hγ
      exact brq_mono this (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
        (le_of_eq (by ring)))
  obtain ⟨Tg, hvg, g1, -, -, g4⟩ := hgain
  obtain ⟨Tz, hvz, -, z2, z3, z4⟩ := hzero
  refine ⟨Tg, Tz, hvg, hvz, ?_, ?_, ?_, ?_⟩
  · refine g1.mono ?_
    calc _ ≤ _ := scal hG0 hϖpos.le hrel0 hcw0
      _ = _ := by ring
  · refine z2.mono ?_
    calc _ ≤ _ := scal hG0 ht0 hrel0 hcw0
      _ = _ := by ring
  · refine z3.mono ?_
    calc _ ≤ _ := scal hG0 (mul_nonneg ht0 (norm_nonneg _)) hrel0 hcw0
      _ = _ := by ring
  · simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    refine (g4.add z4).mono ?_
    have := scal hG0 (mul_nonneg (sq_nonneg ζ) (norm_nonneg (torusHigherConstant (n + d l) 1)))
      hrel0 hcw0
    nlinarith [this]

end AVRegularity.CycleWords.Assembly
end

section
namespace AVRegularity.CycleWords.Assembly

/-! # the sharp letter operators and the letter facts

`sharpLetterAE` from the block statement `slBlockStmt`. -/

universe u v

/-- **The sharp letter facts at almost every time.** -/
theorem sharpLetterAE : SharpLetterAEStatement.{u, v} := sharpLetterAE_of_blocks slBlockStmt

end AVRegularity.CycleWords.Assembly
end
