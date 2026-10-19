-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.B1NegPair
import AVRegularity.CycleWords.MixedWords.Discard.MixedWordsOfBandJet
import AVRegularity.CycleWords.Seam.S3bRoughMain
import AVRegularity.CycleWords.Seam.S3bRoughCore
import AVRegularity.CycleWords.MixedWords.RetainedAmplitudeFactor
import AVRegularity.CycleWords.Seam.OldNegative
import AVRegularity.CycleWords.Assembly.CycleSeamOfIngredients
import AVRegularity.CycleWords.Seam.OldScalar.Assembly
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldWindowFamily
import AVRegularity.CycleJoint.Assembly.CycleJointOfSeam
import AVRegularity.CycleWords.MixedWords.Discard.WeakContinuity

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The quiet entrance quiet margin on the plane

`QuietMarginPlaneStatement`: for a word chain from compactly supported data on a block whose entrance
`[t₀, t₀ + a']` is quiet, the molecular output norm of the endpoint is at most
`CΘ_w P_e^Q (1+S)^Q (e^{-ca'} ‖f‖_{neg} + ‖μ₂(D)f‖_{mom})`.

`s3b_quietMarginPlane_of_parts`: from the quiet margin at the fibre level (`b1_quietMarginFibre`), the stage data in negative
order and in the low band and the Bloch output with the multiplier `0`, through
the frame of the chain, as `chainFullFieldCompactAssembly`. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- The negative norm depends on the field only up to null sets. -/
theorem s3b_negJetNorm_congr_ae {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] (π : ι → ℝ) (p : ℝ) (j : ℕ)
    (s r : ℝ) {g g' : ∀ x, Vec 2 → h x} (hg : ∀ x, g x =ᵐ[volume] g' x) :
    negJetNorm π p j s r g = negJetNorm π p j s r g' := by
  unfold negJetNorm
  refine iSup_congr fun φ => iSup_congr fun _ => iSup_congr fun _ => ?_
  have he : ∀ x, ∫ z, inner ℝ (g x z) (φ x z) = ∫ z, inner ℝ (g' x z) (φ x z) := fun x =>
    integral_congr_ae (by filter_upwards [hg x] with z hz; rw [hz])
  simp only [he]

/-- The cutoff depends on the field only up to null sets. -/
theorem s3b_fourierCutoff_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Vec 2 → ℝ) {g g' : Vec 2 → E} (hg : g =ᵐ[volume] g') :
    fourierCutoff m g = fourierCutoff m g' := by
  funext y
  unfold fourierCutoff
  refine integral_congr_ae ?_
  have h' : (fun x => g (y - x)) =ᵐ[volume] fun x => g' (y - x) :=
    ((volume : Measure (Vec 2)).measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [h'] with x hx
  simp only [hx]

/-- **The quiet entrance quiet margin on the plane.** -/
def QuietMarginPlaneStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D H Kf m k : ℕ) (Cout : ℝ), 0 < Cout → ∀ (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool)
    (μ₂ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ₂ → HasCompactSupport μ₂ → (∀ ξ, μ₂ (-ξ) = μ₂ ξ) →
    (∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ Real.pi / 4 → μ₂ ξ = 1) →
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg rstar t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar (Kf + k) (wordReserveN m Ks) d) d ≤ J →
    0 < rstar → rstar ≤ Cout →
  ∀ a' : ℝ, 0 ≤ a' → a' ≤ S → Icc t₀ (t₀ + a') ⊆ reg.quiet →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), (∀ x, Kf ≤ κ (Fin.last Nw) x) →
    IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    IsCompactDatum f →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z) ≤
      ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q) *
        (ENNReal.ofReal (Real.exp (-c * a')) *
            negJetNorm π ((wordReserveN m Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (f x)) +
          momentNorm π (wordReserveN m Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f x))))

/-- `(A X² + Y²)^{1/2} ≤ A^{1/2} X + Y`. -/
theorem s3b_sqrt_comb_le (A X Y : ℝ≥0∞) :
    (A * X ^ 2 + Y ^ 2) ^ (1 / 2 : ℝ) ≤ A ^ (1 / 2 : ℝ) * X + Y := by
  refine (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half'', sq_rpow_half'']

theorem s3b_exp_sqrt (c a : ℝ) :
    ENNReal.ofReal (Real.exp (-2 * c * a)) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.exp (-c * a)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  congr 2
  ring

/-- **The quiet margin on the plane from the fibre quiet margin, the stage data and the Bloch output.** -/
theorem s3b_quietMarginPlane_of_parts (hB1 : QuietMarginFibreStatement.{u, v})
    (hB4 : QuietMarginDatumStatement.{u, v}) (hO : BlochOutputStatement.{u, v}) :
    QuietMarginPlaneStatement.{u, v} := by
  intro K
  obtain ⟨g₁, hg₁, hB1K⟩ := hB1 K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D H Kf m k Cout hCout d Ks pos μ₂ hμs hμc hμe hμ1
  obtain ⟨C1, c1, Q1, hC1, hc1, hB1s⟩ := hB1K Nw D m Kf k d Ks pos
  obtain ⟨CB, hCB, hBs⟩ := hO Kf m Cout 0 0 hCout le_rfl le_rfl
  obtain ⟨C4, hC4, hB4s⟩ := hB4 K Nw D m k Ks μ₂ hμs hμc hμe hμ1
  refine ⟨CB * C1 * Real.sqrt C4, c1, Q1, by positivity, hc1, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg hB hJ hrstar
    hrstarC a' ha' ha'S hquiet X₀ κ hκf hκ f u w hcd hch
  have hS1 := hB.hS
  have hϖ := hB.ϖ_pos
  have hϖη := hB.ϖ_le
  have hϖ1 : ϖ ≤ 1 := hϖη.trans (Real.sqrt_le_one.2 hB.hη1)
  -- the frame
  obtain ⟨φ, hφ, hfφ⟩ := hcd.exists_family
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J := by
    have := hJ
    unfold wordReserveJstar wordReserveKstar wordReserveN at this ⊢
    omega
  have hcap : ∀ j x, cappedWordSlots κ 0 d j x ≤ J := fun j x =>
    (cappedWordSlots_le_reserve κ 0 m d Ks j x).trans hJ0
  let F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁ :=
    b1wCappedFrame K g₁ H J π letters d (fun i => (hletters i).1) η S ηg t₀ S ϖ t₀ (t₀ + S) G v g
      reg pkg.toCoreScalarPackage hB.toPiece le_rfl (by linarith) le_rfl X₀ κ hκ hcap φ
      (fun x => ⟨(hφ x).1.continuous.stronglyMeasurable, (hφ x).2⟩) f u w hfφ hch
  have hUeq : (fun x => planeValue (F.u (Fin.last Nw) x F.b)) =
      fun x => planeValue (u (Fin.last Nw) x (t₀ + S)) :=
    funext fun x => planeValue_truncate _ _
  have hΘ0 := hB.wordTheta_nonneg
  have hP := one_le_peFactor η
  have hS0 : 0 ≤ S := by linarith
  -- the output from the Bloch fibres with the multiplier `0`
  have hmom : ∀ x, ∀ β ∈ momentIndices m, Integrable (fun y : Vec 2 =>
      (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (u (Fin.last Nw) x (t₀ + S)) y) := by
    intro x β hβ
    have := amplitudeIdMoments K g₁ F (Fin.last Nw) x F.b ⟨F.ordered, le_rfl⟩ m β hβ
    have e : planeValue (F.u (Fin.last Nw) x F.b) = planeValue (u (Fin.last Nw) x (t₀ + S)) :=
      congrFun hUeq x
    rw [e] at this
    exact this
  have hmain := hBs π hB.hπ ϖ rstar hϖ hϖ1 hrstar hrstarC (fun _ => (0 : ℝ)) contDiff_const
    HasCompactSupport.zero (fun _ => rfl) (fun l θ _ => by simp [iteratedFDeriv_fun_zero])
    (fun θ hθ => absurd hθ (not_lt.2 (by
      rw [sq, mul_zero]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)))
    (κ (Fin.last Nw)) hκf (fun x => u (Fin.last Nw) x (t₀ + S)) hmom
  have hJeq : (fun x (a : ℕ) (wd : DerivativeWord2 a) z =>
      planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
        orderedDerivative wd (fourierCutoff (fun _ => (0 : ℝ))
          (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) =
      fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z := by
    funext x a wd z
    rw [ffc_fourierCutoff_zero, orderedDerivative_zero_function, sub_zero]
  rw [hJeq] at hmain
  refine hmain.trans ?_
  -- the quiet margin at each frequency
  set X : ℝ := C1 * peFactor η ^ Q1 * (1 + S) ^ Q1 with hXdef
  set A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2 * c1 * a')) with hAdef
  have hba : F.b - F.a = S := by
    show t₀ + S - t₀ = S
    ring
  have hfib : ∀ θ ∈ freqCube, stageTerminalBandSq F m Ks Kf 0 θ ≤
      ENNReal.ofReal (X ^ 2) *
        (A * stageDatumNegSq F m Ks k θ + stageDatumLowSq F m Ks (Real.pi / 8) θ) := by
    intro θ hθ
    have hlet : ∀ l, (letters l).order = d l ∧ (letters l).slow = Ks l ∧
        (letters l).positive = pos l := fun l =>
      ⟨(hletters l).1, (hletters l).2.1, (hletters l).2.2⟩
    have hv0 : ∀ t ∈ Icc t₀ (t₀ + a'), ∀ z, v t z = 0 := fun t ht z =>
      pkg.quiet_zero t ⟨hquiet ht, ht.1, by linarith [ht.2]⟩ z
    have hb := hB1s F θ hlet hJ (by show t₀ + 1 ≤ t₀ + S; linarith) hθ a' ha'
      (by show t₀ + a' ≤ t₀ + S; linarith) hquiet hv0
    rw [hba] at hb
    exact hb
  -- the datum
  have hNeg : negJetNorm F.π ((wordReserveN m Ks : ℕ) : ℝ) k F.ϖ 1 F.φ =
      negJetNorm π ((wordReserveN m Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (f x)) :=
    s3b_negJetNorm_congr_ae π _ k ϖ 1 (fun x => (hfφ x).symm)
  have hLow : momentNorm F.π (wordReserveN m Ks) F.ϖ (fun x => fourierCutoff μ₂ (F.φ x)) =
      momentNorm π (wordReserveN m Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f x))) := by
    congr 1
    funext x
    exact s3b_fourierCutoff_congr_ae μ₂ (hfφ x).symm
  set NN := negJetNorm π ((wordReserveN m Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (f x))
  set LL := momentNorm π (wordReserveN m Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f x)))
  have hnn : 0 ≤ wordTheta ηg letters * X * Real.sqrt C4 := by positivity
  have hband : ∫⁻ θ in freqCube, outBandSq π ϖ m Kf 0 θ
      (fun x => planeValue (u (Fin.last Nw) x (t₀ + S))) ≤
      ENNReal.ofReal ((wordTheta ηg letters * X * Real.sqrt C4) ^ 2) * (A * NN ^ 2 + LL ^ 2) := by
    by_cases hΘ : wordTheta ηg letters = 0
    · have hz := zeroAmplitudeWord K g₁ F hΘ
      have hz' : ∀ x, planeValue (u (Fin.last Nw) x (t₀ + S)) =ᵐ[volume] 0 := fun x => by
        have := hz x F.b ⟨F.ordered, le_rfl⟩
        rwa [congrFun hUeq x] at this
      simp only [ffc_outBandSq_eq_zero π ϖ m Kf _ _ hz', lintegral_zero]
      exact zero_le
    calc ∫⁻ θ in freqCube, outBandSq π ϖ m Kf 0 θ
          (fun x => planeValue (u (Fin.last Nw) x (t₀ + S)))
        ≤ ∫⁻ θ in freqCube, ENNReal.ofReal ((wordTheta ηg letters * X) ^ 2) *
            (A * stageDatumNegSq F m Ks k θ + stageDatumLowSq F m Ks (Real.pi / 8) θ) := by
          refine setLIntegral_mono' measurableSet_freqCube fun θ hθ => ?_
          have hterm := ffc_outBandSq_eq_terminal F m Ks Kf 0 θ hB.hπ hΘ
          rw [hUeq] at hterm
          calc _ = ENNReal.ofReal (wordTheta ηg letters ^ 2) *
                  stageTerminalBandSq F m Ks Kf 0 θ := hterm
            _ ≤ ENNReal.ofReal (wordTheta ηg letters ^ 2) * (ENNReal.ofReal (X ^ 2) *
                  (A * stageDatumNegSq F m Ks k θ + stageDatumLowSq F m Ks (Real.pi / 8) θ)) :=
                mul_le_mul_right (hfib θ hθ) _
            _ = _ := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
      _ = ENNReal.ofReal ((wordTheta ηg letters * X) ^ 2) *
            ∫⁻ θ in freqCube, (A * stageDatumNegSq F m Ks k θ +
              stageDatumLowSq F m Ks (Real.pi / 8) θ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((wordTheta ηg letters * X) ^ 2) *
            (ENNReal.ofReal C4 * (A * NN ^ 2 + LL ^ 2)) := by
          refine mul_le_mul_right ?_ _
          have := hB4s g₁ F (fun l => (hletters l).2.1) A
          rw [hNeg, hLow] at this
          exact this
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 2
          rw [mul_pow _ (Real.sqrt C4), Real.sq_sqrt hC4.le]
  calc _ ≤ ENNReal.ofReal CB * (ENNReal.ofReal ((wordTheta ηg letters * X * Real.sqrt C4) ^ 2) *
          (A * NN ^ 2 + LL ^ 2)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hband (by norm_num)) _
    _ ≤ ENNReal.ofReal CB * (ENNReal.ofReal (wordTheta ηg letters * X * Real.sqrt C4) *
          (A ^ (1 / 2 : ℝ) * NN + LL)) := by
        refine mul_le_mul_right ?_ _
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hnn,
          sq_rpow_half'']
        exact mul_le_mul_right (s3b_sqrt_comb_le A NN LL) _
    _ = _ := by
        rw [hAdef, s3b_exp_sqrt, ← mul_assoc, ← ENNReal.ofReal_mul hCB.le]
        congr 2
        rw [hXdef]
        ring

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The assembly of the future fast clause

`seamFutureFastAssembly : SeamFutureFastAssembly`. Clause (3) of the seam's future kernel from the
chain discard, weak continuity, the Bloch output, the quiet margin at the fibre
level (`b1_quietMarginFibre`), the stage data in negative order and the lossless cell low pass.

The constants of the discard, the quiet margin and the full field are taken at `C_out = 1` and the
derivative scale `r₀ = min r_* 1` (so that their powers `Q` do not depend on `C_out`); the bound
at `r_*` follows by rescaling. The compact chains sit at the capped slots of
`wordBaseSlots + K_max`; the kernel is `R ∘ μ(D)` on well-buffered blocks with `Θ₊ ≠ 0`
(`s3b_comp_good`, `s3b_klim_good`) and `0` otherwise (`s3b_comp_zero`); the rough data go through
`s3b_rough_core`. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- **The assembly of the future fast clause.** -/
theorem seamFutureFastAssembly : SeamFutureFastAssembly.{u, v} := by
  intro hDis hWC hO hB1 hB4 hB5 K
  have hCP := s3b_quietMarginPlane_of_parts hB1 hB4 hO
  obtain ⟨g₁D, hg₁D, hDisK⟩ := hDis K
  obtain ⟨g₁C, hg₁C, hCPK⟩ := hCP K
  obtain ⟨g₁W, hg₁W, hWCK⟩ := hWC K
  obtain ⟨g₁F, hg₁F, hFFK⟩ := chainFullField.{u, v} K
  obtain ⟨g₁E, hg₁E, hE⟩ := retainedMapExists.{u, v} K
  refine ⟨min (min (min g₁D g₁C) (min g₁W g₁F)) (min g₁E (1 / 4)),
    lt_min (lt_min (lt_min hg₁D hg₁C) (lt_min hg₁W hg₁F)) (lt_min hg₁E (by norm_num)),
    fun χlo hχ μ hμ σ hσ => ?_⟩
  subst hσ
  obtain ⟨c₁E, Q₁E, hc₁E, hE'⟩ := hE (fun ξ => χlo ξ ^ (σ.pout + ∑ i, σ.KsF i + 1))
    (hχ.pow _) σ.Np σ.D σ.H σ.dF σ.KsF σ.posF
  refine ⟨c₁E, Q₁E, hc₁E, fun c₁ Q₁ hc₁ hc₁le hQ₁ => ?_⟩
  -- the cutoff `μ₂`, with `μ₂ μ = μ₂`
  obtain ⟨μ₂, hμ₂s, hμ₂c, hμ₂e, hμ₂1, hμ₂0⟩ :=
    radialCutoff_exists (r₀ := Real.pi / 4) (r₁ := 3 * Real.pi / 8) (by positivity)
      (by linarith [Real.pi_pos])
  have hμ₂R : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ₂ ξ = 0 :=
    fun ξ hξ => hμ₂0 ξ (by linarith [Real.pi_pos])
  have hprod : ∀ θ, μ₂ θ * μ θ = μ₂ θ := fun θ => by
    by_cases hθ : Real.sqrt (vecDot θ θ) ≤ 3 * Real.pi / 8
    · rw [hμ.one θ hθ, mul_one]
    · rw [hμ₂0 θ (not_le.1 hθ).le, zero_mul]
  -- the constants, at `C_out = 1`
  obtain ⟨CD, cD, QD, hCD, hcD, hDs⟩ := hDisK (fun ξ => χlo ξ ^ (σ.pout + ∑ i, σ.KsF i + 1))
    (hχ.pow _) σ.Np σ.D σ.H σ.Kmax σ.pout 1 one_pos σ.dF σ.KsF σ.posF
  obtain ⟨CC, cC, QC, hCC, hcC, hCPs⟩ := hCPK σ.Np σ.D σ.H σ.Kmax σ.pout σ.k 1 one_pos σ.dF
    σ.KsF σ.posF μ₂ hμ₂s hμ₂c hμ₂e hμ₂1
  obtain ⟨CF, QF, hCF, hFFs⟩ := hFFK σ.Np σ.D σ.H σ.Kmax σ.pout 1 one_pos σ.dF σ.KsF σ.posF
  obtain ⟨C₅, hC₅, hB5μ⟩ := hB5 (wordReserveN σ.pout σ.KsF) σ.k μ hμ.smooth hμ.compact hμ.even
    hμ.supp
  obtain ⟨C₅', hC₅', hB5μ₂⟩ := hB5 (wordReserveN σ.pout σ.KsF) σ.k μ₂ hμ₂s hμ₂c hμ₂e hμ₂R
  set C₁ : ℝ := 3 ^ (wordReserveN σ.pout σ.KsF + 1) * (wordReserveN σ.pout σ.KsF).factorial
    with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  set C₃ : ℝ := 3 ^ (σ.pout + 1) * σ.pout.factorial with hC₃def
  have hC₃ : 0 ≤ C₃ := by positivity
  set Bcoef : ℝ := CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅') with hBcoef
  have hBcoef0 : 0 ≤ Bcoef := by positivity
  refine ⟨QD + QC + Q₁, fun Cout hCout => ?_⟩
  refine ⟨C₃ * (max 1 Cout) ^ σ.Kmax * Bcoef, min (min cD cC) c₁, by positivity,
    lt_min (lt_min hcD hcC) hc₁, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ lettersF hlet η S ηg rstar ϖ δ hη hη1 hS hηg hηg1 hrstar hrstarC
    hϖ hδ tF GF vF gF hGm hv hv0 hvs hvw hvj hg0 hg hg1 hGn regF hpkg hL hT hQ hM a ha haS
    hquiet X₀F κF Kout hKoutM hKoutF hκF fF uF wF hfin hseam
  subst hδ
  -- the block
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hϖ0 : 0 < ϖ := by
    rw [hϖ]
    exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hB := isWordBlock_of_seam σ.hD hπ hη hη1 hS hηg hηg1 hϖ hGm hv hv0 hvs hvw hvj hg0 hg hg1
    hGn hL hT hQ hM
  have hpkgW := hpkg.inWindow
  have hξ : 0 < σ.K.ξlo := hpkg.consts_pos.2.1
  have hr : 0 < 2 * σ.K.ξlo * Real.sqrt η := by
    have := Real.sqrt_pos.2 hη
    positivity
  have hΘ0 : 0 ≤ wordTheta ηg lettersF := hB.wordTheta_nonneg
  have hP := one_le_peFactor η
  have hr₀ : 0 < min rstar 1 := lt_min hrstar one_pos
  have hr₀1 : min rstar 1 ≤ 1 := min_le_right _ _
  have hslow : ∀ i, (lettersF i).slow = σ.KsF i := fun i => (hlet i).2.1
  -- the reserves
  have hJK : wordReserveJstar (wordReserveKstar σ.Kmax (wordReserveN σ.pout σ.KsF) σ.dF) σ.dF ≤
      σ.Jstar := s3b_reserve_le σ (Nat.le_add_right _ _) le_rfl
  have hJKk : wordReserveJstar (wordReserveKstar (σ.Kmax + σ.k) (wordReserveN σ.pout σ.KsF) σ.dF)
      σ.dF ≤ σ.Jstar := s3b_reserve_le σ le_rfl le_rfl
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN σ.pout σ.KsF) σ.dF) σ.dF ≤
      σ.Jstar := s3b_reserve_le σ (Nat.zero_le _) le_rfl
  have hnp : wordReserveN σ.pout σ.KsF ≤ σ.pout + ∑ i, σ.KsF i + 2 := by
    unfold wordReserveN
    omega
  -- the slots of the compact chains
  set κ' : Fin (σ.Np + 1) → ι → ℕ := fun j x => wordBaseSlots lettersF j x + σ.Kmax with hκ'def
  have hκ' : IsWordSlots lettersF κ' :=
    s3b_isWordSlots_add (wordBaseSlots_isWordSlots lettersF hB.hlet) σ.Kmax
  have hκ'f : ∀ x, σ.Kmax ≤ κ' (Fin.last σ.Np) x := fun x => Nat.le_add_left _ _
  set κc := cappedWordSlots κ' σ.Kmax σ.dF with hκcdef
  have hκc : IsWordSlots lettersF κc :=
    cappedWordSlots_isWordSlots hB.hlet (fun i => (hlet i).1) hκ' σ.Kmax
  have hκcl : ∀ x, σ.Kmax ≤ κc (Fin.last σ.Np) x :=
    fun x => (cappedWordSlots_last κ' σ.Kmax σ.dF x (hκ'f x)).ge
  have hWcc : IsWordSlots lettersF (cappedWordSlots κc σ.Kmax σ.dF) :=
    cappedWordSlots_isWordSlots hB.hlet (fun i => (hlet i).1) hκc σ.Kmax
  have hcl2 : ∀ x, σ.Kmax ≤ cappedWordSlots κc σ.Kmax σ.dF (Fin.last σ.Np) x :=
    fun x => (cappedWordSlots_last κc σ.Kmax σ.dF x (hκcl x)).ge
  have hExGen : ∀ κ : Fin (σ.Np + 1) → ι → ℕ, (∀ x, σ.Kmax ≤ κ (Fin.last σ.Np) x) →
      IsWordSlots lettersF κ →
      ∀ fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ σ.Kmax σ.dF 0 x) (h x), IsCompactDatum fk →
      ∃ (uk : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ σ.Kmax σ.dF j x) (h x))
        (wk : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ σ.Kmax σ.dF j x + 1) (h x)),
        IsPlaneChain (wordChainData GF lettersF X₀F (ϖ * ηg)) (cappedWordSlots κ σ.Kmax σ.dF) tF
          (tF + S) vF fk (fun _ _ _ => 0) uk wk :=
    fun κ hκf hκ fk hfk => exists_compactChain_capped ((min_le_right _ _).trans (min_le_right _ _))
      hlet hpkgW hB hJK X₀F hκf hκ fk hfk
  have hcfin : ∀ {κ0 : ι → ℕ} (fk : ∀ x, PlaneHk Set.univ (κ0 x) (h x)), IsCompactDatum fk →
      momentNorm π (wordReserveN σ.pout σ.KsF) ϖ (fun x => planeValue (fk x)) < ⊤ := by
    intro κ0 fk hcd
    choose φ hφ1 hφ2 hfφ using hcd
    rw [momentNorm_congr_ae' π _ ϖ hfφ]
    exact momentNorm_lt_top_of_compact π _ ϖ fun x => ⟨hφ1 x, hφ2 x⟩
  have hP1 : ∀ G : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (G x) volume) →
      negJetNorm π ((wordReserveN σ.pout σ.KsF : ℕ) : ℝ) σ.k ϖ 1 G ≤
        ENNReal.ofReal C₁ * momentNorm π (wordReserveN σ.pout σ.KsF) ϖ G :=
    fun G hG => s3b_negJetNorm_le_momentNorm π hπ le_rfl σ.k ϖ 1 G hG
  -- the quiet margin at the slots `κ` with `K_max` derivatives
  have hColAt : ∀ κ : Fin (σ.Np + 1) → ι → ℕ, (∀ x, σ.Kmax ≤ κ (Fin.last σ.Np) x) →
      IsWordSlots lettersF κ →
      ∀ (f' : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u' : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w' : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsCompactDatum f' →
        IsPlaneChain (wordChainData GF lettersF X₀F (ϖ * ηg)) κ tF (tF + S) vF f'
          (fun _ _ _ => 0) u' w' →
        jetOutputNorm π σ.pout σ.Kmax ϖ (min rstar 1)
            (fun x a wd z => planeJetOrder (u' (Fin.last σ.Np) x (tF + S)) a wd z) ≤
          ENNReal.ofReal (CC * wordTheta ηg lettersF * peFactor η ^ QC * (1 + S) ^ QC) *
            (ENNReal.ofReal (Real.exp (-cC * a)) *
                negJetNorm π ((wordReserveN σ.pout σ.KsF : ℕ) : ℝ) σ.k ϖ 1
                  (fun x => planeValue (f' x)) +
              momentNorm π (wordReserveN σ.pout σ.KsF) ϖ
                (fun x => fourierCutoff μ₂ (planeValue (f' x)))) :=
    fun κ hκf hκ f' u' w' hcd hch => hCPs σ.Jstar π lettersF hlet η S ηg (min rstar 1) tF ϖ GF vF gF
      (regF.inWindow tF S) hpkgW
      (hB.mono ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))) hJKk hr₀ hr₀1
      a ha haS (s3b_quiet_margin_quiet haS hquiet) X₀F κ hκf hκ f' u' w' hcd hch
  -- the kernel, and the bound on compact data in its regime
  set Kp := seamFutureKernel σ.K χlo (σ.pout + ∑ i, σ.KsF i) hμ π lettersF η S ηg tF ϖ GF vF X₀F
    c₁ Q₁ regF with hKpdef
  set c := min (min cD cC) c₁ with hcdef
  have hc₁' : c ≤ c₁ := min_le_right _ _
  have hcD' : c ≤ cD := (min_le_left _ _).trans (min_le_left _ _)
  have hcC' : c ≤ cC := (min_le_left _ _).trans (min_le_right _ _)
  set β : ℝ := Bcoef * wordTheta ηg lettersF * peFactor η ^ (QD + QC + Q₁) *
    (1 + S) ^ (QD + QC + Q₁) *
    (Real.exp (-c * S) + (1 + (regF.joins : ℝ)) * Real.exp (-c * regF.buffer) + Real.exp (-c * a))
    with hβdef
  have hβ0 : 0 ≤ β := by
    have := hpkg.buffer_nonneg
    positivity
  have hϖη : ϖ ≤ Real.sqrt η := by
    rw [hϖ]
    exact Real.sqrt_le_sqrt (div_le_self hη.le hS)
  have hϖ1 : ϖ ≤ 1 := hϖη.trans (Real.sqrt_le_one.mpr hη1)
  have hB5a : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN σ.pout σ.KsF) ϖ (fun x => fourierCutoff μ (Gf x)) ≤
        ENNReal.ofReal C₅ * negJetNorm π ((wordReserveN σ.pout σ.KsF : ℕ) : ℝ) σ.k ϖ 1 Gf :=
    fun Gf hG => hB5μ π hπ ϖ hϖ0 hϖ1 Gf hG
  have hB5b : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN σ.pout σ.KsF) ϖ (fun x => fourierCutoff μ₂ (Gf x)) ≤
        ENNReal.ofReal C₅' * negJetNorm π ((wordReserveN σ.pout σ.KsF : ℕ) : ℝ) σ.k ϖ 1 Gf :=
    fun Gf hG => hB5μ₂ π hπ ϖ hϖ0 hϖ1 Gf hG
  have hbuf := hpkg.buffer_nonneg
  have hx₂ : 0 ≤ CC * wordTheta ηg lettersF * peFactor η ^ QC * (1 + S) ^ QC := by positivity
  have hx₁ : 0 ≤ CD * wordTheta ηg lettersF * peFactor η ^ QD * (1 + S) ^ QD *
      (Real.exp (-cD * S) + (1 + ((regF.inWindow tF S).joins : ℝ)) *
        Real.exp (-cD * (regF.inWindow tF S).buffer)) := by
    have : 0 ≤ (regF.inWindow tF S).buffer := hbuf
    positivity
  have hsg := s3b_enn_good hx₁ hx₂ (Real.exp_pos (-cC * a)).le hC₁ hC₅.le (β := β) (by
    rw [hβdef]
    exact s3b_scalar_good hΘ0 hP hS0 hbuf ha (Nat.cast_nonneg _) hCD.le hCC.le hC₅.le hC₁
      hC₅'.le hcD' hcC')
  have hsz : ¬(wordTheta ηg lettersF ≠ 0 ∧ IsWellBuffered c₁ Q₁ η S regF) →
      ENNReal.ofReal (CC * wordTheta ηg lettersF * peFactor η ^ QC * (1 + S) ^ QC) *
        (ENNReal.ofReal (Real.exp (-cC * a)) + ENNReal.ofReal C₅') ≤ ENNReal.ofReal β := by
    intro hng
    refine s3b_enn_zero hx₂ (Real.exp_pos _).le hC₅'.le ?_
    rw [hβdef]
    refine s3b_scalar_zero hΘ0 hP hS0 hbuf ha (Nat.cast_nonneg _) hCD.le hCC.le hC₅.le hC₁
      hC₅'.le hcC.le hc₁' ?_
    rcases not_and_or.1 hng with hΘ | hW
    · exact Or.inl (not_not.1 hΘ)
    · exact Or.inr (not_le.1 hW)
  obtain ⟨Bc, hBc, hKs, hKc, hKlim, hComp, h3⟩ :=
    s3b_regime_exists (pin := σ.pout + ∑ i, σ.KsF i + 2) σ.hD hπ hslow hμ hμ₂s hμ₂c hμ₂e hμ₂R
    hprod hr Kp (wordTheta ηg lettersF ≠ 0 ∧ IsWellBuffered c₁ Q₁ η S regF)
    (fun hg => by
      obtain ⟨hΘ, hW⟩ := hg
      have hWE : IsWellBuffered c₁E Q₁E η S (regF.inWindow tF S) := hW.mono hc₁le hQ₁ hS0 hbuf
      obtain ⟨R0, hR0⟩ := hE' σ.Jstar π lettersF hlet η S ηg tF ϖ GF vF gF (regF.inWindow tF S)
        hpkgW (hB.mono ((min_le_right _ _).trans (min_le_left _ _)))
        (seam_reserve_le σ (Nat.zero_le _)) hWE X₀F
      exact ⟨_, retainedMap_spec ⟨R0, hR0⟩, fun g hg' => seamFutureKernel_apply hμ hΘ hW g hg'⟩)
    (fun hng g _ => by
      rcases not_and_or.1 hng with hΘ | hW
      · rw [hKpdef, seamFutureKernel_of_theta hμ (not_not.1 hΘ)]
        rfl
      · rw [hKpdef, seamFutureKernel_of_not_wellBuffered hμ hW]
        rfl)
    hnp hκcl hκc hWcc ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (hExGen κc hκcl hκc)
    (fun R hR fk' uk' wk' hcd' hch' => hDs σ.Jstar π lettersF hlet η S ηg (min rstar 1) tF ϖ GF
      vF gF (regF.inWindow tF S) hpkgW
      (hB.mono ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))) hJK hr₀ hr₀1
      X₀F R hR (cappedWordSlots κc σ.Kmax σ.dF) hcl2 hWcc fk' uk' wk' (hcfin fk' hcd') hch')
    (hColAt _ hcl2 hWcc) (hColAt κc hκcl hκc) hB5a hB5b hP1 hsg hsz
  -- the full field on compact data, and weak continuity, at the block
  have hFF9 : ∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (uk : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (wk : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData GF lettersF X₀F (ϖ * ηg)) κc tF (tF + S) vF fk
        (fun _ _ _ => 0) uk wk →
      jetOutputNorm π σ.pout σ.Kmax ϖ (min rstar 1)
          (fun x a wd z => planeJetOrder (uk (Fin.last σ.Np) x (tF + S)) a wd z) ≤
        ENNReal.ofReal (CF * wordTheta ηg lettersF * peFactor η ^ QF * (1 + S) ^ QF) *
          momentNorm π (wordReserveN σ.pout σ.KsF) ϖ (fun x => planeValue (fk x)) :=
    fun fk uk wk hcd hch => hFFs σ.Jstar π lettersF hlet η S ηg (min rstar 1) tF ϖ GF vF gF
      (regF.inWindow tF S) hpkgW
      (hB.mono ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hJK hr₀
      hr₀1 X₀F κc hκcl hκc fk uk wk (hcfin fk hcd) hch
  have hκm : IsWordSlots lettersF fun j x => min (κF j x) (κc j x) := s3b_isWordSlots_min hκF hκc
  have hWb9 : ∀ Φ : ∀ x, Vec 2 → h x,
      (∀ x, ContDiff ℝ (⊤ : ℕ∞) (Φ x) ∧ HasCompactSupport (Φ x)) →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : ∀ x, PlaneHk Set.univ (min (κF 0 x) (κc 0 x)) (h x))
        (u' : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (min (κF j x) (κc j x)) (h x))
        (w' : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (min (κF j x) (κc j x) + 1) (h x)),
        momentNorm π (wordReserveN σ.pout σ.KsF) ϖ (fun x => planeValue (f' x)) < ⊤ →
        IsPlaneChain (wordChainData GF lettersF X₀F (ϖ * ηg)) (fun j x => min (κF j x) (κc j x))
          tF (tF + S) vF f' (fun _ _ _ => 0) u' w' →
        ENNReal.ofReal |∑ x, (π x)⁻¹ *
            ∫ z, inner ℝ (planeValue (u' (Fin.last σ.Np) x (tF + S)) z) (Φ x z)| ≤
          ENNReal.ofReal C *
            momentNorm π (wordReserveN σ.pout σ.KsF) ϖ (fun x => planeValue (f' x)) := by
    intro Φ hΦ
    obtain ⟨C, hC, hW⟩ := hWCK σ.Np σ.D σ.H 0 σ.pout σ.dF σ.KsF σ.posF σ.Jstar π lettersF hlet η S
      ηg tF ϖ GF vF gF (regF.inWindow tF S) hpkgW
      (hB.mono ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hJ0 X₀F
      Φ hΦ
    exact ⟨C, hC, fun f' u' w' hfin' hch' =>
      hW (fun j x => min (κF j x) (κc j x)) (fun x => Nat.zero_le _) hκm f' u' w' hfin' hch'⟩
  -- the rough data at the scale `min r_* 1`
  have hP9 := s3b_rough_core (pin := σ.pout + ∑ i, σ.KsF i + 2) σ.hD hπ hr₀ hnp Kp hKs hKc hKlim
    hκc hκcl (hExGen κ' hκ'f hκ') hBc ENNReal.ofReal_ne_top hComp hFF9 hκF hκm
    (fun j x => min_le_left _ _) (fun j x => min_le_right _ _) hKoutF hKoutM hWb9 hP1 hfin hseam
  -- rescaling, and the constant
  have hresc := s3b_weightedJetNorm_rescale π (σ.pout : ℝ) σ.Kmax ϖ hr₀ (min_le_left rstar 1)
    (fun x a wd z => if a ≤ Kout x then planeJetOrder (uF (Fin.last σ.Np) x (tF + S)) a wd z -
      orderedDerivative wd (Kp (fun x' => planeValue (fF x')) x) z else 0)
  have hmono := s3b_negJetNorm_mono π (p := ((wordReserveN σ.pout σ.KsF : ℕ) : ℝ))
    (p' := ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ) : ℝ) ) (by exact_mod_cast hnp) σ.k ϖ 1
    (fun x => planeValue (fF x))
  refine (s3b_final_le (s3b_ratio_le hrstar hrstarC σ.Kmax) hC₃ hβ0 hresc hP9 h3 hmono).trans
    (le_of_eq ?_)
  congr 2
  rw [hβdef]
  ring

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Seam

/-! # The seam future kernel from its open inputs

`seamFutureKernel_of_open`: the future kernel of the seam (`SeamFutureKernelStatement`) from
`SeamGaussianNegStatement`, `SeamLowPassMomentStatement` and
(`QuietMarginDatumStatement`) of the fast remainder. The chain discard (with the band jet),
weak continuity, the Bloch output, the fibre quiet margin (`b1_quietMarginFibre`) and the lossless low pass
(`cellLowPassMoment`) are proved.

`cycleSeamIngredients_of_open`: the five statements of `cycle_seam_of_ingredients` from the
same open inputs (the old negative bound, the old scalar bound through the retained amplitude
factor, the transport and the cutoff complement are proved). -/

section
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- **The seam future kernel from the open inputs.** -/
theorem seamFutureKernel_of_open (hGN : SeamGaussianNegStatement.{u, v})
    (hLP : SeamLowPassMomentStatement.{u, v}) (hB4 : QuietMarginDatumStatement.{u, v}) :
    SeamFutureKernelStatement.{u, v} :=
  seamFutureKernel_of_parts (seamFutureKernelClausesAssembly hGN hLP)
    (seamFutureFastAssembly
      (mixedWordsIngredients_of_bandJet BandJets.bandJetStatement).2.2.1 chainWeakContinuity
      blochOutput b1_quietMarginFibre hB4 cellLowPassMoment)

/-- **The ingredients of `cycle_seam` from the open inputs.** -/
theorem cycleSeamIngredients_of_open (hGN : SeamGaussianNegStatement.{u, v})
    (hLP : SeamLowPassMomentStatement.{u, v}) (hB4 : QuietMarginDatumStatement.{u, v}) :
    SeamOldNegativeStatement.{u, v} ∧ SeamOldScalarStatement.{u, v} ∧
      SeamFutureKernelStatement.{u, v} ∧ SeamTransportStatement.{u, v} ∧
      SeamCutoffComplementStatement.{u, v} :=
  ⟨seamOldNegative, seamOldScalar_of retainedAmplitudeFactor,
    seamFutureKernel_of_open hGN hLP hB4, seamTransport, seamCutoffComplement⟩
end

/-! # `cycle_seam` and `cycle_joint` from the open inputs of the seam

`cycleSeamStatement_of_open`: the statement of `cycle_seam` (the text copy
`CycleSeamStatement`) from `SeamGaussianNegStatement`, `SeamLowPassMomentStatement` and `QuietMarginDatumStatement`, through `cycle_seam_of_ingredients` and
`cycleSeamIngredients_of_open`. `cycleJoint_of_open`: the statement of `cycle_joint` from
the same inputs (`cycle_joint_of_cycleSeam`). With the proved `seamGaussianNeg` and
`seamLowPassMoment`: `cycleSeamStatement_of_quietMarginDatum` and `cycleJoint_of_quietMarginDatum`,
from `QuietMarginDatumStatement` alone. -/

section
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard
open AVRegularity.CycleJointProofs.Assembly

universe u v w x

/-- **`cycle_seam` from the open inputs.** -/
theorem cycleSeamStatement_of_open (hGN : SeamGaussianNegStatement.{u, v})
    (hLP : SeamLowPassMomentStatement.{u, v}) (hB4 : QuietMarginDatumStatement.{u, v}) :
    CycleSeamStatement.{u, v} := fun K =>
  cycle_seam_of_ingredients (cycleSeamIngredients_of_open hGN hLP hB4).1
    (cycleSeamIngredients_of_open hGN hLP hB4).2.1
    (cycleSeamIngredients_of_open hGN hLP hB4).2.2.1
    (cycleSeamIngredients_of_open hGN hLP hB4).2.2.2.1
    (cycleSeamIngredients_of_open hGN hLP hB4).2.2.2.2 K

/-- **`cycle_joint` from the open inputs.** -/
theorem cycleJoint_of_open (hGN : SeamGaussianNegStatement.{0, v})
    (hLP : SeamLowPassMomentStatement.{0, v}) (hB4 : QuietMarginDatumStatement.{0, v}) :
    CycleJointStatement.{u, v, w, x} :=
  cycle_joint_of_cycleSeam (cycleSeamStatement_of_open hGN hLP hB4)

/-- **`cycle_seam` from `QuietMarginDatumStatement` alone.** -/
theorem cycleSeamStatement_of_quietMarginDatum (hB4 : QuietMarginDatumStatement.{u, v}) :
    CycleSeamStatement.{u, v} :=
  cycleSeamStatement_of_open seamGaussianNeg seamLowPassMoment hB4

/-- **`cycle_joint` from `QuietMarginDatumStatement` alone.** -/
theorem cycleJoint_of_quietMarginDatum (hB4 : QuietMarginDatumStatement.{0, v}) :
    CycleJointStatement.{u, v, w, x} :=
  cycleJoint_of_open seamGaussianNeg seamLowPassMoment hB4
end

end AVRegularity.CycleWords.Seam
end
end
