-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.CrudeChartWeights
public import AVRegularity.CycleWords.Seam.LowPassFibre
public import AVRegularity.CycleWords.Seam.Leibniz
public import AVRegularity.CycleWords.OriginalTaylorPairNativeFluxSupported
import AVRegularity.CycleWords.MixedWords.FibreDuality
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The dual estimate on the transform

`transformBound : TransformBoundStatement`.

The amplitude jet norm of `χ_lo(θ/√η) F̂` is at most `A₀ ∑_{j ≤ n} ∑_{|w| = j}` pair sizes of the
moment families `ϖ^j y^w F` (`amplitudeJetNorm_trans_le`; `ϖ^l ‖D^l χ_η‖ ≤ B` since `ϖ ≤ √η`).
Cauchy–Schwarz over the finitely many words, the dual estimate for each moment family
(`trans_dual`, with the negative norm of `F = μ(D)G`), and the bound of the cutoff on the
negative norm (`negJetNorm_fourierCutoff_le`) give the statement. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- Cauchy–Schwarz for a finite sum in `ℝ≥0∞`. -/
theorem sq_sum_le {α : Type*} (s : Finset α) (f : α → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, f i ^ 2 := by
  have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := s) (f := f) (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  rwa [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h

/-- The index set of the moment families. -/
def Words (n : ℕ) : Finset (Σ j : ℕ, DerivativeWord2 j) :=
  (Finset.range (n + 1)).sigma fun _ => Finset.univ

theorem measurable_pair {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (c : ι → ℝ≥0∞)
    (H : ∀ x, Vec 2 → h x) (hH : ∀ x, Integrable (H x)) : Measurable (Pair c H) := by
  unfold Pair
  refine Measurable.pow_const (Finset.measurable_sum _ fun x _ => measurable_const.mul ?_) _
  exact (((Trans_continuous isUnitPhase_cos (hH x)).norm.pow 2).measurable.ennreal_ofReal.add
    ((Trans_continuous isUnitPhase_sin (hH x)).norm.pow 2).measurable.ennreal_ofReal)

/-- **The dual estimate on the transform** (`TransformBoundStatement`). -/
theorem transformBound : TransformBoundStatement.{u, v} := by
  intro n L c hc μ χlo hμ hμc _ hμs hχ hχc
  obtain ⟨Bχ, hBχ0, hBχ⟩ := exists_iteratedFDeriv_bound hχ hχc n
  set s := Words n with hsd
  obtain ⟨A0, hA0d⟩ : ∃ A0 : ℝ, A0 = ((momentIndices n).card : ℝ) * (2 ^ n * Bχ) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A0 := by rw [hA0d]; positivity
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = ∑ j ∈ Finset.range (n + 1), DualConst L j c := ⟨_, rfl⟩
  have hD : ∀ j ∈ Finset.range (n + 1), DualConst L j c ≤ D := fun j hj => hDd ▸
    Finset.single_le_sum (f := fun j => DualConst L j c) (fun j _ => (DualConst_pos L j c).le) hj
  have hD0 : 0 ≤ D := hDd ▸ Finset.sum_nonneg fun j _ => (DualConst_pos L j c).le
  obtain ⟨CA, hCAd⟩ : ∃ CA : ℝ, CA = NegCutoffConst μ (n + 2) := ⟨_, rfl⟩
  have hCA : 0 < CA := hCAd ▸ NegCutoffConst_pos μ (n + 2)
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  refine ⟨(A0 + 1) * ((s.card : ℝ) + 1) * (D + 1) * CA,
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) hCA, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ η ϖ hη hη1 hϖ hϖη G hG hM
  set F : ∀ x, Vec 2 → h x := fun x => fourierCutoff μ (G x) with hFd
  set χ : Vec 2 → ℝ := fun θ' => χlo ((Real.sqrt η)⁻¹ • θ') with hχd
  have hsq : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := hχ.comp (contDiff_const_smul _)
  have hχb : ∀ l ≤ n, ∀ θ, ϖ ^ l * ‖iteratedFDeriv ℝ l χ θ‖ ≤ Bχ := by
    intro l hl θ
    have h1 := norm_iteratedFDeriv_scaled_le hχ (Real.sqrt η)⁻¹ l θ
    rw [abs_of_pos (inv_pos.2 hsq)] at h1
    have hr : ϖ * (Real.sqrt η)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hsq, one_mul]
      exact hϖη
    calc ϖ ^ l * ‖iteratedFDeriv ℝ l χ θ‖
        ≤ ϖ ^ l * (Bχ * (Real.sqrt η)⁻¹ ^ l) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (hBχ l hl _)
            (pow_nonneg (inv_nonneg.2 hsq.le) _))) (pow_nonneg hϖ.le _)
      _ = Bχ * (ϖ * (Real.sqrt η)⁻¹) ^ l := by rw [mul_pow]; ring
      _ ≤ Bχ * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (mul_nonneg hϖ.le (inv_nonneg.2 hsq.le)) hr) hBχ0
      _ = Bχ := mul_one _
  have hϖ1 : ϖ ≤ 1 := hϖη.trans (Real.sqrt_le_one.2 hη1)
  have hFm : ∀ x, AEStronglyMeasurable (F x) volume := fun x =>
    (fourierCutoff_memLp_of_memLp μ (Real.pi / 2) hμs hμ (hG x)).aestronglyMeasurable
  have hFmom : ∀ x, HasIntegrableMoments n (F x) := fun x =>
    ⟨hFm x, integrable_bracket_of_momentNorm hϖ hM (hπ x) (hFm x)⟩
  have hHint : ∀ p ∈ s, ∀ x,
      Integrable (fun y => (ϖ ^ p.1 * wordMonomial p.2 y) • F x y) := by
    intro p hp x
    have hpn : p.1 ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_sigma.1 hp).1)
    have h1 : HasIntegrableMoments (n - p.1 + p.1) (F x) := by
      rw [Nat.sub_add_cancel hpn]
      exact hFmom x
    have h2 := (h1.monomial p.2).integrable.smul (ϖ ^ p.1)
    refine h2.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.smul_apply, mul_smul]
  set cc : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hcc
  set e : Vec 2 → ℝ≥0∞ := fun θ => ENNReal.ofReal (Real.exp (-c * (vecDot θ θ / ϖ ^ 2))) with hed
  set g : (Σ j : ℕ, DerivativeWord2 j) → Vec 2 → ℝ≥0∞ := fun p θ =>
    e θ * Pair cc (fun x y => (ϖ ^ p.1 * wordMonomial p.2 y) • F x y) θ with hgd
  have hpt : ∀ θ, e θ * amplitudeJetNorm π n ϖ
      (fun x θ' => χlo ((Real.sqrt η)⁻¹ • θ') • phaseTransform Real.cos (F x) θ')
      (fun x θ' => χlo ((Real.sqrt η)⁻¹ • θ') • phaseTransform Real.sin (F x) θ') θ ≤
      ENNReal.ofReal A0 * ∑ p ∈ s, g p θ := by
    intro θ
    have h1 := amplitudeJetNorm_trans_le π n hϖ.le hBχ0 hχs hχb hFmom θ
    rw [← hA0d] at h1
    refine (mul_le_mul' le_rfl h1).trans (le_of_eq ?_)
    rw [hsd, Words, Finset.sum_sigma]
    simp only [hgd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  have hgm : ∀ p ∈ s, AEMeasurable (fun θ => g p θ ^ 2) (volume.restrict freqCube) := by
    intro p hp
    refine ((Measurable.mul ?_ (measurable_pair cc _ (hHint p hp))).pow_const 2).aemeasurable
    refine Measurable.ennreal_ofReal (Real.continuous_exp.comp (continuous_const.mul ?_)).measurable
    simp only [vecDot_self]
    fun_prop
  set NF := negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ F with hNFd
  set NG := negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ G with hNGd
  have hNF : NF ≤ ENNReal.ofReal CA * NG :=
    hCAd ▸ negJetNorm_fourierCutoff_le μ (Real.pi / 2) hμs hμ π (n + 2) L
      (by nlinarith [hϖ.le]) ϖ⁻¹ G hG
  have hdual : ∀ p ∈ s, ∫⁻ θ in freqCube, g p θ ^ 2 ≤ (ENNReal.ofReal D * NF) ^ 2 := by
    intro p hp
    have hpn : p.1 ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_sigma.1 hp).1)
    refine (trans_dual π hπ hc n L p.1 hpn p.2 hϖ F (hHint p hp)).trans ?_
    refine pow_le_pow_left₀ zero_le (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (hD p.1 (Finset.mem_sigma.1 hp).1)) le_rfl) 2
  calc ∫⁻ θ in freqCube, (e θ * amplitudeJetNorm π n ϖ
          (fun x θ' => χlo ((Real.sqrt η)⁻¹ • θ') • phaseTransform Real.cos (F x) θ')
          (fun x θ' => χlo ((Real.sqrt η)⁻¹ • θ') • phaseTransform Real.sin (F x) θ') θ) ^ 2
      ≤ ∫⁻ θ in freqCube, ENNReal.ofReal A0 ^ 2 * ((s.card : ℝ≥0∞) * ∑ p ∈ s, g p θ ^ 2) := by
        refine lintegral_mono fun θ => ?_
        refine (pow_le_pow_left₀ zero_le (hpt θ) 2).trans ?_
        rw [mul_pow]
        exact mul_le_mul' le_rfl (sq_sum_le s _)
    _ = ENNReal.ofReal A0 ^ 2 * ((s.card : ℝ≥0∞) * ∑ p ∈ s, ∫⁻ θ in freqCube, g p θ ^ 2) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_finsetSum' _ hgm]
    _ ≤ ENNReal.ofReal A0 ^ 2 * ((s.card : ℝ≥0∞) * ∑ p ∈ s, (ENNReal.ofReal D * NF) ^ 2) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (Finset.sum_le_sum hdual))
    _ = (ENNReal.ofReal A0 * (s.card : ℝ≥0∞) * (ENNReal.ofReal D * NF)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (ENNReal.ofReal ((A0 + 1) * ((s.card : ℝ) + 1) * (D + 1) * CA) * NG) ^ 2 := by
        refine pow_le_pow_left₀ zero_le ?_ 2
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        have h1 : ENNReal.ofReal A0 ≤ ENNReal.ofReal (A0 + 1) := ENNReal.ofReal_le_ofReal (by linarith)
        have h2 : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((s.card : ℝ) + 1) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
          exact le_self_add
        have h3 : ENNReal.ofReal D ≤ ENNReal.ofReal (D + 1) := ENNReal.ofReal_le_ofReal (by linarith)
        calc ENNReal.ofReal A0 * (s.card : ℝ≥0∞) * (ENNReal.ofReal D * NF)
            ≤ ENNReal.ofReal (A0 + 1) * ENNReal.ofReal ((s.card : ℝ) + 1) *
                (ENNReal.ofReal (D + 1) * (ENNReal.ofReal CA * NG)) :=
              mul_le_mul' (mul_le_mul' h1 h2) (mul_le_mul' h3 hNF)
          _ = ENNReal.ofReal (A0 + 1) * ENNReal.ofReal ((s.card : ℝ) + 1) *
                ENNReal.ofReal (D + 1) * ENNReal.ofReal CA * NG := by ring

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords.Seam

/-! **Coefficients of the transposed letter from the letter envelope.** For a cycle letter on
`[a, b] × ℝ²` with fast reserve `J`, the transposed coefficients `c • γ.map†` are `C^J` in the fast
variable at every time of the window, and for almost every time their jets of order `≤ J` grow at
most like `⟨ϖz⟩^{K_s}` (the flagged Taylor price, at `δ = ζϖ`). Hence `LetterTermRegular` holds for
almost every time, for every adjoint family whose jets are in `L²` with the weight `⟨ϖz⟩^{K_s}`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] {D : ℕ}

/-- The original source index of one constituent, at its own order. -/
def constituentSourceIndex (L : CycleLetter ι h D) (v u : ι) (o : Finset.Icc 2 D)
    (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) :
    OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u :=
  ⟨⟨o, q⟩, ⟨o.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp o.2).1, le_rfl⟩⟩, α, k⟩

omit [Fintype ι] [∀ i, CompleteSpace (h i)] in
theorem constituent_taylor_eq (L : CycleLetter ι h D) (v u : ι) (o : Finset.Icc 2 D)
    (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2)
    (ζ ϖ s : ℝ) (X₀ : Vec 2) :
    (fun y => taylorSlow (if L.positive then 1 else 0) L.slow
      (fun Y => (ChartedFamily.ofFiber L.edge).flux () () v u
        (constituentSourceIndex L v u o q α k).1 (constituentSourceIndex L v u o q α k).2.1.1
        (constituentSourceIndex L v u o q α k).2.2.1 s Y (y + 0) k) X₀ ((ζ * ϖ) • y)) =
      letterCoeff L (if L.positive then 1 else 0) X₀ (ζ * ϖ) s v u o q α k := by
  funext y
  simp only [letterCoeff, constituentSourceIndex, add_zero, ChartedFamily.ofFiber, dite_true]

omit [∀ i, CompleteSpace (h i)] in
theorem letterCoeff_contDiff (π : ι → ℝ) (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (hs : s ∈ Set.Icc a b) (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) (n : ℕ) (hn : n ≤ J) :
    ContDiff ℝ (n : ℕ) (letterCoeff L lo X₀ δ s v u o q α k) := by
  have hj := letter_coefficient_joint_contDiff π L a b J H hL v u o q α s hs
  have hf : ContDiff ℝ (L.slow + n : ℕ)
      (Function.uncurry (fun X z => ((L.edge v u o).get q).coeff α s X z k)) :=
    (contDiff_pi.mp hj k).of_le (by exact_mod_cast (show L.slow + n ≤ L.slow + J by omega))
  exact taylorSlow_spatial_contDiff lo L.slow n _ hf X₀ δ

theorem letterCoeffOp_contDiff (π : ι → ℝ) (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (hs : s ∈ Set.Icc a b) (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) (n : ℕ) (hn : n ≤ J) :
    ContDiff ℝ (n : ℕ) (letterCoeffOp L lo X₀ δ s v u o q α k) :=
  (letterCoeff_contDiff π L a b J H hL lo X₀ δ s hs v u o q α k n hn).smul contDiff_const

omit [Fintype ι] in
/-- The operator coefficient costs at most the norm of the constituent map. -/
theorem letterCoeffOp_iteratedFDeriv_le (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1))
    (k : Fin 2) {n : ℕ} (hc : ContDiff ℝ (n : ℕ) (letterCoeff L lo X₀ δ s v u o q α k))
    {l : ℕ} (hl : l ≤ n) (z : Vec 2) :
    ‖iteratedFDeriv ℝ l (letterCoeffOp L lo X₀ δ s v u o q α k) z‖ ≤
      ‖((L.edge v u o).get q).map‖ *
        ‖iteratedFDeriv ℝ l (letterCoeff L lo X₀ δ s v u o q α k) z‖ := by
  set T := ContinuousLinearMap.adjoint ((L.edge v u o).get q).map
  have hfun : (⇑((ContinuousLinearMap.id ℝ ℝ).smulRight T) ∘
      letterCoeff L lo X₀ δ s v u o q α k) = letterCoeffOp L lo X₀ δ s v u o q α k := by
    funext z
    simp [letterCoeffOp, T]
  have hb := ((ContinuousLinearMap.id ℝ ℝ).smulRight T).norm_iteratedFDeriv_comp_left
    (x := z) hc.contDiffAt (by exact_mod_cast hl)
  rw [hfun] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [ContinuousLinearMap.norm_smulRight_apply]
  have hT : ‖T‖ = ‖((L.edge v u o).get q).map‖ := LinearIsometryEquiv.norm_map _ _
  calc ‖ContinuousLinearMap.id ℝ ℝ‖ * ‖T‖ ≤ 1 * ‖T‖ :=
        mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ = ‖((L.edge v u o).get q).map‖ := by rw [one_mul, hT]

/-- **The transposed coefficients are regular for almost every time.** -/
theorem letterTermRegular_ae (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (L : CycleLetter ι h D)
    (a b : ℝ) (J H : ℕ) (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (X₀ : Vec 2) (n d : ℕ) (hJ : n + d ≤ J + 1)
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] :
    ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v),
      (∀ v i, MemLp (fun x => polynomialMomentRoot ϖ x ^ L.slow *
        ‖(Ψ v).toFunction.jet i x‖) 2 volume) →
      LetterTermRegular L (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ := by
  classical
  obtain ⟨hC0, hprice⟩ := analyticOriginalSource_flagged_taylor_fast_price (ι := ι) (h := h)
    (D := D) (P := Unit) (Ctx := fun _ => Unit) L.positive L.slow J
  have hall : ∀ᵐ t ∂volume, ∀ v u (α' : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u),
      (∀ Y : Vec 2, (t, Y) ∈ Set.Icc a b ×ˢ (Set.univ : Set (Vec 2))) → ∀ φ k X j, j ≤ J → ∀ z,
        ‖((ChartedFamily.ofFiber L.edge).identity v u α'.1).map‖ *
          ‖iteratedFDeriv ℝ j (fun y => taylorSlow (if L.positive then 1 else 0) L.slow
            (fun Y => (ChartedFamily.ofFiber L.edge).flux () () v u α'.1 α'.2.1.1 α'.2.2.1 t Y
              (y + φ) k) X ((ζ * ϖ) • y)) z‖ ≤
        originalFlaggedTaylorFastJetPriceConstant L.positive L.slow J *
          analyticOriginalSourcePrice (ChartedFamily.ofFiber L.edge)
            (fun _ _ => Set.Icc a b ×ˢ Set.univ) L.slow J v u α' *
          (if L.positive then ζ else 1) * polynomialMomentRoot ϖ z ^ L.slow :=
    ae_all_iff.mpr fun v => ae_all_iff.mpr fun u => ae_all_iff.mpr fun α' =>
      hprice (ChartedFamily.ofFiber L.edge) π hπ (fun _ _ => Set.Icc a b ×ˢ Set.univ) L.majorant
        hL.analytic v u α' () () ϖ ζ hϖ hϖ1 hζ hζ1
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Icc] with s hs hmem
  intro Ψ hΨ v u o hod q α k
  have ho2 := (Finset.mem_Icc.mp o.2).1
  have hoJ : n + (o.1 - 1) ≤ J := by omega
  have hc := letterCoeff_contDiff π L a b J H hL (if L.positive then 1 else 0) X₀ (ζ * ϖ) s hmem
    v u o q α k (n + (o.1 - 1)) hoJ
  have hC := letterCoeffOp_contDiff π L a b J H hL (if L.positive then 1 else 0) X₀ (ζ * ϖ) s hmem
    v u o q α k (n + (o.1 - 1)) hoJ
  set P := originalFlaggedTaylorFastJetPriceConstant L.positive L.slow J *
    analyticOriginalSourcePrice (ChartedFamily.ofFiber L.edge)
      (fun _ _ => Set.Icc a b ×ˢ Set.univ) L.slow J v u (constituentSourceIndex L v u o q α k) *
    (if L.positive then ζ else 1) with hPdef
  have hP : 0 ≤ P := by
    rw [hPdef]
    refine mul_nonneg (mul_nonneg hC0 ENNReal.toReal_nonneg) ?_
    split_ifs
    · exact hζ
    · exact zero_le_one
  refine ⟨hC, fun x => polynomialMomentRoot ϖ x ^ L.slow,
    fun l => (Fintype.card (DerivativeWord2 l.val) : ℝ) * P, fun idx => ?_, fun l x => ?_⟩
  · have hKL : n + (o.1 - 1) + 1 ≤ n + d := by omega
    refine (hΨ v (truncateJetIndex hKL (prefixIndex2 k idx))).ae_eq ?_
    filter_upwards [planeHkPartial_jet_ae k (truncatePlaneHk hKL (Ψ v)) idx] with x hx
    rw [hx]
    rfl
  · have hl : l.val ≤ n + (o.1 - 1) := Nat.le_of_lt_succ l.isLt
    have hp := hs v u (constituentSourceIndex L v u o q α k)
      (fun Y => ⟨hmem, Set.mem_univ Y⟩) 0 k X₀ l.val (by omega) x
    rw [constituent_taylor_eq] at hp
    have hcl : ContDiff ℝ (l.val : ℕ) (letterCoeffOp L (if L.positive then 1 else 0) X₀ (ζ * ϖ)
        s v u o q α k) := hC.of_le (by exact_mod_cast hl)
    have hop := letterCoeffOp_iteratedFDeriv_le L (if L.positive then 1 else 0) X₀ (ζ * ϖ) s v u o
      q α k hc hl x
    have hprod : ‖iteratedFDeriv ℝ l.val (letterCoeffOp L (if L.positive then 1 else 0) X₀
        (ζ * ϖ) s v u o q α k) x‖ ≤ P * polynomialMomentRoot ϖ x ^ L.slow :=
      hop.trans (hp.trans (le_of_eq (by rw [hPdef])))
    calc ‖coefficientDerivativeArray (letterCoeffOp L (if L.positive then 1 else 0) X₀ (ζ * ϖ)
          s v u o q α k) l.val x‖
        ≤ (Fintype.card (DerivativeWord2 l.val) : ℝ) * (P * polynomialMomentRoot ϖ x ^ L.slow) :=
          coefficientDerivativeArray_norm_le_iterated_bound _ l.val hcl x _
            (mul_nonneg hP (pow_nonneg (by
              unfold polynomialMomentRoot; exact Real.sqrt_nonneg _) _)) hprod
      _ = (Fintype.card (DerivativeWord2 l.val) : ℝ) * P * polynomialMomentRoot ϖ x ^ L.slow := by
          ring
end

/-! **Pointwise bound of the transposed letter.** Every jet of `L*Ψ` at a point is bounded by the
jets of `Ψ` there, through the Leibniz expansion and the jets of the transposed coefficients. Summed
over the constituents these are the actual Taylor jet matrices of the letter, whose Schur sums are
`price · 2θ` for almost every time (`actualTaylorJetMatrix_schur_ae`), so in the inverse-mass
`ℓ²` sum over components

`∑_u π_u⁻¹ |D^i (L*Ψ)_u(z)|² ≤ (C θ ⟨ϖz⟩^{K_s})² ∑_v π_v⁻¹ |Ψ_v|_{n+d}(z)²`,

with `C` depending only on `n + d`, the reserve, the slow degree and the sign flag of the letter. -/

section
/-- The number of position masks through order `K`. -/
def maskCount (K : ℕ) : ℝ := ∑ j ∈ Finset.range (K + 1), (Fintype.card (PositionMask j) : ℝ)

/-- The number of ordered words through order `K`. -/
def wordCount (K : ℕ) : ℝ := ∑ j ∈ Finset.range (K + 1), (Fintype.card (DerivativeWord2 j) : ℝ)

theorem card_positionMask_le_maskCount {j K : ℕ} (hj : j ≤ K) :
    (Fintype.card (PositionMask j) : ℝ) ≤ maskCount K :=
  Finset.single_le_sum (f := fun j => (Fintype.card (PositionMask j) : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem card_word_le_wordCount {j K : ℕ} (hj : j ≤ K) :
    (Fintype.card (DerivativeWord2 j) : ℝ) ≤ wordCount K :=
  Finset.single_le_sum (f := fun j => (Fintype.card (DerivativeWord2 j) : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem maskCount_mono {K K' : ℕ} (h : K ≤ K') : maskCount K ≤ maskCount K' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun _ _ _ => Nat.cast_nonneg _)

theorem maskCount_nonneg (K : ℕ) : 0 ≤ maskCount K :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem wordCount_nonneg (K : ℕ) : 0 ≤ wordCount K :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

section Raw

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem wordPartialRawJet_norm_le {z : Vec 2} {B : ℝ} :
    ∀ {m c : ℕ} (β : DerivativeWord2 c) (Dj : RawJet2 (m + c) E),
      (∀ q, ‖Dj q z‖ ≤ B) → ∀ q, ‖wordPartialRawJet β Dj q z‖ ≤ B
  | _, 0, _, _, hD, q => hD q
  | _, c + 1, β, _, hD, q => wordPartialRawJet_norm_le (c := c) (Fin.init β) _ (fun _ => hD _) q

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem multiplicationRawJet_norm_le {K : ℕ} (C : Vec 2 → E →L[ℝ] F) (Dj : RawJet2 K E)
    (z : Vec 2) {B : ℝ} (hB : 0 ≤ B) (hD : ∀ q, ‖Dj q z‖ ≤ B) (a : JetIndex2 K) :
    ‖multiplicationRawJet C Dj a z‖ ≤
      maskCount K * ((∑ l ∈ Finset.range (K + 1), ‖coefficientDerivativeArray C l z‖) * B) := by
  set S := (∑ l ∈ Finset.range (K + 1), ‖coefficientDerivativeArray C l z‖) * B with hSdef
  have hS : 0 ≤ S := mul_nonneg (Finset.sum_nonneg fun _ _ =>
    ContinuousLinearMap.opNorm_nonneg _) hB
  have hterm : ∀ m : PositionMask a.1.val,
      ‖multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C Dj m a.2 z‖ ≤ S := by
    intro m
    have hl : maskLeftLength a.1.val m ≤ K :=
      (maskLeftLength_le _ m).trans (Nat.le_of_lt_succ a.1.isLt)
    unfold multiplicationTerm
    calc _ ≤ ‖orderedCoefficientDerivative C (maskLeftLength a.1.val m)
            (maskWordEquiv 2 a.1.val m a.2).1 z‖ *
          ‖Dj (maskJetIndex (Nat.le_of_lt_succ a.1.isLt) m a.2) z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖coefficientDerivativeArray C (maskLeftLength a.1.val m) z‖ * B :=
          mul_le_mul (orderedCoefficientDerivative_norm_le_array _ _ _ _) (hD _) (norm_nonneg _)
            (ContinuousLinearMap.opNorm_nonneg _)
      _ ≤ S := mul_le_mul_of_nonneg_right (Finset.single_le_sum
          (f := fun l => ‖coefficientDerivativeArray C l z‖)
          (fun _ _ => ContinuousLinearMap.opNorm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))) hB
  show ‖∑ m : PositionMask a.1.val, multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C Dj m a.2 z‖
    ≤ maskCount K * S
  calc _ ≤ ∑ m : PositionMask a.1.val,
        ‖multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C Dj m a.2 z‖ := norm_sum_le _ _
    _ ≤ ∑ _m : PositionMask a.1.val, S := Finset.sum_le_sum fun m _ => hterm m
    _ = (Fintype.card (PositionMask a.1.val) : ℝ) * S := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ maskCount K * S :=
        mul_le_mul_of_nonneg_right (card_positionMask_le_maskCount (Nat.le_of_lt_succ a.1.isLt)) hS

end Raw

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] {D : ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
theorem letterTransposeTermJet_norm_le (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1))
    (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d) (Ψ : RawJet2 (n + d) (h v)) (z : Vec 2) {B : ℝ}
    (hB : 0 ≤ B) (hΨ : ∀ i, ‖Ψ i z‖ ≤ B) (idx : JetIndex2 n) :
    ‖letterTransposeTermJet L lo X₀ δ s v u o q α k n d hod Ψ idx z‖ ≤
      maskCount (n + d) * ((∑ l ∈ Finset.range (n + (o.1 - 1) + 1),
        ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l z‖) * B) := by
  have ho : n + (o.1 - 1) ≤ n + d := by omega
  have hS : 0 ≤ (∑ l ∈ Finset.range (n + (o.1 - 1) + 1),
      ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l z‖) * B :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => ContinuousLinearMap.opNorm_nonneg _) hB
  unfold letterTransposeTermJet
  exact wordPartialRawJet_norm_le α _ (fun q' =>
    (multiplicationRawJet_norm_le _ _ z hB (fun _ => hΨ _) q').trans
      (mul_le_mul_of_nonneg_right (maskCount_mono ho) hS)) idx

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The coefficient arrays of a transposed constituent, through the scalar Taylor jets. -/
theorem letterCoeffArray_sum_le (π : ι → ℝ) (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ)
    (hs : s ∈ Set.Icc a b) (v u : ι) (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
    (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2) (n d : ℕ) (hod : o.1 ≤ d) (hJ : n + d ≤ J + 1)
    (z : Vec 2) :
    ∑ l ∈ Finset.range (n + (o.1 - 1) + 1),
        ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l z‖ ≤
      wordCount (n + d) * ∑ l ∈ Finset.range (n + d), ‖((L.edge v u o).get q).map‖ *
        ‖iteratedFDeriv ℝ l (letterCoeff L lo X₀ δ s v u o q α k) z‖ := by
  have ho2 := (Finset.mem_Icc.mp o.2).1
  have hoJ : n + (o.1 - 1) ≤ J := by omega
  have hc := letterCoeff_contDiff π L a b J H hL lo X₀ δ s hs v u o q α k (n + (o.1 - 1)) hoJ
  have hC := letterCoeffOp_contDiff π L a b J H hL lo X₀ δ s hs v u o q α k (n + (o.1 - 1)) hoJ
  rw [Finset.mul_sum]
  calc ∑ l ∈ Finset.range (n + (o.1 - 1) + 1),
        ‖coefficientDerivativeArray (letterCoeffOp L lo X₀ δ s v u o q α k) l z‖
      ≤ ∑ l ∈ Finset.range (n + (o.1 - 1) + 1), wordCount (n + d) *
          (‖((L.edge v u o).get q).map‖ *
            ‖iteratedFDeriv ℝ l (letterCoeff L lo X₀ δ s v u o q α k) z‖) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hl' : l ≤ n + (o.1 - 1) := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        have h1 := coefficientDerivativeArray_norm_le_iterated_bound
          (letterCoeffOp L lo X₀ δ s v u o q α k) l (hC.of_le (by exact_mod_cast hl')) z _
          (norm_nonneg _) le_rfl
        have h2 := letterCoeffOp_iteratedFDeriv_le L lo X₀ δ s v u o q α k hc hl' z
        refine h1.trans ?_
        exact mul_le_mul (card_word_le_wordCount (by omega)) h2 (norm_nonneg _)
          (wordCount_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun _ _ _ => mul_nonneg (wordCount_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

omit [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [Fintype ι] in
/-- The admissible constituents of a letter embed in its original source indices. -/
def constituentEmbedding {σ : Type*} (L : CycleLetter ι h D) (κ : σ → ℕ) (a b : σ) (v u : ι) :
    (Σ o : admissibleOrders κ D a b, Fin (L.edge v u (admissibleLetterOrder κ D a b o)).length ×
      DerivativeWord2 (o.1 - 1) × Fin 2) ↪ OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u where
  toFun x := constituentSourceIndex L v u (admissibleLetterOrder κ D a b x.1) x.2.1 x.2.2.1 x.2.2.2
  inj' := by
    rintro ⟨o, q, α, k⟩ ⟨o', q', α', k'⟩ hEq
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hEq
    obtain ⟨h1a, h1b⟩ := Sigma.mk.inj_iff.mp h1
    have hv : (admissibleLetterOrder κ D a b o).1 = (admissibleLetterOrder κ D a b o').1 :=
      congrArg Subtype.val h1a
    have hoo : o = o' := Subtype.ext hv
    subst hoo
    have hq : q = q' := eq_of_heq h1b
    subst hq
    obtain ⟨_, h3⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq h3)
    rfl

omit [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [Fintype ι] in
theorem constituent_sum_le {σ : Type*} (L : CycleLetter ι h D) (κ : σ → ℕ) (a b : σ) (v u : ι)
    (F : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ o : admissibleOrders κ D a b, ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D a b o)).length,
      ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
        F (constituentSourceIndex L v u (admissibleLetterOrder κ D a b o) q α k) ≤ ∑ x, F x := by
  have h1 : ∑ y, F (constituentEmbedding L κ a b v u y) ≤ ∑ x, F x := by
    rw [← Finset.sum_map Finset.univ (constituentEmbedding L κ a b v u) F]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hF x)
  refine le_trans (le_of_eq ?_) h1
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [Fintype ι] in
theorem letterScalarTaylor_constituent (L : CycleLetter ι h D) (v u : ι) (o : Finset.Icc 2 D)
    (q : Fin (L.edge v u o).length) (α : DerivativeWord2 (o.1 - 1)) (k : Fin 2)
    (ϖ ζ s : ℝ) (X₀ : Vec 2) :
    letterScalarTaylor L v u (constituentSourceIndex L v u o q α k) ϖ ζ s 0 X₀
      (constituentSourceIndex L v u o q α k).2.2.2 =
      letterCoeff L (if L.positive then 1 else 0) X₀ (ζ * ϖ) s v u o q α k :=
  constituent_taylor_eq L v u o q α k ζ ϖ s X₀

theorem sqrt_div_mul_sqrt_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt (y / x) * Real.sqrt (x / y) = 1 := by
  rw [← Real.sqrt_mul (div_nonneg hy.le hx.le), div_mul_div_comm, mul_comm y x,
    div_self (mul_pos hx hy).ne', Real.sqrt_one]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- **Pointwise bound of one jet of the transposed letter**, at every time of the window. -/
theorem letterTransposeJet_norm_le {σ : Type*} (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (ϖ ζ : ℝ) (X₀ : Vec 2)
    (κ : σ → ℕ) (a' b' : ι → σ) (n d : ℕ) (hJ : n + d ≤ J + 1) (s : ℝ) (hs : s ∈ Set.Icc a b)
    (Ψ : ∀ v, RawJet2 (n + d) (h v)) (z : Vec 2) (Y : ι → ℝ) (hY : ∀ v, 0 ≤ Y v)
    (hΨ : ∀ v i, ‖Ψ v i z‖ ≤ Y v) (u : ι) (idx : JetIndex2 n) :
    ‖letterTransposeJet π L κ a' b' (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ u idx z‖ ≤
      maskCount (n + d) * wordCount (n + d) * ∑ v, Real.sqrt (π u / π v) *
        (∑ l ∈ Finset.range (n + d), actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v u) * Y v := by
  classical
  set lo := if L.positive then 1 else 0 with hlo
  set W := maskCount (n + d) * wordCount (n + d) with hWdef
  have hW : 0 ≤ W := mul_nonneg (maskCount_nonneg _) (wordCount_nonneg _)
  -- the Taylor jets of one source index, summed over the orders
  set G : ∀ v, OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u → ℝ := fun v x =>
    ∑ l ∈ Finset.range (n + d), ‖((ChartedFamily.ofFiber L.edge).identity v u x.1).map‖ *
      ‖iteratedFDeriv ℝ l (letterScalarTaylor L v u x ϖ ζ s 0 X₀ x.2.2.2) z‖ with hGdef
  have hG : ∀ v x, 0 ≤ G v x := fun v x =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- one admissible order
  have hord : ∀ v (o : admissibleOrders κ D (a' v) (b' u)),
      ‖if hod : o.1 ≤ d then
          ((-1 : ℝ) ^ (o.1 - 1) * (π u / π v)) •
            ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a' v) (b' u) o)).length,
              ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
                letterTransposeTermJet L lo X₀ (ζ * ϖ) s v u
                  (admissibleLetterOrder κ D (a' v) (b' u) o) q α k n d hod (Ψ v) idx z
        else 0‖ ≤
      π u / π v * (W * Y v * ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a' v) (b' u) o)).length,
        ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
          G v (constituentSourceIndex L v u (admissibleLetterOrder κ D (a' v) (b' u) o) q α k)) := by
    intro v o
    have hpos : 0 ≤ π u / π v := (div_pos (hπ u) (hπ v)).le
    have hR : 0 ≤ W * Y v * ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a' v) (b' u) o)).length,
        ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
          G v (constituentSourceIndex L v u (admissibleLetterOrder κ D (a' v) (b' u) o) q α k) :=
      mul_nonneg (mul_nonneg hW (hY v)) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
        fun _ _ => Finset.sum_nonneg fun _ _ => hG _ _)
    by_cases hod : o.1 ≤ d
    · simp only [hod, dite_true]
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg hpos]
      refine mul_le_mul_of_nonneg_left ?_ hpos
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      have h1 := letterTransposeTermJet_norm_le L lo X₀ (ζ * ϖ) s v u
        (admissibleLetterOrder κ D (a' v) (b' u) o) q α k n d hod (Ψ v) z (hY v) (hΨ v) idx
      have h2 := letterCoeffArray_sum_le π L a b J H hL lo X₀ (ζ * ϖ) s hs v u
        (admissibleLetterOrder κ D (a' v) (b' u) o) q α k n d hod hJ z
      have h3 : G v (constituentSourceIndex L v u (admissibleLetterOrder κ D (a' v) (b' u) o) q α k)
          = ∑ l ∈ Finset.range (n + d),
            ‖((L.edge v u (admissibleLetterOrder κ D (a' v) (b' u) o)).get q).map‖ *
              ‖iteratedFDeriv ℝ l (letterCoeff L lo X₀ (ζ * ϖ) s v u
                (admissibleLetterOrder κ D (a' v) (b' u) o) q α k) z‖ := by
        rw [hGdef]
        dsimp only
        rw [letterScalarTaylor_constituent L v u (admissibleLetterOrder κ D (a' v) (b' u) o) q α k
          ϖ ζ s X₀]
        rfl
      rw [h3]
      calc _ ≤ maskCount (n + d) * ((wordCount (n + d) * ∑ l ∈ Finset.range (n + d),
            ‖((L.edge v u (admissibleLetterOrder κ D (a' v) (b' u) o)).get q).map‖ *
              ‖iteratedFDeriv ℝ l (letterCoeff L lo X₀ (ζ * ϖ) s v u
                (admissibleLetterOrder κ D (a' v) (b' u) o) q α k) z‖) * Y v) :=
            h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (hY v))
              (maskCount_nonneg _))
        _ = _ := by rw [hWdef]; ring
    · simp only [hod, dite_false, norm_zero]
      exact mul_nonneg hpos hR
  -- sum over the orders and the targets
  unfold letterTransposeJet
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun o _ => hord v o).trans ?_
  rw [← Finset.mul_sum]
  simp only [← Finset.mul_sum]
  have hcon := constituent_sum_le L κ (a' v) (b' u) v u (G v) (hG v)
  have hsq : π u / π v = Real.sqrt (π u / π v) * Real.sqrt (π u / π v) :=
    (Real.mul_self_sqrt (div_pos (hπ u) (hπ v)).le).symm
  have hmat : Real.sqrt (π u / π v) * ∑ x, G v x =
      ∑ l ∈ Finset.range (n + d), actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v u := by
    rw [hGdef]
    dsimp only
    rw [Finset.sum_comm, Finset.mul_sum]
    rfl
  calc π u / π v * (W * Y v * ∑ o : admissibleOrders κ D (a' v) (b' u),
        ∑ q : Fin (L.edge v u (admissibleLetterOrder κ D (a' v) (b' u) o)).length,
          ∑ α : DerivativeWord2 (o.1 - 1), ∑ k : Fin 2,
            G v (constituentSourceIndex L v u (admissibleLetterOrder κ D (a' v) (b' u) o) q α k))
      ≤ π u / π v * (W * Y v * ∑ x, G v x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcon (mul_nonneg hW (hY v)))
          (div_pos (hπ u) (hπ v)).le
    _ = W * (Real.sqrt (π u / π v) * (Real.sqrt (π u / π v) * ∑ x, G v x) * Y v) := by
        calc π u / π v * (W * Y v * ∑ x, G v x)
            = (Real.sqrt (π u / π v) * Real.sqrt (π u / π v)) * (W * Y v * ∑ x, G v x) := by
              rw [← hsq]
          _ = _ := by ring
    _ = _ := by rw [hmat]

/-- The constant of the pointwise bound. -/
def letterTransposeConst (n d J Ks : ℕ) (pos : Bool) (ζ : ℝ) : ℝ :=
  wordCount (n + d) * (maskCount (n + d) * wordCount (n + d)) * ((n + d : ℕ) : ℝ) *
    (originalFlaggedTaylorFastJetPriceConstant pos Ks J * (if pos then ζ else 1)) * 2
end

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **The weighted bound of the transposed letter.** For almost every time of the window, the
transposed letter loses `d` orders and the slow degree `K_s ≤ K` of weight, at cost `θ`:

`‖L*Ψ‖_{1,n;-(p+K)} ≤ C θ ‖Ψ‖_{1,n+d;-p}`,

`C` depending only on `n`, `d`, the reserve `J`, `K_s`, the sign flag and `ζ`. The pointwise mass
Schur bound `letterTranspose_pointwise_schur_ae` is integrated against the weights; the growth
`⟨ϖz⟩^{K_s}` of the coefficients is absorbed by `⟨ϖz⟩^{-(p+K)} ⟨ϖz⟩^{K_s} ≤ ⟨ϖz⟩^{-p}`. -/

/-- The squared `L²` norm of a real function as a lower integral. -/
theorem eLpNorm_two_sq_real (f : Vec 2 → ℝ) (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ z, ENNReal.ofReal (f z ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- **Mass-weighted families under a pointwise `ℓ²` domination.** -/
theorem familyNorm_le_of_pointwise {ι : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (F G : ι → Vec 2 → ℝ) (hF : ∀ u, AEStronglyMeasurable (F u) volume)
    (hG : ∀ v, AEStronglyMeasurable (G v) volume) (c : ℝ) (hc : 0 ≤ c)
    (hpt : ∀ᵐ z ∂volume, ∑ u, (π u)⁻¹ * F u z ^ 2 ≤ c ^ 2 * ∑ v, (π v)⁻¹ * G v z ^ 2) :
    familyNorm (fun u => ENNReal.ofReal ((π u)⁻¹)) (fun u => eLpNorm (F u) 2 volume) ≤
      ENNReal.ofReal c *
        familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹)) (fun v => eLpNorm (G v) 2 volume) := by
  have hsum : ∀ (H : ι → Vec 2 → ℝ), (∀ u, AEStronglyMeasurable (H u) volume) →
      ∑ u, ENNReal.ofReal ((π u)⁻¹) * eLpNorm (H u) 2 volume ^ 2 =
        ∫⁻ z, ENNReal.ofReal (∑ u, (π u)⁻¹ * H u z ^ 2) := by
    intro H hH
    simp only [fun u => eLpNorm_two_sq_real (H u) (hH u)]
    rw [show (∑ u, ENNReal.ofReal ((π u)⁻¹) * ∫⁻ z, ENNReal.ofReal (H u z ^ 2)) =
        ∑ u, ∫⁻ z, ENNReal.ofReal ((π u)⁻¹) * ENNReal.ofReal (H u z ^ 2) from
      Finset.sum_congr rfl fun u _ => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm]
    rw [← lintegral_finsetSum' _ fun u _ =>
      (((hH u).aemeasurable.pow_const 2).ennreal_ofReal).const_mul _]
    · refine lintegral_congr fun z => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun u _ =>
        mul_nonneg (inv_pos.mpr (hπ u)).le (sq_nonneg _)]
      exact Finset.sum_congr rfl fun u _ =>
        (ENNReal.ofReal_mul (inv_pos.mpr (hπ u)).le).symm
  have hle : ∑ u, ENNReal.ofReal ((π u)⁻¹) * eLpNorm (F u) 2 volume ^ 2 ≤
      ENNReal.ofReal c ^ 2 * ∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (G v) 2 volume ^ 2 := by
    rw [hsum F hF, hsum G hG, ← ENNReal.ofReal_pow hc, ← lintegral_const_mul']
    · refine lintegral_mono_ae ?_
      filter_upwards [hpt] with z hz
      rw [← ENNReal.ofReal_mul (sq_nonneg c)]
      exact ENNReal.ofReal_le_ofReal hz
    · exact ENNReal.ofReal_ne_top
  unfold familyNorm
  calc (∑ u, ENNReal.ofReal ((π u)⁻¹) * eLpNorm (F u) 2 volume ^ 2) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal c ^ 2 * ∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (G v) 2 volume ^ 2) ^
          (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

/-- The weight absorbs the polynomial growth of the coefficients. -/
theorem weight_mul_momentRoot_le (ϖ p : ℝ) (Ks K : ℕ) (hK : Ks ≤ K) (z : Vec 2) :
    (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p + K) / 2) * polynomialMomentRoot ϖ z ^ Ks ≤
      (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) := by
  set x := 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) with hx
  have hx1 : 1 ≤ x := by rw [hx]; nlinarith [sq_nonneg ϖ, sq_nonneg (z 0), sq_nonneg (z 1)]
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hroot : polynomialMomentRoot ϖ z ^ Ks = x ^ ((Ks : ℝ) / 2) := by
    unfold polynomialMomentRoot
    rw [← hx, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    ring_nf
  rw [hroot, ← Real.rpow_add hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx1 (by
    have : (Ks : ℝ) ≤ K := by exact_mod_cast hK
    linarith)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] {D : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- **Pointwise mass Schur bound of the transposed letter**, for almost every time. -/
theorem letterTranspose_pointwise_schur_ae {σ : Type*} (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (X₀ : Vec 2) (κ : σ → ℕ) (a' b' : ι → σ) (n d : ℕ)
    (hJ : n + d ≤ J + 1) :
    ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ (Ψ : ∀ v, RawJet2 (n + d) (h v)) (z : Vec 2)
      (Y : ι → ℝ), (∀ v, 0 ≤ Y v) → (∀ v i, ‖Ψ v i z‖ ≤ Y v) → ∀ (i : ℕ) (hi : i ≤ n),
      ∑ u, (π u)⁻¹ * ∑ w : DerivativeWord2 i, ‖letterTransposeJet π L κ a' b'
        (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ u ⟨⟨i, Nat.lt_succ_of_le hi⟩, w⟩ z‖ ^ 2 ≤
      (letterTransposeConst n d J L.slow L.positive ζ * L.theta *
        polynomialMomentRoot ϖ z ^ L.slow) ^ 2 * ∑ v, (π v)⁻¹ * Y v ^ 2 := by
  have hsch := actualTaylorJetMatrix_schur_ae π hπ L (Set.Icc a b ×ˢ Set.univ) J H hL ϖ ζ hϖ hϖ1
    hζ hζ1
  have hC0 := (analyticOriginalSource_flagged_taylor_fast_price (ι := ι) (h := h) (D := D)
    (P := Unit) (Ctx := fun _ => Unit) L.positive L.slow J).1
  filter_upwards [ae_restrict_of_ae hsch, ae_restrict_mem measurableSet_Icc] with s hs hmem
  intro Ψ z Y hY hΨ i hi
  have hdom : ∀ Y' : Vec 2, (s, Y') ∈ Set.Icc a b ×ˢ (Set.univ : Set (Vec 2)) :=
    fun Y' => ⟨hmem, Set.mem_univ _⟩
  set price := actualTaylorJetMatrixPrice L J ϖ ζ z with hpricedef
  have hprice : 0 ≤ price := by
    have hflag : 0 ≤ (if L.positive then ζ else 1) := by split <;> positivity
    exact mul_nonneg (mul_nonneg hC0 hflag)
      (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) L.slow)
  have hθ := hL.theta_nonneg
  set B : ι → ι → ℝ := fun v u => ∑ l ∈ Finset.range (n + d),
    actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v u with hBdef
  have hB0 : ∀ v u, 0 ≤ B v u := fun v u => Finset.sum_nonneg fun l hl =>
    (hs hdom 0 X₀ l (by have := Finset.mem_range.mp hl; omega) z).1 v u
  have hBrow : ∀ v, ∑ u, B v u ≤ ((n + d : ℕ) : ℝ) * (price * (2 * L.theta)) := by
    intro v
    rw [hBdef]
    dsimp only
    rw [Finset.sum_comm]
    calc ∑ l ∈ Finset.range (n + d), ∑ u, actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v u
        ≤ ∑ _l ∈ Finset.range (n + d), price * (2 * L.theta) := Finset.sum_le_sum fun l hl =>
          (hs hdom 0 X₀ l (by have := Finset.mem_range.mp hl; omega) z).2.1 v
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hBcol : ∀ u, ∑ v, B v u ≤ ((n + d : ℕ) : ℝ) * (price * (2 * L.theta)) := by
    intro u
    rw [hBdef]
    dsimp only
    rw [Finset.sum_comm]
    calc ∑ l ∈ Finset.range (n + d), ∑ v, actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v u
        ≤ ∑ _l ∈ Finset.range (n + d), price * (2 * L.theta) := Finset.sum_le_sum fun l hl =>
          (hs hdom 0 X₀ l (by have := Finset.mem_range.mp hl; omega) z).2.2 u
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set W := maskCount (n + d) * wordCount (n + d) with hWdef
  have hW : 0 ≤ W := mul_nonneg (maskCount_nonneg _) (wordCount_nonneg _)
  set Wc := wordCount (n + d) with hWcdef
  have hWc : 0 ≤ Wc := wordCount_nonneg _
  set T : ι → DerivativeWord2 i → ℝ := fun u w => ‖letterTransposeJet π L κ a' b'
    (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ u ⟨⟨i, Nat.lt_succ_of_le hi⟩, w⟩ z‖
    with hTdef
  set R : ι → ℝ := fun u => W * ∑ v, Real.sqrt (π u / π v) * B v u * Y v with hRdef
  have hR : ∀ u, 0 ≤ R u := fun u => mul_nonneg hW (Finset.sum_nonneg fun v _ =>
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hB0 v u)) (hY v))
  have hent : ∀ u w, T u w ≤ R u := fun u w =>
    letterTransposeJet_norm_le π hπ L a b J H hL ϖ ζ X₀ κ a' b' n d hJ s hmem Ψ z Y hY hΨ u _
  set f : ι → ℝ := fun u => Real.sqrt (∑ w, T u w ^ 2) with hfdef
  have hcard : (1 : ℝ) ≤ (Fintype.card (DerivativeWord2 i) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := DerivativeWord2 i)
  have hf : ∀ u, f u ≤ ∑ v, (Wc * W * Real.sqrt (π u / π v) * B v u) * Y v := by
    intro u
    have h1 : ∑ w, T u w ^ 2 ≤ (Fintype.card (DerivativeWord2 i) : ℝ) * R u ^ 2 := by
      calc ∑ w, T u w ^ 2 ≤ ∑ _w : DerivativeWord2 i, R u ^ 2 :=
            Finset.sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hent u w) 2
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : f u ≤ Real.sqrt (Fintype.card (DerivativeWord2 i) : ℝ) * R u := by
      rw [hfdef]
      dsimp only
      rw [← Real.sqrt_sq (hR u), ← Real.sqrt_mul (Nat.cast_nonneg _)]
      exact Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (Fintype.card (DerivativeWord2 i) : ℝ) ≤ Wc := by
      have h4 : Real.sqrt (Fintype.card (DerivativeWord2 i) : ℝ) ≤
          (Fintype.card (DerivativeWord2 i) : ℝ) :=
        Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      exact h4.trans (card_word_le_wordCount (by omega))
    calc f u ≤ Real.sqrt (Fintype.card (DerivativeWord2 i) : ℝ) * R u := h2
      _ ≤ Wc * R u := mul_le_mul_of_nonneg_right h3 (hR u)
      _ = _ := by
          rw [hRdef]
          dsimp only
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
  set θ' := Wc * W * (((n + d : ℕ) : ℝ) * (price * (2 * L.theta))) with hθ'def
  have hθ' : 0 ≤ θ' := mul_nonneg (mul_nonneg hWc hW)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hprice (mul_nonneg (by norm_num) hθ)))
  have hone : ∀ u v, Real.sqrt (π v / π u) * (Wc * W * Real.sqrt (π u / π v) * B v u) =
      Wc * W * B v u := by
    intro u v
    have h1 := sqrt_div_mul_sqrt_div (hπ u) (hπ v)
    calc _ = Wc * W * B v u * (Real.sqrt (π v / π u) * Real.sqrt (π u / π v)) := by ring
      _ = _ := by rw [h1, mul_one]
  have hsc := finite_mass_schur_square_le π hπ
    (fun u v => Wc * W * Real.sqrt (π u / π v) * B v u)
    (fun u v => mul_nonneg (mul_nonneg (mul_nonneg hWc hW) (Real.sqrt_nonneg _)) (hB0 v u))
    θ' hθ'
    (fun u => by
      simp only [hone]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hBcol u) (mul_nonneg hWc hW))
    (fun v => by
      simp only [hone]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hBrow v) (mul_nonneg hWc hW))
    Y f (fun u => Real.sqrt_nonneg _) hf
  have hfsq : ∀ u, f u ^ 2 = ∑ w, T u w ^ 2 := fun u =>
    Real.sq_sqrt (Finset.sum_nonneg fun w _ => sq_nonneg _)
  calc ∑ u, (π u)⁻¹ * ∑ w, T u w ^ 2 = ∑ u, (π u)⁻¹ * f u ^ 2 := by simp only [hfsq]
    _ ≤ θ' ^ 2 * ∑ v, (π v)⁻¹ * Y v ^ 2 := hsc
    _ = _ := by
        rw [hθ'def, hWdef, hWcdef, hpricedef]
        unfold letterTransposeConst actualTaylorJetMatrixPrice
        ring

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **The weighted norm of the transposed letter.** For almost every time of the window, for every
regular adjoint family `Ψ` of order `n + d`, every real weight `p` and every `K ≥ K_s`:

`‖L*Ψ‖_{1,n;-(p+K)} ≤ (n+1)(n+d)! C θ ‖Ψ‖_{1,n+d;-p}`,

with `C = letterTransposeConst n d J K_s pos ζ`. -/

theorem weightedJetNorm_eq_familyNorm {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) :
    weightedJetNorm π p j s r J = ∑ a ∈ Finset.range (j + 1),
      ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹)) (fun v => eLpNorm (fun z =>
          (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
            Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume) := rfl

theorem letterTransposeConst_nonneg (n d J Ks : ℕ) (pos : Bool) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    0 ≤ letterTransposeConst n d J Ks pos ζ := by
  have hC0 := (analyticOriginalSource_flagged_taylor_fast_price (ι := Unit)
    (h := fun _ => ℝ) (D := 2) (P := Unit) (Ctx := fun _ => Unit) pos Ks J).1
  have hflag : 0 ≤ (if pos then ζ else 1) := by split <;> positivity
  unfold letterTransposeConst
  have := maskCount_nonneg (n + d)
  have := wordCount_nonneg (n + d)
  positivity

theorem sqrt_sum_le_sum_sqrt {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) :
    Real.sqrt (∑ a ∈ s, f a) ≤ ∑ a ∈ s, Real.sqrt (f a) := by
  have hs : 0 ≤ ∑ a ∈ s, Real.sqrt (f a) := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  rw [Real.sqrt_le_left hs]
  calc ∑ a ∈ s, f a = ∑ a ∈ s, Real.sqrt (f a) ^ 2 :=
        Finset.sum_congr rfl fun a ha => (Real.sq_sqrt (hf a ha)).symm
    _ ≤ (∑ a ∈ s, Real.sqrt (f a)) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => Real.sqrt_nonneg _

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] {D : ℕ}

/-- **The weighted bound of the transposed letter**, for almost every time. -/
theorem letterTranspose_weightedJetNorm_le_ae {σ : Type*} (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (X₀ : Vec 2) (κ : σ → ℕ) (a' b' : ι → σ) (n d : ℕ)
    (hJ : n + d ≤ J + 1) :
    ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ (Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v))
      (hreg : LetterTermRegular L (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ)
      (p : ℝ) (K : ℕ), L.slow ≤ K →
      weightedJetNorm π (-(p + K)) n ϖ 1 (fun u i w z => planeJetOrder
        (letterTransposeHk π L κ a' b' (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ hreg u)
          i w z) ≤
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * ((n + d).factorial : ℝ) *
          (letterTransposeConst n d J L.slow L.positive ζ * L.theta)) *
          weightedJetNorm π (-p) (n + d) ϖ 1 (fun v i w z => planeJetOrder (Ψ v) i w z) := by
  filter_upwards [letterTranspose_pointwise_schur_ae π hπ L a b J H hL ϖ ζ hϖ hϖ1 hζ hζ1 X₀ κ a' b'
    n d hJ] with s hs
  intro Ψ hreg p K hK
  -- the jets of the carrier are the raw transposed jets; afterwards the carrier is opaque
  have hjet : ∀ u (i : ℕ) (hi : i ≤ n) (w : DerivativeWord2 i), planeJetOrder
      (letterTransposeHk π L κ a' b' (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ hreg u)
        i w =ᵐ[volume] fun z => letterTransposeJet π L κ a' b' (if L.positive then 1 else 0)
          X₀ (ζ * ϖ) s n d (fun v => (Ψ v).toFunction.jet) u ⟨⟨i, Nat.lt_succ_of_le hi⟩, w⟩ z := by
    intro u i hi w
    filter_upwards [letterTransposeHk_jet_ae π L κ a' b' (if L.positive then 1 else 0) X₀
      (ζ * ϖ) s n d Ψ hreg u ⟨⟨i, Nat.lt_succ_of_le hi⟩, w⟩] with z hz
    simp only [planeJetOrder, hi, dite_true]
    exact hz
  generalize letterTransposeHk π L κ a' b' (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ hreg
    = T at hjet ⊢
  set C0 := letterTransposeConst n d J L.slow L.positive ζ * L.theta with hC0def
  have hC0 : 0 ≤ C0 := mul_nonneg (letterTransposeConst_nonneg _ _ _ _ _ _ hζ) hL.theta_nonneg
  have hwt0 : ∀ (q : ℝ) (z : Vec 2), 0 ≤ (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) :=
    fun q z => Real.rpow_nonneg (by positivity) _
  set Y : ι → Vec 2 → ℝ := fun v z =>
    Real.sqrt (∑ idx : JetIndex2 (n + d), ‖(Ψ v).toFunction.jet idx z‖ ^ 2) with hYdef
  have hY0 : ∀ v z, 0 ≤ Y v z := fun v z => Real.sqrt_nonneg _
  have hYb : ∀ v idx z, ‖(Ψ v).toFunction.jet idx z‖ ≤ Y v z := by
    intro v idx z
    exact (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mpr
      (Finset.single_le_sum (f := fun idx => ‖(Ψ v).toFunction.jet idx z‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ idx))
  have hjm : ∀ v (idx : JetIndex2 (n + d)),
      AEStronglyMeasurable ((Ψ v).toFunction.jet idx) volume := fun v idx => by
    simpa only [Measure.restrict_univ] using ((Ψ v).toFunction.memL2 idx).aestronglyMeasurable
  have hYm : ∀ v, AEStronglyMeasurable (Y v) volume := fun v =>
    Real.continuous_sqrt.comp_aestronglyMeasurable (Finset.aestronglyMeasurable_fun_sum _
      fun idx _ => ((hjm v idx).norm.pow 2))
  set G : ι → Vec 2 → ℝ := fun v z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) * Y v z
    with hGdef
  have hGm : ∀ v, AEStronglyMeasurable (G v) volume := fun v =>
    (weight_continuous ϖ (-p)).aestronglyMeasurable.mul (hYm v)
  -- each order of the transposed letter
  have hord : ∀ i ∈ Finset.range (n + 1),
      familyNorm (fun u => ENNReal.ofReal ((π u)⁻¹)) (fun u => eLpNorm (fun z =>
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p + K) / 2) *
          Real.sqrt (∑ w : DerivativeWord2 i, ‖planeJetOrder (T u) i w z‖ ^ 2)) 2 volume) ≤
        ENNReal.ofReal C0 * familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹))
          (fun v => eLpNorm (G v) 2 volume) := by
    intro i hi
    have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hFm : ∀ u, AEStronglyMeasurable (fun z =>
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p + K) / 2) *
          Real.sqrt (∑ w : DerivativeWord2 i, ‖planeJetOrder (T u) i w z‖ ^ 2)) volume :=
      fun u => weighted_word_norm_aestronglyMeasurable ϖ (-(p + K)) _ fun w =>
        planeJetOrder_aestronglyMeasurable _ i w
    refine familyNorm_le_of_pointwise π hπ (fun u z =>
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p + K) / 2) *
          Real.sqrt (∑ w : DerivativeWord2 i, ‖planeJetOrder (T u) i w z‖ ^ 2)) G hFm hGm
      C0 hC0 ?_
    filter_upwards [ae_all_iff.mpr fun u => ae_all_iff.mpr fun w => hjet u i hi' w] with z hz
    have h1 := hs (fun v => (Ψ v).toFunction.jet) z (fun v => Y v z) (fun v => hY0 v z)
      (fun v idx => hYb v idx z) i hi'
    have hwk := weight_mul_momentRoot_le ϖ p L.slow K hK z
    set ω := (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p + K) / 2) with hωdef
    set ω' := (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) with hω'def
    have hω : 0 ≤ ω := hwt0 _ z
    have hsq : ∀ (S : ℝ), 0 ≤ S → (ω * Real.sqrt S) ^ 2 = ω ^ 2 * S :=
      fun S hS => by rw [mul_pow, Real.sq_sqrt hS]
    have hroot : 0 ≤ polynomialMomentRoot ϖ z ^ L.slow :=
      pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _
    have hYs : 0 ≤ ∑ v, (π v)⁻¹ * Y v z ^ 2 :=
      Finset.sum_nonneg fun v _ => mul_nonneg (inv_pos.mpr (hπ v)).le (sq_nonneg _)
    calc ∑ u, (π u)⁻¹ * (ω * Real.sqrt (∑ w : DerivativeWord2 i,
          ‖planeJetOrder (T u) i w z‖ ^ 2)) ^ 2
        = ω ^ 2 * ∑ u, (π u)⁻¹ * ∑ w : DerivativeWord2 i,
            ‖letterTransposeJet π L κ a' b' (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d
              (fun v => (Ψ v).toFunction.jet) u ⟨⟨i, Nat.lt_succ_of_le hi'⟩, w⟩ z‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [hsq _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
          simp only [hz u]
          ring
      _ ≤ ω ^ 2 * ((C0 * polynomialMomentRoot ϖ z ^ L.slow) ^ 2 *
            ∑ v, (π v)⁻¹ * Y v z ^ 2) :=
          mul_le_mul_of_nonneg_left (le_trans h1 (le_of_eq (by rw [hC0def]))) (sq_nonneg _)
      _ = C0 ^ 2 * ((ω * polynomialMomentRoot ϖ z ^ L.slow) ^ 2 *
            ∑ v, (π v)⁻¹ * Y v z ^ 2) := by ring
      _ ≤ C0 ^ 2 * (ω' ^ 2 * ∑ v, (π v)⁻¹ * Y v z ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (mul_nonneg hω hroot) hwk 2) hYs) (sq_nonneg _)
      _ = C0 ^ 2 * ∑ v, (π v)⁻¹ * G v z ^ 2 := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [hGdef]
          ring
  -- the adjoint family through its orders
  have hmaj := familyNorm_eLpNorm_majorant (fun v => ENNReal.ofReal ((π v)⁻¹))
    (Finset.range (n + d + 1)) (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) G hGm
    (fun i' v z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 i', ‖planeJetOrder (Ψ v) i' w z‖ ^ 2)) (fun v z => by
      rw [abs_of_nonneg (mul_nonneg (hwt0 _ _) (hY0 v z))]
      simp only [one_mul]
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (hwt0 _ _)
      have hsplit : ∑ idx : JetIndex2 (n + d), ‖(Ψ v).toFunction.jet idx z‖ ^ 2 =
          ∑ i' ∈ Finset.range (n + d + 1), ∑ w : DerivativeWord2 i',
            ‖planeJetOrder (Ψ v) i' w z‖ ^ 2 := by
        rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun w _ => ?_
        simp only [planeJetOrder, Nat.le_of_lt_succ i'.isLt, dite_true]
      rw [hYdef]
      dsimp only
      rw [hsplit]
      exact sqrt_sum_le_sum_sqrt _ _ fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hG : familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹)) (fun v => eLpNorm (G v) 2 volume) ≤
      ENNReal.ofReal ((n + d).factorial : ℝ) *
        weightedJetNorm π (-p) (n + d) ϖ 1 (fun v i w z => planeJetOrder (Ψ v) i w z) := by
    refine hmaj.trans ?_
    rw [weightedJetNorm_eq_familyNorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i' hi' => ?_
    rw [ENNReal.ofReal_one, one_mul, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine le_mul_of_one_le_left (by positivity) (ENNReal.one_le_ofReal.mpr ?_)
    have hfac : (i'.factorial : ℝ) ≤ ((n + d).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi'))
    have hpos : (0 : ℝ) < i'.factorial := by exact_mod_cast Nat.factorial_pos i'
    rw [one_pow, mul_one_div, le_div_iff₀ hpos, one_mul]
    exact hfac
  rw [weightedJetNorm_eq_familyNorm]
  calc ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal ((1 : ℝ) ^ i / (i.factorial : ℝ)) *
        familyNorm (fun u => ENNReal.ofReal ((π u)⁻¹)) (fun u => eLpNorm (fun z =>
          (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p + K) / 2) *
            Real.sqrt (∑ w : DerivativeWord2 i, ‖planeJetOrder (T u) i w z‖ ^ 2)) 2 volume)
      ≤ ∑ _i ∈ Finset.range (n + 1), ENNReal.ofReal C0 *
          familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹)) (fun v => eLpNorm (G v) 2 volume) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine le_trans (mul_le_of_le_one_left (by positivity) (ENNReal.ofReal_le_one.mpr ?_))
          (hord i hi)
        have hf1 : (1 : ℝ) ≤ (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
        rw [one_pow]
        exact div_le_one_of_le₀ hf1 (Nat.cast_nonneg _)
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal C0 *
          familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹)) (fun v => eLpNorm (G v) 2 volume)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal C0 * (ENNReal.ofReal ((n + d).factorial : ℝ) *
          weightedJetNorm π (-p) (n + d) ϖ 1 (fun v i w z => planeJetOrder (Ψ v) i w z))) := by
        gcongr
    _ = _ := by
        have h1 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * ((n + d).factorial : ℝ) := by positivity
        rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        ring

end AVRegularity.CycleWords.Seam
end
