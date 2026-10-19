-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.BandRep
public import AVRegularity.CycleWords.MixedWords.ZeroAmplitudeWordStep
import AVRegularity.CycleWords.MixedWords.Discard.WeakContCutCurve
import AVRegularity.CycleWords.MixedWords.AdjointExists
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleWords.MixedWords.Discard.JetFourier
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard.BandJets

/-! # finite-moment Fourier jets

The all-moments facts on Fourier jets (ordered Fourier derivatives are word moments rotated by
quarter-turns; normalized pair norms of the full jets are bounded by the moment pairs), proved with
the integrable moments of order `≤ k` only (`FinMom k`), starting from `phasePair_hasFDerivAt`. -/

open AVRegularity.CycleWords.Discard.BandDatum

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiplication by a word monomial of degree `k` lowers the moment order by `k`. -/
theorem finMom_word : ∀ {k n : ℕ} {g : Vec 2 → E} (wd : DerivativeWord2 k),
    FinMom (n + k) g → FinMom n (fun y => wordMonomial wd y • g y)
  | 0, n, g, wd, hg => by
    simpa only [wordMonomial, Fin.prod_univ_zero, one_smul] using (show FinMom n g from hg)
  | k + 1, n, g, wd, hg => by
    have h1 : FinMom (n + 1 + k) g := by
      have : n + 1 + k = n + (k + 1) := by omega
      rwa [this]
    have hm := (finMom_word (fun i : Fin k => wd i.castSucc) h1).coord (wd (Fin.last k))
    simpa only [wordMonomial_succ, smul_smul] using hm

variable [CompleteSpace E]

private theorem finPhasePair_basis {A B : Vec 2 → E}
    (hA : FinMom 1 A) (hB : FinMom 1 B) (i : Fin 2) (θ : Vec 2) :
    fderiv ℝ (phasePair A B) θ (basisVec i) =
      phasePair (derivAmpA i B) (derivAmpB i A) θ := by
  rw [(phasePair_hasFDerivAt hA hB θ).fderiv]
  fin_cases i <;> simp [coordSmulRight_apply, basisVec_apply, Fin.sum_univ_two]

/-- Every ordered derivative of a trigonometric integral is another one, of a word moment
(finite moments of order `≤ k`). -/
theorem phasePair_orderedDerivative : ∀ {k : ℕ} (wd : DerivativeWord2 k)
    {A B : Vec 2 → E}, FinMom k A → FinMom k B →
    orderedDerivative wd (phasePair A B) =
      phasePair
        (jRot k (fun y => wordMonomial wd y • A y, fun y => wordMonomial wd y • B y)).1
        (jRot k (fun y => wordMonomial wd y • A y, fun y => wordMonomial wd y • B y)).2
  | 0, wd, A, B, _, _ => by
    rw [AVRegularity.orderedDerivative_zero]
    simp only [jRot, wordMonomial, Fin.prod_univ_zero, one_smul]
  | k + 1, wd, A, B, hA, hB => by
    have hA' : FinMom (1 + k) A := by
      have : 1 + k = k + 1 := by omega
      rwa [this]
    have hB' : FinMom (1 + k) B := by
      have : 1 + k = k + 1 := by omega
      rwa [this]
    have hmem := jRot_mem (fun X : Vec 2 → E => FinMom 1 X)
      (fun _ hx => hx.neg) k
      (p := (fun y => wordMonomial (fun i : Fin k => wd i.castSucc) y • A y,
        fun y => wordMonomial (fun i : Fin k => wd i.castSucc) y • B y))
      (finMom_word (fun i : Fin k => wd i.castSucc) hA')
      (finMom_word (fun i : Fin k => wd i.castSucc) hB')
    rw [AVRegularity.orderedDerivative_succ,
      phasePair_orderedDerivative (fun i : Fin k => wd i.castSucc) (hA.mono (by omega))
        (hB.mono (by omega))]
    funext θ
    rw [finPhasePair_basis hmem.1 hmem.2]
    have hp : (fun y => wordMonomial wd y • A y, fun y => wordMonomial wd y • B y) =
        (fun y => y (wd (Fin.last k)) • (wordMonomial (fun i : Fin k => wd i.castSucc) y • A y),
          fun y => y (wd (Fin.last k)) • (wordMonomial (fun i : Fin k => wd i.castSucc) y • B y)) := by
      simp only [wordMonomial_succ, smul_smul]
    rw [hp, jRot_succ_smul]

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem finJRot_neg (j : ℕ) (A B : Vec 2 → E) :
    jRot j (-A, -B) = (-(jRot j (A, B)).1, -(jRot j (A, B)).2) :=
  jRot_comm (fun X : Vec 2 → E => -X) (fun _ => rfl) j (A, B)

omit [CompleteSpace E] in
private theorem finCos_eq_phasePair (g : Vec 2 → E) :
    (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) = phasePair g 0 := by
  funext θ
  simp only [phasePair, Pi.zero_apply, smul_zero, add_zero]
  congr 1
  funext y
  congr 2
  unfold vecDot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

omit [CompleteSpace E] in
private theorem finSin_eq_phasePair (g : Vec 2 → E) :
    (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) = phasePair 0 g := by
  funext θ
  simp only [phasePair, Pi.zero_apply, smul_zero, zero_add]
  congr 1
  funext y
  congr 2
  unfold vecDot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- An ordered Fourier derivative rotates the corresponding word moment without changing its
squared cosine/sine pair norm. -/
theorem finMom_ordered_sq {g : Vec 2 → E} {k : ℕ} (hg : FinMom k g)
    (wd : DerivativeWord2 k) (θ : Vec 2) :
    ‖orderedDerivative wd (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) θ‖ ^ 2 +
      ‖orderedDerivative wd (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) θ‖ ^ 2 =
        ‖∫ y, Real.cos (vecDot θ y) • (wordMonomial wd y • g y)‖ ^ 2 +
          ‖∫ y, Real.sin (vecDot θ y) • (wordMonomial wd y • g y)‖ ^ 2 := by
  rw [finCos_eq_phasePair, finSin_eq_phasePair,
    phasePair_orderedDerivative wd hg finMom_zero,
    phasePair_orderedDerivative wd finMom_zero hg]
  simp only [Pi.zero_apply, smul_zero]
  let M : Vec 2 → E := fun y => wordMonomial wd y • g y
  have he := factorPhasePair_rotation_sq M 0 k θ
  have hn : jRot k (0, -M) = (-(jRot k (0, M)).1, -(jRot k (0, M)).2) := by
    simpa only [neg_zero] using finJRot_neg k (0 : Vec 2 → E) M
  rw [hn] at he
  have hneg : ∀ X Y : Vec 2 → E, factorPhasePair (-X) (-Y) = -factorPhasePair X Y := fun X Y =>
    factorPhasePair_neg X Y
  have h1 : factorPhasePair (-(jRot k (0, M)).1) (-(jRot k (0, M)).2) =
      -factorPhasePair (jRot k (0, M)).1 (jRot k (0, M)).2 := hneg _ _
  rw [h1, Pi.neg_apply, norm_neg] at he
  have hneg' : factorPhasePair 0 (-M) = -factorPhasePair 0 M := by
    simpa only [neg_zero] using factorPhasePair_neg (0 : Vec 2 → E) M
  rw [hneg', Pi.neg_apply, norm_neg] at he
  have c1 : factorPhasePair M 0 = phasePair M 0 := rfl
  have c2 : factorPhasePair 0 M = phasePair 0 M := rfl
  have c3 : ∀ X Y : Vec 2 → E, factorPhasePair X Y = phasePair X Y := fun _ _ => rfl
  simp only [c3] at he
  rw [← finCos_eq_phasePair M, ← finSin_eq_phasePair M] at he
  exact he

/-- Normalized ordered Fourier jets are exactly the normalized moment pairs. -/
theorem finMom_normalized_ordered_sq {g : Vec 2 → E} {k : ℕ} (hg : FinMom k g)
    (wd : DerivativeWord2 k) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) :
    (w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) θ‖) ^ 2 +
      (w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) θ‖) ^ 2 =
      ‖∫ y, (Real.cos (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 *
        (w * y 1) ^ (idxCount wd).2) • g y‖ ^ 2 +
      ‖∫ y, (Real.sin (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 *
        (w * y 1) ^ (idxCount wd).2) • g y‖ ^ 2 := by
  have he (ψ : ℝ → ℝ) : (∫ y, (ψ (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 *
      (w * y 1) ^ (idxCount wd).2) • g y) =
      w ^ k • ∫ y, ψ (vecDot θ y) • (wordMonomial wd y • g y) := by
    rw [← integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    simp only [smul_smul]
    congr 1
    rw [show ψ (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 * (w * y 1) ^ (idxCount wd).2 =
      ψ (vecDot θ y) * ((w * y 0) ^ (idxCount wd).1 * (w * y 1) ^ (idxCount wd).2) by ring,
      ← wordMonomial_smul_eq, wordMonomial_smul_eq_pow]
    ring
  rw [he Real.cos, he Real.sin]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw k)]
  rw [mul_pow, mul_pow, ← mul_add, finMom_ordered_sq hg wd θ]
  ring

end Scalar

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)] [∀ x, CompleteSpace (h x)]

/-- The weighted normalized ordered Fourier pair is the moment amplitude norm. -/
theorem finMom_ordered_pair (π : ι → ℝ) {g : ∀ x, Vec 2 → h x} {k : ℕ}
    (hg : ∀ x, FinMom k (g x)) (wd : DerivativeWord2 k) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) :
    factorFamilyPairNorm π
      (fun x => w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) θ‖)
      (fun x => w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) θ‖) =
        momentAmpNorm π w (idxCount wd) g θ := by
  unfold factorFamilyPairNorm momentAmpNorm
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    finMom_normalized_ordered_sq (hg x) wd θ hw]

/-- Full normalized Fourier jets are bounded by the finite collection of ordered moments. -/
theorem finMom_full_pair_le (π : ι → ℝ) {g : ∀ x, Vec 2 → h x} {k : ℕ}
    (hg : ∀ x, FinMom k (g x)) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) :
    ENNReal.ofReal (w ^ k) * factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) θ‖)
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) θ‖) ≤
        ENNReal.ofReal ((2 : ℝ) ^ k) * ∑ wd : DerivativeWord2 k,
          momentAmpNorm π w (idxCount wd) g θ := by
  let A (ψ : ℝ → ℝ) (x : ι) := w ^ k *
    ‖iteratedFDeriv ℝ k (fun θ => ∫ y, ψ (vecDot θ y) • g x y) θ‖
  let P (ψ : ℝ → ℝ) (wd : DerivativeWord2 k) (x : ι) := w ^ k *
    ‖orderedDerivative wd (fun θ => ∫ y, ψ (vecDot θ y) • g x y) θ‖
  have hb (ψ : ℝ → ℝ) (hψ : ∀ x, ContDiff ℝ k (fun θ => ∫ y, ψ (vecDot θ y) • g x y)) :
      ∀ x, A ψ x ≤ ∑ wd : DerivativeWord2 k, (1 : ℝ) * P ψ wd x := by
    intro x
    have hp := mul_le_mul_of_nonneg_left
      (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words (hψ x) θ) (pow_nonneg hw k)
    simpa only [Finset.mul_sum, one_mul] using hp
  have hc : ∀ x, ContDiff ℝ k (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) :=
    fun x => finMom_cos_contDiff (hg x)
  have hs : ∀ x, ContDiff ℝ k (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) :=
    fun x => finMom_sin_contDiff (hg x)
  have hn := factorFamilyPairNorm_sum_le π (Finset.univ : Finset (DerivativeWord2 k))
    (fun _ => 1) (fun _ _ => zero_le_one) (A Real.cos) (A Real.sin)
    (P Real.cos) (P Real.sin) (fun x => by dsimp [A]; positivity)
    (fun x => by dsimp [A]; positivity) (hb Real.cos hc) (hb Real.sin hs)
  have he : factorFamilyPairNorm π (A Real.cos) (A Real.sin) = ENNReal.ofReal (w ^ k) *
      factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) θ‖)
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) θ‖) := by
    dsimp only [A]
    rw [factorFamilyPairNorm_smul, abs_of_nonneg (pow_nonneg hw k)]
  rw [he] at hn
  have hp (wd : DerivativeWord2 k) : factorFamilyPairNorm π (P Real.cos wd) (P Real.sin wd) =
      momentAmpNorm π w (idxCount wd) g θ := finMom_ordered_pair π hg wd θ hw
  simp only [hp, ENNReal.ofReal_one, one_mul, AVRegularity.ChartTransport.card_derivativeWord2] at hn
  refine hn.trans (mul_le_mul' ?_ le_rfl)
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ≥0∞) ≤ 2 ^ k by exact one_le_pow₀ (by norm_num)) (by norm_num : (1 / 2 : ℝ) ≤ 1)

end Family

end AVRegularity.CycleWords.Discard.BandJets
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # The homogeneous propagator in `H^j` with a kernel

From the core (`kernelCore`): the fields `pos`, `self`, `shrink` and `decay` of
`IsFibreKernel` are all that is used. -/

/-- The homogeneous propagator in `H^j` with a kernel. -/
theorem cellKernelHs : CellKernelHsStatement := by
  intro j ρ A hρ hA
  obtain ⟨C, Q, hC, h⟩ := kernelCore j ρ A hρ hA
  refine ⟨C, Q, hC, ?_⟩
  intro a b L G hG v hv V hb θ hab hL hθ hsm hjet κ hK u slice hu
  exact h a b L G hG hv V hb θ hab hL hθ hsm hjet κ (fun r s => (hK.pos r s).le) hK.self
    (fun p s t h1 h2 h3 h4 h5 => hK.shrink p p s t h1 le_rfl (by linarith) h2 h3 h4 h5)
    hK.decay u slice hu

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard.BandDatum
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard.BandJets

/-! # the Leibniz step and the jets of the Fourier amplitudes in `ℓ²(family)` form

At a fixed frequency `θ`: the weighted pair norm of the `k`-th derivative of `mc · F` is bounded by
`(k+1)² 8^k B_c · T` as soon as the weighted pair norms of the derivatives of `F, G` of order
`j ≤ m` are bounded by `4^j T` and `ϖ^l ‖D^l mc‖ ≤ B_c` (`factorProduct_pair_le`); the cutoff
amplitudes of a field with finite moments satisfy the hypothesis with `T = m! · outMeanSq^{1/2}`
(`finMom_full_pair_le`, `momentAmp_le`). -/

universe u v

section Leibniz

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The Leibniz step.** -/
theorem leibniz_k (π : ι → ℝ) {m : ℕ} {F G : ∀ x, Vec 2 → h x}
    (hF : ∀ x, ContDiff ℝ m (F x)) (hG : ∀ x, ContDiff ℝ m (G x)) {mc : Vec 2 → ℝ}
    (hmc : ContDiff ℝ m mc) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) {Bc : ℝ}
    (hBc : ∀ l ≤ m, w ^ l * ‖iteratedFDeriv ℝ l mc θ‖ ≤ Bc) {T : ℝ≥0∞}
    (hT : ∀ j ≤ m, ENNReal.ofReal (w ^ j) * factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ j (F x) θ‖) (fun x => ‖iteratedFDeriv ℝ j (G x) θ‖) ≤
        ENNReal.ofReal ((4 : ℝ) ^ j) * T) {k : ℕ} (hk : k ≤ m) :
    ENNReal.ofReal (w ^ k) * factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • F x z) θ‖)
      (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • G x z) θ‖) ≤
    ENNReal.ofReal (((k + 1 : ℕ) : ℝ) ^ 2 * 8 ^ k * Bc) * T := by
  have hB0 : 0 ≤ Bc := by
    have := hBc 0 (Nat.zero_le _)
    simpa using this.trans' (by positivity)
  refine (factorProduct_pair_le π hmc hF hG hk θ hw).trans ?_
  have hterm : ∀ l ∈ Finset.range (k + 1),
      ENNReal.ofReal ((k.choose l : ℝ) * (w ^ l * ‖iteratedFDeriv ℝ l mc θ‖)) *
        (ENNReal.ofReal (w ^ (k - l)) * factorFamilyPairNorm π
          (fun x => ‖iteratedFDeriv ℝ (k - l) (F x) θ‖)
          (fun x => ‖iteratedFDeriv ℝ (k - l) (G x) θ‖)) ≤
        ENNReal.ofReal (8 ^ k * Bc) * T := by
    intro l hl
    have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
    have hch : (k.choose l : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (Nat.choose_le_two_pow k l)
    have h1 : ENNReal.ofReal ((k.choose l : ℝ) * (w ^ l * ‖iteratedFDeriv ℝ l mc θ‖)) ≤
        ENNReal.ofReal (2 ^ k * Bc) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul hch (hBc l (hlk.trans hk)) (by positivity) (by positivity))
    have h2 := hT (k - l) (by omega)
    have h3 : ENNReal.ofReal ((4 : ℝ) ^ (k - l)) ≤ ENNReal.ofReal (4 ^ k) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) (Nat.sub_le k l))
    calc _ ≤ ENNReal.ofReal (2 ^ k * Bc) * (ENNReal.ofReal (4 ^ k) * T) :=
          mul_le_mul' h1 (h2.trans (mul_le_mul' h3 le_rfl))
      _ = ENNReal.ofReal (8 ^ k * Bc) * T := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [show (8 : ℝ) ^ k = 2 ^ k * 4 ^ k by rw [← mul_pow]; norm_num]
          ring
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  calc _ ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (8 ^ k * Bc) * T)) := mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) ^ 2 * 8 ^ k * Bc) * T := by
        rw [← ENNReal.ofReal_natCast, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end Leibniz

end AVRegularity.CycleWords.Discard.BandJets
end

section
open MeasureTheory Filter Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard.BandDatum
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Discard.BandJets

/-! # `BandJetStatement`

The amplitude jets of the cutoff `fourierCutoff μ U` against the cell means `outMeanSq`.
Off the band condition the multiplier vanishes near `θ`; on it the jets are bounded by the Leibniz
step (`leibniz_k`) with the moment jets `4^j · m! · outMeanSq^{1/2}`
(`finMom_full_pair_le`, `momentAmp_le`), and `amplitudeJetNorm ≤ (m+1) 2^m · ampDerivNorm`
(`amplitudeJetNorm_le_ampDerivNorm`). -/

universe u v

/-- The multiplier vanishes near `θ` off the band condition. -/
theorem mu_eventually_zero {μ : Vec 2 → ℝ} {ρ₁ : ℝ}
    (hsupp : ∀ θ, μ θ ≠ 0 → ρ₁ ^ 2 ≤ vecDot θ θ ∧ vecDot θ θ ≤ (Real.pi / 2) ^ 2)
    {θ : Vec 2} (hband : ¬ (θ ∈ freqCube ∧ ρ₁ ^ 2 ≤ vecDot θ θ)) :
    μ =ᶠ[𝓝 θ] fun _ => 0 := by
  have hd : Continuous fun θ : Vec 2 => vecDot θ θ := by unfold vecDot; fun_prop
  by_cases hlow : vecDot θ θ < ρ₁ ^ 2
  · filter_upwards [(isOpen_lt hd continuous_const).mem_nhds hlow] with θ' hθ'
    by_contra hne
    exact absurd (hsupp θ' hne).1 (not_le.2 hθ')
  · have hnc : θ ∉ freqCube := fun hc => hband ⟨hc, not_lt.1 hlow⟩
    obtain ⟨i, hi⟩ : ∃ i, ¬ |θ i| ≤ Real.pi := by
      by_contra hcon
      exact hnc fun i => by
        by_contra hi'
        exact hcon ⟨i, hi'⟩
    have hgt : (Real.pi / 2) ^ 2 < vecDot θ θ := by
      have h1 : (θ i) ^ 2 ≤ vecDot θ θ := by
        unfold vecDot
        rw [Fin.sum_univ_two]
        fin_cases i <;> simp <;> nlinarith [sq_nonneg (θ 0), sq_nonneg (θ 1)]
      have h2 : Real.pi ^ 2 < (θ i) ^ 2 := by
        have := not_le.1 hi
        nlinarith [Real.pi_pos, abs_nonneg (θ i), sq_abs (θ i)]
      nlinarith [Real.pi_pos]
    filter_upwards [(isOpen_lt continuous_const hd).mem_nhds hgt] with θ' hθ'
    by_contra hne
    exact absurd (hsupp θ' hne).2 (not_le.2 hθ')

theorem fact_le {m : ℕ} {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ m) :
    ((β.1.factorial * β.2.factorial : ℕ) : ℝ) ≤ (m.factorial : ℝ) := by
  have h1 := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add β.1 β.2)
  exact_mod_cast h1.trans (Nat.factorial_le hβ)

section Main

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The moment jets of the cosine/sine transforms against the cell means. -/
theorem moment_jets (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {ϖ : ℝ} (hϖ : 0 ≤ ϖ) {m : ℕ}
    (U : ∀ x, Vec 2 → h x) (hint : ∀ x, FinMom m (U x)) (θ : Vec 2) {j : ℕ} (hj : j ≤ m) :
    ENNReal.ofReal (ϖ ^ j) * factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ j (fun θ => ∫ y, Real.cos (vecDot θ y) • U x y) θ‖)
      (fun x => ‖iteratedFDeriv ℝ j (fun θ => ∫ y, Real.sin (vecDot θ y) • U x y) θ‖) ≤
    ENNReal.ofReal ((4 : ℝ) ^ j) *
      (ENNReal.ofReal (m.factorial : ℝ) * (outMeanSq π ϖ m θ U) ^ (1 / 2 : ℝ)) := by
  refine (finMom_full_pair_le π (fun x => (hint x).mono hj) θ hϖ).trans ?_
  have hterm : ∀ wd ∈ (Finset.univ : Finset (DerivativeWord2 j)),
      momentAmpNorm π ϖ (idxCount wd) U θ ≤
        ENNReal.ofReal (m.factorial : ℝ) * (outMeanSq π ϖ m θ U) ^ (1 / 2 : ℝ) := by
    intro wd _
    have hsum := idxCount_sum wd
    have hβ : idxCount wd ∈ momentIndices m := by
      simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    refine (momentAmp_le π hπ ϖ hβ θ U hint).trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (fact_le (by omega))) le_rfl
  have hs := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [AVRegularity.ChartTransport.card_derivativeWord2, nsmul_eq_mul] at hs
  calc _ ≤ ENNReal.ofReal ((2 : ℝ) ^ j) * (((2 ^ j : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (m.factorial : ℝ) * (outMeanSq π ϖ m θ U) ^ (1 / 2 : ℝ))) :=
        mul_le_mul' le_rfl hs
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [show ((2 ^ j : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ j) by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]; push_cast; rfl,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← mul_pow]; norm_num

end Main

open scoped Classical in
/-- **The band jet** (`BandJetStatement`). -/
theorem bandJetStatement : BandJetStatement.{u, v} := by
  intro m
  have hcpos : (0 : ℝ) < ((2 * Real.pi)⁻¹) ^ 2 := by positivity
  refine ⟨((m + 1 : ℕ) : ℝ) * 2 ^ m * ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 2 * 8 ^ m) *
    ((2 * Real.pi)⁻¹) ^ 2 * (m.factorial : ℝ), by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ ρ₁ Bμ hϖ hϖ1 hρ hB μ hμ hev hsupp hjet U hmeas hint θ
  by_cases hband : θ ∈ freqCube ∧ ρ₁ ^ 2 ≤ vecDot θ θ
  · simp only [hband, and_self, ↓reduceIte]
    have hμm : ContDiff ℝ m μ := hμ.of_le (by exact_mod_cast le_top)
    have hcd : ContDiff ℝ m (fun z => ((2 * Real.pi)⁻¹ ^ 2) * μ z) := contDiff_const.mul hμm
    have hFd : ∀ x, ContDiff ℝ m (fun θ => ∫ y, Real.cos (vecDot θ y) • U x y) :=
      fun x => finMom_cos_contDiff (hint x)
    have hGd : ∀ x, ContDiff ℝ m (fun θ => ∫ y, Real.sin (vecDot θ y) • U x y) :=
      fun x => finMom_sin_contDiff (hint x)
    have hBc : ∀ l ≤ m, ϖ ^ l * ‖iteratedFDeriv ℝ l (fun z => ((2 * Real.pi)⁻¹ ^ 2) * μ z) θ‖ ≤
        ((2 * Real.pi)⁻¹ ^ 2) * Bμ := by
      intro l hl
      have hca : ContDiffAt ℝ l μ θ := (hμ.of_le (by exact_mod_cast le_top)).contDiffAt
      have he : iteratedFDeriv ℝ l (fun z => ((2 * Real.pi)⁻¹ ^ 2) * μ z) θ =
          ((2 * Real.pi)⁻¹ ^ 2) • iteratedFDeriv ℝ l μ θ := by
        simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := (2 * Real.pi)⁻¹ ^ 2) hca
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
      have hj := hjet l θ hl
      have hϖl : 0 < ϖ ^ l := pow_pos hϖ l
      have : ϖ ^ l * ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ := by
        rwa [le_div_iff₀ hϖl, mul_comm] at hj
      calc ϖ ^ l * (((2 * Real.pi)⁻¹ ^ 2) * ‖iteratedFDeriv ℝ l μ θ‖)
          = ((2 * Real.pi)⁻¹ ^ 2) * (ϖ ^ l * ‖iteratedFDeriv ℝ l μ θ‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hcpos.le
    have hT := fun j (hj : j ≤ m) => moment_jets π hπ hϖ.le U hint θ hj
    have hk : ∀ k ≤ m, ENNReal.ofReal (ϖ ^ k) * factorFamilyPairNorm π
        (fun x => ‖iteratedFDeriv ℝ k (cutoffCosAmplitude μ (U x)) θ‖)
        (fun x => ‖iteratedFDeriv ℝ k (cutoffSinAmplitude μ (U x)) θ‖) ≤
        ENNReal.ofReal ((((m + 1 : ℕ) : ℝ) ^ 2 * 8 ^ m) * (((2 * Real.pi)⁻¹ ^ 2) * Bμ)) *
          (ENNReal.ofReal (m.factorial : ℝ) * (outMeanSq π ϖ m θ U) ^ (1 / 2 : ℝ)) := by
      intro k hk
      refine (leibniz_k π hFd hGd hcd θ hϖ.le hBc hT hk).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have h1 : (((k + 1 : ℕ) : ℝ)) ^ 2 ≤ (((m + 1 : ℕ) : ℝ)) ^ 2 := by
        gcongr
      have h2 : (8 : ℝ) ^ k ≤ 8 ^ m := pow_le_pow_right₀ (by norm_num) hk
      have hB' : 0 ≤ ((2 * Real.pi)⁻¹ ^ 2) * Bμ := by positivity
      exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) le_rfl hB'
        (by positivity)
    refine (amplitudeJetNorm_le_ampDerivNorm π m hϖ.le _ _ θ).trans ?_
    unfold ampDerivNorm
    set X : ℝ≥0∞ := ENNReal.ofReal ((((m + 1 : ℕ) : ℝ) ^ 2 * 8 ^ m) * (((2 * Real.pi)⁻¹ ^ 2) * Bμ)) *
          (ENNReal.ofReal (m.factorial : ℝ) * (outMeanSq π ϖ m θ U) ^ (1 / 2 : ℝ)) with hX
    have hsum : ∑ k ∈ Finset.range (m + 1), ENNReal.ofReal (ϖ ^ k / (k.factorial : ℝ)) *
        (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          (ENNReal.ofReal (‖iteratedFDeriv ℝ k (cutoffCosAmplitude μ (U x)) θ‖ ^ 2) +
            ENNReal.ofReal (‖iteratedFDeriv ℝ k (cutoffSinAmplitude μ (U x)) θ‖ ^ 2))) ^
              (1 / 2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ≥0∞) * X := by
      calc _ ≤ ∑ _k ∈ Finset.range (m + 1), X := Finset.sum_le_sum fun k hkm => by
            have hkm' : k ≤ m := by have := Finset.mem_range.mp hkm; omega
            have hdiv : ENNReal.ofReal (ϖ ^ k / (k.factorial : ℝ)) ≤ ENNReal.ofReal (ϖ ^ k) :=
              ENNReal.ofReal_le_ofReal (div_le_self (pow_nonneg hϖ.le _)
                (Nat.one_le_cast.2 (Nat.factorial_pos k)))
            exact (mul_le_mul' hdiv le_rfl).trans (hk k hkm')
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine (mul_le_mul' le_rfl hsum).trans_eq ?_
    rw [← ENNReal.ofReal_natCast, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  · simp only [hband, ↓reduceIte]
    rw [ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
    refine le_of_eq (amplitudeJetNorm_eq_zero_of_eventually π m ϖ fun x => ?_)
    have hz := mu_eventually_zero hsupp hband
    constructor
    · filter_upwards [hz] with z hz'
      simp [cutoffCosAmplitude, hz']
    · filter_upwards [hz] with z hz'
      simp [cutoffSinAmplitude, hz']

end AVRegularity.CycleWords.Discard.BandJets
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # The adjoint propagator in `H^j` with a kernel

The adjoint curve `Ψ` read backward and conjugated, `t ↦ conj Ψ(-t)`, is a forward curve of the
reversed equation `⟨G(-s), -v(-s), -θ, 0⟩` (`reflect_adjoint_conv`). Its kernel is
`κ'(p, q) = κ(-q, -p)`: the fields `pos`, `self` and `shrink` are inherited, `decay` is the
adjoint decay by duality (`adjoint_decay`). The core (`kernelCore`) does the rest. -/

/-- The reversed real-shift coefficients are the complex reversed coefficients. -/
theorem rev_coeff_eq (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (θ : Vec 2) :
    (⟨fun s _ => G (-s), fun s x => -v (-s) x, fun k => (((-θ k : ℝ)) : ℂ), 0⟩ :
        CellCoefficients) =
      ⟨fun s x => (fun t (_ : Vec 2) => G t) (-s) x, fun s x => -v (-s) x,
        fun j => -((fun k => (θ k : ℂ)) j), 0⟩ := by
  simp

/-- The adjoint propagator in `H^j` with a kernel. -/
theorem cellAdjointKernelHs : CellAdjointKernelHsStatement := by
  intro j ρ A hρ hA
  obtain ⟨C, Q, hC, h⟩ := kernelCore j ρ A hρ hA
  refine ⟨C, Q, hC, ?_⟩
  intro a b L G hG v hv V hb θ hab hL hθ hsm hjet κ hK Ψv Ψs hΨ
  have hGr : IsCellMetric (fun t (_ : Vec 2) => G (-t)) := cellMetric_timeReverse hG
  have hvr : IsCellDrift (fun s x => -v (-s) x) := cellDrift_timeReverse hv
  have hbr : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := fun s x => by
    simpa only [Pi.neg_apply, neg_sq] using hb (-s) x
  have hθr : Real.sqrt (vecDot (fun k => -θ k) (fun k => -θ k)) ≤ ρ := by
    have : vecDot (fun k => -θ k) (fun k => -θ k) = vecDot θ θ := by simp [vecDot]
    rwa [this]
  have hsmr : ∀ t ∈ Set.Icc (-b) (-a), ContDiff ℝ (⊤ : ℕ∞) ((fun s x => -v (-s) x) t) :=
    fun t ht => (hsm (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).neg
  have hjetr : ∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc (-b) (-a) → ∀ x,
      ‖iteratedFDeriv ℝ l ((fun s x => -v (-s) x) t) x‖ ≤ L := by
    intro l t hl ht x
    have he : (fun x => -v (-t) x) = -(v (-t)) := rfl
    show ‖iteratedFDeriv ℝ l (fun x => -v (-t) x) x‖ ≤ L
    rw [he, iteratedFDeriv_neg_apply, norm_neg]
    exact hjet l (-t) hl ⟨by linarith [ht.2], by linarith [ht.1]⟩ x
  -- the reversed curve
  have hcurve := reflect_adjoint_conv (fun s _ => G s) hG hv V hb (fun k => (θ k : ℂ)) hΨ
  have hcurve' : CellWeakHilbertCurve (-b) (-a)
      (fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (Ψv (-t)))
      (fun t => cellH1Conj (Ψs (-t)))
      (fun t => cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun k => (((-θ k : ℝ)) : ℂ), 0⟩ hGr V hvr.1 hbr t (cellH1Conj (Ψs (-t))) 0 0) :=
    curve_congr_coeff (rev_coeff_eq G v θ).symm _ _ V _ _ _ _ hcurve
  have hmain := h (-b) (-a) L (fun s => G (-s)) hGr hvr V hbr (fun k => -θ k) (by linarith) hL
    hθr hsmr hjetr (fun p q => κ (-q) (-p)) (fun r s => (hK.pos _ _).le)
    (fun r => by simpa using hK.self (-r))
    (fun p s t hp hps hst hts htb => by
      have := hK.shrink (-t) (-s) (-p) (-p) (by linarith) (by linarith) (by linarith)
        (by linarith) le_rfl (by linarith) (by linarith)
      exact this)
    (fun p q hp hpq hq u1 slice1 hu1 => by
      have hc1 : CellWeakHilbertCurve p q u1 slice1 (fun t => cellDualDerivative
          ⟨fun s x => (fun t (_ : Vec 2) => G t) (-s) x, fun s x => -v (-s) x,
            fun j => -((fun k => (θ k : ℂ)) j), 0⟩ (cellMetric_timeReverse hG) V
          (cellDrift_timeReverse hv).1 hbr t (slice1 t) 0 0) :=
        curve_congr_coeff (rev_coeff_eq G v θ) _ _ V _ _ _ _ hu1
      have hc2 : CellWeakHilbertCurve (-(-p)) (-(-q)) u1 slice1 (fun t => cellDualDerivative
          ⟨fun s x => (fun t (_ : Vec 2) => G t) (-s) x, fun s x => -v (-s) x,
            fun j => -((fun k => (θ k : ℂ)) j), 0⟩ (cellMetric_timeReverse hG) V
          (cellDrift_timeReverse hv).1 hbr t (slice1 t) 0 0) := by
        rw [neg_neg, neg_neg]
        exact hc1
      have hadj := CellWeakHilbertCurve.reflected_adjoint (a := -q) (b := -p) (fun s _ => G s) hG
        hv V hb (fun k => (θ k : ℂ)) hc2
      have hd := adjoint_decay (r := -q) (s := -p) (by linarith)
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv hb rfl (κ (-q) (-p)) (hK.pos _ _).le
        (fun u sl hu => hK.decay (-q) (-p) (by linarith) (by linarith) (by linarith) u sl hu) hadj
      simp only [neg_neg, cellFiberConj_norm] at hd
      exact hd)
    _ _ hcurve'
  constructor
  · intro w₀ hw₀ r hr
    obtain ⟨w, hw, hn⟩ := hmain.1 (torusHkConj w₀)
      (by
        rw [torusHkConj_value, hw₀]
        show _ = cellFiberCLM _ (Ψv (-(-b)))
        rw [neg_neg])
      (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    refine ⟨torusHkConj w, ?_, ?_⟩
    · rw [torusHkConj_value, hw]
      show _ = Ψv r
      simp only [neg_neg, cellFiberConj_involutive]
    · rw [torusHkConj_norm]
      simp only [neg_neg, torusHkConj_norm] at hn
      exact hn
  · intro τ hτ0 hτ1 r hr hrτ
    obtain ⟨w, hw, hn⟩ := hmain.2 τ hτ0 hτ1 (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
      (by linarith)
    refine ⟨torusHkConj w, ?_, ?_⟩
    · rw [torusHkConj_value, hw]
      show _ = Ψv r
      simp only [neg_neg, cellFiberConj_involutive]
    · rw [torusHkConj_norm]
      simp only [neg_neg, cellFiberConj_norm] at hn
      exact hn

/-! # the dual core

Forward existence of homogeneous curves from `L²` data, and the bound of an adjoint curve against
`H^j` tests: if the terminal value `g` satisfies `⟨z, g⟩ ≤ N ‖z‖_{H^j}`, then so does every
`Ψ(r)`, with the constant `C (1+L)^Q` of K1 (kernel `1`, K3). -/

/-- A homogeneous Hilbert curve exists from every `L²` datum. -/
theorem forward_exists {r t : ℝ} (hrt : r ≤ t)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (init : ComplexCellL2) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve r t u slice (fun s => cellDualDerivative
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb s (slice s) 0 0) ∧
      u r = init := by
  obtain ⟨u, slice, hu, hu0⟩ := cellActual_exists_Hilbert hrt
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V 0 hv.1 hb measurable_const
    (fun _ => by simp) (fun _ _ => 0) (fun _ _ => 0) measurable_const measurable_const
    (by simp [cellL2Norm]) (by simp [cellL2Norm]) init
  refine ⟨u, slice, ?_, hu0⟩
  simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
    show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hu

/-- **The adjoint curve against `H^j` tests.** -/
theorem adjoint_dual_bound (j : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (a t L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
      {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
      (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
      a ≤ t → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
      (∀ s ∈ Set.Icc a t, ContDiff ℝ (⊤ : ℕ∞) (v s)) →
      (∀ (l : ℕ) s, l ≤ j + 1 → s ∈ Set.Icc a t → ∀ x, ‖iteratedFDeriv ℝ l (v s) x‖ ≤ L) →
    ∀ (g : ComplexCellL2) (N : ℝ), 0 ≤ N →
      (∀ z : TorusHk j ℂ, inner ℝ (torusHkValueCLM z) g ≤ N * ‖z‖) →
    ∀ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a t Ψv Ψs (fun r =>
        -cellDualDerivative (cellAdjointCoefficients ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩)
          hG V (cellDrift_neg hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) →
      Ψv t = g → ∀ r ∈ Set.Icc a t, ∀ w : TorusHk j ℂ,
        inner ℝ (torusHkValueCLM w) (Ψv r) ≤ C * (1 + L) ^ Q * N * ‖w‖ := by
  obtain ⟨C, Q, hC, hK⟩ := cellKernelHs j ρ 1 hρ le_rfl
  refine ⟨C, Q, hC, ?_⟩
  intro a t L G hG v hv V hb θ hat hL hθ hsm hjet g N hN hg Ψv Ψs hΨ hΨt r hr w
  obtain ⟨U, slice, hU, hU0⟩ := forward_exists hr.2 G hG hv V hb θ (torusHkValueCLM w)
  have hsub : Icc r t ⊆ Icc a t := Icc_subset_Icc hr.1 le_rfl
  have hk := hK r t L G hG hv V hb θ hr.2 hL hθ (fun s hs => hsm s (hsub hs))
    (fun l s hl hs x => hjet l s hl (hsub hs) x) (fun _ _ => 1)
    (plainKernel r t G hG hv V hb θ) U slice hU
  obtain ⟨z, hz, hzn⟩ := hk.1 w hU0.symm t ⟨hr.2, le_rfl⟩
  have hpair := cellWeakAdjointPairing_forced hr.2
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv hb
    (S := fun _ => 0) (F := fun _ _ => 0) hU (hΨ.mono hsub)
  have hint : ∫ s in r..t, cellComplexSource (fun k => (θ k : ℂ)) 0 (fun _ => 0) (Ψs s) = 0 := by
    simp [cellComplexSource_zero]
  rw [hint, sub_eq_zero] at hpair
  have hre := congrArg Complex.re hpair
  rw [cellComplexPair_re, cellComplexPair_re, hU0, hΨt, ← hz] at hre
  rw [← hre]
  calc inner ℝ (torusHkValueCLM z) g ≤ N * ‖z‖ := hg z
    _ ≤ N * (C * (1 + L) ^ Q * 1 * ‖w‖) := mul_le_mul_of_nonneg_left hzn hN
    _ = C * (1 + L) ^ Q * N * ‖w‖ := by ring

end AVRegularity.CycleWords.Discard
end

section
namespace AVRegularity.CycleWords.Discard

/-! # the Bloch output

`blochOutput : BlochOutputStatement`, from the reduction `blochOutput_of_open_parts` and its
three scalar lemmas: the transform of the jet of `u - μ(D)u` (`jetFourier`), Plancherel with
moments (`momentPlancherel`) and the Fourier calculus (`ftCalculus`).
-/

universe u v

/-- **The Bloch output**. -/
theorem blochOutput : BlochOutputStatement.{u, v} :=
  blochOutput_of_open_parts jetFourier momentPlancherel ftCalculus

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # The forced-curve bound: a forced fibre curve in `H^j`

Duality (`cellWeakAdjointPairing_forced`) against an adjoint curve `Ψ` from a terminal test `g`
turns the forced identity into `⟨u(t), g⟩ = ⟨u(a), Ψ(a)⟩ + ∫ ⟨σ, Ψ⟩`; every pairing is bounded by
`C (1+L)^Q N` times the `H^j` norm (`adjoint_dual_bound`), and the dual criterion
(`mem_of_dual_bound`) produces the `H^j` element. -/

/-- The forced-curve bound. -/
theorem cellForcedHs : CellForcedHsStatement := by
  intro j ρ hρ
  obtain ⟨C, Q, hC, hD⟩ := adjoint_dual_bound j ρ hρ
  refine ⟨C, Q, hC, ?_⟩
  intro a b L G hG v hv V hb θ hab hb1 hL hθ hsm hjet u slice S F hu σ f hf hσ w₀ hw₀ t ht
  have hat : a ≤ t := ht.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  set P : ℝ := 1 + L with hP
  have hP0 : 0 ≤ P := by linarith
  have hCP : 0 ≤ C * P ^ Q := by positivity
  have hfnn : 0 ≤ ∫ r in a..t, f r := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hat ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hσ] with r hr
    exact (norm_nonneg _).trans hr.1
  have hfi : IntervalIntegrable f volume a t :=
    (hf.mono_set (by rw [uIcc_of_le hat]; exact hsub)).intervalIntegrable
  refine mem_of_dual_bound (torusHkValueCLM (E := ℂ) (K := j)) (u t)
    (C * P ^ Q * (‖w₀‖ + ∫ r in a..t, f r)) (by positivity) ?_
  intro g N hN hg
  obtain ⟨Ψv, Ψs, hΨ, hΨt⟩ := adjointCurve_exists hat (fun s _ => G s) hG hv V hb
    (fun k => (θ k : ℂ)) g
  have hbd := hD a t L G hG hv V hb θ hat hL hθ (fun s hs => hsm s (hsub hs))
    (fun l s hl hs x => hjet l s hl (hsub hs) x) g N hN hg Ψv Ψs hΨ hΨt
  have hpair := cellWeakAdjointPairing_forced hat
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv hb (hu.mono hsub) hΨ
  have hint := cellWeakAdjoint_forced_source_intervalIntegrable hat
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv hb (hu.mono hsub) hΨ
  have hre := congrArg Complex.re hpair
  rw [Complex.sub_re, cellComplexPair_re, cellComplexPair_re, hΨt] at hre
  have hintre : (∫ s in a..t, cellComplexSource (fun k => (θ k : ℂ)) (S s) (F s) (Ψs s)).re =
      ∫ s in a..t, (cellComplexSource (fun k => (θ k : ℂ)) (S s) (F s) (Ψs s)).re := by
    rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat]
    exact (integral_re hint.1).symm
  rw [hintre] at hre
  have hfirst : inner ℝ (u a) (Ψv a) ≤ C * P ^ Q * N * ‖w₀‖ := by
    rw [← hw₀]
    exact hbd a ⟨le_rfl, hat⟩ w₀
  have hae : ∀ᵐ r ∂volume.restrict (Ioc a t),
      (cellComplexSource (fun k => (θ k : ℂ)) (S r) (F r) (Ψs r)).re ≤ C * P ^ Q * N * f r := by
    have h1 : ∀ᵐ r ∂volume.restrict (Ioc a t), r ∈ Icc a t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using ⟨hr.1.le, hr.2⟩
    have h2 := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Icc_self.trans hsub) hσ
    have h3 := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self) hΨ.agrees
    filter_upwards [h1, h2, h3] with r hr hr2 hr3
    rw [hr2.2 (Ψs r), cellComplexPair_re, ← hr3]
    calc inner ℝ (torusHkValueCLM (σ r)) (Ψv r) ≤ C * P ^ Q * N * ‖σ r‖ := hbd r hr (σ r)
      _ ≤ C * P ^ Q * N * f r := mul_le_mul_of_nonneg_left hr2.1 (by positivity)
  have hmono : (∫ s in a..t, (cellComplexSource (fun k => (θ k : ℂ)) (S s) (F s) (Ψs s)).re) ≤
      ∫ s in a..t, C * P ^ Q * N * f s := by
    rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat]
    refine integral_mono_ae ?_ ?_ hae
    · exact (Complex.reCLM.integrable_comp hint.1)
    · exact (hfi.1.const_mul _)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hfin : inner ℝ (u t) g ≤ C * P ^ Q * N * ‖w₀‖ + C * P ^ Q * N * ∫ s in a..t, f s := by
    linarith
  calc inner ℝ (u t) g ≤ _ := hfin
    _ = C * P ^ Q * (‖w₀‖ + ∫ r in a..t, f r) * N := by ring

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Discard

/-! # one stage on a terminal window

A forced fibre curve on a window `[t₀, b]` of length at most one, whose value at
`t₀` is bounded against `H^s` tests by `M` (negative order) and whose forcing is represented by
`H^j` elements of size `f(t)`, is in `H^j` after a time `τ`, with norm at most
`C (1+L)^Q (τ^{-(j+s)/2} M + ∫ f)`.

Split `u = u_h + u_f`: `u_h` is the homogeneous curve from `u(t₀)` (`forward_exists`), smoothed
by the negative-smoothing bound (`CellNegativeSmoothingStatement`); `u_f = u − u_h` is forced with
zero datum and bounded by the forced-curve bound (`CellForcedHsStatement`). The family form is
`window_family_hs`. -/

/-- The dual derivative minus a homogeneous one is the dual derivative of the difference. -/
theorem cellDualDerivative_sub_homogeneous (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u w : TorusHk 1 ℂ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative C hG V hv hb t u S F - cellDualDerivative C hG V hv hb t w 0 0 =
      cellDualDerivative C hG V hv hb t (u - w) S F := by
  have h := cellDualDerivative_sub_same_source C hG V hv hb t u (u - w) S F
  rw [sub_sub_cancel] at h
  have h0 : (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 := rfl
  rw [h0] at h
  rw [← h]
  abel

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # The forced-curve bound for families (`CellForcedHsFamilyStatement`)

Test against a family `g_i` with per-curve dual norms `N_i`; adjoint curves `Ψ_i` from each `g_i`;
Cauchy–Schwarz over the family inside the time integral; the family dual criterion
(`mem_of_family_dual_bound`). The constants are sums over the orders `j ≤ jmax` of the
per-order constants of `adjoint_dual_bound`, so they do not depend on the family. -/

/-- Uniform constants for orders `j ≤ jmax`. -/
theorem uniform_const (jmax : ℕ) (Cf : ℕ → ℝ) (Qf : ℕ → ℕ) (hC : ∀ j, 0 < Cf j) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧ ∀ (P : ℝ), 1 ≤ P → ∀ j ≤ jmax, Cf j * P ^ Qf j ≤ C * P ^ Q := by
  refine ⟨∑ j ∈ Finset.range (jmax + 1), Cf j, ∑ j ∈ Finset.range (jmax + 1), Qf j,
    Finset.sum_pos (fun j _ => hC j) ⟨0, by simp⟩, ?_⟩
  intro P hP j hj
  have hjm : j ∈ Finset.range (jmax + 1) := Finset.mem_range.2 (by omega)
  have h1 : Cf j ≤ ∑ j ∈ Finset.range (jmax + 1), Cf j :=
    Finset.single_le_sum (f := Cf) (fun j _ => (hC j).le) hjm
  have h2 : Qf j ≤ ∑ j ∈ Finset.range (jmax + 1), Qf j :=
    Finset.single_le_sum (f := Qf) (fun j _ => Nat.zero_le _) hjm
  exact mul_le_mul h1 (pow_le_pow_right₀ hP h2) (by positivity)
    (Finset.sum_nonneg fun j _ => (hC j).le)

/-- The forced-curve bound for families. -/
theorem cellForcedHsFamily : CellForcedHsFamilyStatement := by
  intro jmax ρ hρ
  choose Cf Qf hCf hD using fun j : ℕ => adjoint_dual_bound j ρ hρ
  obtain ⟨C, Q, hC, hCQ⟩ := uniform_const jmax Cf Qf hCf
  refine ⟨C, Q, hC, ?_⟩
  intro a b L G hG v hv V hb θ hab hb1 hL hθ hsm hjet I _ j hj u slice S F hu σ f hf hσ w₀ hw₀ t ht
  have hat : a ≤ t := ht.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  set P : ℝ := 1 + L with hP
  have hP1 : 1 ≤ P := by linarith
  have hKnn : 0 ≤ C * P ^ Q := by positivity
  have hfnn : 0 ≤ ∫ r in a..t, f r := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hat ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hσ] with r hr
    exact (Real.sqrt_nonneg _).trans hr.1
  have hfi : IntervalIntegrable f volume a t :=
    (hf.mono_set (by rw [uIcc_of_le hat]; exact hsub)).intervalIntegrable
  have h2 := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans hsub) hσ
  refine mem_of_family_dual_bound (fun i => torusHkValueCLM (E := ℂ) (K := j i)) (fun i => u i t)
    (C * P ^ Q * (Real.sqrt (∑ i, ‖w₀ i‖ ^ 2) + ∫ r in a..t, f r))
    (by positivity) ?_
  intro g N hN hg
  have hcurve : ∀ i, ∃ (Ψv : ℝ → ComplexCellL2) (φ : ℝ → ℝ), IntervalIntegrable φ volume a t ∧
      inner ℝ (u i t) (g i) = inner ℝ (u i a) (Ψv a) + ∫ r in a..t, φ r ∧
      (∀ᵐ r ∂volume.restrict (Ioc a t),
        φ r = inner ℝ (torusHkValueCLM (σ i r)) (Ψv r)) ∧
      (∀ r ∈ Icc a t, ∀ w : TorusHk (j i) ℂ,
        inner ℝ (torusHkValueCLM w) (Ψv r) ≤ C * P ^ Q * N i * ‖w‖) := by
    intro i
    obtain ⟨Ψv, Ψs, hΨ, hΨt⟩ := adjointCurve_exists hat (fun s _ => G s) hG hv V hb
      (fun k => (θ k : ℂ)) (g i)
    have hbd := hD (j i) a t L G hG hv V hb θ hat hL hθ (fun s hs => hsm s (hsub hs))
      (fun l s hl hs x => hjet l s (by have := hj i; omega) (hsub hs) x) (g i) (N i) (hN i)
      (hg i) Ψv Ψs hΨ hΨt
    have hpair := cellWeakAdjointPairing_forced hat
      ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv hb (hu i |>.mono hsub) hΨ
    have hint := cellWeakAdjoint_forced_source_intervalIntegrable hat
      ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv hb (hu i |>.mono hsub) hΨ
    have hre := congrArg Complex.re hpair
    rw [Complex.sub_re, cellComplexPair_re, cellComplexPair_re, hΨt] at hre
    have hintre : (∫ s in a..t, cellComplexSource (fun k => (θ k : ℂ)) (S i s) (F i s)
        (Ψs s)).re = ∫ s in a..t, (cellComplexSource (fun k => (θ k : ℂ)) (S i s) (F i s)
        (Ψs s)).re := by
      rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat]
      exact (integral_re hint.1).symm
    rw [hintre] at hre
    have hCP : Cf (j i) * P ^ Qf (j i) ≤ C * P ^ Q := hCQ P hP1 (j i) (hj i)
    refine ⟨Ψv, fun s => (cellComplexSource (fun k => (θ k : ℂ)) (S i s) (F i s) (Ψs s)).re,
      ?_, ?_, ?_, ?_⟩
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat]
      exact Complex.reCLM.integrable_comp hint.1
    · linarith
    · have h1 := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self) hΨ.agrees
      filter_upwards [h2, h1] with r hr2 hr3
      show (cellComplexSource _ _ _ _).re = _
      rw [(hr2.2 i (Ψs r)), cellComplexPair_re, ← hr3]
    · intro r hr w
      refine (hbd r hr w).trans ?_
      have := hN i
      have : 0 ≤ N i * ‖w‖ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hCP this]
  choose Ψv φ hφi hid hae hbd using hcurve
  -- the three estimates
  have hfirst : ∑ i, inner ℝ (u i a) (Ψv i a) ≤
      C * P ^ Q * Real.sqrt (∑ i, N i ^ 2) * Real.sqrt (∑ i, ‖w₀ i‖ ^ 2) := by
    calc ∑ i, inner ℝ (u i a) (Ψv i a) ≤ ∑ i, C * P ^ Q * (N i * ‖w₀ i‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← hw₀ i]
          have := hbd i a ⟨le_rfl, hat⟩ (w₀ i)
          linarith
      _ = C * P ^ Q * ∑ i, N i * ‖w₀ i‖ := by rw [Finset.mul_sum]
      _ ≤ C * P ^ Q * (Real.sqrt (∑ i, N i ^ 2) * Real.sqrt (∑ i, ‖w₀ i‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hKnn
      _ = _ := by ring
  have hsum_ae : ∀ᵐ r ∂volume.restrict (Ioc a t),
      ∑ i, φ i r ≤ C * P ^ Q * Real.sqrt (∑ i, N i ^ 2) * f r := by
    have h3 : ∀ᵐ r ∂volume.restrict (Ioc a t), ∀ i, φ i r =
        inner ℝ (torusHkValueCLM (σ i r)) (Ψv i r) := ae_all_iff.2 hae
    have h1 : ∀ᵐ r ∂volume.restrict (Ioc a t), r ∈ Icc a t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using ⟨hr.1.le, hr.2⟩
    filter_upwards [h1, h2, h3] with r hr hr2 hr3
    calc ∑ i, φ i r ≤ ∑ i, C * P ^ Q * (N i * ‖σ i r‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hr3 i]
          have := hbd i r hr (σ i r)
          linarith
      _ = C * P ^ Q * ∑ i, N i * ‖σ i r‖ := by rw [Finset.mul_sum]
      _ ≤ C * P ^ Q * (Real.sqrt (∑ i, N i ^ 2) * Real.sqrt (∑ i, ‖σ i r‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hKnn
      _ ≤ C * P ^ Q * (Real.sqrt (∑ i, N i ^ 2) * f r) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2.1
            (Real.sqrt_nonneg _)) hKnn
      _ = _ := by ring
  have hmono : (∫ s in a..t, ∑ i, φ i s) ≤
      ∫ s in a..t, C * P ^ Q * Real.sqrt (∑ i, N i ^ 2) * f s := by
    rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat]
    refine integral_mono_ae ?_ ?_ hsum_ae
    · exact integrable_finsetSum _ fun i _ => (hφi i).1
    · exact hfi.1.const_mul _
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun i _ => hφi i)] at hmono
  have hsumid : ∑ i, inner ℝ (u i t) (g i) = ∑ i, inner ℝ (u i a) (Ψv i a) +
      ∑ i, ∫ r in a..t, φ i r := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hid i
  rw [hsumid]
  linarith

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Discard

/-! # a family of stages on a terminal window

`window_family_hs`: a finite family of forced fibre curves on a window `[t₀, b]` of length at most
one, bounded in `ℓ²` against families of `H^s` tests by `M` at `t₀`, whose forcings have an `ℓ²`
majorant `f(t)` in `H^{j_i}`, is in `H^{j_i}` after a time `τ`, with
`(∑‖w_i‖²)^{1/2} ≤ C(1+L)^Q (τ^{-(j_max+s)/2} M + ∫ f)`. Split each curve into the homogeneous
curve from `u_i(t₀)` (`forward_exists`) and the forced remainder with zero datum; the negative-smoothing and forced-curve bounds
for families; the triangle inequality in `ℓ²`. -/

universe w

/-- The triangle inequality for the `ℓ²` norm of a finite family. -/
theorem sqrt_sum_sq_norm_add_le {J : Type*} [Fintype J] {E : J → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] (x y : ∀ i, E i) :
    Real.sqrt (∑ i, ‖x i + y i‖ ^ 2) ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) + Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
  let X : PiLp 2 (fun _ : J => ℝ) := (WithLp.equiv 2 (J → ℝ)).symm fun i => ‖x i‖
  let Y : PiLp 2 (fun _ : J => ℝ) := (WithLp.equiv 2 (J → ℝ)).symm fun i => ‖y i‖
  have hX : ‖X‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
    rw [PiLp.norm_eq_of_L2]
    simp [X]
  have hY : ‖Y‖ = Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
    rw [PiLp.norm_eq_of_L2]
    simp [Y]
  have hXY : ‖X + Y‖ = Real.sqrt (∑ i, (‖x i‖ + ‖y i‖) ^ 2) := by
    rw [PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [X, Y, abs_of_nonneg (add_nonneg (norm_nonneg (x i)) (norm_nonneg (y i)))]
  calc Real.sqrt (∑ i, ‖x i + y i‖ ^ 2) ≤ Real.sqrt (∑ i, (‖x i‖ + ‖y i‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
    _ = ‖X + Y‖ := hXY.symm
    _ ≤ ‖X‖ + ‖Y‖ := norm_add_le _ _
    _ = _ := by rw [hX, hY]

/-- **A family of stages on a terminal window.** -/
theorem window_family_hs (hP4bF : CellForcedHsFamilyStatement.{w})
    (hP4cF : CellNegativeSmoothingFamilyStatement.{w}) (jmax s : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (t₀ b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
      {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
      (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
      t₀ ≤ b → b ≤ t₀ + 1 → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
      (∀ t ∈ Set.Icc t₀ b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t, l ≤ jmax + s + 1 → t ∈ Set.Icc t₀ b → ∀ x,
        ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
    ∀ {J : Type w} [Fintype J] (j : J → ℕ), (∀ i, j i ≤ jmax) →
    ∀ (u : J → ℝ → ComplexCellL2) (slice : J → ℝ → TorusHk 1 ℂ) (S : J → ℝ → ComplexCellL2)
      (F : J → ℝ → Fin 2 → ComplexCellL2),
      (∀ i, CellWeakHilbertCurve t₀ b (u i) (slice i) (fun t =>
        cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
          (slice i t) (S i t) (F i t))) →
    ∀ M : ℝ, 0 ≤ M →
      (∀ ψ : J → TorusHk s ℂ, ‖∑ i, cellComplexPair (u i t₀) (torusHkValueCLM (ψ i))‖ ≤
        M * Real.sqrt (∑ i, ‖ψ i‖ ^ 2)) →
    ∀ (σ : ∀ i, ℝ → TorusHk (j i) ℂ) (f : ℝ → ℝ), IntegrableOn f (Set.Icc t₀ b) →
      (∀ᵐ t ∂volume.restrict (Set.Icc t₀ b), Real.sqrt (∑ i, ‖σ i t‖ ^ 2) ≤ f t ∧
        ∀ i (z : TorusHk 1 ℂ), cellComplexSource (fun k => (θ k : ℂ)) (S i t) (F i t) z =
          cellComplexPair (torusHkValueCLM (σ i t)) (torusHkValueCLM z)) →
    ∀ τ : ℝ, 0 < τ → ∀ t ∈ Set.Icc t₀ b, t₀ + τ ≤ t →
      ∃ X : ∀ i, TorusHk (j i) ℂ, (∀ i, torusHkValueCLM (X i) = u i t) ∧
        Real.sqrt (∑ i, ‖X i‖ ^ 2) ≤
          C * (1 + L) ^ Q * (τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M + ∫ r in t₀..t, f r) := by
  obtain ⟨Cb, Qb, hCb, hB⟩ := hP4bF jmax ρ hρ
  obtain ⟨Cc, Qc, hCc, hCn⟩ := hP4cF jmax s ρ hρ
  refine ⟨Cc + Cb, Qc + Qb, by positivity, ?_⟩
  intro t₀ b L G hG v hv V hb θ ht₀b hb1 hL hθ hsm hjet J _ j hj u slice S F hu M hM hneg σ f hf
    hσ τ hτ t ht htτ
  -- the homogeneous parts from `u_i(t₀)`
  choose uh sh huh huh0 using fun i => forward_exists ht₀b G hG hv V hb θ (u i t₀)
  -- the forced parts, with zero data
  have huf : ∀ i, CellWeakHilbertCurve t₀ b (fun t => u i t - uh i t)
      (fun t => slice i t - sh i t)
      (fun t => cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice i t - sh i t) (S i t) (F i t)) := fun i =>
    CellWeakHilbertCurve.dual_congr ((hu i).sub (huh i)) (Filter.Eventually.of_forall fun r =>
      cellDualDerivative_sub_homogeneous _ hG V hv.1 hb r _ _ _ _)
  obtain ⟨wh, hwh, hwhn⟩ := hCn t₀ b L G hG hv V hb θ ht₀b hb1 hL hθ hsm
    (fun l r hl hr x => hjet l r hl hr x) j hj uh sh huh M hM
    (fun ψ => by simp only [huh0]; exact hneg ψ) τ hτ t ht htτ
  obtain ⟨wf, hwf, hwfn⟩ := hB t₀ b L G hG hv V hb θ ht₀b hb1 hL hθ hsm
    (fun l r hl hr x => hjet l r (by omega) hr x) j hj (fun i t => u i t - uh i t)
    (fun i t => slice i t - sh i t) S F huf σ f hf hσ (fun _ => 0)
    (fun i => by rw [map_zero, huh0, sub_self]) t ht
  refine ⟨fun i => wh i + wf i, fun i => by rw [map_add, hwh, hwf]; abel, ?_⟩
  have hL1 : 1 ≤ 1 + L := by linarith
  have hf0 : 0 ≤ ∫ r in t₀..t, f r := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict ht.1 ?_
    have hsub : Set.Icc t₀ t ⊆ Set.Icc t₀ b := Set.Icc_subset_Icc le_rfl ht.2
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hσ] with r hr
    exact (Real.sqrt_nonneg _).trans hr.1
  have hτM : 0 ≤ τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M :=
    mul_nonneg (Real.rpow_nonneg hτ.le _) hM
  have hc : (1 + L) ^ Qc ≤ (1 + L) ^ (Qc + Qb) := pow_le_pow_right₀ hL1 (by omega)
  have hb' : (1 + L) ^ Qb ≤ (1 + L) ^ (Qc + Qb) := pow_le_pow_right₀ hL1 (by omega)
  have hP0 : 0 ≤ (1 + L) ^ (Qc + Qb) := by positivity
  have h0 : Real.sqrt (∑ i : J, ‖(0 : TorusHk (j i) ℂ)‖ ^ 2) = 0 := by simp
  rw [h0, zero_add] at hwfn
  calc Real.sqrt (∑ i, ‖wh i + wf i‖ ^ 2)
      ≤ Real.sqrt (∑ i, ‖wh i‖ ^ 2) + Real.sqrt (∑ i, ‖wf i‖ ^ 2) :=
        sqrt_sum_sq_norm_add_le wh wf
    _ ≤ Cc * (1 + L) ^ Qc * τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M +
          Cb * (1 + L) ^ Qb * ∫ r in t₀..t, f r := add_le_add hwhn hwfn
    _ ≤ Cc * (1 + L) ^ (Qc + Qb) * (τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M) +
          Cb * (1 + L) ^ (Qc + Qb) * ∫ r in t₀..t, f r := by
        rw [mul_assoc (Cc * (1 + L) ^ Qc)]
        exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hCc.le) hτM)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb' hCb.le) hf0)
    _ ≤ (Cc + Cb) * (1 + L) ^ (Qc + Qb) *
          (τ ^ (-((jmax + s : ℕ) : ℝ) / 2) * M + ∫ r in t₀..t, f r) := by
        nlinarith [mul_nonneg (mul_nonneg hCc.le hP0) hf0,
          mul_nonneg (mul_nonneg hCb.le hP0) hτM]

end AVRegularity.CycleWords.Discard
end
