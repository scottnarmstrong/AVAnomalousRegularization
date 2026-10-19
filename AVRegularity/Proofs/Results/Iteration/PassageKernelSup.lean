-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Results.Iteration.PassageKernelSup.Periodic
public import AVRegularity.Definitions.Iteration.CascadeStatement
public import AVRegularity.Statements.Intermediate.Readout.MultiIndicesBetween
public import AVRegularity.Statements.Intermediate.Readout.PartialDerivative
public import AVRegularity.Statements.Intermediate.Readout.SupNorm
public import AVRegularity.Analysis.Convolution.Kernel.MultiplierUniformOrder
import Mathlib.Algebra.Order.Star.Real

/-! Proof of `passage_kernel_sup`, with an invertible spanning matrix.

The paired average is one kernel average on `E = ℝ² × ℝ²`:
`S V(y) = ∫ K(ζ) V(y - Mζ)`, `K = 𝗄 ⊗ 𝗄`, `M ζ = r(H₁ζ₁ + H₂ζ₂)`. Since the spanning matrix
`P = [H₁e₁, H₂e₂]` is invertible, `R = r⁻¹ ι P⁻¹` (`ι s = (s₁e₁, s₂e₂)`) is a right inverse of `M`
with `‖Re_i‖ ≤ Γ/r`. Of the `m'` coordinate derivatives of `S V`, the first `l'` fall on `V`
(field side), the remaining `m' - l'` on the kernel along `Re_i` (kernel side), each costing
`Γ/r`; the kernel factor is `∫‖D^{m'-l'}K‖`, which depends on the template and `n_k` only. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Analysis.Convolution
open scoped ENNReal

namespace AVRegularity.Providers

open KernelSup

/-- The template has compact support. -/
theorem hasCompactSupport_of_unitBall {φ₀ : Vec 2 → ℝ}
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) : HasCompactSupport φ₀ := by
  have hc : IsCompact closedEuclideanUnitBall := by
    let L := (Homogenization.HilbertVec.continuousLinearEquivVec 2).symm
    have heq : closedEuclideanUnitBall = L ⁻¹' Metric.closedBall 0 1 := by
      ext z
      simp only [closedEuclideanUnitBall, Set.mem_ofPred_eq, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right, euclideanNorm]
      rfl
    rw [heq]
    exact L.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall 0 1)
  have hcl : IsClosed closedEuclideanUnitBall :=
    isClosed_le euclideanNorm_continuous continuous_const
  exact HasCompactSupport.intro' hc hcl (fun x hx => Function.notMem_support.1 fun h => hx (hφsupp h))

/-- The tensor kernel `K(ζ) = 𝗄(ζ₁)𝗄(ζ₂)`. -/
def tensorKer (k : Vec 2 → ℝ) : Vec 2 × Vec 2 → ℝ := fun ζ => k ζ.1 * k ζ.2

theorem isKer_tensorKer {k : Vec 2 → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) k) (hc : HasCompactSupport k) :
    IsKer (tensorKer k) := by
  refine ⟨(hs.comp contDiff_fst).mul (hs.comp contDiff_snd), ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.prod hc.isCompact) (fun ζ hζ => ?_)
  simp only [Set.mem_prod, not_and_or] at hζ
  rcases hζ with h | h
  · simp [tensorKer, image_eq_zero_of_notMem_tsupport h]
  · simp [tensorKer, image_eq_zero_of_notMem_tsupport h]

/-- The kernel map `M ζ = r(H₁ζ₁ + H₂ζ₂)`. -/
def kerMap (r : ℝ) (A B : Vec 2 →L[ℝ] Vec 2) : Vec 2 × Vec 2 →L[ℝ] Vec 2 :=
  r • (A.comp (ContinuousLinearMap.fst ℝ (Vec 2) (Vec 2)) +
    B.comp (ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2)))

/-- The coordinate splitting `ι s = (s₁e₁, s₂e₂)`. -/
def splitMap : Vec 2 →L[ℝ] Vec 2 × Vec 2 :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (basisVec 0)).prod
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (basisVec 1))

theorem norm_basisVec (i : Fin 2) : ‖(basisVec i : Vec 2)‖ = 1 := by
  simp [basisVec, Pi.norm_single]

theorem norm_splitMap_le (u : Vec 2) : ‖splitMap u‖ ≤ ‖u‖ := by
  simp only [splitMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Prod.norm_def, norm_smul, norm_basisVec, mul_one]
  exact max_le (norm_le_pi_norm u 0) (norm_le_pi_norm u 1)

/-- The right inverse of the kernel map. -/
theorem kerMap_splitMap (r : ℝ) (hr : r ≠ 0) (S : KernelSpec) (t : ℝ)
    (hdet : IsUnit (S.span t).det) (y : Vec 2) :
    kerMap r (S.H₁ t) (S.H₂ t) ((r⁻¹ • (splitMap.comp
      (Matrix.toLin' (S.span t)⁻¹).toContinuousLinearMap)) y) = y := by
  set u := Matrix.mulVec (S.span t)⁻¹ y with hu
  have hspan : ∀ a, (Matrix.mulVec (S.span t) u) a = u 0 * S.H₁ t (basisVec 0) a + u 1 * S.H₂ t (basisVec 1) a := by
    intro a
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, KernelSpec.span, mul_comm]
  have hid : Matrix.mulVec (S.span t) u = y := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  funext a
  calc _ = u 0 * S.H₁ t (basisVec 0) a + u 1 * S.H₂ t (basisVec 1) a := by
        simp only [kerMap, splitMap, smul_apply, ContinuousLinearMap.comp_apply, add_apply,
          ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', LinearMap.coe_toContinuousLinearMap',
          Matrix.toLin'_apply, map_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hu]
        field_simp
    _ = (Matrix.mulVec (S.span t) u) a := (hspan a).symm
    _ = y a := by rw [hid]

/-- The paired average is the tensor kernel average. -/
theorem applyClassical_eq_op {φ₀ : Vec 2 → ℝ} (S : KernelSpec) (k : Vec 2 → ℝ)
    (hk : k = momentKernel φ₀ S.order) (hkK : IsKer (tensorKer k)) (t : ℝ)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {V : Vec 2 → H} (hV : Continuous V) {B : ℝ} (hB : ∀ y, ‖V y‖ ≤ B) :
    S.applyClassical φ₀ t V = Op volume (tensorKer k) (kerMap S.width (S.H₁ t) (S.H₂ t)) V := by
  funext y
  have hint := integrable_op (μ := (volume : Measure (Vec 2 × Vec 2))) hkK
    (kerMap S.width (S.H₁ t) (S.H₂ t)) hV hB y
  rw [Measure.volume_eq_prod] at hint
  unfold Op
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  unfold KernelSpec.applyClassical
  rw [← hk]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only [tensorKer, kerMap, mul_smul, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_add, sub_sub]

/-- Splitting a word of order `m' ≥ l'` into its first `l'` and last `m' - l'` derivatives. -/
theorem iterate_split {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (a₀ a₁ l : ℕ)
    (hl : l ≤ a₀ + a₁) (F : Vec 2 → H) :
    (dirD (basisVec 1))^[a₁] ((dirD (basisVec 0))^[a₀] F) =
      (dirD (basisVec 1))^[a₁ - (l - min a₀ l)] ((dirD (basisVec 0))^[a₀ - min a₀ l]
        ((dirD (basisVec 1))^[l - min a₀ l] ((dirD (basisVec 0))^[min a₀ l] F))) := by
  by_cases h : a₀ ≤ l
  · rw [min_eq_left h, Nat.sub_self, Function.iterate_zero_apply,
      ← Function.iterate_add_apply, show a₁ - (l - a₀) + (l - a₀) = a₁ by omega]
  · have h' : l ≤ a₀ := by omega
    rw [min_eq_right h', Nat.sub_self, Function.iterate_zero_apply, Nat.sub_zero,
      ← Function.iterate_add_apply (dirD (basisVec 0)), show a₀ - l + l = a₀ by omega]

/-- Per-word bound in `ℝ≥0∞` from a pointwise bound. -/
theorem supNorm_le_of_pointwise {H : Type*} [NormedAddCommGroup H] {F W : Vec 2 → H} {c : ℝ}
    (hc : 0 ≤ c) (hW : supNorm W ≠ ⊤)
    (h : ∀ B, (∀ y, ‖W y‖ ≤ B) → ∀ x, ‖F x‖ ≤ c * B) :
    supNorm F ≤ ENNReal.ofReal c * supNorm W := by
  have hWb : ∀ y, ‖W y‖ ≤ (supNorm W).toReal := by
    intro y
    have h1 : (‖W y‖₊ : ℝ≥0∞) ≤ supNorm W := le_iSup (fun x => (‖W x‖₊ : ℝ≥0∞)) y
    have := ENNReal.toReal_mono hW h1
    simpa using this
  refine iSup_le fun x => ?_
  have hx := h _ hWb x
  rw [← ENNReal.ofReal_toReal hW, ← ENNReal.ofReal_mul hc]
  calc (‖F x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖F x‖ := (ofReal_norm (F x)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hx

/-- `supNorm` of a continuous periodic field is finite. -/
theorem supNorm_ne_top_of_periodic {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {W : Vec 2 → H} (hW : Continuous W) (hp : AVenhance.IsZ2Periodic W) : supNorm W ≠ ⊤ := by
  obtain ⟨B, hB⟩ := bdd_of_periodic hW hp
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B)) (iSup_le fun y => ?_)
  calc (‖W y‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖W y‖ := (ofReal_norm (W y)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hB y)

instance : (volume : Measure (Vec 2 × Vec 2)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- **The paired kernel in `L^∞`** (Lemma 13.4(a) of the paper). -/
theorem passage_kernel_sup (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall) :
    ∀ (Γ : ℝ) (L : ℕ) (nk : ℕ+) (m' l' : ℕ), 1 ≤ l' → l' ≤ m' → ∃ C : ℝ, 0 < C ∧
    ∀ (S : KernelSpec), S.order = nk → S.IsAdmissible Γ L → 0 < S.width → ∀ (t : ℝ)
      {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] (V : Vec 2 → H),
      ContDiff ℝ l' V → AVenhance.IsZ2Periodic V →
      ∑ α ∈ multiIndicesBetween m' m', supNorm (partialDerivative α (S.applyClassical φ₀ t V)) ≤
        ENNReal.ofReal (C * S.width ^ ((l' : ℝ) - m')) *
          ∑ β ∈ multiIndicesBetween l' l', supNorm (partialDerivative β V) := by
  intro Γ L nk m' l' _hl' hlm
  have _ := hφ₀
  have hφc := hasCompactSupport_of_unitBall hφsupp
  set k := momentKernel φ₀ nk with hk
  have hkK : IsKer (tensorKer k) :=
    isKer_tensorKer (contDiff_momentKernel hφc hφs nk) (hasCompactSupport_momentKernel hφc nk)
  set K := tensorKer k with hKdef
  set j := m' - l' with hj
  set Ij : ℝ := ∫ ζ, ‖iteratedFDeriv ℝ j K ζ‖ with hIj
  have hIj0 : 0 ≤ Ij := integral_nonneg fun _ => norm_nonneg _
  set N : ℝ := ((multiIndicesBetween m' m').card : ℝ) with hN
  set C0 : ℝ := (|Γ| + 1) ^ j * (Ij + 1) with hC0
  have hC0p : 0 < C0 := by positivity
  refine ⟨(N + 1) * C0, by positivity, ?_⟩
  intro S hSo hSadm hr t H _ _ _ V hV hVp
  obtain ⟨hA, -, hdet, hinv⟩ := hSadm.2.2.1 t
  set r := S.width with hrdef
  set M := kerMap r (S.H₁ t) (S.H₂ t) with hM
  set T := (Matrix.toLin' (S.span t)⁻¹).toContinuousLinearMap with hT
  set R : Vec 2 →L[ℝ] Vec 2 × Vec 2 := r⁻¹ • (splitMap.comp T) with hR
  have hMR : ∀ y, M (R y) = y := kerMap_splitMap r hr.ne' S t hdet
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans hA
  have hRe : ∀ i, ‖R (basisVec i)‖ ≤ Γ / r := by
    intro i
    simp only [hR, smul_apply, ContinuousLinearMap.comp_apply, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hr]
    rw [div_eq_inv_mul]
    gcongr
    calc ‖splitMap (T (basisVec i))‖ ≤ ‖T (basisVec i)‖ := norm_splitMap_le _
      _ ≤ ‖T‖ * ‖(basisVec i : Vec 2)‖ := T.le_opNorm _
      _ = ‖T‖ := by rw [norm_basisVec, mul_one]
      _ ≤ Γ := hinv
  obtain ⟨BV, hBV⟩ := bdd_of_periodic hV.continuous hVp
  have hSV : S.applyClassical φ₀ t V = Op volume K M V :=
    applyClassical_eq_op S k (by rw [hSo]) hkK t hV.continuous hBV
  -- the rate constant
  have hrate : (Γ / r) ^ j * Ij ≤ C0 * r ^ ((l' : ℝ) - m') := by
    have hexp : (l' : ℝ) - m' = -((j : ℕ) : ℝ) := by
      rw [hj, Nat.cast_sub hlm]; ring
    rw [hexp, Real.rpow_neg hr.le, Real.rpow_natCast, div_pow, div_eq_mul_inv]
    have h1 : Γ ^ j ≤ (|Γ| + 1) ^ j :=
      pow_le_pow_left₀ hΓ0 (by rw [abs_of_nonneg hΓ0]; linarith) j
    have hrj : 0 ≤ (r ^ j)⁻¹ := by positivity
    calc Γ ^ j * (r ^ j)⁻¹ * Ij ≤ (|Γ| + 1) ^ j * (r ^ j)⁻¹ * (Ij + 1) := by
          gcongr; linarith
      _ = C0 * (r ^ j)⁻¹ := by rw [hC0]; ring
  -- one word
  have hword : ∀ α ∈ multiIndicesBetween m' m', ∃ β ∈ multiIndicesBetween l' l',
      supNorm (partialDerivative α (S.applyClassical φ₀ t V)) ≤
        ENNReal.ofReal (C0 * r ^ ((l' : ℝ) - m')) * supNorm (partialDerivative β V) := by
    intro α hα
    have hαs : α 0 + α 1 = m' := by
      simp only [multiIndicesBetween, Finset.mem_filter] at hα; omega
    set b0 := min (α 0) l' with hb0
    set b1 := l' - b0 with hb1
    set g0 := α 0 - b0 with hg0
    set g1 := α 1 - b1 with hg1
    let β : Fin 2 → ℕ := fun i => if i = 0 then b0 else b1
    have hβ0 : β 0 = b0 := rfl
    have hβ1 : β 1 = b1 := rfl
    refine ⟨β, ?_, ?_⟩
    · simp only [multiIndicesBetween, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun i => ?_, by omega, by omega⟩
      fin_cases i <;> simp [β] <;> omega
    -- field side
    obtain ⟨hV0r, hV0p⟩ := iterate_reg hV hVp (basisVec 0) b0 (by omega)
    set V0 := (dirD (basisVec 0))^[b0] V with hV0
    have hV0r' : ContDiff ℝ b1 V0 := by simpa [hb1] using hV0r
    obtain ⟨hWr, hWp⟩ := iterate_reg hV0r' hV0p (basisVec 1) b1 le_rfl
    set W := (dirD (basisVec 1))^[b1] V0 with hW
    have hWc : Continuous W := hWr.continuous
    have hWeq : partialDerivative β V = W := by
      show (fun G : Vec 2 → H => fun x => fderiv ℝ G x (basisVec 1))^[β 1]
        ((fun G : Vec 2 → H => fun x => fderiv ℝ G x (basisVec 0))^[β 0] V) = W
      rw [hβ0, hβ1]; rfl
    obtain ⟨BW, hBW⟩ := bdd_of_periodic hWc hWp
    have hf0 := iterate_field_hyps (hV.of_le (by exact_mod_cast (show b0 ≤ l' by omega)))
      hVp (basisVec 0)
    have hf1 := iterate_field_hyps hV0r' hV0p (basisVec 1)
    have hfield : (dirD (basisVec 1))^[b1] ((dirD (basisVec 0))^[b0] (Op volume K M V)) =
        Op volume K M W := by
      rw [iterate_op_field hkK M (basisVec 0) b0 V hf0.1 hf0.2,
        iterate_op_field hkK M (basisVec 1) b1 V0 hf1.1 hf1.2]
    -- kernel side
    have hkern : (dirD (basisVec 1))^[g1] ((dirD (basisVec 0))^[g0] (Op volume K M W)) =
        Op volume ((dirD (R (basisVec 1)))^[g1] ((dirD (R (basisVec 0)))^[g0] K)) M W := by
      rw [iterate_op_kernel M R hMR hWc hBW (basisVec 0) g0 K hkK,
        iterate_op_kernel M R hMR hWc hBW (basisVec 1) g1 _ (hkK.iterate_dirD _ g0)]
    have hderiv : partialDerivative α (S.applyClassical φ₀ t V) =
        Op volume ((dirD (R (basisVec 1)))^[g1] ((dirD (R (basisVec 0)))^[g0] K)) M W := by
      rw [hSV]
      show (dirD (basisVec 1))^[α 1] ((dirD (basisVec 0))^[α 0] (Op volume K M V)) = _
      rw [iterate_split (α 0) (α 1) l' (by omega), ← hb0, ← hb1, ← hg0, ← hg1, hfield, hkern]
    -- the kernel factor
    set K' := (dirD (R (basisVec 1)))^[g1] ((dirD (R (basisVec 0)))^[g0] K) with hK'
    have hK'ker : IsKer K' := (hkK.iterate_dirD _ g0).iterate_dirD _ g1
    obtain ⟨w, hw, hrep⟩ := iterate2_rep hkK.smooth (hRe 0) (hRe 1) g0 g1
    have hidx : 0 + g0 + g1 = j := by omega
    have hint : ∫ ζ, ‖K' ζ‖ ≤ (Γ / r) ^ j * Ij := by
      have hρ : 0 ≤ Γ / r := div_nonneg hΓ0 hr.le
      have hI : Integrable (fun ζ => ‖iteratedFDeriv ℝ (0 + g0 + g1) K ζ‖)
          (volume : Measure (Vec 2 × Vec 2)) :=
        ((hkK.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.integrable_of_hasCompactSupport
          (hkK.cpt.iteratedFDeriv _).norm)
      calc ∫ ζ, ‖K' ζ‖ ≤ ∫ ζ, (Γ / r) ^ (0 + g0 + g1) * ‖iteratedFDeriv ℝ (0 + g0 + g1) K ζ‖ := by
            refine integral_mono (hK'ker.integrable.norm) (hI.const_mul _) (fun ζ => ?_)
            simp only [hK', hrep]
            exact norm_iteratedFDeriv_apply_le w hw ζ
        _ = (Γ / r) ^ j * Ij := by rw [integral_const_mul, hidx]
    have hc0 : 0 ≤ (Γ / r) ^ j * Ij := mul_nonneg (pow_nonneg (div_nonneg hΓ0 hr.le) _) hIj0
    rw [hWeq, hderiv]
    calc supNorm (Op volume K' M W) ≤ ENNReal.ofReal ((Γ / r) ^ j * Ij) * supNorm W := by
          refine supNorm_le_of_pointwise hc0 (supNorm_ne_top_of_periodic hWc hWp) ?_
          intro B hB x
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
          calc ‖Op volume K' M W x‖ ≤ (∫ ζ, ‖K' ζ‖) * B := norm_op_le hK'ker M hB x
            _ ≤ (Γ / r) ^ j * Ij * B := mul_le_mul_of_nonneg_right hint hB0
      _ ≤ ENNReal.ofReal (C0 * r ^ ((l' : ℝ) - m')) * supNorm W := by
          gcongr
  -- sum over words
  set X : ℝ≥0∞ := ∑ β ∈ multiIndicesBetween l' l', supNorm (partialDerivative β V)
  have hX : ∀ α ∈ multiIndicesBetween m' m',
      supNorm (partialDerivative α (S.applyClassical φ₀ t V)) ≤
        ENNReal.ofReal (C0 * r ^ ((l' : ℝ) - m')) * X := by
    intro α hα
    obtain ⟨β, hβ, hle⟩ := hword α hα
    exact hle.trans (by gcongr; exact Finset.single_le_sum (f := fun β => supNorm (partialDerivative β V)) (fun _ _ => zero_le) hβ)
  have hrp : 0 ≤ C0 * r ^ ((l' : ℝ) - m') := mul_nonneg hC0p.le (Real.rpow_nonneg hr.le _)
  calc ∑ α ∈ multiIndicesBetween m' m', supNorm (partialDerivative α (S.applyClassical φ₀ t V))
      ≤ (multiIndicesBetween m' m').card • (ENNReal.ofReal (C0 * r ^ ((l' : ℝ) - m')) * X) :=
        Finset.sum_le_card_nsmul _ _ _ hX
    _ = ENNReal.ofReal N * (ENNReal.ofReal (C0 * r ^ ((l' : ℝ) - m')) * X) := by
        rw [nsmul_eq_mul, hN, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (N + 1) * (ENNReal.ofReal (C0 * r ^ ((l' : ℝ) - m')) * X) := by
        gcongr; linarith
    _ = ENNReal.ofReal ((N + 1) * C0 * r ^ ((l' : ℝ) - m')) * X := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hC0]
        ring_nf

end AVRegularity.Providers
