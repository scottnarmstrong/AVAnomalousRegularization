-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section
open scoped ENNReal NNReal
namespace AVRegularity

/-! The weighted Schur test in `ℝ≥0∞`, via a Cauchy–Schwarz inequality for extended
nonnegative reals. -/

/-- Cauchy–Schwarz in `ℝ≥0∞`: `(∑ r)² ≤ (∑ f)(∑ g)` when `r² ≤ f g`. -/
theorem ennreal_sum_sq_le_sum_mul_sum {ι : Type*} (s : Finset ι) (r f g : ι → ℝ≥0∞)
    (h : ∀ i ∈ s, r i ^ 2 ≤ f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
  by_cases hF : ∑ i ∈ s, f i = ∞
  · by_cases hG : ∑ i ∈ s, g i = 0
    · have hg0 : ∀ i ∈ s, g i = 0 := (Finset.sum_eq_zero_iff).1 hG
      have hr : ∀ i ∈ s, r i = 0 := fun i hi => by
        have := h i hi
        rw [hg0 i hi, mul_zero, nonpos_iff_eq_zero] at this
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      rw [Finset.sum_eq_zero hr]; simp
    · rw [hF, ENNReal.top_mul hG]; exact le_top
  by_cases hG : ∑ i ∈ s, g i = ∞
  · by_cases hF0 : ∑ i ∈ s, f i = 0
    · have hf0 : ∀ i ∈ s, f i = 0 := (Finset.sum_eq_zero_iff).1 hF0
      have hr : ∀ i ∈ s, r i = 0 := fun i hi => by
        have := h i hi
        rw [hf0 i hi, zero_mul, nonpos_iff_eq_zero] at this
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      rw [Finset.sum_eq_zero hr]; simp
    · rw [hG, ENNReal.mul_top hF0]; exact le_top
  have hf : ∀ i ∈ s, f i ≠ ∞ := fun i hi =>
    (ENNReal.sum_lt_top.1 (lt_top_iff_ne_top.2 hF) i hi).ne
  have hg : ∀ i ∈ s, g i ≠ ∞ := fun i hi =>
    (ENNReal.sum_lt_top.1 (lt_top_iff_ne_top.2 hG) i hi).ne
  have hr : ∀ i ∈ s, r i ≠ ∞ := fun i hi => by
    intro hri
    have := h i hi
    rw [hri] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.top_pow, top_le_iff,
      ENNReal.mul_eq_top] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hg i hi h2
    · exact hf i hi h1
  have key : (∑ i ∈ s, (r i).toNNReal) ^ 2 ≤
      (∑ i ∈ s, (f i).toNNReal) * ∑ i ∈ s, (g i).toNNReal := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun _ _ => by positivity)
      (fun _ _ => by positivity) fun i hi => ?_
    have := h i hi
    rw [← ENNReal.coe_le_coe]
    simpa [ENNReal.coe_toNNReal (hr i hi), ENNReal.coe_toNNReal (hf i hi),
      ENNReal.coe_toNNReal (hg i hi)] using this
  have key' := (ENNReal.coe_le_coe).2 key
  simp only [ENNReal.coe_pow, ENNReal.coe_mul, ENNReal.ofNNReal_finsetSum] at key'
  have e1 : ∀ x : ι → ℝ≥0∞, (∀ i ∈ s, x i ≠ ∞) → ∑ i ∈ s, ((x i).toNNReal : ℝ≥0∞) = ∑ i ∈ s, x i :=
    fun x hx => Finset.sum_congr rfl fun i hi => ENNReal.coe_toNNReal (hx i hi)
  rwa [e1 r hr, e1 f hf, e1 g hg] at key'

theorem sqrt_ratio_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a⁻¹ * (Real.sqrt (b / a))⁻¹ = Real.sqrt (b / a) * b⁻¹ := by
  have hs : Real.sqrt (b / a) ^ 2 = b / a := Real.sq_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (b / a) := Real.sqrt_pos.2 (by positivity)
  generalize Real.sqrt (b / a) = s at hs hpos
  field_simp
  field_simp at hs
  linarith

theorem schurSums_weighted_sq_le {ι : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * (∑ u, K v u * b u) ^ 2
      ≤ schurSums π K ^ 2 * ∑ u, ENNReal.ofReal (π u)⁻¹ * b u ^ 2 := by
  set S := schurSums π K with hS
  let r : ι → ι → ℝ≥0∞ := fun v u => ENNReal.ofReal (Real.sqrt (π u / π v))
  have hrpos : ∀ v u, 0 < Real.sqrt (π u / π v) := fun v u =>
    Real.sqrt_pos.2 (div_pos (hπ u) (hπ v))
  have hr0 : ∀ v u, r v u ≠ 0 := fun v u => by
    simpa [r] using hrpos v u
  have hrt : ∀ v u, r v u ≠ ∞ := fun v u => ENNReal.ofReal_ne_top
  have hrow : ∀ v, ∑ u, r v u * K v u ≤ S := fun v =>
    (le_iSup (fun v => ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * K v u) v).trans
      (le_max_left _ _)
  have hcol : ∀ u, ∑ v, r v u * K v u ≤ S := fun u =>
    (le_iSup (fun u => ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * K v u) u).trans
      (le_max_right _ _)
  have hv : ∀ v, ENNReal.ofReal (π v)⁻¹ * (∑ u, K v u * b u) ^ 2 ≤
      S * ∑ u, r v u * K v u * (ENNReal.ofReal (π u)⁻¹ * b u ^ 2) := by
    intro v
    have hcs := ennreal_sum_sq_le_sum_mul_sum Finset.univ (fun u => K v u * b u)
      (fun u => r v u * K v u) (fun u => (r v u)⁻¹ * (K v u * b u ^ 2)) (fun u _ => le_of_eq (by
        calc (K v u * b u) ^ 2 = (r v u * (r v u)⁻¹) * (K v u * (K v u * b u ^ 2)) := by
              rw [ENNReal.mul_inv_cancel (hr0 v u) (hrt v u)]; ring
          _ = (r v u * K v u) * ((r v u)⁻¹ * (K v u * b u ^ 2)) := by ring))
    calc ENNReal.ofReal (π v)⁻¹ * (∑ u, K v u * b u) ^ 2
        ≤ ENNReal.ofReal (π v)⁻¹ * ((∑ u, r v u * K v u) *
            ∑ u, (r v u)⁻¹ * (K v u * b u ^ 2)) := by gcongr
      _ = (∑ u, r v u * K v u) * ∑ u, ENNReal.ofReal (π v)⁻¹ * ((r v u)⁻¹ *
            (K v u * b u ^ 2)) := by
          rw [mul_left_comm, Finset.mul_sum]
      _ ≤ S * ∑ u, r v u * K v u * (ENNReal.ofReal (π u)⁻¹ * b u ^ 2) := by
          refine mul_le_mul' (hrow v) (Finset.sum_le_sum fun u _ => le_of_eq ?_)
          have : ENNReal.ofReal (π v)⁻¹ * (r v u)⁻¹ = r v u * ENNReal.ofReal (π u)⁻¹ := by
            simp only [r]
            rw [← ENNReal.ofReal_inv_of_pos (hrpos v u), ← ENNReal.ofReal_mul (by
              exact inv_nonneg.2 (hπ v).le), ← ENNReal.ofReal_mul (hrpos v u).le]
            rw [sqrt_ratio_identity (hπ v) (hπ u)]
          rw [← mul_assoc, this]; ring
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * (∑ u, K v u * b u) ^ 2
      ≤ ∑ v, S * ∑ u, r v u * K v u * (ENNReal.ofReal (π u)⁻¹ * b u ^ 2) :=
        Finset.sum_le_sum fun v _ => hv v
    _ = S * ∑ u, (∑ v, r v u * K v u) * (ENNReal.ofReal (π u)⁻¹ * b u ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ ≤ S * ∑ u, S * (ENNReal.ofReal (π u)⁻¹ * b u ^ 2) := by
        gcongr with u hu; exact hcol u
    _ = S ^ 2 * ∑ u, ENNReal.ofReal (π u)⁻¹ * b u ^ 2 := by
        rw [← Finset.mul_sum, ← mul_assoc, sq]

end AVRegularity
end

section
open MeasureTheory Homogenization
namespace AVRegularity

/-! Continuous linear images of box smooth fields and of cell antidivergences. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsBoxSmooth.clm_comp {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f)
    (L : E →L[ℝ] F) : IsBoxSmooth sX sZ (fun X z => L (f X z)) := by
  obtain ⟨h1, h2, h3⟩ := hf
  have hjet : ∀ b, b ≤ sZ → ∀ X z, iteratedFDeriv ℝ b (fun z' => L (f X z')) z =
      ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F L
        (iteratedFDeriv ℝ b (f X) z) := fun b hb X z =>
    L.iteratedFDeriv_comp_left ((h1 X).contDiffAt) (by exact_mod_cast hb)
  refine ⟨fun X => L.contDiff.comp (h1 X), fun b hb z => ?_, fun a b ha hb => ?_⟩
  · simp_rw [hjet b hb]
    exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F
      L).contDiff.comp (h2 b hb z)
  · have e : ∀ p : Vec 2 × Vec 2,
        iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (fun z' => L (f X' z')) p.2) p.1 =
        ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2)
          (Vec 2 [×b]→L[ℝ] E) (Vec 2 [×b]→L[ℝ] F)
          (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F L)
          (iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f X') p.2) p.1) := by
      intro p
      have : (fun X' => iteratedFDeriv ℝ b (fun z' => L (f X' z')) p.2) =
          (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F L) ∘
            (fun X' => iteratedFDeriv ℝ b (f X') p.2) := by
        funext X'; exact hjet b hb X' p.2
      rw [this]
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F
        L).iteratedFDeriv_comp_left ((h2 b hb p.2).contDiffAt) (by exact_mod_cast ha)
    simp_rw [e]
    exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2)
      (Vec 2 [×b]→L[ℝ] E) (Vec 2 [×b]→L[ℝ] F)
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F
        L)).continuous.comp (h3 a b ha hb)

theorem IsCellAntidivergence.clm_comp [CompleteSpace E] [CompleteSpace F] {sX sZ : ℕ} (hZ : 1 ≤ sZ)
    {f : Vec 2 → Vec 2 → E} {V : Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCellAntidivergence sX sZ f V) (L : E →L[ℝ] F) :
    IsCellAntidivergence sX sZ (fun X z => L (f X z)) (fun X z k => L (V X z k)) := by
  obtain ⟨hVbox, hVper, φ, hφbox, hφper, hφmean, hVφ, hdiv⟩ := hV
  have hφ1 : ∀ X, ContDiff ℝ 1 (φ X) := fun X =>
    (hφbox.1 X).of_le (by exact_mod_cast Nat.le_add_left 1 sZ)
  have hVk : ∀ X k, Differentiable ℝ (fun z => V X z k) := fun X k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k).contDiff.comp
      ((hVbox.1 X).of_le (show (1 : WithTop ℕ∞) ≤ (sZ : ℕ∞) by exact_mod_cast hZ))).differentiable
      (by norm_num)
  unfold IsCellAntidivergence
  refine ⟨?_, fun X n z => ?_, fun X z => L (φ X z), hφbox.clm_comp L, fun X n z => ?_,
    fun X => ?_, fun X z k => ?_, fun X z => ?_⟩
  · exact hVbox.clm_comp (ContinuousLinearMap.pi fun k =>
      L.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k))
  · funext k
    exact congrArg L (congrFun (hVper X n z) k)
  · exact congrArg L (hφper X n z)
  · have hint : IntegrableOn (φ X) AVenhance.unitCube := by
      have h := AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell
        (hφbox.1 X |>.continuous)
      exact h.congr_set_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.symm
    have hm : fieldCellMean (φ X) = 0 := hφmean X
    change ∫ z in AVenhance.unitCube, L (φ X z) = 0
    rw [L.integral_comp_comm hint]
    have : ∫ z in AVenhance.unitCube, φ X z = 0 := hm
    rw [this, map_zero]
  · show L (V X z k) = fderiv ℝ (fun z => L (φ X z)) z (basisVec k)
    rw [hVφ X z k]
    have := (L.hasFDerivAt.comp z ((hφ1 X).differentiable (by norm_num) z).hasFDerivAt).fderiv
    rw [show (fun z => L (φ X z)) = L ∘ φ X from rfl, this]
    rfl
  · have h : ∀ k, fderiv ℝ (fun z' => L (V X z' k)) z (basisVec k) =
        L (fderiv ℝ (fun z' => V X z' k) z (basisVec k)) := fun k => by
      have := (L.hasFDerivAt.comp z (hVk X k z).hasFDerivAt).fderiv
      rw [show (fun z' => L (V X z' k)) = L ∘ (fun z' => V X z' k) from rfl, this]
      rfl
    simp_rw [h]
    rw [← map_sum, hdiv X z]

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Multilinear expansion on `Vec 2` in the coordinate directions, and the comparison of the full
iterated derivative with the ordered word derivatives. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_basisVec (i : Fin 2) : ‖(basisVec i : Vec 2)‖ = 1 := by
  simp [basisVec, Pi.norm_single]

theorem vec2_eq_sum_basisVec (x : Vec 2) : x = ∑ j : Fin 2, x j • basisVec j := by
  ext j; simp [basisVec, Pi.single_apply, Finset.sum_apply]

theorem norm_le_sum_basisVec {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) F) :
    ‖f‖ ≤ ∑ w : DerivativeWord2 q, ‖f (fun i => basisVec (w i))‖ := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun x => ?_
  have hx : x = fun i => ∑ j : Fin 2, x i j • basisVec j := funext fun i => vec2_eq_sum_basisVec _
  have h1 : f x = ∑ r : DerivativeWord2 q, f (fun i => x i (r i) • basisVec (r i)) := by
    conv_lhs => rw [hx]
    exact f.toMultilinearMap.map_sum (fun i j => x i j • basisVec j)
  have h2 : ∀ r : DerivativeWord2 q, ‖f (fun i => x i (r i) • basisVec (r i))‖ ≤
      (∏ i, ‖x i‖) * ‖f (fun i => basisVec (r i))‖ := by
    intro r
    rw [f.map_smul_univ, norm_smul, norm_prod]
    gcongr with i hi
    exact norm_le_pi_norm (x i) (r i)
  rw [h1]
  calc ‖∑ r : DerivativeWord2 q, f (fun i => x i (r i) • basisVec (r i))‖
      ≤ ∑ r : DerivativeWord2 q, ‖f (fun i => x i (r i) • basisVec (r i))‖ := norm_sum_le _ _
    _ ≤ ∑ r : DerivativeWord2 q, (∏ i, ‖x i‖) * ‖f (fun i => basisVec (r i))‖ :=
        Finset.sum_le_sum fun r _ => h2 r
    _ = (∑ w : DerivativeWord2 q, ‖f (fun i => basisVec (w i))‖) * ∏ i, ‖x i‖ := by
        rw [← Finset.mul_sum, mul_comm]


/-- Reversal of a derivative word, as an equivalence. -/
def wordRev (q : ℕ) : DerivativeWord2 q ≃ DerivativeWord2 q where
  toFun w := fun i => w (Fin.rev i)
  invFun w := fun i => w (Fin.rev i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

theorem card_derivativeWord2 (q : ℕ) :
    (Finset.univ : Finset (DerivativeWord2 q)).card = 2 ^ q := by
  simp

theorem norm_iteratedFDeriv_sq_le_words {q : ℕ} {g : Vec 2 → F} (hg : ContDiff ℝ (q : ℕ∞) g)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ q g x‖ ^ 2 ≤
      2 ^ q * ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ ^ 2 := by
  have h1 := norm_le_sum_basisVec (iteratedFDeriv ℝ q g x)
  have h2 : ∑ w : DerivativeWord2 q, ‖iteratedFDeriv ℝ q g x (fun i => basisVec (w i))‖ =
      ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ := by
    rw [← Equiv.sum_comp (wordRev q)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [orderedDerivative_eq_iteratedFDeriv w hg]
    rfl
  rw [h2] at h1
  have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (DerivativeWord2 q)))
    (f := fun w => ‖orderedDerivative w g x‖)
  rw [card_derivativeWord2] at h3
  calc ‖iteratedFDeriv ℝ q g x‖ ^ 2
      ≤ (∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by exact_mod_cast h3

theorem norm_orderedDerivative_le {q : ℕ} {g : Vec 2 → F} (hg : ContDiff ℝ (q : ℕ∞) g)
    (w : DerivativeWord2 q) (x : Vec 2) :
    ‖orderedDerivative w g x‖ ≤ ‖iteratedFDeriv ℝ q g x‖ := by
  rw [orderedDerivative_eq_iteratedFDeriv w hg]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [norm_basisVec]

theorem sum_orderedDerivative_sq_le {q : ℕ} {g : Vec 2 → F} (hg : ContDiff ℝ (q : ℕ∞) g)
    (x : Vec 2) :
    ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ ^ 2 ≤
      2 ^ q * ‖iteratedFDeriv ℝ q g x‖ ^ 2 := by
  calc ∑ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ ^ 2
      ≤ ∑ w : DerivativeWord2 q, ‖iteratedFDeriv ℝ q g x‖ ^ 2 :=
        Finset.sum_le_sum fun w _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_orderedDerivative_le hg w x) 2
    _ = 2 ^ q * ‖iteratedFDeriv ℝ q g x‖ ^ 2 := by
        rw [Finset.sum_const, card_derivativeWord2]; simp

theorem contDiff_orderedDerivative {p q : ℕ} (α : DerivativeWord2 q) {g : Vec 2 → F}
    (hg : ContDiff ℝ ((p + q : ℕ) : ℕ∞) g) : ContDiff ℝ (p : ℕ∞) (orderedDerivative α g) := by
  rw [orderedDerivative_eq_iteratedFDeriv α (hg.of_le (by exact_mod_cast Nat.le_add_left q p))]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) F
    (fun i => basisVec (α (Fin.rev i)))).contDiff.comp
    (hg.iteratedFDeriv_right (by exact_mod_cast le_rfl))

theorem norm_iteratedFDeriv_orderedDerivative_le {p q : ℕ} (α : DerivativeWord2 q)
    {g : Vec 2 → F} (hg : ContDiff ℝ ((p + q : ℕ) : ℕ∞) g) (x : Vec 2) :
    ‖iteratedFDeriv ℝ p (orderedDerivative α g) x‖ ≤ ‖iteratedFDeriv ℝ (p + q) g x‖ := by
  induction q generalizing p with
  | zero =>
    rw [orderedDerivative_zero]; rfl
  | succ q ih =>
    set α0 : DerivativeWord2 q := fun i => α i.castSucc
    have hg1 : ContDiff ℝ (((p + 1) + q : ℕ) : ℕ∞) g := by
      have : (p + 1) + q = p + (q + 1) := by omega
      rw [this]; exact hg
    have hh : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (orderedDerivative α0 g) :=
      contDiff_orderedDerivative α0 hg1
    rw [orderedDerivative_succ]
    have e1 := (ContinuousLinearMap.apply ℝ F (basisVec (α (Fin.last q)))).norm_iteratedFDeriv_comp_left
      (f := fderiv ℝ (orderedDerivative α0 g)) (x := x) (N := (p : ℕ∞))
      ((hh.fderiv_right (by exact_mod_cast le_rfl)).contDiffAt) (n := p) (by exact_mod_cast le_rfl)
    have e2 : ‖ContinuousLinearMap.apply ℝ F (basisVec (α (Fin.last q)))‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
      simpa [norm_basisVec] using T.le_opNorm (basisVec (α (Fin.last q)))
    have e3 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := orderedDerivative α0 g) (n := p) (x := x)
    have e4 := ih α0 hg1
    have e5 : p + 1 + q = p + (q + 1) := by omega
    rw [e5] at e4
    calc _ ≤ ‖ContinuousLinearMap.apply ℝ F (basisVec (α (Fin.last q)))‖ *
          ‖iteratedFDeriv ℝ p (fderiv ℝ (orderedDerivative α0 g)) x‖ := e1
      _ ≤ 1 * ‖iteratedFDeriv ℝ p (fderiv ℝ (orderedDerivative α0 g)) x‖ := by gcongr
      _ ≤ _ := by rw [one_mul, e3]; exact e4

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! Slow dilation of full jets, and the conversion of the full iterated-derivative energy into the
classical gradient factorial norm. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_comp_smul_norm (q : ℕ) (g : Vec 2 → F) (hg : ContDiff ℝ (q : ℕ∞) g)
    (ρ : ℝ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun X' => g (ρ • X')) X‖ =
      |ρ| ^ q * ‖iteratedFDeriv ℝ q g (ρ • X)‖ := by
  rw [iteratedFDeriv_comp_const_smul ρ hg, norm_smul, norm_pow, Real.norm_eq_abs]

omit [NormedSpace ℝ F] in
theorem enorm_sq_eq_ofReal' (w : F) : ‖w‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem lintegral_iteratedFDeriv_sq_le_words {q : ℕ} {g : Vec 2 → F}
    (hg : ContDiff ℝ (q : ℕ∞) g) :
    ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ q g x‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ q) * ∑ w : DerivativeWord2 q,
        ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2 := by
  have hmeas : ∀ w : DerivativeWord2 q, Measurable fun x => ‖orderedDerivative w g x‖ₑ ^ 2 := by
    intro w
    rw [orderedDerivative_eq_iteratedFDeriv w hg]
    have hc : Continuous fun x => iteratedFDeriv ℝ q g x
        (fun i => basisVec (w (Fin.rev i))) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) F _).continuous.comp
        (hg.continuous_iteratedFDeriv (by exact_mod_cast le_rfl))
    exact ((ENNReal.continuous_pow 2).comp hc.enorm).measurable
  rw [← lintegral_finsetSum _ (fun w _ => hmeas w), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  have h := norm_iteratedFDeriv_sq_le_words hg x
  have e : ∀ w : DerivativeWord2 q, ‖orderedDerivative w g x‖ₑ ^ 2 =
      ENNReal.ofReal (‖orderedDerivative w g x‖ ^ 2) := fun w => enorm_sq_eq_ofReal' _
  simp_rw [e]
  rw [enorm_sq_eq_ofReal', ← ENNReal.ofReal_sum_of_nonneg fun w _ => by positivity,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

theorem lintegral_iteratedFDeriv_sq_le_classicalGradFactorialSq (m q : ℕ) (hq1 : 1 ≤ q)
    (hqm : q ≤ m + 1) {g : Vec 2 → F} (hg : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) g) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ENNReal.ofReal (ρ ^ (2 * q)) * ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ q g x‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 ^ q * ((q - 1).factorial : ℝ) ^ 2 * ρ ^ 2) *
        classicalGradFactorialSq ρ m g := by
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  have hjm : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hg' : ContDiff ℝ ((j + 1 : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast hqm)
  have h1 := lintegral_iteratedFDeriv_sq_le_words hg'
  have h2 : ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∑ w : DerivativeWord2 (j + 1), ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2 ≤
      classicalGradFactorialSq ρ m g :=
    Finset.single_le_sum (f := fun j => ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∑ w : DerivativeWord2 (j + 1), ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2)
      (fun _ _ => bot_le) hjm
  have hfac : (0 : ℝ) < ((j.factorial : ℝ)) ^ 2 := by positivity
  have hcoef : ρ ^ (2 * (j + 1)) * 2 ^ (j + 1) =
      (2 ^ (j + 1) * ((j + 1 - 1).factorial : ℝ) ^ 2 * ρ ^ 2) *
        (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) := by
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  calc ENNReal.ofReal (ρ ^ (2 * (j + 1))) *
        ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ (j + 1) g x‖ₑ ^ 2
      ≤ ENNReal.ofReal (ρ ^ (2 * (j + 1))) * (ENNReal.ofReal (2 ^ (j + 1)) *
          ∑ w : DerivativeWord2 (j + 1),
            ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2) := by gcongr
    _ = ENNReal.ofReal ((2 ^ (j + 1) * ((j + 1 - 1).factorial : ℝ) ^ 2 * ρ ^ 2) *
          (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2)) *
          ∑ w : DerivativeWord2 (j + 1),
            ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← hcoef]
    _ = ENNReal.ofReal (2 ^ (j + 1) * ((j + 1 - 1).factorial : ℝ) ^ 2 * ρ ^ 2) *
          (ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
          ∑ w : DerivativeWord2 (j + 1),
            ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ _ := by gcongr

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Leibniz bound for the slow jets of a lift action. -/

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem contDiff_orderedDerivative_comp {p M m : ℕ} (hm : m ≤ M) (α : DerivativeWord2 m)
    {a : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) a) (u : ι) :
    ContDiff ℝ (p : ℕ∞) (fun X' => orderedDerivative α a X' u) := by
  have h1 : ContDiff ℝ ((p + m : ℕ) : ℕ∞) a := ha.of_le (by exact_mod_cast Nat.add_le_add_left hm p)
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp
    (contDiff_orderedDerivative α h1)

theorem contDiff_liftApply {M p : ℕ} (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (y : Vec 2) (v : ι)
    (hc : ∀ m α u, ContDiff ℝ (p : ℕ∞) (fun X => c m α t X y v u))
    (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (a t)) :
    ContDiff ℝ (p : ℕ∞) (fun X' => liftApply M c a t X' y v) := by
  show ContDiff ℝ (p : ℕ∞) (fun X' => ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m,
    ∑ u : ι, c m α t X' y v u (orderedDerivative α (a t) X' u))
  refine ContDiff.sum fun m hm => ContDiff.sum fun α _ => ContDiff.sum fun u _ => ?_
  exact (hc m α u).clm_apply (contDiff_orderedDerivative_comp
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) α ha u)

theorem norm_iteratedFDeriv_sum_le' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : Type*} (s : Finset κ) {f : κ → E → F} {p : ℕ}
    (hf : ∀ j ∈ s, ContDiff ℝ (p : ℕ∞) (f j)) (x : E) :
    ‖iteratedFDeriv ℝ p (fun z => ∑ j ∈ s, f j z) x‖ ≤
      ∑ j ∈ s, ‖iteratedFDeriv ℝ p (f j) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply fun j hj => (hf j hj).contDiffAt]
  exact norm_sum_le _ _

theorem norm_iteratedFDeriv_liftApply_le (M p : ℕ) (c : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (y : Vec 2) (v : ι)
    (hc : ∀ m α u, ContDiff ℝ (p : ℕ∞) (fun X => c m α t X y v u))
    (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (a t)) (X : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun X' => liftApply M c a t X' y v) X‖ ≤
      ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m, ∑ u : ι, ∑ i ∈ Finset.range (p + 1),
        (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun X' => c m α t X' y v u) X‖ *
          ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a t X' u) X‖ := by
  have hg : ∀ m, m ≤ M → ∀ (α : DerivativeWord2 m) u,
      ContDiff ℝ (p : ℕ∞) (fun X' => orderedDerivative α (a t) X' u) := fun m hm α u =>
    contDiff_orderedDerivative_comp hm α ha u
  have hterm : ∀ m, m ≤ M → ∀ (α : DerivativeWord2 m) (u : ι),
      ContDiff ℝ (p : ℕ∞) (fun X' => c m α t X' y v u (orderedDerivative α (a t) X' u)) :=
    fun m hm α u => (hc m α u).clm_apply (hg m hm α u)
  have hmem : ∀ m ∈ Finset.range (M + 1), m ≤ M := fun m hm =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  show ‖iteratedFDeriv ℝ p (fun X' => ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m,
    ∑ u : ι, c m α t X' y v u (orderedDerivative α (a t) X' u)) X‖ ≤ _
  refine (norm_iteratedFDeriv_sum_le' _ (fun m hm => ContDiff.sum fun α _ =>
    ContDiff.sum fun u _ => hterm m (hmem m hm) α u) X).trans ?_
  refine Finset.sum_le_sum fun m hm => ?_
  refine (norm_iteratedFDeriv_sum_le' _ (fun α _ => ContDiff.sum fun u _ =>
    hterm m (hmem m hm) α u) X).trans ?_
  refine Finset.sum_le_sum fun α _ => ?_
  refine (norm_iteratedFDeriv_sum_le' _ (fun u _ => hterm m (hmem m hm) α u) X).trans ?_
  refine Finset.sum_le_sum fun u _ => ?_
  refine (norm_iteratedFDeriv_clm_apply (hc m α u) (hg m (hmem m hm) α u) X le_rfl).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hip : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hmM : m ≤ M := hmem m hm
  have hau : ContDiff ℝ ((p - i + m : ℕ) : ℕ∞) (fun X' => a t X' u) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp ha).of_le
      (by exact_mod_cast (by omega : p - i + m ≤ p + M))
  have hcomm : (fun X' => orderedDerivative α (a t) X' u) =
      orderedDerivative α (fun X' => a t X' u) := by
    have := orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u) α
      ((ha.of_le (by exact_mod_cast (by omega : m ≤ p + M))))
    funext X'
    exact (congrFun this X').symm
  rw [hcomm]
  have := norm_iteratedFDeriv_orderedDerivative_le (p := p - i) α hau X
  gcongr

end Lift

end AVRegularity
end
