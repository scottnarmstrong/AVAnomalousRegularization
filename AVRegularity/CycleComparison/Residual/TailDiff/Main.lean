-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
public import AVRegularity.CycleComparison.Residual.BoundPointwise
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.Residual.CoarseFlux
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Residual.FastJets.Chain
import AVRegularity.CycleComparison.Residual.Jets.Lift

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.TailDiff

/-! The conditional differentiated tail residual estimate (D1, part (b)).

This is the statement of `cycle_residual_differentiated` with the constructed tail presentation
replaced by its consequences that the estimate uses: box smoothness through slow order
`Acl + 2 + r` and fast order `r + 1`, periodicity, vanishing at order zero, and mixed slow/fast
Schur jets bounded by `S`. The constant `K` depends only on `Acl N D r`. -/

/-- The differentiated cell-tail reconstruction from mixed jets of the tail arrays. -/
def Statement (Acl N D r : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (π : ι → ℝ) (t₀ t₁ e ν B ρ rs ℓ εc S : ℝ) (sZ kres : ℕ),
      (∀ v, 0 < π v) → t₀ ≤ t₁ → 0 < e → 0 < ν → 0 < B → 0 < ρ → 0 < rs → rs ≤ e → e ≤ ρ →
      (∃ M : ℕ, e⁻¹ = (M : ℝ)) → ℓ = e / Real.sqrt ν → εc = ℓ * Real.sqrt B / ρ → εc ≤ 1 →
      0 ≤ S → r + 1 ≤ sZ → kres = 4 * (N + D) + 2 * Acl + 16 →
      ∀ (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h),
        (∀ n, N + 1 ≤ n → n ≤ 2 * N + D → ∀ τ ∈ Set.Icc t₀ t₁,
          (∀ m α v u, IsBoxSmooth (Acl + 2 + r) (r + 1) (fun X y => f n m α τ X y v u)) ∧
          (∀ k m α v u, IsBoxSmooth (Acl + 2 + r) (r + 1) (fun X y => F n k m α τ X y v u)) ∧
          (∀ m α v u X, AVenhance.IsZ2Periodic (fun z => f n m α τ X z v u)) ∧
          (∀ k m α v u X, AVenhance.IsZ2Periodic (fun z => F n k m α τ X z v u))) →
        (∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
          (∀ α t X z v u, f n 0 α t X z v u = 0) ∧ ∀ k α t X z v u, F n k 0 α t X z v u = 0) →
        (∀ n, N + 1 ≤ n → n ≤ 2 * N + D → ∀ b, b ≤ r → ∀ δ : DerivativeWord2 b,
          ∀ i, i ≤ Acl + 2 + r → ∀ m,
            MixedTail.schurMixedJet π (Set.Icc t₀ t₁) i δ (f n m) ≤ ENNReal.ofReal S ∧
            MixedTail.schurMixedJet π (Set.Icc t₀ t₁) i δ
              (fun q : DerivativeWord2 m × Fin 2 => F n q.2 m q.1) ≤ ENNReal.ofReal S) →
      ∀ a : ℝ → Vec 2 → ∀ i, h i,
        (∀ t, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t)) →
        (∀ j, j ≤ kres + r + 1 → ∀ (w : DerivativeWord2 j) (v : ι), Measurable
          (fun p : ℝ × Vec 2 => ‖orderedDerivative w (fun x => a p.1 x v) p.2‖ₑ)) →
      ∀ Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
        (∀ τ ∈ Set.Icc t₀ t₁,
          IsCleanupChain (Acl + 2 + r) sZ Acl
            (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ)
            (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) (fun j => Vc j τ)) →
      ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
        ∀ (j : ℕ), j ≤ r → ∀ β : DerivativeWord2 j,
        residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
            (fun t x k => rs ^ j • orderedDerivative β
              (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl Vc t x' k) x)
            (fun t x => rs ^ j • orderedDerivative β
              (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl Vc t x') x)
          ≤ ENNReal.ofReal (K * S * εc ^ N * (1 + Z)) *
            classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) (kres + r) a

end AVRegularity.TailDiff
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.TailDiff

/-! Differentiated tail residual: monotonicity of cleanup chains in the orders, and the word
derivatives of the sampled cleanup flux and remainder of a chain with a nonzero initial flux, in
terms of the mixed pair jets `vecJetF F₀ + scalJetF f₀` of the initial pair. -/

section
section Mono

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A cell antidivergence of orders `(sX, sZ)` is one of all lower orders. -/
theorem isCellAntidivergence_mono {sX sZ sX' sZ' : ℕ} (hX : sX' ≤ sX) (hZ : sZ' ≤ sZ)
    {f : Vec 2 → Vec 2 → E} {V : Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCellAntidivergence sX sZ f V) : IsCellAntidivergence sX' sZ' f V := by
  obtain ⟨hVbox, hVper, φ, hφbox, hφper, hφmean, hVφ, hdiv⟩ := hV
  exact ⟨hVbox.mono hX hZ, hVper, φ, hφbox.mono hX (by omega), hφper, hφmean, hVφ, hdiv⟩

/-- A cleanup chain of orders `(sX, sZ)` is one of all lower orders. -/
theorem isCleanupChain_mono {sX sZ sX' sZ' A : ℕ} (hX : sX' ≤ sX) (hZ : sZ' ≤ sZ)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E} (hV : IsCleanupChain sX sZ A f₀ F₀ V) :
    IsCleanupChain sX' sZ' A f₀ F₀ V := by
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  exact ⟨⟨W₀, isCellAntidivergence_mono hX hZ hW₀, hV0⟩,
    fun j h1 h2 => isCellAntidivergence_mono hX hZ (hVj j h1 h2)⟩

/-- Box smoothness of a field with values in a finite product, from that of its components. -/
theorem isBoxSmooth_pi {κ : Type*} [Fintype κ] {H : κ → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)] {sX sZ : ℕ}
    {f : Vec 2 → Vec 2 → ∀ i, H i} (hf : ∀ i, IsBoxSmooth sX sZ (fun X z => f X z i)) :
    IsBoxSmooth sX sZ f := by
  classical
  have he : f = fun X z => ∑ i, (ContinuousLinearMap.single ℝ H i) (f X z i) := by
    funext X z
    ext j
    simp [Finset.sum_apply]
  rw [he]
  exact IsBoxSmooth.sum Finset.univ fun i _ =>
    (hf i).clm_comp (ContinuousLinearMap.single ℝ H i)

/-- The mixed pair jet `vecJetF F₀ + scalJetF f₀` of the initial pair of a cleanup chain. -/
def pairF (f₀ : Vec 2 → Vec 2 → E) (F₀ : Vec 2 → Vec 2 → Fin 2 → E) (p : ℕ) {b : ℕ}
    (δ : DerivativeWord2 b) (X : Vec 2) : ℝ≥0∞ :=
  FastJets.vecJetF F₀ p δ X + FastJets.scalJetF f₀ p δ X

end Mono

section Chain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A cleanup chain of a box-smooth periodic initial flux, at fast order `r + 1`. -/
structure ChainData (sX A r : ℕ) (f₀ : Vec 2 → Vec 2 → E) (F₀ : Vec 2 → Vec 2 → Fin 2 → E)
    (V : ℕ → Vec 2 → Vec 2 → Fin 2 → E) : Prop where
  hA : 1 ≤ A
  hsX : A + 2 + r ≤ sX
  box : IsBoxSmooth sX (r + 1) F₀
  per : ∀ X, AVenhance.IsZ2Periodic (F₀ X)
  chain : IsCleanupChain sX (r + 1) A f₀ F₀ V

namespace ChainData

variable {sX A r : ℕ} {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
  {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}

/-- The first member of the chain is controlled by the pair jet. -/
theorem zero_le (hd : ChainData sX A r f₀ F₀ V) {b : ℕ} (hb : b ≤ r) (δ : DerivativeWord2 b)
    {q : ℕ} (hq : q ≤ sX) (X : Vec 2) :
    FastJets.vecJetF (V 0) q δ X ≤ 2 * pairF f₀ F₀ q δ X := by
  refine (FastJets.vecJetF_cleanupChain_zero_le δ (by omega) hd.box hd.chain hq X).trans ?_
  unfold pairF
  rw [mul_add]
  gcongr
  calc antidivConst * FastJets.scalJetF f₀ q δ X ≤ 1 * FastJets.scalJetF f₀ q δ X := by
        gcongr; exact antidivConst_le_one
    _ = _ := one_mul _

/-- Every member of the chain is controlled by the pair jet of a higher order. -/
theorem member_le (hd : ChainData sX A r f₀ F₀ V) {j' : ℕ} (hj' : j' < A) {b : ℕ} (hb : b ≤ r)
    (δ : DerivativeWord2 b) {q : ℕ} (hq : q + j' ≤ sX) (X : Vec 2) :
    FastJets.vecJetF (V j') q δ X ≤ 2 * pairF f₀ F₀ (q + j') δ X := by
  calc FastJets.vecJetF (V j') q δ X
      ≤ (2 * antidivConst) ^ j' * FastJets.vecJetF (V 0) (q + j') δ X :=
        FastJets.vecJetF_cleanupChain_le δ (by omega) hd.box hd.chain j' hj' q hq X
    _ ≤ 1 * FastJets.vecJetF (V 0) (q + j') δ X := by
        gcongr; exact pow_le_one₀ bot_le two_mul_antidivConst_le_one
    _ = FastJets.vecJetF (V 0) (q + j') δ X := one_mul _
    _ ≤ _ := hd.zero_le hb δ hq X

/-- One member of the chain: its mixed jets in a window of three orders. -/
theorem flux_member (hd : ChainData sX A r f₀ F₀ V) {j' : ℕ} (hj' : j' < A) {a b : ℕ}
    (ha : a ≤ r) (hb : b ≤ r) (δ : DerivativeWord2 b) (ρ : ℝ) :
    ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, FastJets.vecJetF (V j') (a + m) δ X
      ≤ 2 * ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X := by
  have hsX := hd.hsX
  calc ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, FastJets.vecJetF (V j') (a + m) δ X
      ≤ ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, 2 * pairF f₀ F₀ (m + (a + j')) δ X := by
        refine Finset.sum_le_sum fun m hm => lintegral_mono fun X => ?_
        have hm3 := Finset.mem_range.1 hm
        rw [show m + (a + j') = a + m + j' by omega]
        exact hd.member_le hj' hb δ (by omega) X
    _ = 2 * ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, pairF f₀ F₀ (m + (a + j')) δ X := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)
    _ ≤ _ := by
        gcongr
        exact sum_range_shift_le (fun p => ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X) (by omega)

/-- One member of the chain: the `L²` norm of the weighted word derivative of its sample. -/
theorem flux_member_word (hd : ChainData sX A r f₀ F₀ V) {j' : ℕ} (hj' : j' < A) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e)
    (heρ : e ≤ ρ) {M : ℕ} (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2
      ≤ 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        ∑ δ : DerivativeWord2 ab.2,
          2 * ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X := by
  have hsX := hd.hsX
  have hbox := IsCleanupChain.isBoxSmooth hd.box hd.chain j' hj'
  have hW : IsBoxSmooth (j + 2) j (V j') := hbox.mono (by omega) (by omega)
  have hper : ∀ X, AVenhance.IsZ2Periodic (V j' X) :=
    IsCleanupChain.periodic hd.per hd.chain j' hj'
  refine (CoarseFluxDiff.sampled_word_vec_le β hW hper hrs hrse heρ M hM).trans ?_
  gcongr with ab hab δ _
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  exact hd.flux_member hj' (by omega) (by omega) δ ρ

/-- The weighted word derivative of the sampled cleanup flux of the chain. -/
theorem flux_word_component (hd : ChainData sX A r f₀ F₀ V) {j : ℕ} (hj : j ≤ r)
    (β : DerivativeWord2 j) {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) {M : ℕ}
    (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x)‖ₑ ^ 2
      ≤ (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) *
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          2 * ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X := by
  have hsX := hd.hsX
  have he : 0 < e := hrs.trans_le hrse
  have hρ : 0 < ρ := he.trans_le heρ
  have hϑ0 : 0 ≤ e / ρ := div_nonneg he.le hρ.le
  have hϑ1 : e / ρ ≤ 1 := (div_le_one hρ).2 heρ
  have hbox := IsCleanupChain.isBoxSmooth hd.box hd.chain
  have hmeas : ∀ j' ∈ Finset.range A, Measurable fun x : Vec 2 => ∑ k : Fin 2,
      ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2 := by
    intro j' hj'
    refine Finset.measurable_sum _ fun k _ => ?_
    exact CoarseFluxDiff.measurable_sampled_word β (W := fun X y => V j' X y k)
      ((hbox j' (Finset.mem_range.1 hj')).clm_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k))
      (by omega) (by omega) ρ e _
  have hpt : ∀ x : Vec 2, ∑ k : Fin 2,
      ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
        (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x)‖ₑ ^ 2 ≤
      (A : ℝ≥0∞) * ∑ j' ∈ Finset.range A, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2 := by
    intro x
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    exact CoarseFluxDiff.enorm_sq_sum_pow_smul_le A hϑ0 hϑ1 _
  calc ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x)‖ₑ ^ 2
      ≤ ∫⁻ x in AVenhance.unitCube, (A : ℝ≥0∞) * ∑ j' ∈ Finset.range A, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = (A : ℝ≥0∞) * ∑ j' ∈ Finset.range A, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ hmeas]
    _ ≤ (A : ℝ≥0∞) * ∑ _j' ∈ Finset.range A, 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) *
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          2 * ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X := by
        gcongr with j' hj'
        exact hd.flux_member_word (Finset.mem_range.1 hj') hj β hrs hrse heρ hM
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- The source of the chain: its mixed jets in a window of three orders. -/
theorem rem_member (hd : ChainData sX A r f₀ F₀ V) {a b : ℕ} (ha : a ≤ r) (hb : b ≤ r)
    (δ : DerivativeWord2 b) (ρ : ℝ) :
    ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (cleanupSource V A) (a + m) δ X
      ≤ 4 * ∑ p ∈ Finset.range (A + r + 3), ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X := by
  have hsX := hd.hsX
  have hA := hd.hA
  calc ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (cleanupSource V A) (a + m) δ X
      ≤ ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, 4 * pairF f₀ F₀ (m + (a + A)) δ X := by
        refine Finset.sum_le_sum fun m hm => lintegral_mono fun X => ?_
        have hm3 := Finset.mem_range.1 hm
        calc FastJets.scalJetF (cleanupSource V A) (a + m) δ X
            ≤ 2 * ((2 * antidivConst) ^ (A - 1) * FastJets.vecJetF (V 0) (a + m + A) δ X) :=
              FastJets.scalJetF_cleanupChain_remainder_le δ (by omega) hA hd.box hd.chain
                (m := a + m) (by omega) X
          _ ≤ 2 * (1 * FastJets.vecJetF (V 0) (a + m + A) δ X) := by
              gcongr; exact pow_le_one₀ bot_le two_mul_antidivConst_le_one
          _ ≤ 2 * (2 * pairF f₀ F₀ (a + m + A) δ X) := by
              rw [one_mul]
              gcongr
              exact hd.zero_le hb δ (by omega) X
          _ = 4 * pairF f₀ F₀ (m + (a + A)) δ X := by
              rw [show m + (a + A) = a + m + A by omega, ← mul_assoc]
              norm_num
    _ = 4 * ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, pairF f₀ F₀ (m + (a + A)) δ X := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)
    _ ≤ _ := by
        gcongr
        exact sum_range_shift_le (fun p => ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X) (by omega)

/-- The weighted word derivative of the sampled cleanup source of the chain. -/
theorem rem_word_component (hd : ChainData sX A r f₀ F₀ V) {j : ℕ} (hj : j ≤ r)
    (β : DerivativeWord2 j) {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) {M : ℕ}
    (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x')) x‖ₑ ^ 2
      ≤ 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        ∑ δ : DerivativeWord2 ab.2,
          4 * ∑ p ∈ Finset.range (A + r + 3), ∫⁻ X in slowCell ρ, pairF f₀ F₀ p δ X := by
  have hsX := hd.hsX
  have hA := hd.hA
  have hV : IsBoxSmooth (j + 2 + 1) (r + 1) (V (A - 1)) :=
    (IsCleanupChain.isBoxSmooth hd.box hd.chain (A - 1) (by omega)).mono (by omega) le_rfl
  have hW : IsBoxSmooth (j + 2) j (cleanupSource V A) :=
    (CoarseFluxDiff.isBoxSmooth_cleanupSource hV).mono le_rfl (by omega)
  have hper : ∀ X, AVenhance.IsZ2Periodic (cleanupSource V A X) := fun X =>
    cleanupSource_periodic (IsCleanupChain.periodic hd.per hd.chain (A - 1) (by omega)) X
  refine (FastJets.lintegral_rs_odL_diag_sq_le β hW hper hrs hrse heρ M hM).trans ?_
  gcongr with ab hab δ _
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  exact hd.rem_member (by omega) (by omega) δ ρ

end ChainData

end Chain
end

/-! Differentiated tail residual: a fast word `δ` of the divided tail fields `f_a, F_a` is the
divided tail of the fast-differentiated presentation arrays `fastCoeff δ f_n, fastCoeff δ F_n`
(the coarse field is fast independent). The mixed pair jets of the tail fields are therefore the
pair jets of a divided tail, and the order-zero slow-cell bound `slowCell_tail_pairJet_le` applies
with the mixed Schur jets of the arrays. -/

section
section Fast

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Fast smoothness of a component of a lift action. -/
theorem contDiff_liftApply_fast {b : ℕ} (M : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    (τ : ℝ) (X : Vec 2) (v : ι) (hc : ∀ m α u, ContDiff ℝ (b : ℕ∞) (fun y => c m α τ X y v u)) :
    ContDiff ℝ (b : ℕ∞) (fun y => liftApply M c a τ X y v) := by
  show ContDiff ℝ (b : ℕ∞) (fun y => ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m,
    ∑ u, c m α τ X y v u (orderedDerivative α (a τ) X u))
  exact ContDiff.sum fun m _ => ContDiff.sum fun α _ => ContDiff.sum fun u _ =>
    (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (a τ) X u)).contDiff.comp (hc m α u)

/-- The fast word of a finite combination of lift actions falls on the coefficients. -/
theorem orderedDerivative_sum_liftApply {b : ℕ} (δ : DerivativeWord2 b) (s : Finset ℕ)
    (w : ℕ → ℝ) (M : ℕ) (c : ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (X : Vec 2)
    (v : ι) (hc : ∀ n ∈ s, ∀ m α v u, ContDiff ℝ (b : ℕ∞) (fun y => c n m α τ X y v u))
    (y : Vec 2) :
    orderedDerivative δ (fun y' => ∑ n ∈ s, w n • liftApply M (c n) a τ X y' v) y =
      ∑ n ∈ s, w n • liftApply M (MixedTail.fastCoeff δ (c n)) a τ X y v := by
  have hn : ∀ n ∈ s, ContDiff ℝ (b : ℕ∞) (fun y' => liftApply M (c n) a τ X y' v) :=
    fun n hn => contDiff_liftApply_fast M (c n) a τ X v fun m α u => hc n hn m α v u
  rw [congrFun (MixedTail.orderedDerivative_sum s δ
    (g := fun n y' => w n • liftApply M (c n) a τ X y' v)
    fun n hn' => (hn n hn').const_smul (w n)) y]
  refine Finset.sum_congr rfl fun n hn' => ?_
  rw [congrFun (CoarseFluxDiff.orderedDerivative_const_smul δ (w n) (hn n hn')) y,
    MixedTail.liftApply_fastCoeff δ M (c n) a τ X (hc n hn') y v]

/-- The fast word of the tail scalar field is the tail scalar field of the fast word. -/
theorem fast_tailScalarField {b : ℕ} (δ : DerivativeWord2 b) (f : ℕ → LiftCoeff ι h) (N D : ℕ)
    (εc : ℝ) (ac : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (X : Vec 2)
    (hf : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ m α v u,
      ContDiff ℝ (b : ℕ∞) (fun y => f n m α τ X y v u)) (y : Vec 2) (v : ι) :
    orderedDerivative δ (fun y' => tailScalarField f N D εc ac τ X y' v) y =
      tailScalarField (fun n => MixedTail.fastCoeff δ (f n)) N D εc ac τ X y v := by
  have e1 : (fun y' => tailScalarField f N D εc ac τ X y' v) = fun y' =>
      ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
        εc ^ (n - N - 1) • liftApply (2 * N + D) (f n) ac τ X y' v := by
    funext y'
    simp only [tailScalarField, Finset.sum_apply, Pi.smul_apply]
  rw [e1, orderedDerivative_sum_liftApply δ _ _ _ f ac τ X v hf y]
  simp only [tailScalarField, Finset.sum_apply, Pi.smul_apply]

/-- The fast word of the tail flux field is the tail flux field of the fast word. -/
theorem fast_tailFluxField {b : ℕ} (δ : DerivativeWord2 b) (F : ℕ → Fin 2 → LiftCoeff ι h)
    (N D : ℕ) (εc : ℝ) (ac : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (X : Vec 2) (k : Fin 2)
    (hF : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ m α v u,
      ContDiff ℝ (b : ℕ∞) (fun y => F n k m α τ X y v u)) (y : Vec 2) (v : ι) :
    orderedDerivative δ (fun y' => tailFluxField F N D εc ac τ X y' k v) y =
      tailFluxField (fun n k => MixedTail.fastCoeff δ (F n k)) N D εc ac τ X y k v := by
  have e1 : (fun y' => tailFluxField F N D εc ac τ X y' k v) = fun y' =>
      ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
        εc ^ (n - N - 1) • liftApply (2 * N + D) (F n k) ac τ X y' v := by
    funext y'
    simp only [tailFluxField, Finset.sum_apply, Pi.smul_apply]
  rw [e1, orderedDerivative_sum_liftApply δ _ _ _ (fun n => F n k) ac τ X v hF y]
  simp only [tailFluxField, Finset.sum_apply, Pi.smul_apply]

/-- The scalar mixed jet of the tail scalar field. -/
theorem scalJetF_tail_eq {b : ℕ} (δ : DerivativeWord2 b) (f : ℕ → LiftCoeff ι h) (N D : ℕ)
    (εc : ℝ) (ac : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ)
    (hf : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ m α v u X,
      ContDiff ℝ (b : ℕ∞) (fun y => f n m α τ X y v u)) (p : ℕ) (v : ι) (X : Vec 2) :
    FastJets.scalJetF (fun X y => tailScalarField f N D εc ac τ X y v) p δ X =
      scalJet (fun X y => tailScalarField (fun n => MixedTail.fastCoeff δ (f n)) N D εc ac τ X y v)
        p X := by
  have hg : (fun X y => orderedDerivative δ (fun y' => tailScalarField f N D εc ac τ X y' v) y) =
      fun X y => tailScalarField (fun n => MixedTail.fastCoeff δ (f n)) N D εc ac τ X y v :=
    funext fun X => funext fun y =>
      fast_tailScalarField δ f N D εc ac τ X (fun n hn m α v u => hf n hn m α v u X) y v
  show scalJet (fun X y => orderedDerivative δ (fun y' => tailScalarField f N D εc ac τ X y' v) y)
    p X = _
  rw [hg]

/-- The vector mixed jet of the tail flux field. -/
theorem vecJetF_tail_eq {b : ℕ} (δ : DerivativeWord2 b) (F : ℕ → Fin 2 → LiftCoeff ι h)
    (N D : ℕ) (εc : ℝ) (ac : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ)
    (hF : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ k m α v u X,
      ContDiff ℝ (b : ℕ∞) (fun y => F n k m α τ X y v u)) (p : ℕ) (v : ι) (X : Vec 2) :
    FastJets.vecJetF (fun X y k => tailFluxField F N D εc ac τ X y k v) p δ X =
      vecJet (fun X y k => tailFluxField (fun n k => MixedTail.fastCoeff δ (F n k)) N D εc ac τ
        X y k v) p X := by
  have hg : (fun X y k => orderedDerivative δ (fun y' => tailFluxField F N D εc ac τ X y' k v) y) =
      fun X y k => tailFluxField (fun n k => MixedTail.fastCoeff δ (F n k)) N D εc ac τ X y k v :=
    funext fun X => funext fun y => funext fun k =>
      fast_tailFluxField δ F N D εc ac τ X k (fun n hn m α v u => hF n hn k m α v u X) y v
  show vecJet (fun X y k => orderedDerivative δ
    (fun y' => tailFluxField F N D εc ac τ X y' k v) y) p X = _
  rw [hg]

end Fast

section Pair

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The Schur cell jet of the fast word of an array is its mixed Schur jet. -/
theorem schurCellL2Jet_fastCoeff (π : ι → ℝ) (I : Set ℝ) (i : ℕ) {b : ℕ}
    (δ : DerivativeWord2 b) (c : LiftCoeff ι h) (m : ℕ) :
    schurCellL2Jet π I i (MixedTail.fastCoeff δ c m) = MixedTail.schurMixedJet π I i δ (c m) :=
  rfl

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The flux version of `schurCellL2Jet_fastCoeff`. -/
theorem schurCellL2Jet_fastCoeff_flux (π : ι → ℝ) (I : Set ℝ) (i : ℕ) {b : ℕ}
    (δ : DerivativeWord2 b) (F : Fin 2 → LiftCoeff ι h) (m : ℕ) :
    schurCellL2Jet π I i
        (fun q : DerivativeWord2 m × Fin 2 => MixedTail.fastCoeff δ (F q.2) m q.1) =
      MixedTail.schurMixedJet π I i δ (fun q : DerivativeWord2 m × Fin 2 => F q.2 m q.1) :=
  rfl

/-- The mass-weighted slow-cell mixed pair jets of the divided tail fields at one time. -/
theorem sum_slowCell_pairF_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (N D p : ℕ) {b : ℕ}
    (δ : DerivativeWord2 b) (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h) (εc : ℝ)
    (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1) (a : ℝ → Vec 2 → ∀ i, h i) (ℓ ρ : ℝ) (hρ : 0 < ρ) (t : ℝ)
    {τ : ℝ} (hτ : τ ∈ I) (hτt : ℓ ^ 2 * τ = t) (S : ℝ)
    (hbox : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ m α v u, IsBoxSmooth p b (fun X y => f n m α τ X y v u)) ∧
        ∀ k m α v u, IsBoxSmooth p b (fun X y => F n k m α τ X y v u))
    (hzero : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ α t X z v u, f n 0 α t X z v u = 0) ∧ ∀ k α t X z v u, F n k 0 α t X z v u = 0)
    (hjet : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ i, i ≤ p → ∀ m,
      MixedTail.schurMixedJet π I i δ (f n m) ≤ ENNReal.ofReal S ∧
        MixedTail.schurMixedJet π I i δ (fun q : DerivativeWord2 m × Fin 2 => F n q.2 m q.1)
          ≤ ENNReal.ofReal S)
    (m : ℕ) (hpm : p + (2 * N + D) ≤ m + 1) (ha : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (a t)) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
        pairF (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
          (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X
      ≤ ENNReal.ofReal (tailPairConst N D p * coarseJetConst (p + (2 * N + D))) *
          ENNReal.ofReal S ^ 2 *
          ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalGradFactorialSq ρ m (fun x => a t x u) := by
  have hf : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ m α v u X,
      ContDiff ℝ (b : ℕ∞) (fun y => f n m α τ X y v u) :=
    fun n hn m α v u X => ((hbox n hn).1 m α v u).1 X
  have hF : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ k m α v u X,
      ContDiff ℝ (b : ℕ∞) (fun y => F n k m α τ X y v u) :=
    fun n hn k m α v u X => ((hbox n hn).2 k m α v u).1 X
  have heq : ∀ v X, pairF
      (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
      (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X =
      pairJet (fun X y => tailScalarField (fun n => MixedTail.fastCoeff δ (f n)) N D εc
          (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
        (fun X y k => tailFluxField (fun n k => MixedTail.fastCoeff δ (F n k)) N D εc
          (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p X := by
    intro v X
    unfold pairF pairJet
    rw [scalJetF_tail_eq δ f N D εc _ τ hf p v X, vecJetF_tail_eq δ F N D εc _ τ hF p v X]
  have hbox' : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ m α v u, IsBoxSmooth p 0 (fun X y => MixedTail.fastCoeff δ (f n) m α τ X y v u)) ∧
        ∀ k m α v u, IsBoxSmooth p 0 (fun X y => MixedTail.fastCoeff δ (F n k) m α τ X y v u) :=
    fun n hn =>
    ⟨fun m α v u => FastJets.isBoxSmooth_fastL (sX := p) (sZ := 0) (List.ofFn δ)
        (F := fun X y => f n m α τ X y v u) (by simpa using (hbox n hn).1 m α v u),
      fun k m α v u => FastJets.isBoxSmooth_fastL (sX := p) (sZ := 0) (List.ofFn δ)
        (F := fun X y => F n k m α τ X y v u) (by simpa using (hbox n hn).2 k m α v u)⟩
  have hzero' : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ α t X z v u, MixedTail.fastCoeff δ (f n) 0 α t X z v u = 0) ∧
        ∀ k α t X z v u, MixedTail.fastCoeff δ (F n k) 0 α t X z v u = 0 := by
    intro n hn
    refine ⟨fun α t X z v u => ?_, fun k α t X z v u => ?_⟩
    · have h0 : (fun z' => f n 0 α t X z' v u) = fun _ => 0 :=
        funext fun z' => (hzero n hn).1 α t X z' v u
      show orderedDerivative δ (fun z' => f n 0 α t X z' v u) z = 0
      rw [h0, orderedDerivative_const_zero]
    · have h0 : (fun z' => F n k 0 α t X z' v u) = fun _ => 0 :=
        funext fun z' => (hzero n hn).2 k α t X z' v u
      show orderedDerivative δ (fun z' => F n k 0 α t X z' v u) z = 0
      rw [h0, orderedDerivative_const_zero]
  have hjet' : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ i, i ≤ p → ∀ m,
      schurCellL2Jet π I i (MixedTail.fastCoeff δ (f n) m) ≤ ENNReal.ofReal S ∧
        schurCellL2Jet π I i
          (fun q : DerivativeWord2 m × Fin 2 => MixedTail.fastCoeff δ (F n q.2) m q.1)
          ≤ ENNReal.ofReal S := fun n hn i hi m =>
    ⟨(schurCellL2Jet_fastCoeff π I i δ (f n) m).trans_le (hjet n hn i hi m).1,
      (schurCellL2Jet_fastCoeff_flux π I i δ (F n) m).trans_le (hjet n hn i hi m).2⟩
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
        pairF (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
          (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X
      = ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
          pairJet (fun X y => tailScalarField (fun n => MixedTail.fastCoeff δ (f n)) N D εc
              (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField (fun n k => MixedTail.fastCoeff δ (F n k)) N D εc
              (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p X :=
        Finset.sum_congr rfl fun v _ => by rw [lintegral_congr fun X => heq v X]
    _ ≤ ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
          pairJet (fun X y => tailScalarField (fun n => MixedTail.fastCoeff δ (f n)) N D εc
              (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField (fun n k => MixedTail.fastCoeff δ (F n k)) N D εc
              (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p X := by
        simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact sum_lintegral_le_lintegral_sum _ _
    _ ≤ _ := slowCell_tail_pairJet_le π hπ I N D p (fun n => MixedTail.fastCoeff δ (f n))
        (fun n k => MixedTail.fastCoeff δ (F n k)) εc hε0 hε1 a ℓ ρ hρ t hτ hτt S hbox' hzero'
        hjet' m hpm ha

end Pair
end

/-! Differentiated tail residual: the data of one cell time (the tail presentation arrays, the
physical field and a cleanup chain of the divided tail), and the mass-weighted bounds of the word
derivatives of the sampled cleanup flux and remainder by the gradient energy density. -/

section
/-- The constant of the word derivatives of the sampled cleanup flux. -/
def fluxConst (N D A r j : ℕ) : ℝ :=
  (A : ℝ) ^ 2 * 4 ^ j * 4 * 2 * CoarseFluxDiff.wordCount j * tailSumConst N D (A + r + 2)

/-- The constant of the word derivatives of the sampled cleanup remainder. -/
def remConst (N D A r j : ℕ) : ℝ :=
  4 ^ j * 4 * 4 * CoarseFluxDiff.wordCount j * tailSumConst N D (A + r + 3)

theorem fluxConst_nonneg (N D A r j : ℕ) : 0 ≤ fluxConst N D A r j :=
  mul_nonneg (mul_nonneg (by positivity) (CoarseFluxDiff.wordCount_nonneg j))
    (tailSumConst_nonneg N D _)

theorem remConst_nonneg (N D A r j : ℕ) : 0 ≤ remConst N D A r j :=
  mul_nonneg (mul_nonneg (by positivity) (CoarseFluxDiff.wordCount_nonneg j))
    (tailSumConst_nonneg N D _)

theorem ofReal_flux_split (A j : ℕ) (ρ x : ℝ) :
    ENNReal.ofReal ((A : ℝ) * ((A : ℝ) * ((4 : ℝ) ^ j * (4 * ρ ^ 2))) * x) =
      (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (A : ℝ) * ((A : ℝ) * ((4 : ℝ) ^ j * (4 * ρ ^ 2))) by
      positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ (A : ℝ) by positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ (A : ℝ) by positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ (4 : ℝ) ^ j by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (show (0 : ℝ) ≤ 4 by norm_num),
    ENNReal.ofReal_ofNat]

theorem ofReal_rem_split (j : ℕ) (ρ x : ℝ) :
    ENNReal.ofReal ((4 : ℝ) ^ j * (4 * ρ ^ 2) * x) =
      4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (4 : ℝ) ^ j * (4 * ρ ^ 2) by positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ (4 : ℝ) ^ j by positivity),
    ENNReal.ofReal_pow (show (0 : ℝ) ≤ 4 by norm_num), ENNReal.ofReal_ofNat]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The data of one cell time of the differentiated tail residual. -/
structure TailTime (π : ι → ℝ) (I : Set ℝ) (N D A r m : ℕ) (f : ℕ → LiftCoeff ι h)
    (F : ℕ → Fin 2 → LiftCoeff ι h) (εc : ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (ℓ ρ t τ S : ℝ)
    (V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) : Prop where
  mass_pos : ∀ v, 0 < π v
  ε_nonneg : 0 ≤ εc
  ε_le : εc ≤ 1
  ρ_pos : 0 < ρ
  τ_mem : τ ∈ I
  τ_eq : ℓ ^ 2 * τ = t
  hA : 1 ≤ A
  box : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
    (∀ m' α v u, IsBoxSmooth (A + 2 + r) (r + 1) (fun X y => f n m' α τ X y v u)) ∧
      ∀ k m' α v u, IsBoxSmooth (A + 2 + r) (r + 1) (fun X y => F n k m' α τ X y v u)
  per : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ k m' α v u X,
    AVenhance.IsZ2Periodic (fun z => F n k m' α τ X z v u)
  zero : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
    (∀ α t X z v u, f n 0 α t X z v u = 0) ∧ ∀ k α t X z v u, F n k 0 α t X z v u = 0
  jet : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ b, b ≤ r → ∀ δ : DerivativeWord2 b,
    ∀ i, i ≤ A + 2 + r → ∀ m',
      MixedTail.schurMixedJet π I i δ (f n m') ≤ ENNReal.ofReal S ∧
        MixedTail.schurMixedJet π I i δ (fun q : DerivativeWord2 m' × Fin 2 => F n q.2 m' q.1)
          ≤ ENNReal.ofReal S
  order : A + 2 + r + (2 * N + D) ≤ m + 1
  smooth : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (a t)
  chain : IsCleanupChain (A + 2 + r) (r + 1) A
    (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ)
    (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) V

namespace TailTime

variable {π : ι → ℝ} {I : Set ℝ} {N D A r m : ℕ} {f : ℕ → LiftCoeff ι h}
  {F : ℕ → Fin 2 → LiftCoeff ι h} {εc : ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {ℓ ρ t τ S : ℝ}
  {V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem ac_smooth (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) :
    ContDiff ℝ ((A + 2 + r + (2 * N + D) : ℕ) : ℕ∞) (fun X => a (ℓ ^ 2 * τ) (ρ • X)) := by
  rw [hd.τ_eq]
  exact (hd.smooth.comp (contDiff_const_smul ρ)).of_le (by exact_mod_cast hd.order)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- A component of the tail flux field is box smooth. -/
theorem flux_box_comp (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) (k : Fin 2) (v : ι) :
    IsBoxSmooth (A + 2 + r) (r + 1)
      (fun X y => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) := by
  have e : (fun X y => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) =
      fun X y => ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), εc ^ (n - N - 1) •
        liftApply (2 * N + D) (F n k) (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v := by
    funext X y
    simp only [tailFluxField, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  exact IsBoxSmooth.sum _ fun n hn =>
    (QuietDecay.Partition.isBoxSmooth_liftApply (2 * N + D) (A + 2 + r) (r + 1) (F n k) _ τ
      (fun m' α v u => (hd.box n hn).2 k m' α v u) hd.ac_smooth v).const_smul _

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The tail flux field is box smooth. -/
theorem flux_box (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) :
    IsBoxSmooth (A + 2 + r) (r + 1)
      (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) :=
  isBoxSmooth_pi (H := fun _ : Fin 2 => ∀ i, h i) fun k =>
    isBoxSmooth_pi (H := h) fun v => hd.flux_box_comp k v

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The chain projected on one component. -/
theorem chainData (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) (v : ι) :
    ChainData (A + 2 + r) A r
      (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
      (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
      (fun j X y k => V j X y k v) where
  hA := hd.hA
  hsX := le_rfl
  box := isBoxSmooth_pi (H := fun _ : Fin 2 => h v) fun k => hd.flux_box_comp k v
  per := fun X => by
    intro l y
    funext k
    exact congrFun (congrFun (tailFluxField_periodic F εc _ τ hd.per X l y) k) v
  chain := IsCleanupChain.clm_comp (by omega) (by omega) hd.flux_box.isSlowSmooth hd.chain
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

omit [∀ i, CompleteSpace (h i)] in
/-- The mass-weighted slow-cell mixed pair jets of one order. -/
theorem pairF_sum_le (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) {p : ℕ}
    (hp : p ≤ A + 2 + r) {b : ℕ} (hb : b ≤ r) (δ : DerivativeWord2 b) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
        pairF (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
          (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X
      ≤ ENNReal.ofReal (tailPairConst N D p * coarseJetConst (p + (2 * N + D))) *
          ENNReal.ofReal S ^ 2 * ResidualTimeData.gradDensity π ρ m a t :=
  sum_slowCell_pairF_le π hd.mass_pos I N D p δ f F εc hd.ε_nonneg hd.ε_le a ℓ ρ hd.ρ_pos t
    hd.τ_mem hd.τ_eq S
    (fun n hn => ⟨fun m' α v u => ((hd.box n hn).1 m' α v u).mono hp (by omega),
      fun k m' α v u => ((hd.box n hn).2 k m' α v u).mono hp (by omega)⟩)
    hd.zero (fun n hn i hi m' => hd.jet n hn b hb δ i (hi.trans hp) m') m
    (by have := hd.order; omega) hd.smooth

omit [∀ i, CompleteSpace (h i)] in
/-- The mass-weighted slow-cell mixed pair jets of all orders below `P`. -/
theorem sum_pairF_le (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) (P : ℕ)
    (hP : P ≤ A + r + 3) {b : ℕ} (hb : b ≤ r) (δ : DerivativeWord2 b) :
    ∑ p ∈ Finset.range P, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
        pairF (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
          (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X
      ≤ ENNReal.ofReal (tailSumConst N D P) * ENNReal.ofReal S ^ 2 *
          ResidualTimeData.gradDensity π ρ m a t := by
  unfold tailSumConst
  rw [ENNReal.ofReal_sum_of_nonneg fun p _ =>
    mul_nonneg (tailPairConst_nonneg N D p) (coarseJetConst_nonneg _), Finset.sum_mul,
    Finset.sum_mul]
  exact Finset.sum_le_sum fun p hp =>
    hd.pairF_sum_le (by have := Finset.mem_range.1 hp; omega) hb δ

/-- The word derivative of the sampled cleanup flux, with the mass weights. -/
theorem flux_word_bound (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) {e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e)
    (heρ : e ≤ ρ) {M : ℕ} (hM : e⁻¹ = (M : ℝ)) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2
      ≤ ENNReal.ofReal (fluxConst N D A r j * ρ ^ 2) * ENNReal.ofReal S ^ 2 *
          ResidualTimeData.gradDensity π ρ m a t := by
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
          (rs ^ j • orderedDerivative β (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ *
          ((A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) *
            ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
              2 * ∑ p ∈ Finset.range (A + r + 2), ∫⁻ X in slowCell ρ,
                pairF (fun X y => tailScalarField f N D εc
                    (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
                  (fun X y k => tailFluxField F N D εc
                    (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X) :=
        Finset.sum_le_sum fun v _ => by
          gcongr
          exact (hd.chainData v).flux_word_component hj β hrs hrse heρ hM
    _ = (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) *
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
            2 * ∑ p ∈ Finset.range (A + r + 2), ∑ v, ENNReal.ofReal (π v)⁻¹ *
              ∫⁻ X in slowCell ρ,
                pairF (fun X y => tailScalarField f N D εc
                    (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
                  (fun X y k => tailFluxField F N D εc
                    (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ (A : ℝ≥0∞) * ((A : ℝ≥0∞) * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2))) *
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2,
            2 * (ENNReal.ofReal (tailSumConst N D (A + r + 2)) * ENNReal.ofReal S ^ 2 *
              ResidualTimeData.gradDensity π ρ m a t) := by
        gcongr with ab hab δ _
        have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
        exact hd.sum_pairF_le (A + r + 2) (by omega) (by omega) δ
    _ = _ := by
        rw [CoarseFluxDiff.sum_words_const]
        have hwc := CoarseFluxDiff.wordCount_nonneg j
        have hts := tailSumConst_nonneg N D (A + r + 2)
        have e1 : fluxConst N D A r j * ρ ^ 2 =
            (A : ℝ) * ((A : ℝ) * ((4 : ℝ) ^ j * (4 * ρ ^ 2))) *
              (CoarseFluxDiff.wordCount j * (2 * tailSumConst N D (A + r + 2))) := by
          unfold fluxConst; ring
        rw [e1, ofReal_flux_split A j ρ _, ENNReal.ofReal_mul hwc,
          ENNReal.ofReal_mul (p := 2) (q := tailSumConst N D (A + r + 2)) (by norm_num),
          ENNReal.ofReal_ofNat]
        ring

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem cleanupSource_comp (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) (v : ι) :
    cleanupSource (fun j' X y k => V j' X y k v) A = fun X y => cleanupSource V A X y v := by
  have hbox := IsCleanupChain.isBoxSmooth hd.flux_box hd.chain (A - 1) (by have := hd.hA; omega)
  exact cleanupSource_clm_comp (sX := A + 2 + r) (by omega) (V := V) (j := A)
    hbox.isSlowSmooth (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

/-- The word derivative of the sampled cleanup source, with the mass weights. -/
theorem rem_word_bound (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) {j : ℕ}
    (hj : j ≤ r) (β : DerivativeWord2 j) {e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e)
    (heρ : e ≤ ρ) {M : ℕ} (hM : e⁻¹ = (M : ℝ)) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
      ≤ ENNReal.ofReal (remConst N D A r j * ρ ^ 2) * ENNReal.ofReal S ^ 2 *
          ResidualTimeData.gradDensity π ρ m a t := by
  have hcomp : ∀ v, (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x') v) =
      fun x' => cleanupSource (fun j' X y k => V j' X y k v) A (ρ⁻¹ • x') (e⁻¹ • x') := by
    intro v
    funext x'
    rw [hd.cleanupSource_comp v]
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) *
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
            4 * ∑ p ∈ Finset.range (A + r + 3), ∫⁻ X in slowCell ρ,
              pairF (fun X y => tailScalarField f N D εc
                  (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
                (fun X y k => tailFluxField F N D εc
                  (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X) :=
        Finset.sum_le_sum fun v _ => by
          gcongr
          rw [hcomp v]
          exact (hd.chainData v).rem_word_component hj β hrs hrse heρ hM
    _ = 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) *
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
            4 * ∑ p ∈ Finset.range (A + r + 3), ∑ v, ENNReal.ofReal (π v)⁻¹ *
              ∫⁻ X in slowCell ρ,
                pairF (fun X y => tailScalarField f N D εc
                    (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
                  (fun X y k => tailFluxField F N D εc
                    (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p δ X := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) *
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2,
            4 * (ENNReal.ofReal (tailSumConst N D (A + r + 3)) * ENNReal.ofReal S ^ 2 *
              ResidualTimeData.gradDensity π ρ m a t) := by
        gcongr with ab hab δ _
        have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
        exact hd.sum_pairF_le (A + r + 3) le_rfl (by omega) δ
    _ = _ := by
        rw [CoarseFluxDiff.sum_words_const]
        have hwc := CoarseFluxDiff.wordCount_nonneg j
        have hts := tailSumConst_nonneg N D (A + r + 3)
        have e1 : remConst N D A r j * ρ ^ 2 =
            (4 : ℝ) ^ j * (4 * ρ ^ 2) *
              (CoarseFluxDiff.wordCount j * (4 * tailSumConst N D (A + r + 3))) := by
          unfold remConst; ring
        rw [e1, ofReal_rem_split j ρ _, ENNReal.ofReal_mul hwc,
          ENNReal.ofReal_mul (p := 4) (q := tailSumConst N D (A + r + 3)) (by norm_num),
          ENNReal.ofReal_ofNat]
        ring

end TailTime
end

/-! Differentiated tail residual: the coordinates of the weighted word derivatives of the physical
residual flux `R = ℓ^{-2} ε_c^{N+1} e ∑_j ϑ^j (V_j)_diag` and scalar `q = ℓ^{-2} ε_c^{N+1} ϑ^A
(f_A)_diag`, and their pointwise-in-time bounds in the form consumed by
`residualNorm_le_of_pointwise`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

namespace TailTime

variable {π : ι → ℝ} {I : Set ℝ} {N D A r m : ℕ} {f : ℕ → LiftCoeff ι h}
  {F : ℕ → Fin 2 → LiftCoeff ι h} {εc : ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {ℓ ρ t τ S : ℝ}
  {V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The samples of the chain members are smooth. -/
theorem contDiff_member_sample (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) {j : ℕ}
    (hj : j ≤ r) {j' : ℕ} (hj' : j' < A) (k : Fin 2) (e : ℝ) :
    ContDiff ℝ (j : ℕ∞) (fun x' => V j' (ρ⁻¹ • x') (e⁻¹ • x') k) := by
  have hb := (IsCleanupChain.isBoxSmooth hd.flux_box hd.chain j' hj').clm_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ∀ i, h i) k)
  exact CoarseFluxDiff.contDiff_sample hb (by omega) (by omega) ρ e

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The sample of the source of the chain is smooth. -/
theorem contDiff_source_sample (hd : TailTime π I N D A r m f F εc a ℓ ρ t τ S V) {j : ℕ}
    (hj : j ≤ r) (e : ℝ) :
    ContDiff ℝ (j : ℕ∞) (fun x' => cleanupSource V A (ρ⁻¹ • x') (e⁻¹ • x')) := by
  have hA := hd.hA
  have hbox : IsBoxSmooth (A + 1 + r + 1) (r + 1) (V (A - 1)) := by
    have := IsCleanupChain.isBoxSmooth hd.flux_box hd.chain (A - 1) (by omega)
    rwa [show A + 1 + r + 1 = A + 2 + r by omega]
  exact CoarseFluxDiff.contDiff_sample (CoarseFluxDiff.isBoxSmooth_cleanupSource hbox)
    (by omega) (by omega) ρ e

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The coordinate of the weighted word derivative of the physical residual flux. -/
theorem flux_coord {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hd : TailTime π I N D A r m f F εc a ℓ ρ t ((ℓ ^ 2)⁻¹ * t) S
      (fun j => Vc j ((ℓ ^ 2)⁻¹ * t))) {e rs : ℝ} {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j)
    (x : Vec 2) (k : Fin 2) (v : ι) :
    (rs ^ j • orderedDerivative β
        (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A Vc t x' k) x) v =
      ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e) • ∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
        (rs ^ j • orderedDerivative β
          (fun x' => Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k v) x) := by
  have hfun : (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A Vc t x' k) =
      fun x' => ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e) • ∑ j' ∈ Finset.range A,
        (e / ρ) ^ j' • Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k := by
    funext x'
    simp only [cleanupFlux, diagSample, smul_smul, mul_assoc]
  have hS : ∀ j' ∈ Finset.range A, ContDiff ℝ (j : ℕ∞)
      (fun x' => Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k) :=
    fun j' hj' => hd.contDiff_member_sample hj (Finset.mem_range.1 hj') k e
  have hSv : ∀ j' ∈ Finset.range A, ContDiff ℝ (j : ℕ∞)
      (fun x' => Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k v) :=
    fun j' hj' => (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).contDiff.comp (hS j' hj')
  have hG : ContDiff ℝ (j : ℕ∞) (fun x' => ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e) •
      ∑ j' ∈ Finset.range A, (e / ρ) ^ j' • Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k) :=
    (ContDiff.sum fun j' hj' => (hS j' hj').const_smul _).const_smul _
  rw [hfun, Pi.smul_apply, CoarseFluxDiff.orderedDerivative_apply β hG v x]
  have hfunv : (fun x' => (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e) • ∑ j' ∈ Finset.range A,
      (e / ρ) ^ j' • Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k) v) =
      fun x' => ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e) • ∑ j' ∈ Finset.range A,
        (e / ρ) ^ j' • Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k v := by
    funext x'
    simp only [Pi.smul_apply, Finset.sum_apply]
  rw [hfunv, CoarseFluxDiff.orderedDerivative_sum_smul β (Finset.range A) _
    (fun j' => (e / ρ) ^ j') hSv]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 1
  ring

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The coordinate of the weighted word derivative of the physical residual scalar. -/
theorem rem_coord {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hd : TailTime π I N D A r m f F εc a ℓ ρ t ((ℓ ^ 2)⁻¹ * t) S
      (fun j => Vc j ((ℓ ^ 2)⁻¹ * t))) {e rs : ℝ} {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j)
    (x : Vec 2) (v : ι) :
    (rs ^ j • orderedDerivative β
        (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A Vc t x') x) v =
      ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A) • (rs ^ j • orderedDerivative β
        (fun x' => cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x') (e⁻¹ • x') v) x) := by
  have hfun : (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A Vc t x') =
      fun x' => ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A) •
        cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x') (e⁻¹ • x') := by
    funext x'
    simp only [cleanupRemainder, diagSample, smul_smul, mul_assoc]
  have hW : ContDiff ℝ (j : ℕ∞)
      (fun x' => cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x') (e⁻¹ • x')) :=
    hd.contDiff_source_sample hj e
  rw [hfun, CoarseFluxDiff.orderedDerivative_const_smul β _ hW]
  simp only [Pi.smul_apply]
  rw [CoarseFluxDiff.orderedDerivative_apply β hW v x]
  exact smul_comm _ _ _

/-- The pointwise-in-time bound of the weighted word derivative of the residual flux. -/
theorem flux_pointwise {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hd : TailTime π I N D A r m f F εc a ℓ ρ t ((ℓ ^ 2)⁻¹ * t) S
      (fun j => Vc j ((ℓ ^ 2)⁻¹ * t))) (hS : 0 ≤ S) {e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e)
    (heρ : e ≤ ρ) {M : ℕ} (hM : e⁻¹ = (M : ℝ)) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j)
    (hpR0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e) :
    ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖(rs ^ j • orderedDerivative β
          (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A Vc t x' k) x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ *
          Real.sqrt (fluxConst N D A r j) * S) ^ 2) *
        ResidualTimeData.gradDensity π ρ m a t := by
  set pR : ℝ := (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e
  have hpt : ∀ x k v, ‖(rs ^ j • orderedDerivative β
      (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A Vc t x' k) x) v‖ₑ ^ 2 =
      ENNReal.ofReal (pR ^ 2) * ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' • (rs ^ j •
        orderedDerivative β
          (fun x' => Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 := by
    intro x k v
    rw [hd.flux_coord hj β x k v, enorm_smul, mul_pow, Real.enorm_eq_ofReal hpR0,
      ← ENNReal.ofReal_pow hpR0]
  simp_rw [hpt, ← Finset.mul_sum]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hcf := fluxConst_nonneg N D A r j
  have hsplit : ENNReal.ofReal ((pR * ρ * Real.sqrt (fluxConst N D A r j) * S) ^ 2) =
      ENNReal.ofReal (pR ^ 2) *
        (ENNReal.ofReal (fluxConst N D A r j * ρ ^ 2) * ENNReal.ofReal S ^ 2) := by
    rw [show (pR * ρ * Real.sqrt (fluxConst N D A r j) * S) ^ 2 =
        pR ^ 2 * (fluxConst N D A r j * ρ ^ 2 * S ^ 2) by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hcf]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hS]
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (pR ^ 2) * _)
      = ENNReal.ofReal (pR ^ 2) * ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖∑ j' ∈ Finset.range A, (e / ρ) ^ j' •
            (rs ^ j • orderedDerivative β
              (fun x' => Vc j' ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x') (e⁻¹ • x') k v) x)‖ₑ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ENNReal.ofReal (pR ^ 2) * (ENNReal.ofReal (fluxConst N D A r j * ρ ^ 2) *
          ENNReal.ofReal S ^ 2 * ResidualTimeData.gradDensity π ρ m a t) := by
        gcongr
        exact hd.flux_word_bound hj β hrs hrse heρ hM
    _ = _ := by rw [hsplit]; ring

/-- The pointwise-in-time bound of the weighted word derivative of the residual scalar. -/
theorem rem_pointwise {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hd : TailTime π I N D A r m f F εc a ℓ ρ t ((ℓ ^ 2)⁻¹ * t) S
      (fun j => Vc j ((ℓ ^ 2)⁻¹ * t))) (hS : 0 ≤ S) {e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e)
    (heρ : e ≤ ρ) {M : ℕ} (hM : e⁻¹ = (M : ℝ)) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j)
    (hpq0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A) :
    ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β
          (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A Vc t x') x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A * ρ *
          Real.sqrt (remConst N D A r j) * S) ^ 2) *
        ResidualTimeData.gradDensity π ρ m a t := by
  set pq : ℝ := (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A
  have hpt : ∀ x v, ‖(rs ^ j • orderedDerivative β
      (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A Vc t x') x) v‖ₑ ^ 2 =
      ENNReal.ofReal (pq ^ 2) * ‖rs ^ j • orderedDerivative β (fun x' =>
        cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
    intro x v
    rw [hd.rem_coord hj β x v, enorm_smul, mul_pow, Real.enorm_eq_ofReal hpq0,
      ← ENNReal.ofReal_pow hpq0]
  simp_rw [hpt]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hcr := remConst_nonneg N D A r j
  have hsplit : ENNReal.ofReal ((pq * ρ * Real.sqrt (remConst N D A r j) * S) ^ 2) =
      ENNReal.ofReal (pq ^ 2) *
        (ENNReal.ofReal (remConst N D A r j * ρ ^ 2) * ENNReal.ofReal S ^ 2) := by
    rw [show (pq * ρ * Real.sqrt (remConst N D A r j) * S) ^ 2 =
        pq ^ 2 * (remConst N D A r j * ρ ^ 2 * S ^ 2) by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hcr]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hS]
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (pq ^ 2) * _)
      = ENNReal.ofReal (pq ^ 2) * ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β (fun x' =>
            cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ENNReal.ofReal (pq ^ 2) * (ENNReal.ofReal (remConst N D A r j * ρ ^ 2) *
          ENNReal.ofReal S ^ 2 * ResidualTimeData.gradDensity π ρ m a t) := by
        gcongr
        exact hd.rem_word_bound hj β hrs hrse heρ hM
    _ = _ := by rw [hsplit]; ring

end TailTime
end

/-! The differentiated tail residual estimate `TailDiff.Statement`: the pointwise-in-time bounds
of `Pointwise`, integrated in time against the dissipative part of the strong energy of order
`kres + r`, with the scale conversions of the order-zero residual bound. -/

/-- The constant of the differentiated tail residual bound. -/
def tailDiffConst (Acl N D r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    (Real.sqrt (fluxConst N D Acl r j) + Real.sqrt (remConst N D Acl r j))

theorem tailDiffConst_nonneg (Acl N D r : ℕ) : 0 ≤ tailDiffConst Acl N D r :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The real inequality closing the differentiated tail residual bound. -/
theorem tailDiff_real {cf cr K S εN Z : ℝ} (hK : Real.sqrt cf + Real.sqrt cr ≤ K) (hS : 0 ≤ S)
    (hεN : 0 ≤ εN) (hZ : 0 ≤ Z) :
    εN * Real.sqrt cf * S + εN * Z * Real.sqrt cr * S ≤ K * S * εN * (1 + Z) := by
  have h1 := residual_bound_real (Real.sqrt_nonneg cf) (Real.sqrt_nonneg cr) (M0 := S) (Θh := 1)
    (mul_one S).symm hS hεN hZ
  have hpos : 0 ≤ S * εN * (1 + Z) := by positivity
  refine h1.trans ?_
  calc (Real.sqrt cf + Real.sqrt cr) * S * 1 * εN * (1 + Z)
      = (Real.sqrt cf + Real.sqrt cr) * (S * εN * (1 + Z)) := by ring
    _ ≤ K * (S * εN * (1 + Z)) := mul_le_mul_of_nonneg_right hK hpos
    _ = K * S * εN * (1 + Z) := by ring

theorem statement_holds (Acl N D r : ℕ) (hA : 1 ≤ Acl) : Statement Acl N D r := by
  refine ⟨tailDiffConst Acl N D r, tailDiffConst_nonneg Acl N D r, ?_⟩
  intro ι _ h _ _ _ _ π t₀ t₁ e ν B ρ rs ℓ εc S sZ kres hπ hwin he hν hB hρ hrs hrse heρ hMe hℓeq
    hεeq hε1 hS hsZ hkres f F hbox hzero hjet a ha hmeas Vc hVc Z hZ j hj β
  obtain ⟨Mn, hMn⟩ := hMe
  have hsν := Real.sqrt_pos.2 hν
  have hℓ : 0 < ℓ := by rw [hℓeq]; exact div_pos he hsν
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have he_eq : e = ℓ * Real.sqrt ν := by rw [hℓeq]; field_simp
  have hεc0 : 0 ≤ εc := by rw [hεeq]; positivity
  have h1 : εc * ρ = ℓ * Real.sqrt B := by rw [hεeq]; field_simp
  -- per-time data
  have hdata : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      TailTime π (Set.Icc t₀ t₁) N D Acl r (kres + r) f F εc a ℓ ρ t ((ℓ ^ 2)⁻¹ * t) S
        (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) := by
    intro t ht
    have hτ : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc t₀ t₁ := by
      constructor
      · rw [le_inv_mul_iff₀ hℓ2]; linarith [ht.1]
      · rw [inv_mul_le_iff₀ hℓ2]; linarith [ht.2]
    exact {
      mass_pos := hπ
      ε_nonneg := hεc0
      ε_le := hε1
      ρ_pos := hρ
      τ_mem := hτ
      τ_eq := by rw [← mul_assoc, mul_inv_cancel₀ hℓ2.ne', one_mul]
      hA := hA
      box := fun n hn =>
        ⟨(hbox n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 _ hτ).1,
          (hbox n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 _ hτ).2.1⟩
      per := fun n hn => (hbox n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 _ hτ).2.2.2
      zero := fun n hn => hzero n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
      jet := fun n hn b hb δ i hi m' =>
        hjet n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 b hb δ i hi m'
      order := by omega
      smooth := ha t
      chain := isCleanupChain_mono le_rfl hsZ (hVc _ hτ) }
  -- time integration
  have hpR0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e := by positivity
  have hpq0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl := by positivity
  have hres := residualNorm_le_of_pointwise ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
    (fun t x k => rs ^ j • orderedDerivative β
      (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl Vc t x' k) x)
    (fun t x => rs ^ j • orderedDerivative β
      (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl Vc t x') x)
    (ResidualTimeData.gradDensity π ρ (kres + r) a) (by positivity) (by positivity)
    measurableSet_Icc
    (fun t ht => (hdata t ht).flux_pointwise hS hrs hrse heρ hMn hj β hpR0)
    (fun t ht => (hdata t ht).rem_pointwise hS hrs hrse heρ hMn hj β hpq0)
  have hG : ∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      ResidualTimeData.gradDensity π ρ (kres + r) a t
      ≤ ENNReal.ofReal B⁻¹ *
        classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) (kres + r) a ^ 2 :=
    lintegral_gradDensity_le ρ B hB π _ (kres + r) a fun v =>
      measurable_classicalGradFactorialSq ρ (kres + r) a v fun i hi w => hmeas i hi w v
  have hGs : (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      ResidualTimeData.gradDensity π ρ (kres + r) a t) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt B)⁻¹ *
        classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) (kres + r) a := by
    refine (ENNReal.rpow_le_rpow hG (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg
      (inv_nonneg.2 hB.le) (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← Real.sqrt_eq_rpow, Real.sqrt_inv]
    norm_num
  have hwin' : 0 ≤ ℓ ^ 2 * t₁ - ℓ ^ 2 * t₀ := by
    have := mul_le_mul_of_nonneg_left hwin hℓ2.le
    linarith
  have hvol : volume (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) := by
    rw [Real.volume_Icc, ENNReal.ofReal_rpow_of_nonneg hwin' (by norm_num),
      ← Real.sqrt_eq_rpow]
    congr 2; ring
  rw [hvol] at hres
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  refine residual_bound_combine (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) hres hGs ?_
  rw [residual_scale_flux hν hB hℓ he_eq h1 N, residual_scale_scalar hB hℓ h1 N, ← hZ]
  have hK : Real.sqrt (fluxConst N D Acl r j) + Real.sqrt (remConst N D Acl r j) ≤
      tailDiffConst Acl N D r :=
    Finset.single_le_sum (f := fun j' => Real.sqrt (fluxConst N D Acl r j') +
      Real.sqrt (remConst N D Acl r j')) (fun _ _ => by positivity)
      (Finset.mem_range.2 (by omega))
  exact tailDiff_real hK hS (pow_nonneg hεc0 N) hZ0

end AVRegularity.TailDiff
end
end
