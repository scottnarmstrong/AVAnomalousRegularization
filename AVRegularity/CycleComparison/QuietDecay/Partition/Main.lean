-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.TailJets
public import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleComparison.QuietDecay.Statement
import AVRegularity.CycleComparison.Residual.BoundPointwise
import AVRegularity.CycleComparison.Residual.Jets.Lift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

section
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.QuietDecay.Partition

/-! The time integral of the exponential decay over the trimmed quiet window. -/

/-- The tail bound `∫_A^B e^{-λ(t-g)} dt ≤ e^{-λ(A-g)}/λ`. -/
theorem lintegral_exp_Icc_le_tail (g lam A B : ℝ) (hlam : 0 < lam) :
    ∫⁻ t in Icc A B, ENNReal.ofReal (Real.exp (-(lam * (t - g))))
      ≤ ENNReal.ofReal (Real.exp (-(lam * (A - g))) / lam) := by
  have hf : ∀ t : ℝ, Real.exp (-(lam * (t - g))) = Real.exp (lam * g) * Real.exp ((-lam) * t) := by
    intro t
    rw [← Real.exp_add]; congr 1; ring
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(lam * (t - g)))) (Ioi A) := by
    simp_rw [hf]
    exact (integrableOn_exp_mul_Ioi (a := -lam) (by linarith) A).const_mul _
  have hI : ∫ t in Ioi A, Real.exp (-(lam * (t - g))) = Real.exp (-(lam * (A - g))) / lam := by
    simp_rw [hf]
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -lam) (by linarith) A, ← Real.exp_add]
    field_simp
    rw [← Real.exp_add]
    congr 1; ring
  have h1 : ∫⁻ t in Ioi A, ENNReal.ofReal (Real.exp (-(lam * (t - g)))) =
      ENNReal.ofReal (Real.exp (-(lam * (A - g))) / lam) := by
    rw [← hI]
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)).symm
  rw [← h1]
  calc ∫⁻ t in Icc A B, ENNReal.ofReal (Real.exp (-(lam * (t - g))))
      = ∫⁻ t in Ioc A B, ENNReal.ofReal (Real.exp (-(lam * (t - g)))) :=
        (setLIntegral_congr Ioc_ae_eq_Icc).symm
    _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self

/-- The length bound `∫_A^B e^{-λ(t-g)} dt ≤ e^{-λ(A-g)} (B-A)`. -/
theorem lintegral_exp_Icc_le_length (g lam A B : ℝ) (hlam : 0 < lam) :
    ∫⁻ t in Icc A B, ENNReal.ofReal (Real.exp (-(lam * (t - g))))
      ≤ ENNReal.ofReal (Real.exp (-(lam * (A - g))) * (B - A)) := by
  calc ∫⁻ t in Icc A B, ENNReal.ofReal (Real.exp (-(lam * (t - g))))
      ≤ ∫⁻ _t in Icc A B, ENNReal.ofReal (Real.exp (-(lam * (A - g)))) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have := mul_nonneg hlam.le (sub_nonneg.2 ht.1)
        linarith
    _ = ENNReal.ofReal (Real.exp (-(lam * (A - g))) * (B - A)) := by
        rw [setLIntegral_const, Real.volume_Icc,
          ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- The combined bound: `∫_A^B e^{-λ(t-g)} dt ≤ e^{-λ(A-g)} √((B-A)/λ)`. -/
theorem lintegral_exp_Icc_le (g lam A B : ℝ) (hlam : 0 < lam) (hAB : A ≤ B) :
    ∫⁻ t in Icc A B, ENNReal.ofReal (Real.exp (-(lam * (t - g))))
      ≤ ENNReal.ofReal (Real.exp (-(lam * (A - g))) * Real.sqrt ((B - A) / lam)) := by
  set E0 := Real.exp (-(lam * (A - g))) with hE0
  have hE : 0 < E0 := Real.exp_pos _
  have hD : 0 ≤ B - A := by linarith
  have hmin : min (B - A) (1 / lam) ≤ Real.sqrt ((B - A) / lam) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : min (B - A) (1 / lam) ≤ B - A := min_le_left _ _
    have h2 : min (B - A) (1 / lam) ≤ 1 / lam := min_le_right _ _
    have h0 : 0 ≤ min (B - A) (1 / lam) := le_min hD (by positivity)
    calc min (B - A) (1 / lam) ^ 2 = min (B - A) (1 / lam) * min (B - A) (1 / lam) := by ring
      _ ≤ (B - A) * (1 / lam) := mul_le_mul h1 h2 h0 hD
      _ = (B - A) / lam := by ring
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmin hE.le))
  rcases le_total (B - A) (1 / lam) with hle | hle
  · rw [min_eq_left hle]
    exact lintegral_exp_Icc_le_length g lam A B hlam
  · rw [min_eq_right hle]
    refine (lintegral_exp_Icc_le_tail g lam A B hlam).trans (le_of_eq ?_)
    congr 1
    rw [div_eq_mul_one_div]

end AVRegularity.QuietDecay.Partition
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay.Partition

/-! Auxiliary facts for the time integration of the transition source bound: the zero flux
residual norm, the square root of the factorial density against the strong energy, the square
root of a squared pointwise bound, and the final real inequality. -/

/-- With zero flux the residual norm is the `L¹_t L²_x` norm of the scalar part. -/
theorem residualNorm_zero_flux {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (ν : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (q : ℝ → Vec 2 → ∀ i, h i) :
    residualNorm ν π I (fun _ _ _ => 0) q =
      ∫⁻ t in I, (∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ‖q t x v‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  simp [residualNorm]

/-- The square root of the factorial density at a time of `I` is at most the strong energy. -/
theorem sqrt_factorialSq_le_energy {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (ρ B : ℝ) (π : ι → ℝ)
    (I : Set ℝ) (m : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ I) :
    (∑ u, ENNReal.ofReal (π u)⁻¹ * classicalFactorialSq ρ m (fun x => a t x u)) ^ (1 / 2 : ℝ)
      ≤ classicalStrongEnergy ρ B π I m a := by
  unfold classicalStrongEnergy
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun u _ => ?_) (by norm_num)
  refine mul_le_mul' le_rfl (le_trans ?_ le_self_add)
  exact le_iSup₂_of_le t ht le_rfl

/-- The square root of a squared pointwise bound. -/
theorem rpow_half_bound (ψt K X : ℝ) (hK : 0 ≤ K) (hX : 0 ≤ X) (S : ℝ≥0∞) :
    (ENNReal.ofReal (ψt ^ 2 * K) * ENNReal.ofReal X ^ 2 * S) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (|ψt| * Real.sqrt K * X) * S ^ (1 / 2 : ℝ) := by
  have hb : 0 ≤ |ψt| * Real.sqrt K * X := by positivity
  have e : ENNReal.ofReal (ψt ^ 2 * K) * ENNReal.ofReal X ^ 2 =
      ENNReal.ofReal (|ψt| * Real.sqrt K * X) ^ 2 := by
    rw [← ENNReal.ofReal_pow hX, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hb]
    congr 1
    rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hK]
  rw [e, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- The final real inequality of the time integral. -/
theorem final_real_ineq {g Kj Ks M A c₀ ℓ d δ lam : ℝ} (hKj : 0 ≤ Kj) (hKs : Kj ≤ Ks) (hM : 0 ≤ M)
    (hA : 0 ≤ A) (hc : 0 < c₀) (hℓ : 0 < ℓ) (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hlam : lam = c₀ / ℓ ^ 2) :
    M * Kj * A * (Real.exp (-(lam * (g + δ - g))) * Real.sqrt ((g + d - (g + δ)) / lam)) ≤
      Ks / Real.sqrt c₀ * A * M * ℓ * Real.sqrt d * Real.exp (-(c₀ * δ / ℓ ^ 2)) := by
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hsc : 0 < Real.sqrt c₀ := Real.sqrt_pos.2 hc
  have hexp : -(lam * (g + δ - g)) = -(c₀ * δ / ℓ ^ 2) := by
    rw [hlam]; ring
  have hsq : Real.sqrt ((g + d - (g + δ)) / lam) ≤ Real.sqrt d * ℓ / Real.sqrt c₀ := by
    have h1 : (g + d - (g + δ)) / lam ≤ d * ℓ ^ 2 / c₀ := by
      have : (g + d - (g + δ)) / lam ≤ d / lam :=
        div_le_div_of_nonneg_right (by linarith) hlam0.le
      refine this.trans (le_of_eq ?_)
      rw [hlam]; field_simp
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ hc.le, Real.sqrt_mul hd, Real.sqrt_sq hℓ.le]
  have hE : 0 < Real.exp (-(c₀ * δ / ℓ ^ 2)) := Real.exp_pos _
  rw [hexp]
  calc M * Kj * A * (Real.exp (-(c₀ * δ / ℓ ^ 2)) * Real.sqrt ((g + d - (g + δ)) / lam))
      ≤ M * Kj * A * (Real.exp (-(c₀ * δ / ℓ ^ 2)) * (Real.sqrt d * ℓ / Real.sqrt c₀)) := by
        gcongr
    _ ≤ M * Ks * A * (Real.exp (-(c₀ * δ / ℓ ^ 2)) * (Real.sqrt d * ℓ / Real.sqrt c₀)) := by
        gcongr
    _ = _ := by ring

end AVRegularity.QuietDecay.Partition
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay.Partition

/-! Box smoothness of the components of a lift action `liftApply M c a τ`: the fast jets of
`z ↦ c X z w` are `(apply w) ∘ iteratedFDeriv`, and the slow smoothness is that of
`IsSlowSmooth.clm_apply`. -/

section Apply

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- Box smoothness of `(X,z) ↦ T(X,z) (w X)` for a box smooth operator field `T` and a slow
smooth vector field `w`. -/
theorem isBoxSmooth_clm_apply {sX sZ : ℕ} {T : Vec 2 → Vec 2 → (E →L[ℝ] G)}
    (hT : IsBoxSmooth sX sZ T) {w : Vec 2 → E} (hw : ContDiff ℝ (sX : ℕ∞) w) :
    IsBoxSmooth sX sZ (fun X z => T X z (w X)) := by
  rw [isBoxSmooth_iff] at hT ⊢
  refine ⟨fun X => (hT.1 X).clm_apply contDiff_const, fun b hb => ?_⟩
  let Φ : ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2) (E →L[ℝ] G) →L[ℝ]
      (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2) G) :=
    (ContinuousLinearMap.flipMultilinearEquiv ℝ (fun _ : Fin b => Vec 2) E G).symm.toContinuousLinearMap
  have hfun : (fun X z => iteratedFDeriv ℝ b (fun z' => T X z' (w X)) z) =
      fun X z => (Φ (iteratedFDeriv ℝ b (T X) z)) (w X) := by
    funext X z
    have h1 := (ContinuousLinearMap.apply ℝ G (w X)).iteratedFDeriv_comp_left
      (hT.1 X).contDiffAt (x := z) (i := b) (by exact_mod_cast hb)
    refine h1.trans ?_
    ext m
    rfl
  rw [hfun]
  exact (isSlowSmooth_clm_comp Φ (hT.2 b hb)).clm_apply hw

end Apply

section Lift

variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, NormedSpace ℝ (H i)]

/-- The components of a lift action are box smooth. -/
theorem isBoxSmooth_liftApply (M sX sZ : ℕ) (c : LiftCoeff ι H) (a : ℝ → Vec 2 → ∀ i, H i)
    (t : ℝ) (hc : ∀ m α v u, IsBoxSmooth sX sZ (fun X y => c m α t X y v u))
    (ha : ContDiff ℝ ((sX + M : ℕ) : ℕ∞) (a t)) (v : ι) :
    IsBoxSmooth sX sZ (fun X y => liftApply M c a t X y v) := by
  show IsBoxSmooth sX sZ (fun X y => ∑ m' ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m',
    ∑ u : ι, c m' α t X y v u (orderedDerivative α (a t) X u))
  refine IsBoxSmooth.sum _ fun m' hm' => IsBoxSmooth.sum _ fun α _ =>
    IsBoxSmooth.sum _ fun u _ => ?_
  exact isBoxSmooth_clm_apply (hc m' α v u) (contDiff_orderedDerivative_comp
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm')) α ha u)

end Lift

end AVRegularity.QuietDecay.Partition
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay.Partition

/-! Bridge from the word-based mixed cell jets `mixedCellL2Jet` (sup over slow words and fast
words, the quantity of the decay lemma) to the `iteratedFDeriv`-based slow jets of a fixed fast
word, `MixedTail.mixedCellJet`, which the lift jet bounds consume. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The slow `i`-jet of the fast word `δ` is controlled by `2^i` times the word-based mixed cell
jet. -/
theorem mixedCellJet_le_mixedCellL2Jet (I : Set ℝ) {i b : ℕ} (δ : DerivativeWord2 b)
    (f : ℝ → Vec 2 → Vec 2 → E) (hf : ∀ t ∈ I, IsBoxSmooth i b (f t)) :
    MixedTail.mixedCellJet I i δ f ≤ 2 ^ i * mixedCellL2Jet I i b f := by
  unfold MixedTail.mixedCellJet
  refine iSup₂_le fun t ht => iSup_le fun X => ?_
  have hFt := hf t ht
  set μ := volume.restrict AVenhance.unitCube with hμ
  set J : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E :=
    fun z => iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (f t X') z) X with hJ
  have h0 : IsBoxSmooth i 0 (FastJets.fastL (List.ofFn δ) (f t)) :=
    FastJets.isBoxSmooth_fastL (sX := i) (sZ := 0) _ (by simpa using hFt)
  have hJc : Continuous J :=
    (h0.isSlowSmooth.2 i le_rfl).comp (Continuous.prodMk_right X)
  have hg : ∀ z, ContDiff ℝ (i : ℕ∞) (fun X' => orderedDerivative δ (f t X') z) := fun z =>
    h0.contDiff_slow z
  have hcoord : ∀ w' : DerivativeWord2 i, (fun z => J z (fun k => basisVec (w' k))) =
      fun z => orderedDerivative (fun k => w' (Fin.rev k))
        (fun X' => orderedDerivative δ (f t X') z) X := by
    intro w'
    funext z
    rw [orderedDerivative_eq_iteratedFDeriv _ (hg z)]
    simp [hJ, Fin.rev_rev]
  have hmono : eLpNorm J 2 μ ≤ eLpNorm (fun z => ∑ w' : DerivativeWord2 i,
      ‖J z (fun k => basisVec (w' k))‖) 2 μ := by
    refine eLpNorm_mono_ae_real hJc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    exact norm_le_sum_basisVec (J z)
  refine hmono.trans ?_
  have hsum : (fun z => ∑ w' : DerivativeWord2 i, ‖J z (fun k => basisVec (w' k))‖) =
      ∑ w' : DerivativeWord2 i, fun z => ‖J z (fun k => basisVec (w' k))‖ := by
    funext z; simp [Finset.sum_apply]
  rw [hsum]
  refine (eLpNorm_sum_le (by norm_num)).trans ?_
  have hterm : ∀ w' : DerivativeWord2 i,
      eLpNorm (fun z => ‖J z (fun k => basisVec (w' k))‖) 2 μ ≤ mixedCellL2Jet I i b f := by
    intro w'
    have hm : AEStronglyMeasurable (fun z => J z (fun k => basisVec (w' k))) μ :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => Vec 2) E
        (fun k => basisVec (w' k))).continuous.comp hJc).aestronglyMeasurable
    rw [eLpNorm_norm _ hm, hcoord w']
    unfold mixedCellL2Jet
    exact le_iSup₂_of_le t ht (le_iSup_of_le X (le_iSup_of_le (fun k => w' (Fin.rev k))
      (le_iSup_of_le δ le_rfl)))
  calc ∑ w' : DerivativeWord2 i, eLpNorm (fun z => ‖J z (fun k => basisVec (w' k))‖) 2 μ
      ≤ ∑ _w' : DerivativeWord2 i, mixedCellL2Jet I i b f := Finset.sum_le_sum fun w' _ => hterm w'
    _ = 2 ^ i * mixedCellL2Jet I i b f := by
        rw [Finset.sum_const, card_derivativeWord2]; simp

/-- The weighted block norm version. -/
theorem schurMixedJet_le_schurMixedCellL2Jet {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) {i b : ℕ} (δ : DerivativeWord2 b)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a v u, ∀ t ∈ I, IsBoxSmooth i b (fun X z => c a t X z v u)) :
    MixedTail.schurMixedJet π I i δ c ≤ 2 ^ i * schurMixedCellL2Jet π I i b c := by
  unfold MixedTail.schurMixedJet schurMixedCellL2Jet
  refine le_trans (schurSums_mono π fun v u => ?_) (MixedTail.schurSums_const_mul_le π _ _)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    mixedCellJet_le_mixedCellL2Jet I δ _ (fun t ht => hc a v u t ht)
end

/-! The mass-weighted mixed slow jet of one lift action of the dilated physical field
`a_ρ(X) = g(ρ X)`, without any vanishing assumption on the order-zero coefficient jets, and its
slow-cell integral in terms of the classical factorial norm of the components of `g`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The pointwise jet bound for one lift action: only the entrance bound `s` on the mixed jets of
the coefficients of order at most `n` is used (the order-zero coefficient is not assumed to
vanish). -/
theorem lift_scalJetF_le' (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (n p : ℕ) {b : ℕ}
    (δ : DerivativeWord2 b) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ I)
    (hbox : ∀ m α v u, IsBoxSmooth p b (fun X y => c m α τ X y v u)) (s : ℝ≥0∞)
    (hjet : ∀ i, i ≤ p → ∀ m, m ≤ n → MixedTail.schurMixedJet π I i δ (c m) ≤ s)
    (ha : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (a τ)) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X
      ≤ ENNReal.ofReal (2 ^ p * tailJetConst n p) * s ^ 2 *
          ∑ m ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (p + 1),
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 := by
  have hbox0 : ∀ m α v u, IsBoxSmooth p 0 (fun X y => MixedTail.fastCoeff δ c m α τ X y v u) :=
    fun m α v u => FastJets.isBoxSmooth_fastL (sX := p) (sZ := 0) (List.ofFn δ)
      (F := fun X y => c m α τ X y v u) (by simpa using hbox m α v u)
  have hrew : ∀ X' y v, liftApply n (MixedTail.fastCoeff δ c) a τ X' y v =
      orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y := fun X' y v =>
    MixedTail.liftApply_fastCoeff δ n c a τ X' (fun m α v u => (hbox m α v u).1 X') y v
  have hsc : ∀ v y, ContDiff ℝ (p : ℕ∞)
      (fun X' => liftApply n (MixedTail.fastCoeff δ c) a τ X' y v) :=
    fun v y => contDiff_liftApply (MixedTail.fastCoeff δ c) a τ y v
      (fun m α u => ((hbox0 m α v u).isSlowSmooth).1 y) ha
  have h1 : ∀ v, FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X ≤
      2 ^ p * ∫⁻ y in AVenhance.unitCube, ‖iteratedFDeriv ℝ p
        (fun X' => orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y) X‖ₑ ^ 2 := by
    intro v
    exact scalJet_le_iteratedFDeriv
      (fun X y => orderedDerivative δ (fun y' => liftApply n c a τ X y' v) y)
      (fun y => by simpa only [hrew] using hsc v y) X
  have hT2 := MixedTail.sum_mass_lintegral_iteratedFDeriv_fast_le π hπ I n p δ c a hτ hbox ha X
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (2 ^ p * ∫⁻ y in AVenhance.unitCube,
          ‖iteratedFDeriv ℝ p
            (fun X' => orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y) X‖ₑ ^ 2) :=
        Finset.sum_le_sum fun v _ => by gcongr; exact h1 v
    _ = 2 ^ p * ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube,
          ‖iteratedFDeriv ℝ p
            (fun X' => orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y) X‖ₑ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ 2 ^ p * (ENNReal.ofReal (tailJetConst n p) * ∑ m ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (p + 1), MixedTail.schurMixedJet π I i δ (c m) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2) := by gcongr
    _ ≤ 2 ^ p * (ENNReal.ofReal (tailJetConst n p) * ∑ m ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (p + 1), s ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2) := by
        gcongr with m hm i hi
        exact hjet i (by have := Finset.mem_range.1 hi; omega) m
          (by have := Finset.mem_range.1 hm; omega)
    _ = _ := by
        have ht : 0 ≤ tailJetConst n p := by unfold tailJetConst; positivity
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp only [ENNReal.ofReal_ofNat, ← Finset.mul_sum]
        ring

/-- The constant of the slow-cell integral of the jets of one lift action. -/
def liftWeight (n p : ℕ) : ℝ :=
  2 ^ p * tailJetConst n p * (((n + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
    (2 ^ (p + n) * (((p + n).factorial : ℝ)) ^ 2)

theorem liftWeight_nonneg (n p : ℕ) : 0 ≤ liftWeight n p := by
  unfold liftWeight tailJetConst; positivity

theorem aux_const (A : ℝ) (n1 p1 : ℕ) (Y : ℝ) (hA : 0 ≤ A) (s S : ℝ≥0∞) :
    ENNReal.ofReal A * s ^ 2 * ((n1 : ℝ≥0∞) * ((p1 : ℝ≥0∞) * (ENNReal.ofReal Y * S))) =
      ENNReal.ofReal (A * ((n1 : ℝ) * (p1 : ℝ)) * Y) * s ^ 2 * S := by
  rw [ENNReal.ofReal_mul (mul_nonneg hA (by positivity)), ENNReal.ofReal_mul hA,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  ring

/-- The slow-cell integral of the mass-weighted mixed jet of a lift action of the dilated field
`a τ = g(ρ ·)`, in terms of the classical factorial norm of the components of `g`. -/
theorem slowCell_scalJetF_le' (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (n p M : ℕ) {b : ℕ}
    (δ : DerivativeWord2 b) (hpM : p + n ≤ M) (c : LiftCoeff ι h) {τ : ℝ} (hτ : τ ∈ I)
    (hbox : ∀ m α v u, IsBoxSmooth p b (fun X y => c m α τ X y v u)) (s : ℝ≥0∞)
    (hjet : ∀ i, i ≤ p → ∀ m, m ≤ n → MixedTail.schurMixedJet π I i δ (c m) ≤ s)
    (a : ℝ → Vec 2 → ∀ i, h i) (g : Vec 2 → ∀ i, h i) {ρ : ℝ} (hρ : 0 < ρ)
    (hag : a τ = fun X' => g (ρ • X')) (hg : ContDiff ℝ (M : ℕ∞) g) :
    ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
        FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X
      ≤ ENNReal.ofReal (ρ⁻¹ ^ 2 * liftWeight n p) * s ^ 2 *
          ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalFactorialSq ρ M (fun x => g x u) := by
  have hga : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast hpM)
  have ha : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (a τ) := by
    rw [hag]; exact hga.comp (contDiff_const_smul ρ)
  have hgu : ∀ u, ContDiff ℝ (M : ℕ∞) (fun x => g x u) := fun u =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp hg
  have hmeas : ∀ q ∈ Finset.range (p + n + 1), Measurable fun X : Vec 2 => ∑ u,
      ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2 := by
    intro q hq
    have hq' : q ≤ p + n := by have := Finset.mem_range.1 hq; omega
    refine Finset.measurable_sum _ fun u _ => Measurable.const_mul ?_ _
    have hau : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun X' => a τ X' u) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp ha
    exact ((hau.continuous_iteratedFDeriv (by exact_mod_cast hq')).enorm.measurable).pow_const 2
  have hpt := fun X => lift_scalJetF_le' π hπ I n p δ c a hτ hbox s hjet ha X
  set S : ℝ≥0∞ := ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalFactorialSq ρ M (fun x => g x u) with hS
  -- the integral of one jet density
  have hq : ∀ q, q ≤ p + n → ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
      ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2 ≤
      ENNReal.ofReal (ρ⁻¹ ^ 2 * (2 ^ (p + n) * (((p + n).factorial : ℝ)) ^ 2)) * S := by
    intro q hqn
    have hmq : ∀ u ∈ (Finset.univ : Finset ι), Measurable fun X : Vec 2 =>
        ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2 := by
      intro u _
      have hau : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun X' => a τ X' u) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp ha
      exact Measurable.const_mul
        (((hau.continuous_iteratedFDeriv (by exact_mod_cast hqn)).enorm.measurable).pow_const 2) _
    rw [lintegral_finsetSum _ hmq]
    have hB : 2 ^ q * (((q.factorial : ℕ) : ℝ)) ^ 2 ≤
        2 ^ (p + n) * (((p + n).factorial : ℝ)) ^ 2 := by
      have h1 : (2 : ℝ) ^ q ≤ 2 ^ (p + n) := pow_le_pow_right₀ (by norm_num) hqn
      have h2 : ((q.factorial : ℕ) : ℝ) ≤ (((p + n).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_le hqn
      have h3 : (((q.factorial : ℕ) : ℝ)) ^ 2 ≤ (((p + n).factorial : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      exact mul_le_mul h1 h3 (by positivity) (by positivity)
    calc ∑ u, ∫⁻ X in slowCell ρ, ENNReal.ofReal (π u)⁻¹ *
          ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2
        ≤ ∑ u, ENNReal.ofReal (π u)⁻¹ * (ENNReal.ofReal (ρ⁻¹ ^ 2 *
            (2 ^ (p + n) * (((p + n).factorial : ℝ)) ^ 2)) *
              classicalFactorialSq ρ M (fun x => g x u)) := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          have hau : ∀ X', a τ X' u = g (ρ • X') u := fun X' => by rw [hag]
          have e : (fun X' => a τ X' u) = fun X' => (fun x => g x u) (ρ • X') := by
            funext X'; exact hau X'
          rw [e]
          refine (CoarseFluxDiff.lintegral_slowCell_dilate_le_classicalFactorialSq M q
            (by omega) (hgu u) hρ).trans ?_
          gcongr
      _ = _ := by
          rw [hS, Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring
  calc ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
        FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X
      ≤ ∫⁻ X in slowCell ρ, ENNReal.ofReal (2 ^ p * tailJetConst n p) * s ^ 2 *
          ∑ m ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (p + 1),
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ p * tailJetConst n p) * s ^ 2 *
          ∑ m ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (p + 1),
            ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 := by
        have hmq : ∀ m ∈ Finset.range (n + 1), Measurable fun X : Vec 2 =>
            ∑ i ∈ Finset.range (p + 1), ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 := by
          intro m hm
          exact Finset.measurable_sum _ fun i hi => hmeas _ (Finset.mem_range.2
            (by have := Finset.mem_range.1 hm; have := Finset.mem_range.1 hi; omega))
        have hmi : ∀ m ∈ Finset.range (n + 1), ∀ i ∈ Finset.range (p + 1), Measurable fun X : Vec 2 =>
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 := by
          intro m hm i hi
          exact hmeas _ (Finset.mem_range.2
            (by have := Finset.mem_range.1 hm; have := Finset.mem_range.1 hi; omega))
        rw [lintegral_const_mul _ (Finset.measurable_sum _ hmq), lintegral_finsetSum _ hmq]
        congr 1
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [lintegral_finsetSum _ (hmi m hm)]
    _ ≤ ENNReal.ofReal (2 ^ p * tailJetConst n p) * s ^ 2 *
          ∑ m ∈ Finset.range (n + 1), ∑ _i ∈ Finset.range (p + 1),
            (ENNReal.ofReal (ρ⁻¹ ^ 2 * (2 ^ (p + n) * (((p + n).factorial : ℝ)) ^ 2)) * S) := by
        gcongr with m hm i hi
        exact hq _ (by have := Finset.mem_range.1 hm; have := Finset.mem_range.1 hi; omega)
    _ = _ := by
        have ht : 0 ≤ tailJetConst n p := by unfold tailJetConst; positivity
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        unfold liftWeight
        have e : ρ⁻¹ ^ 2 * (2 ^ p * tailJetConst n p * (((n + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
            (2 ^ (p + n) * (((p + n).factorial : ℝ)) ^ 2)) =
            (2 ^ p * tailJetConst n p) * (((n + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
              (ρ⁻¹ ^ 2 * (2 ^ (p + n) * (((p + n).factorial : ℝ)) ^ 2)) := by ring
        rw [e, ← aux_const _ (n + 1) (p + 1) _ (by positivity) s S]
end

/-! The word derivatives of the diagonal sample of one lift action of the physical field, in terms
of the entrance jets of the coefficients and the factorial norm of the field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The constant of the word derivatives of the sample of the degree-`n` lift action. -/
def degConst (n j : ℕ) : ℝ :=
  4 ^ j * 4 * CoarseFluxDiff.wordCount j * 3 * ∑ p ∈ Finset.range (j + 3), liftWeight n p

theorem degConst_nonneg (n j : ℕ) : 0 ≤ degConst n j :=
  mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (CoarseFluxDiff.wordCount_nonneg j))
    (by norm_num)) (Finset.sum_nonneg fun p _ => liftWeight_nonneg n p)

theorem deg_const_eq (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (L : ℝ) (s S : ℝ≥0∞) :
    (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2)) *
        (ENNReal.ofReal (CoarseFluxDiff.wordCount j) *
          (3 * (ENNReal.ofReal (ρ⁻¹ ^ 2 * L) * s ^ 2 * S))) =
      ENNReal.ofReal (4 ^ j * 4 * CoarseFluxDiff.wordCount j * 3 * L) * s ^ 2 * S := by
  have hρ2 : ρ ^ 2 * ρ⁻¹ ^ 2 = 1 := by field_simp
  have hwc := CoarseFluxDiff.wordCount_nonneg j
  have hX : (4 : ℝ) ^ j * 4 * CoarseFluxDiff.wordCount j * 3 * L =
      (4 ^ j * (4 * ρ ^ 2)) * (CoarseFluxDiff.wordCount j * (3 * (ρ⁻¹ ^ 2 * L))) := by
    calc (4 : ℝ) ^ j * 4 * CoarseFluxDiff.wordCount j * 3 * L
        = (4 : ℝ) ^ j * 4 * CoarseFluxDiff.wordCount j * 3 * ((ρ ^ 2 * ρ⁻¹ ^ 2) * L) := by
          rw [hρ2, one_mul]
      _ = _ := by ring
  have h4 : ENNReal.ofReal ((4 : ℝ) ^ j) = 4 ^ j := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  have hR : ENNReal.ofReal ((4 : ℝ) ^ j * 4 * CoarseFluxDiff.wordCount j * 3 * L) =
      (4 ^ j * ENNReal.ofReal (4 * ρ ^ 2)) * (ENNReal.ofReal (CoarseFluxDiff.wordCount j) *
        (3 * ENNReal.ofReal (ρ⁻¹ ^ 2 * L))) := by
    rw [hX, ENNReal.ofReal_mul (p := (4 : ℝ) ^ j * (4 * ρ ^ 2)) (by positivity),
      ENNReal.ofReal_mul (p := (4 : ℝ) ^ j) (by positivity), h4,
      ENNReal.ofReal_mul (p := CoarseFluxDiff.wordCount j) hwc,
      ENNReal.ofReal_mul (p := (3 : ℝ)) (by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
  rw [hR]
  ring

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- Periodicity of the components of a lift action. -/
theorem isZ2Periodic_liftApply (M : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hper : ∀ m α v u X, AVenhance.IsZ2Periodic (fun y => c m α t X y v u)) (X : Vec 2) (v : ι) :
    AVenhance.IsZ2Periodic (fun y => liftApply M c a t X y v) := by
  intro n y
  have := fun m α u => hper m α v u X n y
  simp only [liftApply, this]

/-- **Word derivatives of the sample of one lift action.** -/
theorem degree_word_bound (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (n MM : ℕ)
    (c : LiftCoeff ι h) {τ : ℝ} (hτ : τ ∈ I) {j : ℕ} (β : DerivativeWord2 j) {ρ e rs : ℝ}
    (hρ : 0 < ρ) (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ))
    (hk : j + 2 + n ≤ MM)
    (hbox : ∀ m α v u, IsBoxSmooth (j + 2) j (fun X y => c m α τ X y v u))
    (hper : ∀ m α v u X, AVenhance.IsZ2Periodic (fun y => c m α τ X y v u)) (s : ℝ≥0∞)
    (hjet : ∀ b, b ≤ j → ∀ δ : DerivativeWord2 b, ∀ i, i ≤ j + 2 → ∀ m, m ≤ n →
      MixedTail.schurMixedJet π I i δ (c m) ≤ s)
    (a : ℝ → Vec 2 → ∀ i, h i) (g : Vec 2 → ∀ i, h i)
    (hag : a τ = fun X' => g (ρ • X')) (hg : ContDiff ℝ (MM : ℕ∞) g) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β
          (fun x' => liftApply n c a τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
      ≤ ENNReal.ofReal (degConst n j) * s ^ 2 *
          ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalFactorialSq ρ MM (fun x => g x u) := by
  set S : ℝ≥0∞ := ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalFactorialSq ρ MM (fun x => g x u)
    with hS
  have ha : ContDiff ℝ (((j + 2) + n : ℕ) : ℕ∞) (a τ) := by
    rw [hag]
    exact (hg.of_le (by exact_mod_cast hk)).comp (contDiff_const_smul ρ)
  have hW : ∀ v, IsBoxSmooth (j + 2) j (fun X y => liftApply n c a τ X y v) := fun v =>
    isBoxSmooth_liftApply n (j + 2) j c a τ hbox ha v
  set Lw : ℝ := ∑ p ∈ Finset.range (j + 3), liftWeight n p with hLw
  have hLw0 : 0 ≤ Lw := Finset.sum_nonneg fun p _ => liftWeight_nonneg n p
  -- the bound of one jet integral
  have hT : ∀ (ab : ℕ × ℕ), ab ∈ Finset.HasAntidiagonal.antidiagonal j →
      ∀ (δ : DerivativeWord2 ab.2), ∀ m ∈ Finset.range 3,
      ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
        FastJets.scalJetF (fun X y => liftApply n c a τ X y v) (ab.1 + m) δ X
      ≤ ENNReal.ofReal (ρ⁻¹ ^ 2 * Lw) * s ^ 2 * S := by
    intro ab hab δ m hm
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    have hm3 := Finset.mem_range.1 hm
    have hp : ab.1 + m ≤ j + 2 := by omega
    have hb : ab.2 ≤ j := by omega
    have key := slowCell_scalJetF_le' π hπ I n (ab.1 + m) MM δ (by omega) c hτ
      (fun m' α v u => (hbox m' α v u).mono hp hb) s
      (fun i hi m' hm' => hjet ab.2 hb δ i (by omega) m' hm') a g hρ hag hg
    refine le_trans ?_ (key.trans ?_)
    · simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact sum_lintegral_le_lintegral_sum _ _
    · gcongr
      have : liftWeight n (ab.1 + m) ≤ Lw :=
        Finset.single_le_sum (f := fun p => liftWeight n p)
          (fun p _ => liftWeight_nonneg n p) (Finset.mem_range.2 (by omega))
      exact this
  set C : ℝ≥0∞ := 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) with hC
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β
          (fun x' => liftApply n c a τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
          ∑ δ : DerivativeWord2 ab.2, ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c a τ X y v) (ab.1 + m) δ X) :=
        Finset.sum_le_sum fun v _ => by
          gcongr
          exact FastJets.lintegral_rs_odL_diag_sq_le β (hW v)
            (isZ2Periodic_liftApply n c a τ hper · v) hrs hrse heρ M hM
    _ = C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ δ : DerivativeWord2 ab.2,
          ∑ m ∈ Finset.range 3, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => liftApply n c a τ X y v) (ab.1 + m) δ X := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ C * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j, ∑ _δ : DerivativeWord2 ab.2,
          ∑ _m ∈ Finset.range 3, (ENNReal.ofReal (ρ⁻¹ ^ 2 * Lw) * s ^ 2 * S) := by
        gcongr with ab hab δ _ m hm
        exact hT ab hab δ m hm
    _ = _ := by
        have h3 : ∀ T : ℝ≥0∞, ∑ _m ∈ Finset.range 3, T = 3 * T := fun T => by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        simp only [h3]
        rw [CoarseFluxDiff.sum_words_const, hC, deg_const_eq j hρ Lw s S]
        rfl
end

/-! The word derivatives of the transition source field at one physical time, in terms of the
word derivatives of the samples of the individual degrees. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The constant of the word derivatives of the transition source field. -/
def srcConst (N j : ℕ) : ℝ := N * ∑ n ∈ Finset.Icc 1 N, degConst n j

theorem srcConst_nonneg (N j : ℕ) : 0 ≤ srcConst N j :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => degConst_nonneg n j)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The components of the transition source field at the physical time `t`. -/
theorem transitionSourceField_apply (N hh : ℕ) (ℓ ρ e εc : ℝ) (ψ : ℝ → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t τ : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (x : Vec 2) (v : ι) :
    transitionSourceField N hh ℓ ρ e εc ψ Cc a t x v =
      ψ t • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
        liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x) (e⁻¹ • x) v := by
  simp only [transitionSourceField, diagSample, hτt, Pi.smul_apply, Finset.sum_apply]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem source_word_bound (π : ι → ℝ) (N hh : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (ℓ ρ e rs εc : ℝ) (ψ : ℝ → ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (t τ : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1) {j : ℕ} (β : DerivativeWord2 j)
    (hsm : ∀ n ∈ Finset.Icc 1 N, ∀ v, ContDiff ℝ (j : ℕ∞) (fun x' =>
      liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v))
    (s S : ℝ≥0∞)
    (hdeg : ∀ n ∈ Finset.Icc 1 N, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
      ‖rs ^ j • orderedDerivative β (fun x' => liftApply n (Cc hh n)
        (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2
        ≤ ENNReal.ofReal (degConst n j) * s ^ 2 * S) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β
          (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (ψ t ^ 2 * srcConst N j) * s ^ 2 * S := by
  classical
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  have hfun : ∀ v, (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x' v) = fun x' =>
      ψ t • ∑ n ∈ Finset.Icc 1 N, εc ^ n • liftApply n (Cc hh n)
        (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v := fun v =>
    funext fun x' => transitionSourceField_apply N hh ℓ ρ e εc ψ Cc a t τ hτt x' v
  have hG : ContDiff ℝ (j : ℕ∞) (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') := by
    refine contDiff_pi.2 fun v => ?_
    rw [hfun v]
    exact ContDiff.const_smul _ (ContDiff.sum fun n hn => (hsm n hn v).const_smul _)
  have hcoord : ∀ (v : ι) (x : Vec 2),
      (rs ^ j • orderedDerivative β
        (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v =
      ψ t • ∑ n ∈ Finset.Icc 1 N, εc ^ n • (rs ^ j • orderedDerivative β
        (fun x' => liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ
          (ρ⁻¹ • x') (e⁻¹ • x') v) x) := by
    intro v x
    rw [Pi.smul_apply, CoarseFluxDiff.orderedDerivative_apply β hG v x, hfun v,
      CoarseFluxDiff.orderedDerivative_sum_smul β (Finset.Icc 1 N) (ψ t) (fun n => εc ^ n)
        (H := fun n x' => liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ
          (ρ⁻¹ • x') (e⁻¹ • x') v) (fun n hn => hsm n hn v)]
    show rs ^ j • (ψ t • ∑ n ∈ Finset.Icc 1 N, εc ^ n • _) = _
    rw [smul_comm (rs ^ j) (ψ t), Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_comm (rs ^ j) (εc ^ n)]
  have hpt : ∀ (v : ι) (x : Vec 2),
      ‖(rs ^ j • orderedDerivative β
        (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * ψ t ^ 2 * (εc ^ n) ^ 2) *
        ‖rs ^ j • orderedDerivative β (fun x' => liftApply n (Cc hh n)
          (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
    intro v x
    rw [hcoord v x]
    have := CoarseFluxDiff.enorm_sq_sum_smul_le (Finset.Icc 1 N) (ψ t) (fun n => εc ^ n)
      (fun n => rs ^ j • orderedDerivative β (fun x' => liftApply n (Cc hh n)
        (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) x)
    rwa [hcard] at this
  have hmeas : ∀ (v : ι), ∀ n ∈ Finset.Icc 1 N, Measurable fun x : Vec 2 =>
      ‖rs ^ j • orderedDerivative β (fun x' => liftApply n (Cc hh n)
        (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 :=
    fun v n hn => (((continuous_const.smul (contDiff_orderedDerivative (p := 0) β
      (by simpa using hsm n hn v)).continuous)).enorm.measurable).pow_const 2
  have hint : ∀ v : ι, ∫⁻ x in AVenhance.unitCube,
      ‖(rs ^ j • orderedDerivative β
        (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * ψ t ^ 2 * (εc ^ n) ^ 2) *
        ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β (fun x' => liftApply n (Cc hh n)
          (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
    intro v
    refine (lintegral_mono (hpt v)).trans (le_of_eq ?_)
    rw [lintegral_finsetSum _ fun n hn => (hmeas v n hn).const_mul _]
    exact Finset.sum_congr rfl fun n hn => lintegral_const_mul _ (hmeas v n hn)
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β
          (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
          ENNReal.ofReal (N * ψ t ^ 2 * (εc ^ n) ^ 2) *
            ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative β (fun x' => liftApply n (Cc hh n)
              (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 :=
        Finset.sum_le_sum fun v _ => by gcongr; exact hint v
    _ = ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * ψ t ^ 2 * (εc ^ n) ^ 2) *
          ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
            ‖rs ^ j • orderedDerivative β (fun x' => liftApply n (Cc hh n)
              (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) x‖ₑ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun v _ => by ring_nf
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * ψ t ^ 2) *
          (ENNReal.ofReal (degConst n j) * s ^ 2 * S) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have h1 : εc ^ n ≤ 1 := pow_le_one₀ hε0 hε1
        have h2 : (εc ^ n) ^ 2 ≤ 1 := pow_le_one₀ (pow_nonneg hε0 n) h1
        have h3 : (N : ℝ) * ψ t ^ 2 * (εc ^ n) ^ 2 ≤ N * ψ t ^ 2 :=
          mul_le_of_le_one_right (by positivity) h2
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal h3) (hdeg n hn)
    _ = _ := by
        unfold srcConst
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul,
          ← ENNReal.ofReal_sum_of_nonneg fun n _ => degConst_nonneg n j]
        have hD : 0 ≤ ∑ n ∈ Finset.Icc 1 N, degConst n j :=
          Finset.sum_nonneg fun n _ => degConst_nonneg n j
        rw [show ψ t ^ 2 * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, degConst n j) =
          ((N : ℝ) * ψ t ^ 2) * ∑ n ∈ Finset.Icc 1 N, degConst n j by ring,
          ENNReal.ofReal_mul (p := (N : ℝ) * ψ t ^ 2) (by positivity)]
        ring
end

/-! The pointwise-in-time bound of the word derivatives of the transition source field, from the
quiet-gap decay of the mixed Schur jets of the coefficients at the cell time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The entrance bound on the slow jets of a fixed fast word, from the decay of the Schur sums. -/
theorem schurMixedJet_le_of_decay (π : ι → ℝ) (N hh r : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h) {τ : ℝ}
    (hbox : ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u,
      IsBoxSmooth (r + 2) r (fun X y => Cc hh n m α τ X y v u))
    (θ : ℝ)
    (hdecay : ∀ p, p ≤ r + 2 → ∀ q, q ≤ r →
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1),
        schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤ ENNReal.ofReal θ)
    {n : ℕ} (hn : n ∈ Finset.Icc 1 N) {b : ℕ} (hb : b ≤ r) (δ : DerivativeWord2 b) {i : ℕ}
    (hi : i ≤ r + 2) {m : ℕ} (hm : m ≤ n) :
    MixedTail.schurMixedJet π {τ} i δ (Cc hh n m) ≤ ENNReal.ofReal (2 ^ (r + 2) * θ) := by
  have hn1 := (Finset.mem_Icc.1 hn).1
  have hnN := (Finset.mem_Icc.1 hn).2
  have h1 : MixedTail.schurMixedJet π {τ} i δ (Cc hh n m) ≤
      2 ^ i * schurMixedCellL2Jet π {τ} i b (Cc hh n m) :=
    schurMixedJet_le_schurMixedCellL2Jet π {τ} δ (Cc hh n m) fun α v u t ht => by
      rw [Set.mem_singleton_iff.1 ht]
      exact (hbox n hn1 hnN m α v u).mono hi hb
  have h2 : schurMixedCellL2Jet π {τ} i b (Cc hh n m) ≤ ENNReal.ofReal θ := by
    refine le_trans ?_ (hdecay i hi b hb)
    refine le_trans ?_ (Finset.single_le_sum (f := fun n' => ∑ m' ∈ Finset.range (n' + 1),
      schurMixedCellL2Jet π {τ} i b (Cc hh n' m')) (fun _ _ => zero_le) hn)
    exact Finset.single_le_sum (f := fun m' => schurMixedCellL2Jet π {τ} i b (Cc hh n m'))
      (fun _ _ => zero_le) (Finset.mem_range.2 (by omega))
  refine h1.trans ?_
  have h3 : (2 : ℝ≥0∞) ^ i ≤ 2 ^ (r + 2) := pow_le_pow_right₀ (by norm_num) hi
  calc (2 : ℝ≥0∞) ^ i * schurMixedCellL2Jet π {τ} i b (Cc hh n m)
      ≤ 2 ^ (r + 2) * ENNReal.ofReal θ := mul_le_mul' h3 h2
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp

/-- **Pointwise-in-time bound** of the word derivatives of the transition source field. -/
theorem time_pointwise (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (N hh r kres : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) {ℓ ρ e rs εc : ℝ} (ψ : ℝ → ℝ) (a : ℝ → Vec 2 → ∀ i, h i)
    (t τ : ℝ) (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) (hρ : 0 < ρ) (hrs : 0 < rs)
    (hrse : rs ≤ e) (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1)
    (hk : N + 2 ≤ kres) (ha : ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t))
    (hbox : ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u,
      IsBoxSmooth (r + 2) r (fun X y => Cc hh n m α τ X y v u))
    (hper : ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u X,
      AVenhance.IsZ2Periodic (fun y => Cc hh n m α τ X y v u))
    (θ : ℝ)
    (hdecay : ∀ p, p ≤ r + 2 → ∀ q, q ≤ r →
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1),
        schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤ ENNReal.ofReal θ)
    {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β
          (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (ψ t ^ 2 * srcConst N j) * ENNReal.ofReal (2 ^ (r + 2) * θ) ^ 2 *
          ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalFactorialSq ρ (kres + r) (fun x => a t x u) := by
  have hag : (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ = fun X' => a t (ρ • X') := by
    simp only [hℓτ]
  have hg : ContDiff ℝ ((kres + r : ℕ) : ℕ∞) (a t) :=
    ha.of_le (by exact_mod_cast Nat.le_succ _)
  have hbox' : ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u,
      IsBoxSmooth (j + 2) j (fun X y => Cc hh n m α τ X y v u) := fun n hn1 hnN m α v u =>
    (hbox n hn1 hnN m α v u).mono (by omega) (by omega)
  have hsm : ∀ n ∈ Finset.Icc 1 N, ∀ v, ContDiff ℝ (j : ℕ∞) (fun x' =>
      liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ (ρ⁻¹ • x') (e⁻¹ • x') v) := by
    intro n hn v
    have hn1 := (Finset.mem_Icc.1 hn).1
    have hnN := (Finset.mem_Icc.1 hn).2
    have ha' : ContDiff ℝ (((j + 2) + n : ℕ) : ℕ∞) ((fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) τ) := by
      rw [hag]
      exact (hg.of_le (by exact_mod_cast (by omega : j + 2 + n ≤ kres + r))).comp
        (contDiff_const_smul ρ)
    exact CoarseFluxDiff.contDiff_sample
      (isBoxSmooth_liftApply n (j + 2) j (Cc hh n) _ τ (hbox' n hn1 hnN) ha' v)
      (by omega) le_rfl ρ e
  refine source_word_bound π N hh Cc ℓ ρ e rs εc ψ a t τ hτt hε0 hε1 β hsm
    (ENNReal.ofReal (2 ^ (r + 2) * θ)) _ fun n hn => ?_
  have hn1 := (Finset.mem_Icc.1 hn).1
  have hnN := (Finset.mem_Icc.1 hn).2
  exact degree_word_bound π hπ {τ} n (kres + r) (Cc hh n) (Set.mem_singleton τ) β hρ hrs hrse heρ
    M hM (by omega) (hbox' n hn1 hnN) (hper n hn1 hnN) _
    (fun b hb δ i hi m hm => schurMixedJet_le_of_decay π N hh r Cc hbox θ hdecay hn
      (by omega) δ (by omega) hm) _ (a t) hag hg
end

/-! The residual norm of the transition source field from the pointwise-in-time bound and the
exponential decay of the entrance jets over the trimmed quiet window. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The constant of the word derivative of length `j`. -/
def wordConst (N r j : ℕ) (C₀ : ℝ) : ℝ := Real.sqrt (srcConst N j) * 2 ^ (r + 2) * C₀

theorem wordConst_nonneg (N r j : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 0 ≤ wordConst N r j C₀ := by
  unfold wordConst; positivity

/-- The pointwise bound at a time in the trimmed window (or zero outside the support of `ψ`). -/
theorem sqrt_bound_at (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (N hh r kres : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) {B ℓ ρ e rs εc c₀ C₀ A M δ g d : ℝ} (ψ : ℝ → ℝ)
    (a : ℝ → Vec 2 → ∀ i, h i) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hrs : 0 < rs) (hrse : rs ≤ e)
    (heρ : e ≤ ρ) (M₀ : ℕ) (hM₀ : e⁻¹ = (M₀ : ℝ)) (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1)
    (hk : N + 2 ≤ kres) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hδ0 : 0 ≤ δ)
    (hψM : ∀ t, |ψ t| ≤ M) (hψsupp : Function.support ψ ⊆ Set.Icc (g + δ) (g + d))
    (ha : ∀ t, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t))
    (hbox : ∀ τ, g / ℓ ^ 2 ≤ τ → τ ≤ (g + d) / ℓ ^ 2 → ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u,
      IsBoxSmooth (r + 2) r (fun X y => Cc hh n m α τ X y v u))
    (hper : ∀ τ, g / ℓ ^ 2 ≤ τ → τ ≤ (g + d) / ℓ ^ 2 → ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u X,
      AVenhance.IsZ2Periodic (fun y => Cc hh n m α τ X y v u))
    (hdecay : ∀ τ, g / ℓ ^ 2 ≤ τ → τ ≤ (g + d) / ℓ ^ 2 → ∀ p, p ≤ r + 2 → ∀ q, q ≤ r →
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1),
        schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤
          ENNReal.ofReal (C₀ * A * Real.exp (-(c₀ * (τ - g / ℓ ^ 2)))))
    {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) {t : ℝ} (ht : t ∈ Set.Icc g (g + d)) :
    (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β
          (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (Set.Icc (g + δ) (g + d)).indicator (fun t => ENNReal.ofReal (M * wordConst N r j C₀ * A) *
          classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (kres + r) a *
          ENNReal.ofReal (Real.exp (-(c₀ / ℓ ^ 2 * (t - g))))) t := by
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  by_cases hψt : ψ t = 0
  · have h0 : (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') = fun _ => 0 := by
      funext x'; simp [transitionSourceField, hψt]
    rw [h0, orderedDerivative_const_zero]
    simp
  · have htI : t ∈ Set.Icc (g + δ) (g + d) := hψsupp (Function.mem_support.2 hψt)
    rw [Set.indicator_of_mem htI]
    set τ : ℝ := (ℓ ^ 2)⁻¹ * t with hτ
    have hℓτ : ℓ ^ 2 * τ = t := by rw [hτ, ← mul_assoc, mul_inv_cancel₀ hℓ2.ne', one_mul]
    have hτ1 : g / ℓ ^ 2 ≤ τ := by
      rw [hτ, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (by linarith [htI.1]) (inv_nonneg.2 hℓ2.le)
    have hτ2 : τ ≤ (g + d) / ℓ ^ 2 := by
      rw [hτ, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left htI.2 (inv_nonneg.2 hℓ2.le)
    have hθ : 0 ≤ C₀ * A * Real.exp (-(c₀ * (τ - g / ℓ ^ 2))) := by positivity
    have key := time_pointwise π hπ N hh r kres Cc ψ a t τ rfl hℓτ hρ hrs hrse heρ M₀ hM₀ hε0 hε1
      hk (ha t) (hbox τ hτ1 hτ2) (hper τ hτ1 hτ2)
      (C₀ * A * Real.exp (-(c₀ * (τ - g / ℓ ^ 2)))) (hdecay τ hτ1 hτ2) hj β
    have hexp : c₀ * (τ - g / ℓ ^ 2) = c₀ / ℓ ^ 2 * (t - g) := by
      rw [hτ]; ring
    have hreal : |ψ t| * Real.sqrt (srcConst N j) *
        (2 ^ (r + 2) * (C₀ * A * Real.exp (-(c₀ * (τ - g / ℓ ^ 2))))) ≤
        M * wordConst N r j C₀ * A * Real.exp (-(c₀ / ℓ ^ 2 * (t - g))) := by
      rw [hexp]
      unfold wordConst
      calc |ψ t| * Real.sqrt (srcConst N j) *
            (2 ^ (r + 2) * (C₀ * A * Real.exp (-(c₀ / ℓ ^ 2 * (t - g)))))
          = |ψ t| * (Real.sqrt (srcConst N j) * 2 ^ (r + 2) * C₀ * A *
              Real.exp (-(c₀ / ℓ ^ 2 * (t - g)))) := by ring
        _ ≤ M * (Real.sqrt (srcConst N j) * 2 ^ (r + 2) * C₀ * A *
              Real.exp (-(c₀ / ℓ ^ 2 * (t - g)))) :=
            mul_le_mul_of_nonneg_right (hψM t) (by positivity)
        _ = _ := by ring
    calc (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
          ‖(rs ^ j • orderedDerivative β
            (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (ψ t ^ 2 * srcConst N j) *
            ENNReal.ofReal (2 ^ (r + 2) * (C₀ * A * Real.exp (-(c₀ * (τ - g / ℓ ^ 2))))) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              classicalFactorialSq ρ (kres + r) (fun x => a t x u)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow key (by norm_num)
      _ = ENNReal.ofReal (|ψ t| * Real.sqrt (srcConst N j) *
            (2 ^ (r + 2) * (C₀ * A * Real.exp (-(c₀ * (τ - g / ℓ ^ 2)))))) *
          (∑ u, ENNReal.ofReal (π u)⁻¹ *
              classicalFactorialSq ρ (kres + r) (fun x => a t x u)) ^ (1 / 2 : ℝ) :=
          rpow_half_bound _ _ _ (srcConst_nonneg N j) (by positivity) _
      _ ≤ ENNReal.ofReal (M * wordConst N r j C₀ * A * Real.exp (-(c₀ / ℓ ^ 2 * (t - g)))) *
          classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (kres + r) a :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hreal)
            (sqrt_factorialSq_le_energy ρ B π _ (kres + r) a ht)
      _ = _ := by
          have hM0 : 0 ≤ M := (abs_nonneg _).trans (hψM 0)
          rw [ENNReal.ofReal_mul (by have := wordConst_nonneg N r j hC₀; positivity)]
          ring

/-- **The residual norm of the transition source field.** -/
theorem core_bound (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (N hh r kres : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) {ν B ℓ ρ e rs εc c₀ C₀ A M δ g d Ks : ℝ} (ψ : ℝ → ℝ)
    (a : ℝ → Vec 2 → ∀ i, h i) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hrs : 0 < rs) (hrse : rs ≤ e)
    (heρ : e ≤ ρ) (M₀ : ℕ) (hM₀ : e⁻¹ = (M₀ : ℝ)) (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1)
    (hk : N + 2 ≤ kres) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hd : 0 < d) (hδ0 : 0 ≤ δ) (hδd : δ ≤ d)
    (hψM : ∀ t, |ψ t| ≤ M) (hψsupp : Function.support ψ ⊆ Set.Icc (g + δ) (g + d))
    (ha : ∀ t, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t))
    (hbox : ∀ τ, g / ℓ ^ 2 ≤ τ → τ ≤ (g + d) / ℓ ^ 2 → ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u,
      IsBoxSmooth (r + 2) r (fun X y => Cc hh n m α τ X y v u))
    (hper : ∀ τ, g / ℓ ^ 2 ≤ τ → τ ≤ (g + d) / ℓ ^ 2 → ∀ n, 1 ≤ n → n ≤ N → ∀ m α v u X,
      AVenhance.IsZ2Periodic (fun y => Cc hh n m α τ X y v u))
    (hdecay : ∀ τ, g / ℓ ^ 2 ≤ τ → τ ≤ (g + d) / ℓ ^ 2 → ∀ p, p ≤ r + 2 → ∀ q, q ≤ r →
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1),
        schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤
          ENNReal.ofReal (C₀ * A * Real.exp (-(c₀ * (τ - g / ℓ ^ 2)))))
    {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) (hKs : wordConst N r j C₀ ≤ Ks) :
    residualNorm ν π (Set.Icc g (g + d)) (fun _ _ _ => 0)
        (fun t x => rs ^ j • orderedDerivative β
          (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x)
      ≤ ENNReal.ofReal (Ks / Real.sqrt c₀ * A * M * ℓ * Real.sqrt d *
          Real.exp (-(c₀ * δ / ℓ ^ 2))) *
        classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (kres + r) a := by
  have hlam : 0 < c₀ / ℓ ^ 2 := by positivity
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hψM 0)
  set Eng := classicalStrongEnergy ρ B π (Set.Icc g (g + d)) (kres + r) a with hEng
  set Kj := wordConst N r j C₀ with hKj
  have hKj0 : 0 ≤ Kj := wordConst_nonneg N r j hC₀
  rw [residualNorm_zero_flux]
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(c₀ / ℓ ^ 2 * (t - g)))) :=
    Measurable.ennreal_ofReal (by fun_prop)
  calc ∫⁻ t in Set.Icc g (g + d), (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(rs ^ j • orderedDerivative β
          (fun x' => transitionSourceField N hh ℓ ρ e εc ψ Cc a t x') x) v‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ t in Set.Icc g (g + d), (Set.Icc (g + δ) (g + d)).indicator
          (fun t => ENNReal.ofReal (M * Kj * A) * Eng *
            ENNReal.ofReal (Real.exp (-(c₀ / ℓ ^ 2 * (t - g))))) t :=
        setLIntegral_mono' measurableSet_Icc fun t ht =>
          sqrt_bound_at π hπ N hh r kres Cc ψ a hℓ hρ hrs hrse heρ M₀ hM₀ hε0 hε1 hk hC₀ hA hδ0
            hψM hψsupp ha hbox hper hdecay hj β ht
    _ = ∫⁻ t in Set.Icc (g + δ) (g + d), ENNReal.ofReal (M * Kj * A) * Eng *
            ENNReal.ofReal (Real.exp (-(c₀ / ℓ ^ 2 * (t - g))))
          ∂(volume.restrict (Set.Icc g (g + d))) :=
        lintegral_indicator measurableSet_Icc _
    _ ≤ ∫⁻ t in Set.Icc (g + δ) (g + d), ENNReal.ofReal (M * Kj * A) * Eng *
            ENNReal.ofReal (Real.exp (-(c₀ / ℓ ^ 2 * (t - g)))) :=
        lintegral_mono' (Measure.restrict_mono_measure Measure.restrict_le_self _) le_rfl
    _ = ENNReal.ofReal (M * Kj * A) * Eng * ∫⁻ t in Set.Icc (g + δ) (g + d),
            ENNReal.ofReal (Real.exp (-(c₀ / ℓ ^ 2 * (t - g)))) :=
        lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal (M * Kj * A) * Eng * ENNReal.ofReal (Real.exp (-(c₀ / ℓ ^ 2 * (g + δ - g))) *
            Real.sqrt ((g + d - (g + δ)) / (c₀ / ℓ ^ 2))) := by
        gcongr
        exact lintegral_exp_Icc_le g (c₀ / ℓ ^ 2) (g + δ) (g + d) hlam (by linarith)
    _ = ENNReal.ofReal (M * Kj * A * (Real.exp (-(c₀ / ℓ ^ 2 * (g + δ - g))) *
            Real.sqrt ((g + d - (g + δ)) / (c₀ / ℓ ^ 2)))) * Eng := by
        rw [ENNReal.ofReal_mul (p := M * Kj * A) (by positivity)]
        ring
    _ ≤ _ := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (final_real_ineq (g := g) hKj0 hKs hM0 hA hc₀ hℓ hd.le hδ0 rfl)) le_rfl
end

end AVRegularity.QuietDecay.Partition
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! **The statement `Statement` from the quiet-gap decay lemma**.
Given the decay statement `DecayStatementU` at every raised order, the differentiated residual of a
transition of the time partition (statement `Statement`) holds. The residual flux vanishes, so the residual
norm is the `L¹_t L²_x` norm of the word derivatives of the transition source, which is bounded pointwise in time by the decaying
entrance jets of the coefficients (`Partition.time_pointwise`) and integrated over the trimmed
window (`Partition.core_bound`). -/

universe u v

/-- The differentiated partition statement from the decay statement without the slow scale factor. -/
theorem statement_of_decayU (Acl N D H kl Ll : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (hdec : ∀ r : ℕ, DecayStatementU.{u, v} N D H (Acl + 2 + r) (kl + r) (Ll + r) CG Cw Cj) :
    Statement.{u, v} Acl N D H kl Ll CG Cw Cj := by
  intro hA r
  obtain ⟨C₀, c₀, hC₀, hc₀, hd⟩ := hdec r
  refine ⟨(∑ j ∈ Finset.range (r + 1), Partition.wordConst N r j C₀) / Real.sqrt c₀, c₀,
    div_nonneg (Finset.sum_nonneg fun j _ => Partition.wordConst_nonneg N r j hC₀)
      (Real.sqrt_nonneg _), hc₀, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam hrs hrse heρ par V qs qf b Θ kres s0
    hkres hs0 hset hM Cc hseq g d hd0 hg1 hg2 hquiet I hI ψ M δ hδ0 hδd hψM hψsupp hh hhH a ha
    hper j hj β
  subst hs0
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨v₀⟩⟩
  · simp [residualNorm, Finset.univ_eq_empty]
  obtain ⟨M₀, hM₀⟩ := hM
  have he := hset.e_pos
  have hν := hset.ν_pos
  have hB := hset.B_pos
  have hρ := hset.ρ_pos
  have hsν := Real.sqrt_pos.2 hν
  have hℓ : 0 < ℓ := by rw [hset.ℓ_eq]; exact div_pos he hsν
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hεc_eq : εc = ℓ * Real.sqrt B / ρ := by rw [hset.εc_eq, hset.dstar_eq]
  have hεc0 : 0 ≤ εc := by rw [hεc_eq]; positivity
  have hΘ : 0 ≤ Θ := le_trans (Finset.sum_nonneg fun u _ => hset.envelope.nonneg v₀ u)
    (hset.envelope.row_sum v₀)
  have hlam0 : 0 ≤ lam := by rw [hset.lam_eq]; exact div_nonneg hρ.le hset.E_pos.le
  have hA0 : 0 ≤ ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') * I b' :=
    Finset.sum_nonneg fun b' hb' => mul_nonneg (pow_nonneg hΘ _)
      (hI.1 b' (by have := Finset.mem_range.1 hb'; omega))
  have hT : 0 < d / ℓ ^ 2 := by positivity
  have ht0 : t₀ ≤ g / ℓ ^ 2 := by rw [le_div_iff₀ hℓ2, mul_comm]; exact hg1
  have hsT : g / ℓ ^ 2 + d / ℓ ^ 2 ≤ t₁ := by
    rw [← add_div, div_le_iff₀ hℓ2, mul_comm]; exact hg2
  have hquiet' : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z)
      (Set.Icc (g / ℓ ^ 2) (g / ℓ ^ 2 + d / ℓ ^ 2)) := by
    rw [← add_div]; exact hquiet
  have hdec' := hd Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq (g / ℓ ^ 2)
    (d / ℓ ^ 2) hT ht0 hsT hquiet' I hI hh hhH
  have hτ0 : ∀ τ, g / ℓ ^ 2 ≤ τ → τ ≤ (g + d) / ℓ ^ 2 → τ ∈ Set.Icc t₀ t₁ := fun τ h1 h2 =>
    ⟨ht0.trans h1, h2.trans (by rw [add_div]; exact hsT)⟩
  refine (Partition.core_bound π hset.mass_pos N hh r kres Cc ψ a hℓ hρ hrs hrse heρ M₀ hM₀ hεc0
    hset.εc_le (by omega) hc₀ hC₀ hA0 hd0 hδ0 hδd hψM hψsupp ha ?_ ?_ ?_ hj β
    (Finset.single_le_sum (f := fun j' => Partition.wordConst N r j' C₀)
      (fun j' _ => Partition.wordConst_nonneg N r j' hC₀) (Finset.mem_range.2 (by omega)))).trans
    (le_of_eq rfl)
  · intro τ h1 h2 n hn1 hnN m α v u
    exact ((hseq.2.2.2.2.2.1 hh hhH n m α v u τ (hτ0 τ h1 h2)).1).mono (by omega)
      (le_trans (by omega) (le_max_left _ _))
  · intro τ h1 h2 n hn1 hnN m α v u X
    exact (hseq.2.2.2.2.2.1 hh hhH n m α v u τ (hτ0 τ h1 h2)).2 X
  · intro τ h1 h2 p hp q hq
    refine (hdec' τ ⟨h1, by rwa [add_div] at h2⟩ p (by omega) q
      (le_trans hq (le_trans (by omega) (le_max_left _ _)))).trans ?_
    exact le_rfl

end AVRegularity.QuietDecay
end
end
