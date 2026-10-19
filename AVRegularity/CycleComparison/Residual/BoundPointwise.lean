-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.ChainProject
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.TailJets
public import AVRegularity.CycleComparison.Residual.TailJets.Main

section
/-! Facade for the chart-transport helpers: `part1` (Piola-pushed pair), `part2` (pull-back strong
energy), `part3` (inverse-Piola pull-back flux). -/
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The sampling inequality for vector and scalar two-scale fields, in terms of the fibrewise
slow jets `vecJet` and `scalJet`, for `ϑ = e/ρ ≤ 1`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lower integrals are superadditive over finite sums. -/
theorem sum_lintegral_le_lintegral_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    simp_rw [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- Sampling a scalar two-scale field. -/
theorem diag_scal_sq_le (z : Vec 2 → Vec 2 → E) (hz : IsSlowSmooth 2 z)
    (hper : ∀ X, AVenhance.IsZ2Periodic (z X)) {ρ e : ℝ} (hρ : 0 < ρ) (he : 0 < e)
    (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ‖z (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2
      ≤ ENNReal.ofReal (4 * ρ ^ 2) *
          ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, scalJet z m X := by
  refine (diag_sampling_sq_le z hz hper hρ he M hM).trans ?_
  gcongr with m _
  refine le_trans ?_ (sum_lintegral_le_lintegral_sum _ _)
  gcongr with β _
  have hϑ : (e / ρ) ^ (2 * m) ≤ 1 :=
    pow_le_one₀ (div_nonneg he.le hρ.le) ((div_le_one hρ).2 heρ)
  calc ENNReal.ofReal ((e / ρ) ^ (2 * m)) * _ ≤ 1 * _ := by
        gcongr; exact ENNReal.ofReal_le_one.2 hϑ
    _ = _ := one_mul _

/-- Sampling a vector two-scale field. -/
theorem diag_vec_sq_le (W : Vec 2 → Vec 2 → Fin 2 → E) (hW : IsSlowSmooth 2 W)
    (hper : ∀ X, AVenhance.IsZ2Periodic (W X)) {ρ e : ℝ} (hρ : 0 < ρ) (he : 0 < e)
    (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖W (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2
      ≤ ENNReal.ofReal (4 * ρ ^ 2) *
          ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, vecJet W m X := by
  have hcomp : ∀ k : Fin 2, IsSlowSmooth 2 (fun X y => W X y k) := fun k => hW.component k
  have hperk : ∀ k : Fin 2, ∀ X, AVenhance.IsZ2Periodic (fun y => W X y k) := by
    intro k X n y
    exact congrFun (hper X n y) k
  have hmeas : ∀ k : Fin 2, Measurable fun x : Vec 2 => ‖W (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2 := by
    intro k
    have hc : Continuous fun x : Vec 2 => W (ρ⁻¹ • x) (e⁻¹ • x) k :=
      (hcomp k).continuous_uncurry.comp
        ((continuous_const_smul _).prodMk (continuous_const_smul _))
    exact hc.enorm.measurable.pow_const 2
  rw [lintegral_finsetSum _ fun k _ => hmeas k]
  calc ∑ k : Fin 2, ∫⁻ x in AVenhance.unitCube, ‖W (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2
      ≤ ∑ k : Fin 2, ENNReal.ofReal (4 * ρ ^ 2) *
          ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, scalJet (fun X y => W X y k) m X :=
        Finset.sum_le_sum fun k _ =>
          diag_scal_sq_le (fun X y => W X y k) (hcomp k) (hperk k) hρ he heρ M hM
    _ = ENNReal.ofReal (4 * ρ ^ 2) * ∑ m ∈ Finset.range 3,
          ∑ k : Fin 2, ∫⁻ X in slowCell ρ, scalJet (fun X y => W X y k) m X := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
        gcongr with m _
        refine (sum_lintegral_le_lintegral_sum _ _).trans (lintegral_mono fun X => ?_)
        unfold scalJet vecJet
        rw [Finset.sum_comm]
        gcongr with β _
        exact sum_lintegral_le_lintegral_sum _ _

end AVRegularity
end
end

section
/-! The sampled flux `∑_{j<A} ϑ^j (V_j)_diag` and the sampled remainder `(f_A)_diag` of a cleanup
chain, bounded by the slow jets of the initial pair `(f₀, F₀)`, for one Hilbert component. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The jet density of the initial pair of a cleanup chain. -/
def pairJet (f₀ : Vec 2 → Vec 2 → E) (F₀ : Vec 2 → Vec 2 → Fin 2 → E) (p : ℕ) (X : Vec 2) :
    ℝ≥0∞ :=
  vecJet F₀ p X + scalJet f₀ p X

theorem two_mul_antidivConst_le_one : 2 * antidivConst ≤ 1 := by
  unfold antidivConst
  have hπ : (2 : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) Real.two_le_pi 2
  have h1 : (2 : ℝ) * (4 * Real.pi ^ 2)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (by positivity)]
    linarith
  calc (2 : ℝ≥0∞) * ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹)
      = ENNReal.ofReal (2 * (4 * Real.pi ^ 2)⁻¹) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; simp
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h1
    _ = 1 := ENNReal.ofReal_one

theorem antidivConst_le_one : antidivConst ≤ 1 :=
  le_trans (by
    calc antidivConst = 1 * antidivConst := (one_mul _).symm
      _ ≤ 2 * antidivConst := by gcongr; norm_num) two_mul_antidivConst_le_one

/-- `V_0 = F₀ + 𝒜_z f₀` is bounded by the pair jet. -/
theorem vecJet_cleanupChain_zero_le_pairJet {sX sZ A : ℕ} (hZ : 1 ≤ sZ)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsSlowSmooth sX F₀) (hf₀ : IsSlowSmooth sX f₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V)
    {p : ℕ} (hp : p ≤ sX) (X : Vec 2) : vecJet (V 0) p X ≤ 2 * pairJet f₀ F₀ p X := by
  refine (vecJet_cleanupChain_zero_le hZ hF hV hp (hf₀.mono hp) X).trans ?_
  unfold pairJet
  rw [mul_add]
  gcongr
  calc antidivConst * scalJet f₀ p X ≤ 1 * scalJet f₀ p X := by
        gcongr; exact antidivConst_le_one
    _ = _ := one_mul _

/-- Reindexing a shifted window of jets into a fixed range. -/
theorem sum_range_shift_le (g : ℕ → ℝ≥0∞) {j n K : ℕ} (h : n + j ≤ K) :
    ∑ m ∈ Finset.range n, g (m + j) ≤ ∑ p ∈ Finset.range K, g p := by
  have hinj : Set.InjOn (fun m => m + j) (Finset.range n : Set ℕ) :=
    fun a _ b _ hab => by simpa using hab
  rw [← Finset.sum_image (f := g) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => zero_le
  intro p hp
  simp only [Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨m, hm, rfl⟩ := hp
  exact Finset.mem_range.2 (by omega)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The members of a cleanup chain of a periodic flux are periodic in the fast variable. -/
theorem IsCleanupChain.periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {sX sZ A : ℕ} {f₀ : Vec 2 → Vec 2 → F} {F₀ : Vec 2 → Vec 2 → Fin 2 → F}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F} (hFper : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) :
    ∀ j, j < A → ∀ X, AVenhance.IsZ2Periodic (V j X) := by
  obtain ⟨⟨W₀, hW₀, hV0⟩, hVj⟩ := hV
  intro j hj X
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · intro n y
    rw [hV0]
    funext k
    simp only
    rw [congrFun (hFper X n y) k, congrFun (hW₀.2.1 X n y) k]
  · exact (hVj j hjpos hj).2.1 X

/-- A cleanup source of a periodic field is periodic in the fast variable. -/
theorem cleanupSource_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → F} {j : ℕ}
    (hper : ∀ X, AVenhance.IsZ2Periodic (V (j - 1) X)) (X : Vec 2) :
    AVenhance.IsZ2Periodic (cleanupSource V j X) := by
  intro n y
  simp only [cleanupSource, slowPartial]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (fun X' => V (j - 1) X' (y + AVenhance.latticeShift n) k) = fun X' => V (j - 1) X' y k := by
    funext X'; exact congrFun (hper X' n y) k
  rw [this]

/-- The sampled cleanup flux of one component. -/
theorem cleanupFlux_density_le {sX sZ A : ℕ} (hZ : 1 ≤ sZ) (hsX : A + 1 ≤ sX)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsSlowSmooth sX F₀) (hFper : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hf₀ : IsSlowSmooth sX f₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) {ρ e : ℝ} (hρ : 0 < ρ)
    (he : 0 < e) (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2
      ≤ ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
          ∑ p ∈ Finset.range (A + 2), ∫⁻ X in slowCell ρ, pairJet f₀ F₀ p X := by
  have hslow := IsCleanupChain.isSlowSmooth hF hV
  have hper := IsCleanupChain.periodic hFper hV
  have hϑ : ∀ j : ℕ, ‖(e / ρ) ^ j‖ₑ ≤ 1 := by
    intro j
    rw [enorm_pow]
    refine pow_le_one₀ bot_le ?_
    rw [Real.enorm_eq_ofReal (div_nonneg he.le hρ.le)]
    exact ENNReal.ofReal_le_one.2 ((div_le_one hρ).2 heρ)
  -- pointwise
  have hpt : ∀ x, ∑ k : Fin 2,
      ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2 ≤
      (A : ℝ≥0∞) * ∑ j ∈ Finset.range A, ∑ k : Fin 2, ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2 := by
    intro x
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2
        ≤ (∑ j ∈ Finset.range A, ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ) ^ 2 := by
          gcongr
          refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [enorm_smul]
          calc ‖(e / ρ) ^ j‖ₑ * ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ
              ≤ 1 * ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ := by gcongr; exact hϑ j
            _ = _ := one_mul _
      _ ≤ _ := by
          simpa using ennreal_sq_sum_le_card_mul_sum_sq (Finset.range A)
            (fun j => ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ)
  have hmeas : ∀ j ∈ Finset.range A, Measurable fun x : Vec 2 =>
      ∑ k : Fin 2, ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2 := by
    intro j hj
    have hc : Continuous fun x : Vec 2 => V j (ρ⁻¹ • x) (e⁻¹ • x) :=
      (hslow j (Finset.mem_range.1 hj)).continuous_uncurry.comp
        ((continuous_const_smul _).prodMk (continuous_const_smul _))
    exact Finset.measurable_sum _ fun k _ =>
      ((continuous_apply k).comp hc).enorm.measurable.pow_const 2
  -- each member
  have hmem : ∀ j ∈ Finset.range A, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
      ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2 ≤ ENNReal.ofReal (4 * ρ ^ 2) *
        (2 * ∑ p ∈ Finset.range (A + 2), ∫⁻ X in slowCell ρ, pairJet f₀ F₀ p X) := by
    intro j hj
    have hjA := Finset.mem_range.1 hj
    refine (diag_vec_sq_le (V j) ((hslow j hjA).mono (by omega)) (hper j hjA) hρ he heρ M
      hM).trans ?_
    gcongr
    calc ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, vecJet (V j) m X
        ≤ ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, 2 * pairJet f₀ F₀ (m + j) X := by
          refine Finset.sum_le_sum fun m hm => lintegral_mono fun X => ?_
          have hm3 := Finset.mem_range.1 hm
          calc vecJet (V j) m X ≤ (2 * antidivConst) ^ j * vecJet (V 0) (m + j) X :=
                vecJet_cleanupChain_le hZ hF hV j hjA m (by omega) X
            _ ≤ 1 * vecJet (V 0) (m + j) X := by
                gcongr; exact pow_le_one₀ bot_le two_mul_antidivConst_le_one
            _ ≤ _ := by
                rw [one_mul]
                exact vecJet_cleanupChain_zero_le_pairJet hZ hF hf₀ hV (by omega) X
      _ = 2 * ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, pairJet f₀ F₀ (m + j) X := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          exact lintegral_const_mul' _ _ (by norm_num)
      _ ≤ _ := by
          gcongr
          exact sum_range_shift_le (fun p => ∫⁻ X in slowCell ρ, pairJet f₀ F₀ p X) (by omega)
  calc ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2
      ≤ ∫⁻ x in AVenhance.unitCube, (A : ℝ≥0∞) *
          ∑ j ∈ Finset.range A, ∑ k : Fin 2, ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = (A : ℝ≥0∞) * ∑ j ∈ Finset.range A, ∫⁻ x in AVenhance.unitCube,
          ∑ k : Fin 2, ‖V j (ρ⁻¹ • x) (e⁻¹ • x) k‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ hmeas]
    _ ≤ (A : ℝ≥0∞) * ∑ j ∈ Finset.range A, ENNReal.ofReal (4 * ρ ^ 2) *
          (2 * ∑ p ∈ Finset.range (A + 2), ∫⁻ X in slowCell ρ, pairJet f₀ F₀ p X) := by
        gcongr with j hj
        exact hmem j hj
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          ← mul_assoc]
        congr 1
        rw [show (8 : ℝ) * (A : ℝ) ^ 2 * ρ ^ 2 = A * A * (4 * ρ ^ 2) * 2 by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp

/-- The sampled cleanup remainder of one component. -/
theorem cleanupRemainder_density_le {sX sZ A : ℕ} (hZ : 1 ≤ sZ) (hA : 1 ≤ A) (hsX : A + 2 ≤ sX)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E} {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hF : IsSlowSmooth sX F₀) (hFper : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hf₀ : IsSlowSmooth sX f₀) (hV : IsCleanupChain sX sZ A f₀ F₀ V) {ρ e : ℝ} (hρ : 0 < ρ)
    (he : 0 < e) (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ‖cleanupSource V A (ρ⁻¹ • x) (e⁻¹ • x)‖ₑ ^ 2
      ≤ ENNReal.ofReal (16 * ρ ^ 2) *
          ∑ p ∈ Finset.range (A + 3), ∫⁻ X in slowCell ρ, pairJet f₀ F₀ p X := by
  have hslow := IsCleanupChain.isSlowSmooth hF hV
  have hper := IsCleanupChain.periodic hFper hV
  have hsrc : IsSlowSmooth 2 (cleanupSource V A) :=
    isSlowSmooth_cleanupSource ((hslow (A - 1) (by omega)).mono (by omega))
  refine (diag_scal_sq_le _ hsrc (cleanupSource_periodic (hper (A - 1) (by omega))) hρ he heρ M
    hM).trans ?_
  calc ENNReal.ofReal (4 * ρ ^ 2) *
        ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, scalJet (cleanupSource V A) m X
      ≤ ENNReal.ofReal (4 * ρ ^ 2) *
          ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, 4 * pairJet f₀ F₀ (m + A) X := by
        gcongr with m hm X
        have hm3 := Finset.mem_range.1 hm
        calc scalJet (cleanupSource V A) m X
            ≤ 2 * ((2 * antidivConst) ^ (A - 1) * vecJet (V 0) (m + A) X) :=
              scalJet_cleanupChain_remainder_le hZ hA hF hV (by omega) X
          _ ≤ 2 * (1 * (2 * pairJet f₀ F₀ (m + A) X)) := by
              gcongr
              · exact pow_le_one₀ bot_le two_mul_antidivConst_le_one
              · exact vecJet_cleanupChain_zero_le_pairJet hZ hF hf₀ hV (by omega) X
          _ = 4 * pairJet f₀ F₀ (m + A) X := by ring
    _ = ENNReal.ofReal (4 * ρ ^ 2) * (4 *
          ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ, pairJet f₀ F₀ (m + A) X) := by
        rw [Finset.mul_sum (s := Finset.range 3) (a := (4 : ℝ≥0∞))]
        congr 1
        exact Finset.sum_congr rfl fun m _ => lintegral_const_mul' _ _ (by norm_num)
    _ ≤ ENNReal.ofReal (4 * ρ ^ 2) * (4 *
          ∑ p ∈ Finset.range (A + 3), ∫⁻ X in slowCell ρ, pairJet f₀ F₀ p X) := by
        gcongr
        exact sum_range_shift_le (fun p => ∫⁻ X in slowCell ρ, pairJet f₀ F₀ p X) (by omega)
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [show (16 : ℝ) * ρ ^ 2 = 4 * ρ ^ 2 * 4 by ring,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * ρ ^ 2)]
        simp

end AVRegularity

namespace AVRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise word-to-full conversion in `ℝ≥0∞`. -/
theorem sum_orderedDerivative_enorm_sq_le {p : ℕ} {g : Vec 2 → E} (hg : ContDiff ℝ (p : ℕ∞) g)
    (X : Vec 2) :
    ∑ β : DerivativeWord2 p, ‖orderedDerivative β g X‖ₑ ^ 2 ≤
      2 ^ p * ‖iteratedFDeriv ℝ p g X‖ₑ ^ 2 := by
  have h := sum_orderedDerivative_sq_le hg X
  have h' : ∑ β : DerivativeWord2 p, ‖orderedDerivative β g X‖ₑ ^ 2 =
      ENNReal.ofReal (∑ β : DerivativeWord2 p, ‖orderedDerivative β g X‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
    exact Finset.sum_congr rfl fun β _ => enorm_sq_eq_ofReal' _
  rw [h', enorm_sq_eq_ofReal', show (2 : ℝ≥0∞) ^ p = ENNReal.ofReal (2 ^ p) by simp,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- Word jets are controlled by the full slow derivative. -/
theorem scalJet_le_iteratedFDeriv {p : ℕ} (g : Vec 2 → Vec 2 → E)
    (hg : ∀ y, ContDiff ℝ (p : ℕ∞) (fun X => g X y)) (X : Vec 2) :
    scalJet g p X ≤ 2 ^ p * ∫⁻ y in AVenhance.unitCube,
      ‖iteratedFDeriv ℝ p (fun X' => g X' y) X‖ₑ ^ 2 := by
  unfold scalJet
  refine (sum_lintegral_le_lintegral_sum _ _).trans ?_
  rw [← lintegral_const_mul' _ _ (by simp)]
  exact lintegral_mono fun y => sum_orderedDerivative_enorm_sq_le (hg y) X

/-- Word jets of a vector field are controlled by the full slow derivatives. -/
theorem vecJet_le_iteratedFDeriv {p : ℕ} (W : Vec 2 → Vec 2 → Fin 2 → E)
    (hW : ∀ y k, ContDiff ℝ (p : ℕ∞) (fun X => W X y k)) (X : Vec 2) :
    vecJet W p X ≤ 2 ^ p * ∫⁻ y in AVenhance.unitCube, ∑ k : Fin 2,
      ‖iteratedFDeriv ℝ p (fun X' => W X' y k) X‖ₑ ^ 2 := by
  unfold vecJet
  refine (sum_lintegral_le_lintegral_sum _ _).trans ?_
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun y => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => sum_orderedDerivative_enorm_sq_le (hW y k) X

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The mass-weighted slow jets of the divided tail fields `f_a, F_a` at a fixed cell time, bounded by the Schur cell-`L²` jets of the presentation arrays
times positive jets of the coarse field. -/

section
namespace BoundTail

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The full slow jet of a finite combination with coefficients of size at most one. -/
theorem enorm_iteratedFDeriv_sum_sq_le {p : ℕ} (s : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ n ∈ s, |c n| ≤ 1) (g : ℕ → Vec 2 → F)
    (hg : ∀ n ∈ s, ContDiff ℝ (p : ℕ∞) (g n)) (X : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun X' => ∑ n ∈ s, c n • g n X') X‖ₑ ^ 2 ≤
      (s.card : ℝ≥0∞) * ∑ n ∈ s, ‖iteratedFDeriv ℝ p (g n) X‖ₑ ^ 2 := by
  have hsum : iteratedFDeriv ℝ p (fun X' => ∑ n ∈ s, c n • g n X') X =
      ∑ n ∈ s, c n • iteratedFDeriv ℝ p (g n) X := by
    rw [iteratedFDeriv_sum fun n hn => (hg n hn).const_smul (c n), Finset.sum_apply]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact iteratedFDeriv_const_smul_apply ((hg n hn).contDiffAt)
  rw [hsum]
  calc ‖∑ n ∈ s, c n • iteratedFDeriv ℝ p (g n) X‖ₑ ^ 2
      ≤ (∑ n ∈ s, ‖iteratedFDeriv ℝ p (g n) X‖ₑ) ^ 2 := by
        gcongr
        refine (enorm_sum_le s (fun n => c n • iteratedFDeriv ℝ p (g n) X)).trans
          (Finset.sum_le_sum fun n hn => ?_)
        rw [enorm_smul]
        calc ‖c n‖ₑ * ‖iteratedFDeriv ℝ p (g n) X‖ₑ ≤ 1 * ‖iteratedFDeriv ℝ p (g n) X‖ₑ := by
              gcongr
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_one.2 (hc n hn)
          _ = _ := one_mul _
    _ ≤ _ := ennreal_sq_sum_le_card_mul_sum_sq s _

/-- The cell jet of the zero field. -/
theorem cellL2Jet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (i : ℕ) :
    cellL2Jet I i (fun (_ : ℝ) (_ _ : Vec 2) => (0 : E)) = 0 := by
  unfold cellL2Jet
  refine le_antisymm (iSup₂_le fun t _ => iSup_le fun X => ?_) bot_le
  refine le_of_eq ?_
  have h0 : (fun z : Vec 2 => iteratedFDeriv ℝ i (fun _ : Vec 2 => (0 : E)) X) = 0 := by
    funext z; simp [iteratedFDeriv_fun_zero]
  rw [h0]
  exact eLpNorm_zero (ε := ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E)

/-- The Schur jet of an array that vanishes identically. -/
theorem schurCellL2Jet_eq_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) (i : ℕ) (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a t X z v u, c a t X z v u = 0) : schurCellL2Jet π I i c = 0 := by
  have h0 : ∀ a v u, (fun t X z => c a t X z v u) = fun _ _ _ => 0 := by
    intro a v u; funext t X z; exact hc a t X z v u
  unfold schurCellL2Jet schurSums
  simp only [h0, cellL2Jet_zero]
  simp

/-- Box smoothness gives the slow jets with no fast regularity. -/
theorem isBoxSmooth_slow_zero {sX sZ p : ℕ} {f : Vec 2 → Vec 2 → F}
    (hf : IsBoxSmooth sX sZ f) (hp : p ≤ sX) : IsBoxSmooth p 0 f := by
  refine ⟨fun X => (hf.1 X).of_le (by exact_mod_cast Nat.zero_le _), fun b hb z => ?_,
    fun a b ha hb => hf.2.2 a b (ha.trans hp) (hb.trans (Nat.zero_le _))⟩
  obtain rfl : b = 0 := by omega
  exact (hf.2.1 0 (Nat.zero_le _) z).of_le (by exact_mod_cast hp)

/-- Continuity in the fast variable of a full slow jet of a slow-smooth field. -/
theorem measurable_enorm_iteratedFDeriv_sq {m p : ℕ} {g : Vec 2 → Vec 2 → F}
    (hg : IsSlowSmooth m g) (hp : p ≤ m) (X : Vec 2) :
    Measurable fun y => ‖iteratedFDeriv ℝ p (fun X' => g X' y) X‖ₑ ^ 2 := by
  have hc : Continuous fun y => iteratedFDeriv ℝ p (fun X' => g X' y) X :=
    (hg.2 p hp).comp (Continuous.prodMk_right X)
  exact hc.enorm.measurable.pow_const 2

/-- Collapsing the Schur-weighted double sum onto positive coarse jets. -/
theorem collapse_le (M p : ℕ) (Sj : ℕ → ℕ → ℝ≥0∞) (W : ℕ → ℝ≥0∞) (s : ℝ≥0∞)
    (h0 : ∀ i, Sj 0 i = 0) (hs : ∀ m, ∀ i, i ≤ p → Sj m i ≤ s) :
    ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1), Sj m i ^ 2 * W (p - i + m)
      ≤ ((M + 1 : ℕ) : ℝ≥0∞) * ((p + 1 : ℕ) : ℝ≥0∞) * s ^ 2 *
          ∑ q ∈ Finset.Icc 1 (p + M), W q := by
  have hterm : ∀ m ∈ Finset.range (M + 1), ∀ i ∈ Finset.range (p + 1),
      Sj m i ^ 2 * W (p - i + m) ≤ s ^ 2 * ∑ q ∈ Finset.Icc 1 (p + M), W q := by
    intro m hm i hi
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp [h0]
    · have hq : p - i + m ∈ Finset.Icc 1 (p + M) := by
        simp only [Finset.mem_Icc]; have := Finset.mem_range.1 hm; omega
      gcongr
      · exact hs m i (by have := Finset.mem_range.1 hi; omega)
      · exact Finset.single_le_sum (f := W) (fun _ _ => bot_le) hq
  calc _ ≤ ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
        s ^ 2 * ∑ q ∈ Finset.Icc 1 (p + M), W q :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun i hi => hterm m hm i hi
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end BoundTail

section Tail

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The constant of `tail_pairJet_le`. -/
def tailPairConst (N D p : ℕ) : ℝ :=
  2 ^ p * ((N + D : ℕ) : ℝ) ^ 2 * (3 * tailJetConst (2 * N + D) p) *
    (((2 * N + D + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))

theorem tailPairConst_nonneg (N D p : ℕ) : 0 ≤ tailPairConst N D p := by
  unfold tailPairConst tailJetConst; positivity

/-- The mass-weighted pair jet of the divided tail fields at a fixed cell time. -/
theorem tail_pairJet_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (N D p : ℕ)
    (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h) (εc : ℝ) (hε0 : 0 ≤ εc)
    (hε1 : εc ≤ 1) (ac : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ I) (S : ℝ)
    (hbox : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ m α v u, IsBoxSmooth p 0 (fun X y => f n m α τ X y v u)) ∧
        ∀ k m α v u, IsBoxSmooth p 0 (fun X y => F n k m α τ X y v u))
    (hzero : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ α t X z v u, f n 0 α t X z v u = 0) ∧ ∀ k α t X z v u, F n k 0 α t X z v u = 0)
    (hjet : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ i, i ≤ p → ∀ m,
      schurCellL2Jet π I i (f n m) ≤ ENNReal.ofReal S ∧
        schurCellL2Jet π I i (fun q : DerivativeWord2 m × Fin 2 => F n q.2 m q.1)
          ≤ ENNReal.ofReal S)
    (ha : ContDiff ℝ ((p + (2 * N + D) : ℕ) : ℕ∞) (ac τ)) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ *
        pairJet (fun X y => tailScalarField f N D εc ac τ X y v)
          (fun X y k => tailFluxField F N D εc ac τ X y k v) p X
      ≤ ENNReal.ofReal (tailPairConst N D p) * ENNReal.ofReal S ^ 2 *
          ∑ q ∈ Finset.Icc 1 (p + (2 * N + D)),
            ∑ u, ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => ac τ X' u) X‖ₑ ^ 2 := by
  set M := 2 * N + D with hM
  set s := Finset.Icc (N + 1) (2 * N + D) with hsdef
  set W : ℕ → ℝ≥0∞ := fun q =>
    ∑ u, ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => ac τ X' u) X‖ₑ ^ 2 with hW
  have hcard : (s.card : ℝ≥0∞) = ((N + D : ℕ) : ℝ≥0∞) := by
    rw [hsdef, Nat.card_Icc]; congr 1; omega
  have hc : ∀ n ∈ s, |εc ^ (n - N - 1)| ≤ 1 := fun n _ => by
    rw [abs_of_nonneg (pow_nonneg hε0 _)]; exact pow_le_one₀ hε0 hε1
  -- scalar and flux pieces, per degree
  set gs : ℕ → ι → Vec 2 → Vec 2 → ℝ≥0∞ := fun n v X y =>
    ‖iteratedFDeriv ℝ p (fun X' => liftApply M (f n) ac τ X' y v) X‖ₑ ^ 2
  set gf : ℕ → ι → Vec 2 → Vec 2 → ℝ≥0∞ := fun n v X y => ∑ k : Fin 2,
    ‖iteratedFDeriv ℝ p (fun X' => liftApply M (F n k) ac τ X' y v) X‖ₑ ^ 2
  have hsc : ∀ n ∈ s, ∀ v y, ContDiff ℝ (p : ℕ∞) (fun X' => liftApply M (f n) ac τ X' y v) :=
    fun n hn v y => contDiff_liftApply (f n) ac τ y v
      (fun m α u => ((hbox n hn).1 m α v u).isSlowSmooth.1 y) ha
  have hfc : ∀ n ∈ s, ∀ v y k,
      ContDiff ℝ (p : ℕ∞) (fun X' => liftApply M (F n k) ac τ X' y v) :=
    fun n hn v y k => contDiff_liftApply (F n k) ac τ y v
      (fun m α u => ((hbox n hn).2 k m α v u).isSlowSmooth.1 y) ha
  have hms : ∀ n ∈ s, ∀ v, Measurable (gs n v X) := fun n hn v =>
    BoundTail.measurable_enorm_iteratedFDeriv_sq
      ((isSlowSmooth_liftApply M p (f n) ac τ
        (fun m α v u => ((hbox n hn).1 m α v u).isSlowSmooth) ha).clm_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)) le_rfl X
  have hmf : ∀ n ∈ s, ∀ v, Measurable (gf n v X) := fun n hn v =>
    Finset.measurable_sum _ fun k _ => BoundTail.measurable_enorm_iteratedFDeriv_sq
      ((isSlowSmooth_liftApply M p (F n k) ac τ
        (fun m α v u => ((hbox n hn).2 k m α v u).isSlowSmooth) ha).clm_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)) le_rfl X
  have hfunS : ∀ v y, (fun X' => tailScalarField f N D εc ac τ X' y v) =
      fun X' => ∑ n ∈ s, εc ^ (n - N - 1) • liftApply M (f n) ac τ X' y v := by
    intro v y; funext X'; simp [tailScalarField, Finset.sum_apply, hsdef, hM]
  have hfunF : ∀ v y k, (fun X' => tailFluxField F N D εc ac τ X' y k v) =
      fun X' => ∑ n ∈ s, εc ^ (n - N - 1) • liftApply M (F n k) ac τ X' y v := by
    intro v y k; funext X'; simp [tailFluxField, Finset.sum_apply, hsdef, hM]
  -- pointwise bounds on the tail fields
  have hscal : ∀ v y, ‖iteratedFDeriv ℝ p
      (fun X' => tailScalarField f N D εc ac τ X' y v) X‖ₑ ^ 2 ≤
      (s.card : ℝ≥0∞) * ∑ n ∈ s, gs n v X y := by
    intro v y
    rw [hfunS]
    exact BoundTail.enorm_iteratedFDeriv_sum_sq_le s _ hc _ (fun n hn => hsc n hn v y) X
  have hflux : ∀ v y, ∑ k : Fin 2, ‖iteratedFDeriv ℝ p
      (fun X' => tailFluxField F N D εc ac τ X' y k v) X‖ₑ ^ 2 ≤
      (s.card : ℝ≥0∞) * ∑ n ∈ s, gf n v X y := by
    intro v y
    simp only [gf]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hfunF]
    exact BoundTail.enorm_iteratedFDeriv_sum_sq_le s _ hc _ (fun n hn => hfc n hn v y k) X
  -- the Schur bounds per degree
  set Wsum := ∑ q ∈ Finset.Icc 1 (p + M), W q with hWsum
  set K0 : ℝ≥0∞ := ((M + 1 : ℕ) : ℝ≥0∞) * ((p + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal S ^ 2 * Wsum
  have hT2 : ∀ n ∈ s, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube, gs n v X y
      ≤ ENNReal.ofReal (tailJetConst M p) * K0 := by
    intro n hn
    refine (sum_mass_lintegral_iteratedFDeriv_liftApply_le π hπ I M p (f n) ac hτ
      (hbox n hn).1 ha X).trans ?_
    gcongr
    exact BoundTail.collapse_le M p (fun m i => schurCellL2Jet π I i (f n m)) W _
      (fun i => BoundTail.schurCellL2Jet_eq_zero π I i _ (hzero n hn).1)
      (fun m i hi => (hjet n hn i hi m).1)
  have hT3 : ∀ n ∈ s, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube, gf n v X y
      ≤ ENNReal.ofReal (2 * tailJetConst M p) * K0 := by
    intro n hn
    refine (sum_mass_lintegral_iteratedFDeriv_liftApply_flux_le π hπ I M p (F n) ac hτ
      (hbox n hn).2 ha X).trans ?_
    gcongr
    exact BoundTail.collapse_le M p
      (fun m i => schurCellL2Jet π I i (fun q : DerivativeWord2 m × Fin 2 => F n q.2 m q.1)) W _
      (fun i => BoundTail.schurCellL2Jet_eq_zero π I i _ fun q => (hzero n hn).2 q.2 q.1)
      (fun m i hi => (hjet n hn i hi m).2)
  -- each component
  have hcomp : ∀ v, pairJet (fun X y => tailScalarField f N D εc ac τ X y v)
      (fun X y k => tailFluxField F N D εc ac τ X y k v) p X ≤
      2 ^ p * ((s.card : ℝ≥0∞) * (∑ n ∈ s, ∫⁻ y in AVenhance.unitCube, gf n v X y)
        + (s.card : ℝ≥0∞) * ∑ n ∈ s, ∫⁻ y in AVenhance.unitCube, gs n v X y) := by
    intro v
    unfold pairJet
    have h1 := vecJet_le_iteratedFDeriv (fun X y k => tailFluxField F N D εc ac τ X y k v)
      (fun y k => by rw [hfunF]; exact ContDiff.sum fun n hn => (hfc n hn v y k).const_smul _) X
    have h2 := scalJet_le_iteratedFDeriv (fun X y => tailScalarField f N D εc ac τ X y v)
      (fun y => by rw [hfunS]; exact ContDiff.sum fun n hn => (hsc n hn v y).const_smul _) X
    refine (add_le_add h1 h2).trans ?_
    rw [← mul_add]
    gcongr 2 ^ p * (?_ + ?_)
    · refine (lintegral_mono fun y => hflux v y).trans ?_
      rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ fun n hn => hmf n hn v]
    · refine (lintegral_mono fun y => hscal v y).trans ?_
      rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ fun n hn => hms n hn v]
  have ht0 : 0 ≤ tailJetConst M p := by unfold tailJetConst; positivity
  have hK : ENNReal.ofReal (tailPairConst N D p) = 2 ^ p * (s.card : ℝ≥0∞) ^ 2 *
      (ENNReal.ofReal (2 * tailJetConst M p) + ENNReal.ofReal (tailJetConst M p)) *
        (((M + 1 : ℕ) : ℝ≥0∞) * ((p + 1 : ℕ) : ℝ≥0∞)) := by
    rw [← ENNReal.ofReal_add (by positivity) ht0, hcard]
    unfold tailPairConst
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity)]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, hM]
    congr 2
    · rw [show (2 : ℝ) * tailJetConst (2 * N + D) p + tailJetConst (2 * N + D) p =
        3 * tailJetConst (2 * N + D) p by ring, ENNReal.ofReal_mul (by norm_num)]
      simp
    · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have e : ∀ v, ENNReal.ofReal (π v)⁻¹ * (2 ^ p * ((s.card : ℝ≥0∞) *
      (∑ n ∈ s, ∫⁻ y in AVenhance.unitCube, gf n v X y)
        + (s.card : ℝ≥0∞) * ∑ n ∈ s, ∫⁻ y in AVenhance.unitCube, gs n v X y)) =
      2 ^ p * (s.card : ℝ≥0∞) * ∑ n ∈ s, (ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ y in AVenhance.unitCube, gf n v X y)
      + 2 ^ p * (s.card : ℝ≥0∞) * ∑ n ∈ s, (ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ y in AVenhance.unitCube, gs n v X y) := by
    intro v; rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ *
        pairJet (fun X y => tailScalarField f N D εc ac τ X y v)
          (fun X y k => tailFluxField F N D εc ac τ X y k v) p X
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (2 ^ p * ((s.card : ℝ≥0∞) *
          (∑ n ∈ s, ∫⁻ y in AVenhance.unitCube, gf n v X y)
            + (s.card : ℝ≥0∞) * ∑ n ∈ s, ∫⁻ y in AVenhance.unitCube, gs n v X y)) :=
        Finset.sum_le_sum fun v _ => by gcongr; exact hcomp v
    _ = 2 ^ p * (s.card : ℝ≥0∞) * (∑ n ∈ s, ∑ v, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ y in AVenhance.unitCube, gf n v X y)
        + 2 ^ p * (s.card : ℝ≥0∞) * (∑ n ∈ s, ∑ v, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ y in AVenhance.unitCube, gs n v X y) := by
        rw [Finset.sum_congr rfl fun v _ => e v, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
    _ ≤ 2 ^ p * (s.card : ℝ≥0∞) * (∑ n ∈ s, ENNReal.ofReal (2 * tailJetConst M p) * K0)
        + 2 ^ p * (s.card : ℝ≥0∞) * (∑ n ∈ s, ENNReal.ofReal (tailJetConst M p) * K0) := by
        gcongr with n hn n hn
        · exact hT3 n hn
        · exact hT2 n hn
    _ = _ := by
        rw [hK]
        simp only [Finset.sum_const, nsmul_eq_mul, K0]
        ring

end Tail
end

/-! Regularity of the divided tail fields, and the slow-cell integral of their pair jets in
terms of the gradient energy density of the physical field at one time. -/

section
section Tail

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The tail scalar field is slow smooth. -/
theorem isSlowSmooth_tailScalarField {N D m : ℕ} (f : ℕ → LiftCoeff ι h) (εc : ℝ)
    (ac : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ)
    (hf : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ m' α v u,
      IsSlowSmooth m (fun X y => f n m' α τ X y v u))
    (ha : ContDiff ℝ ((m + (2 * N + D) : ℕ) : ℕ∞) (ac τ)) :
    IsSlowSmooth m (tailScalarField f N D εc ac τ) := by
  unfold tailScalarField
  exact IsSlowSmooth.sum _ fun n hn =>
    (isSlowSmooth_liftApply (2 * N + D) m (f n) ac τ (hf n hn) ha).const_smul _

/-- The tail flux field is slow smooth. -/
theorem isSlowSmooth_tailFluxField {N D m : ℕ} (F : ℕ → Fin 2 → LiftCoeff ι h) (εc : ℝ)
    (ac : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ)
    (hF : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ k m' α v u,
      IsSlowSmooth m (fun X y => F n k m' α τ X y v u))
    (ha : ContDiff ℝ ((m + (2 * N + D) : ℕ) : ℕ∞) (ac τ)) :
    IsSlowSmooth m (tailFluxField F N D εc ac τ) := by
  refine IsSlowSmooth.pi (H := fun _ : Fin 2 => ∀ i, h i) fun k => ?_
  show IsSlowSmooth m (fun X y => ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
    εc ^ (n - N - 1) • liftApply (2 * N + D) (F n k) ac τ X y)
  exact IsSlowSmooth.sum _ fun n hn =>
    (isSlowSmooth_liftApply (2 * N + D) m (F n k) ac τ (hF n hn k) ha).const_smul _

/-- The tail flux field is periodic in the fast variable. -/
theorem tailFluxField_periodic {N D : ℕ} (F : ℕ → Fin 2 → LiftCoeff ι h) (εc : ℝ)
    (ac : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ)
    (hF : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ k m' α v u X,
      AVenhance.IsZ2Periodic (fun z => F n k m' α τ X z v u)) (X : Vec 2) :
    AVenhance.IsZ2Periodic (tailFluxField F N D εc ac τ X) := by
  intro l y
  funext k v
  simp only [tailFluxField, liftApply, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun n hn => ?_
  congr 1
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have := hF n hn k m α v u X l y
  simp only at this
  rw [this]

end Tail

section Integral

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The coarse-jet weights `∑_{q} 2^q ((q-1)!)²`. -/
def coarseJetConst (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, 2 ^ q * ((q - 1).factorial : ℝ) ^ 2

theorem coarseJetConst_nonneg (Q : ℕ) : 0 ≤ coarseJetConst Q := by
  unfold coarseJetConst; positivity

/-- The slow-cell integral of the mass-weighted tail pair jets at one time. -/
theorem slowCell_tail_pairJet_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (N D p : ℕ)
    (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h) (εc : ℝ) (hε0 : 0 ≤ εc)
    (hε1 : εc ≤ 1) (a : ℝ → Vec 2 → ∀ i, h i) (ℓ ρ : ℝ) (hρ : 0 < ρ) (t : ℝ) {τ : ℝ}
    (hτ : τ ∈ I) (hτt : ℓ ^ 2 * τ = t) (S : ℝ)
    (hbox : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ m α v u, IsBoxSmooth p 0 (fun X y => f n m α τ X y v u)) ∧
        ∀ k m α v u, IsBoxSmooth p 0 (fun X y => F n k m α τ X y v u))
    (hzero : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ α t X z v u, f n 0 α t X z v u = 0) ∧ ∀ k α t X z v u, F n k 0 α t X z v u = 0)
    (hjet : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ i, i ≤ p → ∀ m,
      schurCellL2Jet π I i (f n m) ≤ ENNReal.ofReal S ∧
        schurCellL2Jet π I i (fun q : DerivativeWord2 m × Fin 2 => F n q.2 m q.1)
          ≤ ENNReal.ofReal S)
    (m : ℕ) (hpm : p + (2 * N + D) ≤ m + 1) (ha : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (a t)) :
    ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
        pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
          (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p X
      ≤ ENNReal.ofReal (tailPairConst N D p * coarseJetConst (p + (2 * N + D))) *
          ENNReal.ofReal S ^ 2 *
          ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalGradFactorialSq ρ m (fun x => a t x u) := by
  set M := 2 * N + D with hM
  have hu : ∀ u, ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun x => a t x u) := fun u =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp ha
  have hac : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (fun X => a (ℓ ^ 2 * τ) (ρ • X)) := by
    rw [hτt]
    exact (ha.comp (contDiff_const_smul ρ)).of_le (by exact_mod_cast hpm)
  have hacu : ∀ u, ContDiff ℝ ((p + M : ℕ) : ℕ∞) (fun X => a (ℓ ^ 2 * τ) (ρ • X) u) := fun u =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp hac
  have hmeas : ∀ q ∈ Finset.Icc 1 (p + M), ∀ u, Measurable fun X =>
      ‖iteratedFDeriv ℝ q (fun X' => a (ℓ ^ 2 * τ) (ρ • X') u) X‖ₑ ^ 2 := by
    intro q hq u
    have hq' : q ≤ p + M := (Finset.mem_Icc.1 hq).2
    exact ((hacu u).continuous_iteratedFDeriv (by exact_mod_cast hq')).enorm.measurable.pow_const 2
  have hpt := fun X => tail_pairJet_le π hπ I N D p f F εc hε0 hε1
    (fun s X => a (ℓ ^ 2 * s) (ρ • X)) hτ S hbox hzero hjet hac X
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]),
    lintegral_finsetSum _ fun q hq => Finset.measurable_sum _ fun u _ =>
      (hmeas q hq u).const_mul _]
  have hq : ∀ q ∈ Finset.Icc 1 (p + M), ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
      ‖iteratedFDeriv ℝ q (fun X' => a (ℓ ^ 2 * τ) (ρ • X') u) X‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ q * ((q - 1).factorial : ℝ) ^ 2) *
        ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalGradFactorialSq ρ m (fun x => a t x u) := by
    intro q hqI
    obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.1 hqI
    rw [lintegral_finsetSum _ fun u _ => (hmeas q hqI u).const_mul _, Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [lintegral_const_mul _ (hmeas q hqI u), mul_left_comm]
    gcongr
    rw [hτt]
    exact lintegral_slowCell_iteratedFDeriv_dilate_le m q hq1 (by omega) (hu u) hρ
  calc ENNReal.ofReal (tailPairConst N D p) * ENNReal.ofReal S ^ 2 *
        ∑ q ∈ Finset.Icc 1 (p + M), ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
          ‖iteratedFDeriv ℝ q (fun X' => a (ℓ ^ 2 * τ) (ρ • X') u) X‖ₑ ^ 2
      ≤ ENNReal.ofReal (tailPairConst N D p) * ENNReal.ofReal S ^ 2 *
        ∑ q ∈ Finset.Icc 1 (p + M), ENNReal.ofReal (2 ^ q * ((q - 1).factorial : ℝ) ^ 2) *
          ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalGradFactorialSq ρ m (fun x => a t x u) := by
        gcongr with q hq'
        exact hq q hq'
    _ = _ := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun q _ => by positivity,
          ENNReal.ofReal_mul (tailPairConst_nonneg N D p)]
        unfold coarseJetConst
        ring

end Integral
end

/-! Pointwise-in-time bounds of the residual densities of the cleanup presentation
`R = (e/ℓ²) ε_c^{N+1} ∑_j ϑ^j (V_j)_diag`, `q = ℓ^{-2} ε_c^{N+1} ϑ^{A} (f_A)_diag` of the divided
tail of a lift, in terms
of the mass-weighted gradient energy density of the physical field at the same time. -/

section
/-- The constant of the per-time residual densities. -/
def densConst (N D A : ℕ) : ℝ :=
  8 * (A : ℝ) ^ 2 * ∑ p ∈ Finset.range (A + 2),
      tailPairConst N D p * coarseJetConst (p + (2 * N + D))
    + 16 * ∑ p ∈ Finset.range (A + 3), tailPairConst N D p * coarseJetConst (p + (2 * N + D))

theorem densConst_nonneg (N D A : ℕ) : 0 ≤ densConst N D A := by
  unfold densConst
  have := fun p => tailPairConst_nonneg N D p
  have := fun Q => coarseJetConst_nonneg Q
  refine add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => ?_))
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => ?_)) <;>
  exact mul_nonneg (tailPairConst_nonneg N D p) (coarseJetConst_nonneg _)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- Data of one cell time of the order-zero residual: the tail presentation, the coarse field,
and a cleanup chain of the divided tail. -/
structure ResidualTimeData (π : ι → ℝ) (I : Set ℝ) (N D A sZ : ℕ) (f : ℕ → LiftCoeff ι h)
    (F : ℕ → Fin 2 → LiftCoeff ι h) (εc : ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (ℓ ρ : ℝ) (t τ : ℝ)
    (S : ℝ) (m : ℕ) (Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) : Prop where
  mass_pos : ∀ v, 0 < π v
  ε_nonneg : 0 ≤ εc
  ε_le : εc ≤ 1
  ρ_pos : 0 < ρ
  τ_mem : τ ∈ I
  τ_eq : ℓ ^ 2 * τ = t
  hZ : 1 ≤ sZ
  hA : 1 ≤ A
  box : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ m α v u, IsBoxSmooth (A + 2) 0 (fun X y => f n m α τ X y v u)) ∧
        ∀ k m α v u, IsBoxSmooth (A + 2) 0 (fun X y => F n k m α τ X y v u)
  per : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ k m α v u X,
      AVenhance.IsZ2Periodic (fun z => F n k m α τ X z v u)
  zero : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      (∀ α t X z v u, f n 0 α t X z v u = 0) ∧ ∀ k α t X z v u, F n k 0 α t X z v u = 0
  jet : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ i, i ≤ A + 2 → ∀ m,
      schurCellL2Jet π I i (f n m) ≤ ENNReal.ofReal S ∧
        schurCellL2Jet π I i (fun q : DerivativeWord2 m × Fin 2 => F n q.2 m q.1)
          ≤ ENNReal.ofReal S
  order : A + 2 + (2 * N + D) ≤ m + 1
  smooth : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (a t)
  chain : IsCleanupChain (A + 2) sZ A
      (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ)
      (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) (fun j => Vc j τ)

namespace ResidualTimeData

variable {π : ι → ℝ} {I : Set ℝ} {N D A sZ : ℕ} {f : ℕ → LiftCoeff ι h}
  {F : ℕ → Fin 2 → LiftCoeff ι h} {εc : ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {ℓ ρ t τ S : ℝ} {m : ℕ}
  {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem ac_smooth (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc) :
    ContDiff ℝ (((A + 2) + (2 * N + D) : ℕ) : ℕ∞) (fun X => a (ℓ ^ 2 * τ) (ρ • X)) := by
  rw [hd.τ_eq]
  exact (hd.smooth.comp (contDiff_const_smul ρ)).of_le (by exact_mod_cast hd.order)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem scal_slow (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc) :
    IsSlowSmooth (A + 2) (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) := by
  exact isSlowSmooth_tailScalarField f εc _ τ
    (fun n hn m' α v u => ((hd.box n hn).1 m' α v u).isSlowSmooth) hd.ac_smooth

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem flux_slow (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc) :
    IsSlowSmooth (A + 2) (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) :=
  isSlowSmooth_tailFluxField F εc _ τ
    (fun n hn k m' α v u => ((hd.box n hn).2 k m' α v u).isSlowSmooth) hd.ac_smooth

/-- The chain projected on one component. -/
theorem chain_component (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc) (v : ι) :
    IsCleanupChain (A + 2) sZ A
      (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
      (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
      (fun j X y k => Vc j τ X y k v) :=
  IsCleanupChain.clm_comp (by omega) hd.hZ hd.flux_slow hd.chain
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

/-- The energy density at time `t`. -/
def gradDensity (π : ι → ℝ) (ρ : ℝ) (m : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) : ℝ≥0∞ :=
  ∑ u, ENNReal.ofReal (π u)⁻¹ * classicalGradFactorialSq ρ m (fun x => a t x u)

/-- The slow-cell pair jets of every order up to `P` at this time. -/
theorem sum_slowCell_pairJet_le (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc)
    (P : ℕ) (hP : P ≤ A + 3) :
    ∑ p ∈ Finset.range P, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
        pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
          (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) p X
      ≤ ENNReal.ofReal (∑ p ∈ Finset.range P,
          tailPairConst N D p * coarseJetConst (p + (2 * N + D))) *
          ENNReal.ofReal S ^ 2 * gradDensity π ρ m a t := by
  rw [ENNReal.ofReal_sum_of_nonneg fun p _ =>
    mul_nonneg (tailPairConst_nonneg N D p) (coarseJetConst_nonneg _), Finset.sum_mul,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpP : p ≤ A + 2 := by have := Finset.mem_range.1 hp; omega
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ, _
      ≤ ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ * pairJet
          (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
          (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
            p X := by
        simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact sum_lintegral_le_lintegral_sum _ _
    _ ≤ _ := slowCell_tail_pairJet_le π hd.mass_pos I N D p f F εc hd.ε_nonneg hd.ε_le a ℓ ρ
        hd.ρ_pos t hd.τ_mem hd.τ_eq S
        (fun n hn => ⟨fun m α v u => BoundTail.isBoxSmooth_slow_zero ((hd.box n hn).1 m α v u)
            hpP, fun k m α v u => BoundTail.isBoxSmooth_slow_zero ((hd.box n hn).2 k m α v u) hpP⟩)
        hd.zero (fun n hn i hi m' => hd.jet n hn i (hi.trans hpP) m') m
        (by have := hd.order; omega) hd.smooth

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem flux_component_slow (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc)
    (v : ι) : IsSlowSmooth (A + 2)
      (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) :=
  hd.flux_slow.clm_comp (clmVec (ContinuousLinearMap.proj (R := ℝ) (φ := h) v))

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem scal_component_slow (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc)
    (v : ι) : IsSlowSmooth (A + 2)
      (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v) :=
  hd.scal_slow.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem flux_component_periodic (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc)
    (v : ι) (X : Vec 2) : AVenhance.IsZ2Periodic
      (fun y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v) := by
  intro l y
  funext k
  exact congrFun (congrFun (tailFluxField_periodic F εc _ τ hd.per X l y) k) v

/-- The flux density of the sampled chain at this time. -/
theorem flux_density_le (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc) {e : ℝ}
    (he : 0 < e) (heρ : e ≤ ρ) (Mn : ℕ) (hM : e⁻¹ = (Mn : ℝ)) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • Vc j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2
      ≤ ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
          (ENNReal.ofReal (∑ p ∈ Finset.range (A + 2),
            tailPairConst N D p * coarseJetConst (p + (2 * N + D))) *
          ENNReal.ofReal S ^ 2 * gradDensity π ρ m a t) := by
  have hv : ∀ v, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
      ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • Vc j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 ≤
      ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 2),
        ∫⁻ X in slowCell ρ,
          pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
            p X := by
    intro v
    have := cleanupFlux_density_le (E := h v) hd.hZ (by omega) (hd.flux_component_slow v)
      (hd.flux_component_periodic v) (hd.scal_component_slow v) (hd.chain_component v)
      hd.ρ_pos he heρ Mn hM
    simpa [Finset.sum_apply, Pi.smul_apply] using this
  calc _ ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
        ∑ p ∈ Finset.range (A + 2), ∫⁻ X in slowCell ρ,
          pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
            p X) := Finset.sum_le_sum fun v _ => by gcongr; exact hv v
    _ = ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 2),
        ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
          pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
            p X := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ _ := by gcongr; exact hd.sum_slowCell_pairJet_le (A + 2) (by omega)

/-- The remainder density of the sampled chain at this time. -/
theorem remainder_density_le (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t τ S m Vc)
    {e : ℝ} (he : 0 < e) (heρ : e ≤ ρ) (Mn : ℕ) (hM : e⁻¹ = (Mn : ℝ)) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖cleanupSource (fun j => Vc j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (16 * ρ ^ 2) *
          (ENNReal.ofReal (∑ p ∈ Finset.range (A + 3),
            tailPairConst N D p * coarseJetConst (p + (2 * N + D))) *
          ENNReal.ofReal S ^ 2 * gradDensity π ρ m a t) := by
  have hslowV := IsCleanupChain.isSlowSmooth hd.flux_slow hd.chain (A - 1) (by have := hd.hA; omega)
  have hv : ∀ v, ∫⁻ x in AVenhance.unitCube,
      ‖cleanupSource (fun j => Vc j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 ≤
      ENNReal.ofReal (16 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 3),
        ∫⁻ X in slowCell ρ,
          pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
            p X := by
    intro v
    have := cleanupRemainder_density_le (E := h v) hd.hZ hd.hA le_rfl (hd.flux_component_slow v)
      (hd.flux_component_periodic v) (hd.scal_component_slow v) (hd.chain_component v)
      hd.ρ_pos he heρ Mn hM
    have hsrc := cleanupSource_clm_comp (V := fun j => Vc j τ) (j := A) (by omega) hslowV
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
    have heq : cleanupSource (fun j X y k => Vc j τ X y k v) A =
        fun X z => cleanupSource (fun j => Vc j τ) A X z v := hsrc
    rw [heq] at this
    exact this
  calc _ ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (16 * ρ ^ 2) *
        ∑ p ∈ Finset.range (A + 3), ∫⁻ X in slowCell ρ,
          pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
            p X) := Finset.sum_le_sum fun v _ => by gcongr; exact hv v
    _ = ENNReal.ofReal (16 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 3),
        ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
          pairJet (fun X y => tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y v)
            (fun X y k => tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ X y k v)
            p X := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ _ := by gcongr; exact hd.sum_slowCell_pairJet_le (A + 3) le_rfl

end ResidualTimeData
end

/-! The physical residual densities `R`, `q` of the cleanup presentation at one time, in the
form consumed by `residualNorm_le_of_pointwise`. -/

section
/-- `∑_{p<P} C_tail(p) C_coarse(p + 2N + D)`. -/
def tailSumConst (N D P : ℕ) : ℝ :=
  ∑ p ∈ Finset.range P, tailPairConst N D p * coarseJetConst (p + (2 * N + D))

theorem tailSumConst_nonneg (N D P : ℕ) : 0 ≤ tailSumConst N D P :=
  Finset.sum_nonneg fun p _ => mul_nonneg (tailPairConst_nonneg N D p) (coarseJetConst_nonneg _)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

namespace ResidualTimeData

variable {π : ι → ℝ} {I : Set ℝ} {N D A sZ : ℕ} {f : ℕ → LiftCoeff ι h}
  {F : ℕ → Fin 2 → LiftCoeff ι h} {εc : ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {ℓ ρ t S : ℝ} {m : ℕ}
  {Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}

theorem flux_pointwise
    (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t ((ℓ ^ 2)⁻¹ * t) S m Vc) {e : ℝ}
    (he : 0 < e) (heρ : e ≤ ρ) (Mn : ℕ) (hMn : e⁻¹ = (Mn : ℝ)) {Sp : ℝ} (hSSp : S ≤ Sp)
    (hSp0 : 0 ≤ Sp) (hpR0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e) :
    ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖((ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A Vc t x k) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ *
          Real.sqrt (8 * (A : ℝ) ^ 2 * tailSumConst N D (A + 2)) * Sp) ^ 2) *
        gradDensity π ρ m a t := by
  set pR : ℝ := (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e with hpR
  have hpt : ∀ x k v, ‖((ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A Vc t x k) v‖ₑ ^ 2
      = ENNReal.ofReal (pR ^ 2) * ‖∑ j ∈ Finset.range A,
        (e / ρ) ^ j • Vc j ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 := by
    intro x k v
    have hv : ((ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A Vc t x k) v =
        pR • ∑ j ∈ Finset.range A, (e / ρ) ^ j • Vc j ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x) (e⁻¹ • x) k v := by
      simp [cleanupFlux, diagSample, smul_smul, Finset.sum_apply, hpR, mul_assoc]
    rw [hv, enorm_smul, mul_pow, Real.enorm_eq_ofReal hpR0, ← ENNReal.ofReal_pow hpR0]
  simp_rw [hpt, ← Finset.mul_sum]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hSsq : ENNReal.ofReal S ^ 2 ≤ ENNReal.ofReal (Sp ^ 2) := by
    rw [ENNReal.ofReal_pow hSp0]; gcongr
  have hsplit : ENNReal.ofReal ((pR * ρ * Real.sqrt (8 * (A : ℝ) ^ 2 * tailSumConst N D (A + 2))
      * Sp) ^ 2) = ENNReal.ofReal (pR ^ 2) * ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
        ENNReal.ofReal (tailSumConst N D (A + 2)) * ENNReal.ofReal (Sp ^ 2) := by
    have hT := tailSumConst_nonneg N D (A + 2)
    rw [show (pR * ρ * Real.sqrt (8 * (A : ℝ) ^ 2 * tailSumConst N D (A + 2)) * Sp) ^ 2 =
        pR ^ 2 * (8 * (A : ℝ) ^ 2 * ρ ^ 2) * tailSumConst N D (A + 2) * Sp ^ 2 by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (pR ^ 2) * _)
      = ENNReal.ofReal (pR ^ 2) * ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
          ∑ k : Fin 2, ‖∑ j ∈ Finset.range A,
            (e / ρ) ^ j • Vc j ((ℓ ^ 2)⁻¹ * t) (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ENNReal.ofReal (pR ^ 2) * (ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
        (ENNReal.ofReal (tailSumConst N D (A + 2)) * ENNReal.ofReal S ^ 2 *
          gradDensity π ρ m a t)) := by
        gcongr; exact hd.flux_density_le he heρ Mn hMn
    _ ≤ ENNReal.ofReal (pR ^ 2) * (ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
        (ENNReal.ofReal (tailSumConst N D (A + 2)) * ENNReal.ofReal (Sp ^ 2) *
          gradDensity π ρ m a t)) := by gcongr
    _ = _ := by rw [hsplit]; ring

theorem remainder_pointwise
    (hd : ResidualTimeData π I N D A sZ f F εc a ℓ ρ t ((ℓ ^ 2)⁻¹ * t) S m Vc) {e : ℝ}
    (he : 0 < e) (heρ : e ≤ ρ) (Mn : ℕ) (hMn : e⁻¹ = (Mn : ℝ)) {Sp : ℝ} (hSSp : S ≤ Sp)
    (hSp0 : 0 ≤ Sp) (hpq0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A) :
    ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖((ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A Vc t x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A * ρ *
          Real.sqrt (16 * tailSumConst N D (A + 3)) * Sp) ^ 2) *
        gradDensity π ρ m a t := by
  set pq : ℝ := (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ A with hpq
  have hpt : ∀ x v, ‖((ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A Vc t x) v‖ₑ ^ 2
      = ENNReal.ofReal (pq ^ 2) *
        ‖cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 := by
    intro x v
    have hv : ((ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A Vc t x) v =
        pq • cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x) (e⁻¹ • x) v := by
      simp [cleanupRemainder, diagSample, smul_smul, hpq, mul_assoc]
    rw [hv, enorm_smul, mul_pow, Real.enorm_eq_ofReal hpq0, ← ENNReal.ofReal_pow hpq0]
  simp_rw [hpt]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hSsq : ENNReal.ofReal S ^ 2 ≤ ENNReal.ofReal (Sp ^ 2) := by
    rw [ENNReal.ofReal_pow hSp0]; gcongr
  have hsplit : ENNReal.ofReal ((pq * ρ * Real.sqrt (16 * tailSumConst N D (A + 3)) * Sp) ^ 2) =
      ENNReal.ofReal (pq ^ 2) * ENNReal.ofReal (16 * ρ ^ 2) *
        ENNReal.ofReal (tailSumConst N D (A + 3)) * ENNReal.ofReal (Sp ^ 2) := by
    have hT := tailSumConst_nonneg N D (A + 3)
    rw [show (pq * ρ * Real.sqrt (16 * tailSumConst N D (A + 3)) * Sp) ^ 2 =
        pq ^ 2 * (16 * ρ ^ 2) * tailSumConst N D (A + 3) * Sp ^ 2 by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (pq ^ 2) * _)
      = ENNReal.ofReal (pq ^ 2) * ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
          ‖cleanupSource (fun j => Vc j ((ℓ ^ 2)⁻¹ * t)) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ENNReal.ofReal (pq ^ 2) * (ENNReal.ofReal (16 * ρ ^ 2) *
        (ENNReal.ofReal (tailSumConst N D (A + 3)) * ENNReal.ofReal S ^ 2 *
          gradDensity π ρ m a t)) := by
        gcongr; exact hd.remainder_density_le he heρ Mn hMn
    _ ≤ ENNReal.ofReal (pq ^ 2) * (ENNReal.ofReal (16 * ρ ^ 2) *
        (ENNReal.ofReal (tailSumConst N D (A + 3)) * ENNReal.ofReal (Sp ^ 2) *
          gradDensity π ρ m a t)) := by gcongr
    _ = _ := by rw [hsplit]; ring

end ResidualTimeData
end

end AVRegularity
end
end
