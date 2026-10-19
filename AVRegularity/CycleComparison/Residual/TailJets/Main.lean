-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import AVRegularity.CycleComparison.Residual.Jets.Lift

@[expose] public section

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.TailJets

/-! Minkowski's inequality in `L²` of the unit cell for finite sums of nonnegative continuous
profiles times constants. -/

theorem lintegral_enorm_sq_eq_eLpNorm_sq {G : Vec 2 → ℝ} (hG : Continuous G) :
    ∫⁻ y in AVenhance.unitCube, ‖G y‖ₑ ^ 2 =
      eLpNorm G 2 (volume.restrict AVenhance.unitCube) ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := volume.restrict AVenhance.unitCube)
    (p := 2) (f := G) (by norm_num) hG.aestronglyMeasurable
  simpa using this.symm

theorem lintegral_sq_sum_le {κ ι : Type*} [Fintype κ] [Fintype ι] (r : κ → ι → Vec 2 → ℝ)
    (hr : ∀ a u, Continuous (r a u)) (hr0 : ∀ a u y, 0 ≤ r a u y) (N : ι → ℝ)
    (hN : ∀ u, 0 ≤ N u) (A : κ → ι → ℝ≥0∞)
    (hA : ∀ a u, eLpNorm (r a u) 2 (volume.restrict AVenhance.unitCube) ≤ A a u) :
    ∫⁻ y in AVenhance.unitCube,
        (∑ a, ∑ u, ENNReal.ofReal (r a u y) * ENNReal.ofReal (N u)) ^ 2 ≤
      (∑ u, (∑ a, A a u) * ENNReal.ofReal (N u)) ^ 2 := by
  set μ := volume.restrict AVenhance.unitCube with hμ
  let g : κ → ι → Vec 2 → ℝ := fun a u y => r a u y * N u
  let G : Vec 2 → ℝ := fun y => ∑ a, ∑ u, g a u y
  have hGc : Continuous G :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun u _ =>
      (hr a u).mul continuous_const
  have hG0 : ∀ y, 0 ≤ G y := fun y =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun u _ => mul_nonneg (hr0 a u y) (hN u)
  have step1 : ∀ y, ∑ a, ∑ u, ENNReal.ofReal (r a u y) * ENNReal.ofReal (N u) = ‖G y‖ₑ := by
    intro y
    rw [← ofReal_norm, Real.norm_of_nonneg (hG0 y)]
    simp only [G, g]
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => Finset.sum_nonneg fun u _ =>
      mul_nonneg (hr0 a u y) (hN u)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun u _ => mul_nonneg (hr0 a u y) (hN u)]
    exact Finset.sum_congr rfl fun u _ => (ENNReal.ofReal_mul (hr0 a u y)).symm
  simp_rw [step1]
  rw [lintegral_enorm_sq_eq_eLpNorm_sq hGc]
  have hG : G = ∑ a, ∑ u, (N u • r a u) := by
    funext y
    simp only [G, g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hmink : eLpNorm G 2 μ ≤ ∑ a, ∑ u, ENNReal.ofReal (N u) * A a u := by
    rw [hG]
    refine (eLpNorm_sum_le (p := 2) (by norm_num)).trans ?_
    refine Finset.sum_le_sum fun a _ => ?_
    refine (eLpNorm_sum_le (p := 2) (by norm_num)).trans ?_
    refine Finset.sum_le_sum fun u _ => ?_
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hN u)]
    exact mul_le_mul' le_rfl (hA a u)
  have hre : ∑ a, ∑ u, ENNReal.ofReal (N u) * A a u =
      ∑ u, (∑ a, A a u) * ENNReal.ofReal (N u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [hre] at hmink
  gcongr

end AVRegularity.TailJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The fibrewise `L²_y` bound for the slow jet of a lift action: one slow point, one output
component, grouped by tested order `m` and Leibniz index `i`. -/

section
theorem schurSums_mono {ι : Type*} [Fintype ι] (π : ι → ℝ) {K K' : ι → ι → ℝ≥0∞}
    (h : ∀ v u, K v u ≤ K' v u) : schurSums π K ≤ schurSums π K' := by
  unfold schurSums
  refine max_le_max (iSup_mono fun v => Finset.sum_le_sum fun u _ => ?_)
    (iSup_mono fun u => Finset.sum_le_sum fun v _ => ?_)
  · exact mul_le_mul' le_rfl (h v u)
  · exact mul_le_mul' le_rfl (h v u)

/-- The numerical constant of the tail jet bounds: `(M+1)(p+1) 4^p`. -/
def tailJetConst (M p : ℕ) : ℝ := ((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ) * 4 ^ p

namespace TailJets

theorem sq_sum_le_card_mul {κ : Type*} (s : Finset κ) (x : κ → ℝ≥0∞) :
    (∑ k ∈ s, x k) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ k ∈ s, x k ^ 2 := by
  have := ennreal_sum_sq_le_sum_mul_sum s x (fun _ => 1) (fun k => x k ^ 2)
    (fun k _ => by rw [one_mul])
  simpa using this

theorem regroup {κ ι : Type*} [Fintype κ] [Fintype ι] (s : Finset ℕ) (t : κ → ι → ℕ → ℝ≥0∞) :
    ∑ a, ∑ u, ∑ i ∈ s, t a u i = ∑ i ∈ s, ∑ a, ∑ u, t a u i := by
  calc ∑ a, ∑ u, ∑ i ∈ s, t a u i = ∑ a, ∑ i ∈ s, ∑ u, t a u i :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

section Fibre

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem fibre_majorant (I : Set ℝ) (M p : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    {τ : ℝ} (hτ : τ ∈ I)
    (hc : ∀ m α v u, IsBoxSmooth p 0 (fun X y => c m α τ X y v u))
    (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (a τ)) (X : Vec 2) (v : ι) :
    ∃ g : Vec 2 → ℝ≥0∞, Measurable g ∧
      (∀ y, ‖iteratedFDeriv ℝ p (fun X' => liftApply M c a τ X' y v) X‖ₑ ^ 2 ≤ g y) ∧
      ∫⁻ y in AVenhance.unitCube, g y ≤
      ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            (∑ u, (∑ α : DerivativeWord2 m,
                cellL2Jet I i (fun t X z => c m α t X z v u)) *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ) ^ 2 := by
  have hcS : ∀ m (α : DerivativeWord2 m) u, IsSlowSmooth p (fun X y => c m α τ X y v u) :=
    fun m α u => (hc m α v u).isSlowSmooth
  let r : ∀ m : ℕ, ℕ → DerivativeWord2 m → ι → Vec 2 → ℝ := fun m i α u y =>
    ‖iteratedFDeriv ℝ i (fun X' => c m α τ X' y v u) X‖
  let N : ℕ → ℕ → ι → ℝ := fun m i u =>
    ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖
  have hrc : ∀ m i, i ≤ p → ∀ α u, Continuous (r m i α u) := fun m i hi α u =>
    (((hcS m α u).2 i hi).comp
      (Continuous.prodMk continuous_const continuous_id)).norm
  let H : ℕ → ℕ → Vec 2 → ℝ≥0∞ := fun m i y => ∑ α : DerivativeWord2 m, ∑ u,
    ENNReal.ofReal (r m i α u y) * ENNReal.ofReal (N m i u)
  have hpt : ∀ y, ‖iteratedFDeriv ℝ p (fun X' => liftApply M c a τ X' y v) X‖ₑ ≤
      ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
        ENNReal.ofReal (p.choose i : ℝ) * H m i y := by
    intro y
    have h2 := norm_iteratedFDeriv_liftApply_le M p c a τ y v
      (fun m α u => (hcS m α u).1 y) ha X
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal h2).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity]
    refine Finset.sum_le_sum fun m _ => le_of_eq ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun α _ => by positivity]
    have : ∀ α : DerivativeWord2 m, ENNReal.ofReal (∑ u : ι, ∑ i ∈ Finset.range (p + 1),
        (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun X' => c m α τ X' y v u) X‖ *
          ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖) =
        ∑ u : ι, ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal (p.choose i : ℝ) * (ENNReal.ofReal (r m i α u y) *
            ENNReal.ofReal (N m i u)) := by
      intro α
      rw [ENNReal.ofReal_sum_of_nonneg fun u _ => by positivity]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
    simp_rw [this]
    rw [regroup (Finset.range (p + 1)) (fun α u i => ENNReal.ofReal (p.choose i : ℝ) *
      (ENNReal.ofReal (r m i α u y) * ENNReal.ofReal (N m i u)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H, Finset.mul_sum]
  have hHmeas : ∀ m i, i ≤ p → Measurable (H m i) := fun m i hi => by
    refine Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun u _ => ?_
    exact (ENNReal.measurable_ofReal.comp (hrc m i hi α u).measurable).mul measurable_const
  have hsq : ∀ y, ‖iteratedFDeriv ℝ p (fun X' => liftApply M c a τ X' y v) X‖ₑ ^ 2 ≤
      ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * H m i y ^ 2 := by
    intro y
    have hn : ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) =
        ((M + 1 : ℕ) : ℝ≥0∞) * ((p + 1 : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hx : ∀ m i, (ENNReal.ofReal (p.choose i : ℝ) * H m i y) ^ 2 =
        ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * H m i y ^ 2 := fun m i => by
      rw [mul_pow, ← ENNReal.ofReal_pow (by positivity)]
    calc _ ≤ (∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal (p.choose i : ℝ) * H m i y) ^ 2 := pow_le_pow_left₀ bot_le (hpt y) 2
      _ ≤ ((M + 1 : ℕ) : ℝ≥0∞) * ∑ m ∈ Finset.range (M + 1),
          (∑ i ∈ Finset.range (p + 1), ENNReal.ofReal (p.choose i : ℝ) * H m i y) ^ 2 := by
          simpa using sq_sum_le_card_mul (Finset.range (M + 1))
            (fun m => ∑ i ∈ Finset.range (p + 1), ENNReal.ofReal (p.choose i : ℝ) * H m i y)
      _ ≤ ((M + 1 : ℕ) : ℝ≥0∞) * ∑ m ∈ Finset.range (M + 1), ((p + 1 : ℕ) : ℝ≥0∞) *
          ∑ i ∈ Finset.range (p + 1), (ENNReal.ofReal (p.choose i : ℝ) * H m i y) ^ 2 := by
          refine mul_le_mul' le_rfl (Finset.sum_le_sum fun m _ => ?_)
          simpa using sq_sum_le_card_mul (Finset.range (p + 1))
            (fun i => ENNReal.ofReal (p.choose i : ℝ) * H m i y)
      _ = _ := by
          simp_rw [hx]
          rw [hn, ← Finset.mul_sum, mul_assoc]
  have hA : ∀ m i, i ≤ p → ∀ (α : DerivativeWord2 m) u,
      eLpNorm (r m i α u) 2 (volume.restrict AVenhance.unitCube) ≤
        cellL2Jet I i (fun t X z => c m α t X z v u) := by
    intro m i hi α u
    have hD : Continuous (fun y => iteratedFDeriv ℝ i (fun X' => c m α τ X' y v u) X) :=
      ((hcS m α u).2 i hi).comp (Continuous.prodMk continuous_const continuous_id)
    have : r m i α u = fun y => ‖iteratedFDeriv ℝ i (fun X' => c m α τ X' y v u) X‖ := rfl
    rw [this, eLpNorm_norm _ hD.aestronglyMeasurable]
    unfold cellL2Jet
    exact le_iSup₂_of_le τ hτ (le_iSup_of_le X le_rfl)
  refine ⟨fun y => ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * H m i y ^ 2, ?_, hsq, ?_⟩
  · exact measurable_const.mul (Finset.measurable_sum _ fun m _ =>
      Finset.measurable_sum _ fun i hi => measurable_const.mul
        ((hHmeas m i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).pow_const 2))
  calc ∫⁻ y in AVenhance.unitCube, ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * H m i y ^ 2
      = ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * ∫⁻ y in AVenhance.unitCube, H m i y ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        have hm1 : ∀ m ∈ Finset.range (M + 1), ∀ i ∈ Finset.range (p + 1),
            Measurable fun y => ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * H m i y ^ 2 :=
          fun m _ i hi => measurable_const.mul
            ((hHmeas m i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).pow_const 2)
        have e1 : ∫⁻ y in AVenhance.unitCube, ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
            ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * H m i y ^ 2 =
            ∑ m ∈ Finset.range (M + 1), ∫⁻ y in AVenhance.unitCube,
              ∑ i ∈ Finset.range (p + 1), ENNReal.ofReal ((p.choose i : ℝ) ^ 2) * H m i y ^ 2 :=
          lintegral_finsetSum _ fun m hm => Finset.measurable_sum _ (hm1 m hm)
        rw [e1]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [lintegral_finsetSum _ (hm1 m hm)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i hi => ?_)
        have hi' : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        refine mul_le_mul' le_rfl ?_
        have := lintegral_sq_sum_le (r m i) (hrc m i hi') (fun α u y => norm_nonneg _)
          (N m i) (fun u => norm_nonneg _)
          (fun α u => cellL2Jet I i (fun t X z => c m α t X z v u)) (hA m i hi')
        simpa [H, N, ofReal_norm] using this

theorem fibre_bound (I : Set ℝ) (M p : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    {τ : ℝ} (hτ : τ ∈ I)
    (hc : ∀ m α v u, IsBoxSmooth p 0 (fun X y => c m α τ X y v u))
    (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (a τ)) (X : Vec 2) (v : ι) :
    ∫⁻ y in AVenhance.unitCube,
        ‖iteratedFDeriv ℝ p (fun X' => liftApply M c a τ X' y v) X‖ₑ ^ 2 ≤
      ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            (∑ u, (∑ α : DerivativeWord2 m,
                cellL2Jet I i (fun t X z => c m α t X z v u)) *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ) ^ 2 := by
  obtain ⟨g, -, hg, hint⟩ := fibre_majorant I M p c a hτ hc ha X v
  exact (lintegral_mono hg).trans hint

end Fibre

end TailJets
end

/-! The Schur-weighted fibrewise slow jet of a lift action, and its flux version. -/

namespace TailJets

theorem sum_swap3 {ι : Type*} [Fintype ι] (s t : Finset ℕ) (F : ι → ℕ → ℕ → ℝ≥0∞) :
    ∑ v, ∑ m ∈ s, ∑ i ∈ t, F v m i = ∑ m ∈ s, ∑ i ∈ t, ∑ v, F v m i := by
  calc ∑ v, ∑ m ∈ s, ∑ i ∈ t, F v m i = ∑ m ∈ s, ∑ v, ∑ i ∈ t, F v m i := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m _ => Finset.sum_comm

end TailJets

theorem mass_fibre_rhs_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (M p : ℕ) (c : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            (∑ u, (∑ α : DerivativeWord2 m,
                cellL2Jet I i (fun t X z => c m α t X z v u)) *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ) ^ 2)
      ≤ ENNReal.ofReal (tailJetConst M p) * ∑ m ∈ Finset.range (M + 1),
          ∑ i ∈ Finset.range (p + 1),
          schurCellL2Jet π I i (c m) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 := by
  let K : ∀ m : ℕ, ℕ → ι → ι → ℝ≥0∞ := fun m i v u =>
    ∑ α : DerivativeWord2 m, cellL2Jet I i (fun t X z => c m α t X z v u)
  let b : ℕ → ℕ → ι → ℝ≥0∞ := fun m i u =>
    ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ
  let n : ℝ≥0∞ := ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * (n * ∑ m ∈ Finset.range (M + 1),
          ∑ i ∈ Finset.range (p + 1), ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            (∑ u, K m i v u * b m i u) ^ 2)
    _ = ∑ v, ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          n * (ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            (ENNReal.ofReal (π v)⁻¹ * (∑ u, K m i v u * b m i u) ^ 2)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          n * (ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            ∑ v, ENNReal.ofReal (π v)⁻¹ * (∑ u, K m i v u * b m i u) ^ 2) := by
        rw [TailJets.sum_swap3 (F := fun v m i => n * (ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            (ENNReal.ofReal (π v)⁻¹ * (∑ u, K m i v u * b m i u) ^ 2)))]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal (tailJetConst M p) * (schurCellL2Jet π I i (c m) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ * b m i u ^ 2) := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i hi => ?_
        have hS := schurSums_weighted_sq_le π hπ (K m i) (b m i)
        have hcst : n * ENNReal.ofReal ((p.choose i : ℝ) ^ 2) ≤ ENNReal.ofReal (tailJetConst M p) := by
          rw [← ENNReal.ofReal_mul (by positivity), tailJetConst]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ((p.choose i : ℕ) : ℝ) ≤ 2 ^ p := by exact_mod_cast Nat.choose_le_two_pow p i
          have h2 : ((p.choose i : ℝ)) ^ 2 ≤ 4 ^ p := by
            calc ((p.choose i : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
              _ = 4 ^ p := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          have : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left h2 this |>.trans_eq (by ring)
        calc n * (ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
              ∑ v, ENNReal.ofReal (π v)⁻¹ * (∑ u, K m i v u * b m i u) ^ 2)
            ≤ n * (ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
              (schurCellL2Jet π I i (c m) ^ 2 *
                ∑ u, ENNReal.ofReal (π u)⁻¹ * b m i u ^ 2)) := by
              gcongr
              exact hS
          _ = (n * ENNReal.ofReal ((p.choose i : ℝ) ^ 2)) * (schurCellL2Jet π I i (c m) ^ 2 *
                ∑ u, ENNReal.ofReal (π u)⁻¹ * b m i u ^ 2) := by ring
          _ ≤ _ := by gcongr
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

theorem sum_mass_lintegral_iteratedFDeriv_liftApply_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)]
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (M p : ℕ) (c : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ I)
    (hc : ∀ m α v u, IsBoxSmooth p 0 (fun X y => c m α τ X y v u))
    (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (a τ)) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube,
        ‖iteratedFDeriv ℝ p (fun X' => liftApply M c a τ X' y v) X‖ₑ ^ 2
      ≤ ENNReal.ofReal (tailJetConst M p) * ∑ m ∈ Finset.range (M + 1),
          ∑ i ∈ Finset.range (p + 1),
          schurCellL2Jet π I i (c m) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 :=
  (Finset.sum_le_sum fun v _ => mul_le_mul' le_rfl
    (TailJets.fibre_bound I M p c a hτ hc ha X v)).trans
    (mass_fibre_rhs_le π hπ I M p c a τ X)

theorem schurCellL2Jet_le_prod {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (π : ι → ℝ) (I : Set ℝ) (i m : ℕ) (F : Fin 2 → LiftCoeff ι h) (k : Fin 2) :
    schurCellL2Jet π I i (F k m) ≤
      schurCellL2Jet π I i (fun q : DerivativeWord2 m × Fin 2 => F q.2 m q.1) := by
  unfold schurCellL2Jet
  refine schurSums_mono π fun v u => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun α _ =>
    Finset.single_le_sum (f := fun k' : Fin 2 => cellL2Jet I i (fun t X z => F k' m α t X z v u))
      (fun _ _ => bot_le) (Finset.mem_univ k)

theorem sum_mass_lintegral_iteratedFDeriv_liftApply_flux_le {ι : Type*} [Fintype ι]
    {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)]
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (M p : ℕ) (F : Fin 2 → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ I)
    (hc : ∀ k m α v u, IsBoxSmooth p 0 (fun X y => F k m α τ X y v u))
    (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (a τ)) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube, ∑ k : Fin 2,
        ‖iteratedFDeriv ℝ p (fun X' => liftApply M (F k) a τ X' y v) X‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * tailJetConst M p) * ∑ m ∈ Finset.range (M + 1),
          ∑ i ∈ Finset.range (p + 1),
          schurCellL2Jet π I i (fun q : DerivativeWord2 m × Fin 2 => F q.2 m q.1) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 := by
  set B : ℝ≥0∞ := ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
    schurCellL2Jet π I i (fun q : DerivativeWord2 m × Fin 2 => F q.2 m q.1) ^ 2 *
      ∑ u, ENNReal.ofReal (π u)⁻¹ *
        ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 with hB
  let R : Fin 2 → ι → ℝ≥0∞ := fun k v => ENNReal.ofReal (((M + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        ∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (p + 1),
          ENNReal.ofReal ((p.choose i : ℝ) ^ 2) *
            (∑ u, (∑ α : DerivativeWord2 m,
                cellL2Jet I i (fun t X z => F k m α t X z v u)) *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ) ^ 2
  have hv : ∀ v, ∫⁻ y in AVenhance.unitCube, ∑ k : Fin 2,
      ‖iteratedFDeriv ℝ p (fun X' => liftApply M (F k) a τ X' y v) X‖ₑ ^ 2 ≤ ∑ k, R k v := by
    intro v
    choose g hgm hg hint using fun k => TailJets.fibre_majorant I M p (F k) a hτ (hc k) ha X v
    calc _ ≤ ∫⁻ y in AVenhance.unitCube, ∑ k : Fin 2, g k y :=
          lintegral_mono fun y => Finset.sum_le_sum fun k _ => hg k y
      _ = ∑ k, ∫⁻ y in AVenhance.unitCube, g k y := lintegral_finsetSum _ fun k _ => hgm k
      _ ≤ _ := Finset.sum_le_sum fun k _ => hint k
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube, ∑ k : Fin 2,
        ‖iteratedFDeriv ℝ p (fun X' => liftApply M (F k) a τ X' y v) X‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * ∑ k, R k v :=
        Finset.sum_le_sum fun v _ => mul_le_mul' le_rfl (hv v)
    _ = ∑ k, ∑ v, ENNReal.ofReal (π v)⁻¹ * R k v := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ ∑ k : Fin 2, ENNReal.ofReal (tailJetConst M p) * B := by
        refine Finset.sum_le_sum fun k _ => (mass_fibre_rhs_le π hπ I M p (F k) a τ X).trans ?_
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i _ => ?_)
        exact mul_le_mul' (pow_le_pow_left₀ bot_le (schurCellL2Jet_le_prod π I i m F k) 2) le_rfl
    _ = ENNReal.ofReal (2 * tailJetConst M p) * B := by
        rw [Fin.sum_univ_two, ← add_mul, ENNReal.ofReal_mul (by norm_num)]
        simp [two_mul]

end AVRegularity
end
