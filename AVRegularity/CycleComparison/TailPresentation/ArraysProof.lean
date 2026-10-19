-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.TailPresentation.O6Main
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.SettingTailFluxCoefficientCellBound
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
public import AVRegularity.CycleComparison.Lift.LiftSourceBlockCoefficientAction
public import AVRegularity.CycleComparison.TailConstructed.RawFluxTests

section
/-! Preparation for the constructed tail arrays, independent of the tail coefficient: removing the
order-zero slice of an array (`zero0`), fast periodicity of fast partials and of the cross flux,
and fast periodicity of the raw flux under the lift setting. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
  AVRegularity.CycleComparison.TailConstructed
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

section ZeroSlice
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The array with its order-zero slice removed. -/
def zero0 (c : LiftCoeff ι h) : LiftCoeff ι h := fun m => if m = 0 then 0 else c m

omit [Fintype ι] in
theorem zero0_zero (c : LiftCoeff ι h) (α : DerivativeWord2 0) (t : ℝ) (X z : Vec 2)
    (v u : ι) : zero0 c 0 α t X z v u = 0 := by
  simp [zero0]

omit [Fintype ι] in
theorem zero0_of_ne (c : LiftCoeff ι h) {m : ℕ} (hm : m ≠ 0) (α : DerivativeWord2 m) (t : ℝ)
    (X z : Vec 2) (v u : ι) : zero0 c m α t X z v u = c m α t X z v u := by
  simp [zero0, hm]

omit [Fintype ι] in
theorem zero0_perm (c : LiftCoeff ι h) (m : ℕ)
    (hc : ∀ (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) : zero0 c m (β ∘ σ) = zero0 c m β := by
  unfold zero0
  split_ifs
  · rfl
  · exact hc β σ

/-- Removing a vanishing order-zero slice does not change the lift action. -/
theorem liftApply_zero0 (n : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (X z : Vec 2) (h0 : ∀ (α : DerivativeWord2 0) v u, c 0 α t X z v u = 0) :
    liftApply n (zero0 c) a t X z = liftApply n c a t X z := by
  funext v
  simp only [liftApply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun u _ => ?_
    rw [zero0_zero, h0]
  · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun u _ => ?_
    rw [zero0_of_ne c hm.ne']

omit [Fintype ι] in
/-- Box smoothness, periodicity and a bound of a nonzero-order entry pass to `zero0`. -/
theorem zero0_entry (c : LiftCoeff ι h) {p q m : ℕ} (α : DerivativeWord2 m) (t : ℝ) (v u : ι)
    (M : ℝ) (hM : 0 ≤ M)
    (hc : m ≠ 0 → IsBoxSmooth p q (fun X z => c m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => c m α t X z v u)) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => c m α t Y y v u) z) X‖ ≤ M) :
    IsBoxSmooth p q (fun X z => zero0 c m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => zero0 c m α t X z v u)) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => zero0 c m α t Y y v u) z) X‖ ≤ M := by
  by_cases hm : m = 0
  · subst hm
    have he : ∀ X z, zero0 c 0 α t X z v u = 0 := fun X z => zero0_zero c α t X z v u
    refine ⟨?_, fun X s z => ?_, fun r _ s _ X z => ?_⟩
    · rw [show (fun X z => zero0 c 0 α t X z v u) = fun _ _ => 0 from
        funext fun X => funext fun z => he X z]
      exact IsBoxSmooth.zero
    · show zero0 c 0 α t X (z + AVenhance.latticeShift s) v u = zero0 c 0 α t X z v u
      rw [he, he]
    · simp only [he, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact hM
  · obtain ⟨hb, hp, hB⟩ := hc hm
    have he : ∀ X z, zero0 c m α t X z v u = c m α t X z v u := fun X z =>
      zero0_of_ne c hm α t X z v u
    refine ⟨?_, fun X s z => ?_, fun r hr s hs X z => ?_⟩
    · rw [show (fun X z => zero0 c m α t X z v u) = fun X z => c m α t X z v u from
        funext fun X => funext fun z => he X z]
      exact hb
    · show zero0 c m α t X (z + AVenhance.latticeShift s) v u = zero0 c m α t X z v u
      rw [he, he]
      exact hp X s z
    · simp only [he]
      exact hB r hr s hs X z

end ZeroSlice

/-! ### Fast periodicity of partials and of the cross flux -/

section Periodic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_shift_isZ2Periodic (g : Vec 2 → E) (hg : AVenhance.IsZ2Periodic g)
    (s : Fin 2 → ℤ) (z : Vec 2) :
    fderiv ℝ g (z + AVenhance.latticeShift s) = fderiv ℝ g z := by
  rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := g) (AVenhance.latticeShift s)]
  congr 1
  funext x
  exact hg s x

theorem fastPartial_isZ2Periodic (k : Fin 2) (Φ : Vec 2 → Vec 2 → E) (X : Vec 2)
    (hΦ : AVenhance.IsZ2Periodic (Φ X)) :
    AVenhance.IsZ2Periodic (fun z => fastPartial k Φ X z) := by
  intro s z
  exact congrArg (fun L : Vec 2 →L[ℝ] E => L (basisVec k))
    (fderiv_shift_isZ2Periodic (fun z' => Φ X z') hΦ s z)

theorem crossFluxField_isZ2Periodic (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2)
    (Φ : Vec 2 → Vec 2 → E) (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) (X : Vec 2) :
    AVenhance.IsZ2Periodic (crossFluxField η G k Φ X) := by
  intro s z
  have h1 : ∀ X', Φ X' (z + AVenhance.latticeShift s) = Φ X' z := fun X' => hΦ X' s z
  simp only [crossFluxField, slowPartial, h1]

end Periodic

section Setting
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The components of the raw flux are fast periodic. -/
theorem setting_rawFlux_isZ2Periodic
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (k₀ : Fin 2)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (v : ι) :
    AVenhance.IsZ2Periodic
      (fun z => constructedLiftTailRawFlux Q Cc N hh n (fun _ => f) t X z k₀ v) := by
  have hG := setting_metric_contDiff_one P t ht
  have hΦ : IsBoxSmooth 1 0 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t) :=
    liftApply_box_reserve (n - 1) 1 0 (Cc hh (n - 1)) (fun _ => f) t (hf.of_le (by simp))
      (fun m _ α v' u => setting_tailRaw_coefficient_box P sX sZ hsZ Cc hseq 1 0
        (by omega) (by omega) hh hhh (n - 1) m α v' u t ht)
  have hcross := crossFluxField_isZ2Periodic Q.η (Q.G t) k₀
    (fun Y y => liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y y v)
    (fun X' s z => congrFun
      (liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh (n - 1) (fun _ => f) t ht X' s z) v) X
  intro s z
  show constructedLiftTailRawFlux Q Cc N hh n (fun _ => f) t X (z + AVenhance.latticeShift s)
      k₀ v = constructedLiftTailRawFlux Q Cc N hh n (fun _ => f) t X z k₀ v
  rw [constructedLiftTailRawFlux_apply Q Cc N hh n _ t X (z + AVenhance.latticeShift s) k₀ v
      hΦ hG, constructedLiftTailRawFlux_apply Q Cc N hh n _ t X z k₀ v hΦ hG, hcross s z]
  by_cases hh0 : hh = 0
  · rw [ite_eq_left hh0, ite_eq_left hh0]
  · have hgood := setting_lift_polynomial_sourceFlux_good_one P sX sZ hsZ Cc hseq (hh - 1)
      (by omega) n k₀ f hf t ht
    rw [ite_eq_right hh0, ite_eq_right hh0, hgood.2 X s z]


end Setting

section MeanEntry
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

omit [Fintype ι] in
/-- Entries of the cell-mean array: box smooth in every fast order, with slow bounds doubled per
order (operator-valued instance of `cellMean_box_bound`). -/
theorem cellMeanCoeff_entry_box_bound (c : LiftCoeff ι h) {m : ℕ} (α : DerivativeWord2 m)
    (t : ℝ) (v u : ι) (p q : ℕ) (hf : IsBoxSmooth p 0 (fun X z => c m α t X z v u)) {B : ℝ}
    (hb : ∀ j ≤ p, ∀ X z, ‖iteratedFDeriv ℝ j (fun Y => c m α t Y z v u) X‖ ≤ B) :
    IsBoxSmooth p q (fun X z => cellMeanCoeff c m α t X z v u) ∧
      ∀ r ≤ p, ∀ s, ∀ X z, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => cellMeanCoeff c m α t Y y v u) z) X‖ ≤ 2 ^ r * B := by
  let : MeasurableSpace (h u →L[ℝ] h v) := borel _
  have : BorelSpace (h u →L[ℝ] h v) := ⟨rfl⟩
  exact cellMean_box_bound p q (fun X z => c m α t X z v u) hf hb

end MeanEntry

end AVRegularity.CycleComparison.TailPresentation
end
end

section
/-! A proof of `ArraysStatement`.

At grade `hh` and tail degree `n`, with `R k := rawFluxCoefficient Q Cc hh n k` and
`T := tailLeftCoefficient Q Cc N hh n`, the arrays are
* `Fc k := zero0 (R k - cellMean (R k))`;
* `fc := 0` when `constructedScalarTailEnd N D hh < n` (then the scalar tail vanishes on the window,
  `diagonal_tail_sub_rawFlux_div_zero`), and `fc := zero0 (T - fastDiv R)` otherwise.

`zero0` removes the order-zero slice, which already vanishes on the window
(`setting_rawFluxCoefficient_order_zero`, `setting_tailLeftCoefficient_zero_order`), so the actions
on the window are unchanged while the support clause holds at every time. The entry bounds come
from the test-to-array lemma applied to the normalized test bounds of `R` and `T`, summed over the
finitely many degrees, orders and words, with `lam ≤ 1`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
  AVRegularity.CycleComparison.TailConstructed
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! ### The constants -/

theorem entry_weaken {c T M l : ℝ} (hc : 0 ≤ c) (hcT : c ≤ T) (hM : 0 ≤ M) (hl : l ≤ 1) :
    c * M * l ≤ T * M :=
  calc
    c * M * l ≤ c * M * 1 := mul_le_mul_of_nonneg_left hl (mul_nonneg hc hM)
    _ = c * M := mul_one _
    _ ≤ T * M := mul_le_mul_of_nonneg_right hcT hM

section Constants
variable (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)

/-- The calibration constant of one raw-flux coefficient (`symmetric_lift_coefficient_graded_bound_of_tests`). -/
def rawEntryConst (n m : ℕ) (α : DerivativeWord2 m) : ℝ :=
  ∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α 1 j| *
    rawFluxTestBudget K k L D H N CG Cw Cj ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))

/-- The calibration constant of one tail coefficient (`setting_tail_coefficient_box_and_bound`). -/
def tailEntryConst (hh n m : ℕ) (α : DerivativeWord2 m) : ℝ :=
  ∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α 1 j| *
    tailTestScalarBudget K k L D H N hh n K (arrayFastOrder k L D) CG Cw Cj
      ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))

/-- All raw-flux coefficient constants, summed over degrees `≤ 2N+D`, orders and words. -/
def rawEntryTotal : ℝ :=
  ∑ n ∈ Finset.range (2 * N + D + 1), ∑ m ∈ Finset.range (n + 1),
    ∑ α : DerivativeWord2 m, rawEntryConst K k L D H N CG Cw Cj n m α

/-- All tail coefficient constants, summed over grades `≤ H`, degrees, orders and words. -/
def tailEntryTotal : ℝ :=
  ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (2 * N + D + 1),
    ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
      tailEntryConst K k L D H N CG Cw Cj hh n m α

/-- The constant `Cm` of `ArraysStatement`. -/
def arraysConstant : ℝ :=
  (3 + 2 ^ K) * rawEntryTotal K k L D H N CG Cw Cj + tailEntryTotal K k L D H N CG Cw Cj

theorem rawEntryConst_nonneg (n m : ℕ) (α : DerivativeWord2 m) :
    0 ≤ rawEntryConst K k L D H N CG Cw Cj n m α :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (abs_nonneg _) (rawFluxTestBudget_nonneg _ _ _ _ _ _ _ _ _ _)

theorem tailEntryConst_nonneg (hh n m : ℕ) (α : DerivativeWord2 m) :
    0 ≤ tailEntryConst K k L D H N CG Cw Cj hh n m α :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (abs_nonneg _) (tailTestScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem rawEntryTotal_nonneg : 0 ≤ rawEntryTotal K k L D H N CG Cw Cj :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    rawEntryConst_nonneg K k L D H N CG Cw Cj _ _ _

theorem tailEntryTotal_nonneg : 0 ≤ tailEntryTotal K k L D H N CG Cw Cj :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => tailEntryConst_nonneg K k L D H N CG Cw Cj _ _ _ _

theorem rawEntryConst_le_total (n m : ℕ) (hn : n ≤ 2 * N + D) (hm : m ≤ n)
    (α : DerivativeWord2 m) :
    rawEntryConst K k L D H N CG Cw Cj n m α ≤ rawEntryTotal K k L D H N CG Cw Cj := by
  unfold rawEntryTotal
  have h1 : rawEntryConst K k L D H N CG Cw Cj n m α ≤
      ∑ α' : DerivativeWord2 m, rawEntryConst K k L D H N CG Cw Cj n m α' :=
    Finset.single_le_sum (f := fun α' => rawEntryConst K k L D H N CG Cw Cj n m α')
      (fun _ _ => rawEntryConst_nonneg K k L D H N CG Cw Cj _ _ _) (Finset.mem_univ α)
  have h2 : (∑ α' : DerivativeWord2 m, rawEntryConst K k L D H N CG Cw Cj n m α') ≤
      ∑ m' ∈ Finset.range (n + 1), ∑ α' : DerivativeWord2 m',
        rawEntryConst K k L D H N CG Cw Cj n m' α' :=
    Finset.single_le_sum (f := fun m' => ∑ α' : DerivativeWord2 m',
        rawEntryConst K k L D H N CG Cw Cj n m' α')
      (fun _ _ => Finset.sum_nonneg fun _ _ => rawEntryConst_nonneg K k L D H N CG Cw Cj _ _ _)
      (Finset.mem_range.mpr (by omega))
  have h3 : (∑ m' ∈ Finset.range (n + 1), ∑ α' : DerivativeWord2 m',
        rawEntryConst K k L D H N CG Cw Cj n m' α') ≤
      ∑ n' ∈ Finset.range (2 * N + D + 1), ∑ m' ∈ Finset.range (n' + 1),
        ∑ α' : DerivativeWord2 m', rawEntryConst K k L D H N CG Cw Cj n' m' α' :=
    Finset.single_le_sum (f := fun n' => ∑ m' ∈ Finset.range (n' + 1),
        ∑ α' : DerivativeWord2 m', rawEntryConst K k L D H N CG Cw Cj n' m' α')
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        rawEntryConst_nonneg K k L D H N CG Cw Cj _ _ _)
      (Finset.mem_range.mpr (by omega))
  exact h1.trans (h2.trans h3)

theorem tailEntryConst_le_total (hh n m : ℕ) (hhh : hh ≤ H) (hn : n ≤ 2 * N + D)
    (hm : m ≤ n) (α : DerivativeWord2 m) :
    tailEntryConst K k L D H N CG Cw Cj hh n m α ≤ tailEntryTotal K k L D H N CG Cw Cj := by
  unfold tailEntryTotal
  have h1 : tailEntryConst K k L D H N CG Cw Cj hh n m α ≤
      ∑ α' : DerivativeWord2 m, tailEntryConst K k L D H N CG Cw Cj hh n m α' :=
    Finset.single_le_sum (f := fun α' => tailEntryConst K k L D H N CG Cw Cj hh n m α')
      (fun _ _ => tailEntryConst_nonneg K k L D H N CG Cw Cj _ _ _ _) (Finset.mem_univ α)
  have h2 : (∑ α' : DerivativeWord2 m, tailEntryConst K k L D H N CG Cw Cj hh n m α') ≤
      ∑ m' ∈ Finset.range (n + 1), ∑ α' : DerivativeWord2 m',
        tailEntryConst K k L D H N CG Cw Cj hh n m' α' :=
    Finset.single_le_sum (f := fun m' => ∑ α' : DerivativeWord2 m',
        tailEntryConst K k L D H N CG Cw Cj hh n m' α')
      (fun _ _ => Finset.sum_nonneg fun _ _ =>
        tailEntryConst_nonneg K k L D H N CG Cw Cj _ _ _ _)
      (Finset.mem_range.mpr (by omega))
  have h3 : (∑ m' ∈ Finset.range (n + 1), ∑ α' : DerivativeWord2 m',
        tailEntryConst K k L D H N CG Cw Cj hh n m' α') ≤
      ∑ n' ∈ Finset.range (2 * N + D + 1), ∑ m' ∈ Finset.range (n' + 1),
        ∑ α' : DerivativeWord2 m', tailEntryConst K k L D H N CG Cw Cj hh n' m' α' :=
    Finset.single_le_sum (f := fun n' => ∑ m' ∈ Finset.range (n' + 1),
        ∑ α' : DerivativeWord2 m', tailEntryConst K k L D H N CG Cw Cj hh n' m' α')
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        tailEntryConst_nonneg K k L D H N CG Cw Cj _ _ _ _)
      (Finset.mem_range.mpr (by omega))
  have h4 : (∑ n' ∈ Finset.range (2 * N + D + 1), ∑ m' ∈ Finset.range (n' + 1),
        ∑ α' : DerivativeWord2 m', tailEntryConst K k L D H N CG Cw Cj hh n' m' α') ≤
      ∑ hh' ∈ Finset.range (H + 1), ∑ n' ∈ Finset.range (2 * N + D + 1),
        ∑ m' ∈ Finset.range (n' + 1), ∑ α' : DerivativeWord2 m',
          tailEntryConst K k L D H N CG Cw Cj hh' n' m' α' :=
    Finset.single_le_sum (f := fun hh' => ∑ n' ∈ Finset.range (2 * N + D + 1),
        ∑ m' ∈ Finset.range (n' + 1), ∑ α' : DerivativeWord2 m',
          tailEntryConst K k L D H N CG Cw Cj hh' n' m' α')
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => tailEntryConst_nonneg K k L D H N CG Cw Cj _ _ _ _)
      (Finset.mem_range.mpr (by omega))
  exact h1.trans (h2.trans (h3.trans h4))

theorem arraysConstant_nonneg : 0 ≤ arraysConstant K k L D H N CG Cw Cj := by
  unfold arraysConstant
  have := rawEntryTotal_nonneg K k L D H N CG Cw Cj
  have := tailEntryTotal_nonneg K k L D H N CG Cw Cj
  positivity

theorem flux_le_arraysConstant :
    (1 + 2 ^ K) * rawEntryTotal K k L D H N CG Cw Cj ≤ arraysConstant K k L D H N CG Cw Cj := by
  unfold arraysConstant
  have := rawEntryTotal_nonneg K k L D H N CG Cw Cj
  have := tailEntryTotal_nonneg K k L D H N CG Cw Cj
  linarith

theorem scalar_le_arraysConstant :
    tailEntryTotal K k L D H N CG Cw Cj + 2 * rawEntryTotal K k L D H N CG Cw Cj ≤
      arraysConstant K k L D H N CG Cw Cj := by
  unfold arraysConstant
  have hR := rawEntryTotal_nonneg K k L D H N CG Cw Cj
  have hK : 0 ≤ (2 : ℝ) ^ K * rawEntryTotal K k L D H N CG Cw Cj :=
    mul_nonneg (by positivity) hR
  linarith

end Constants

/-! ### Entries under the lift setting -/

section Setting
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- Every raw-flux coefficient: box smooth through `(K, max k (L+2) + D)`, fast periodic, and
bounded by the uniform constant times the envelope power. -/
theorem setting_rawEntry (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IsBoxSmooth K (max k (L + 2) + D)
        (fun X z => rawFluxCoefficient Q Cc hh n k₀ m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => rawFluxCoefficient Q Cc hh n k₀ m α t X z v u)) ∧
      ∀ r ≤ K, ∀ s ≤ max k (L + 2) + D, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => rawFluxCoefficient Q Cc hh n k₀ m α t Y y v u) z) X‖ ≤
          rawEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hsZ : 1 ≤ max (k + 1) (L + 2) := by omega
  have hw := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u
  have hT := rawEntryTotal_nonneg K k L D H N CG Cw Cj
  by_cases hm : m ≤ n
  · have hperm : ∀ (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
        rawFluxCoefficient Q Cc hh n k₀ m (β ∘ σ) = rawFluxCoefficient Q Cc hh n k₀ m β :=
      fun β σ => rawFluxCoefficient_perm Q Cc hh n k₀ m β σ
    have htest (ξ : h u) (A : Vec 2 →L[ℝ] ℝ) := setting_rawFlux_normalized_test_box_and_bound P
      (K + D + 2) (max (k + 1) (L + 2)) hsZ Cc hseq hh hhh n hn hnR k₀ K (max k (L + 2) + D)
      (by omega) le_rfl A u v ξ t ht
    refine ⟨symmetric_lift_coefficient_box_of_tests (rawFluxCoefficient Q Cc hh n k₀) n m K
      (max k (L + 2) + D) hm hperm α lam hlam.ne' u v t (fun ξ A => (htest ξ A).1), ?_, ?_⟩
    · intro X
      apply symmetric_lift_coefficient_periodic_of_tests n m hm
        (rawFluxCoefficient Q Cc hh n k₀) hperm α t X v u
      intro A ξ s z
      have hfA : ContDiff ℝ (⊤ : ℕ∞) (fun Y => Real.exp (A Y) • (Pi.single u ξ : ∀ i, h i)) :=
        (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
      have e1 := setting_rawFluxCoefficient_normalized_test_eq P (K + D + 2)
        (max (k + 1) (L + 2)) hsZ Cc hseq hh hhh n hn k₀ A u v ξ t ht X
        (z + AVenhance.latticeShift s)
      have e2 := setting_rawFluxCoefficient_normalized_test_eq P (K + D + 2)
        (max (k + 1) (L + 2)) hsZ Cc hseq hh hhh n hn k₀ A u v ξ t ht X z
      have hp := setting_rawFlux_isZ2Periodic P (K + D + 2) (max (k + 1) (L + 2)) hsZ Cc hseq
        hh hhh n k₀ _ hfA t ht X v s z
      exact e1.trans ((congrArg (fun y : h v => (Real.exp (A X))⁻¹ • y) hp).trans e2.symm)
    · intro r hr s hs X z
      have hb := symmetric_lift_coefficient_graded_bound_of_tests
        (rawFluxCoefficient Q Cc hh n k₀) n m K (max k (L + 2) + D) hm hperm α lam hlam u v t
        (rawFluxTestBudget K k L D H N CG Cw Cj) (rawFluxTestBudget_nonneg K k L D H N CG Cw Cj)
        _ hw (fun ξ A => (htest ξ A).1) (fun ξ A => (htest ξ A).2) r s hr hs X z
      exact hb.trans (entry_weaken (rawEntryConst_nonneg K k L D H N CG Cw Cj n m α)
        (rawEntryConst_le_total K k L D H N CG Cw Cj n m hnR hm α) hw
        (pow_le_one₀ hlam.le P.lam_le))
  · have hz : ∀ X z, rawFluxCoefficient Q Cc hh n k₀ m α t X z v u = 0 := fun X z =>
      rawFluxCoefficient_above_order Q Cc hh n hn k₀ m (by omega) α t X z v u
    refine ⟨?_, fun X s z => ?_, fun r _ s _ X z => ?_⟩
    · rw [show (fun X z => rawFluxCoefficient Q Cc hh n k₀ m α t X z v u) = fun _ _ => 0 from
        funext fun X => funext fun z => hz X z]
      exact IsBoxSmooth.zero
    · show rawFluxCoefficient Q Cc hh n k₀ m α t X (z + AVenhance.latticeShift s) v u =
        rawFluxCoefficient Q Cc hh n k₀ m α t X z v u
      rw [hz, hz]
    · simp only [hz, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg hT hw

include P in
/-- Every tail coefficient: box smooth through `(K, arrayFastOrder)`, fast periodic, and bounded
by the uniform constant times the envelope power. -/
theorem setting_tailEntry (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IsBoxSmooth K (arrayFastOrder k L D)
        (fun X z => tailLeftCoefficient Q Cc N hh n m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => tailLeftCoefficient Q Cc N hh n m α t X z v u)) ∧
      ∀ r ≤ K, ∀ s ≤ arrayFastOrder k L D, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => tailLeftCoefficient Q Cc N hh n m α t Y y v u) z) X‖ ≤
          tailEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hw := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u
  have hT := tailEntryTotal_nonneg K k L D H N CG Cw Cj
  by_cases hm : m ≤ n
  · obtain ⟨hbox, hbd⟩ := setting_tail_coefficient_box_and_bound P (K + D + 2)
      (max (k + 1) (L + 2)) (by omega) (by omega) Cc hseq K (arrayFastOrder k L D) (by omega)
      (by unfold arrayFastOrder; omega) hh hhh n hn m hm α u v t ht
    refine ⟨hbox, fun X => setting_tailLeftCoefficient_periodic P (K + D + 2)
      (max (k + 1) (L + 2)) (by omega) (by omega) Cc hseq hh hhh n hn hnR m (by omega) α t ht
      X v u, ?_⟩
    intro r hr s hs X z
    exact (hbd r hr s hs X z).trans (entry_weaken
      (tailEntryConst_nonneg K k L D H N CG Cw Cj hh n m α)
      (tailEntryConst_le_total K k L D H N CG Cw Cj hh n m hhh hnR hm α) hw
      (pow_le_one₀ hlam.le P.lam_le))
  · have hz : ∀ X z, tailLeftCoefficient Q Cc N hh n m α t X z v u = 0 := fun X z =>
      tailLeftCoefficient_above_order Q Cc N hh n hn m (by omega) α t X z v u
    refine ⟨?_, fun X s z => ?_, fun r _ s _ X z => ?_⟩
    · rw [show (fun X z => tailLeftCoefficient Q Cc N hh n m α t X z v u) = fun _ _ => 0 from
        funext fun X => funext fun z => hz X z]
      exact IsBoxSmooth.zero
    · show tailLeftCoefficient Q Cc N hh n m α t X (z + AVenhance.latticeShift s) v u =
        tailLeftCoefficient Q Cc N hh n m α t X z v u
      rw [hz, hz]
    · simp only [hz, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg hT hw

include P in
/-- The entries of the centered flux `R k - cellMean (R k)`. -/
theorem setting_fluxEntry (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IsBoxSmooth K (arrayFastOrder k L D) (fun X z => subCoeff (rawFluxCoefficient Q Cc hh n k₀)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n k₀)) m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => subCoeff (rawFluxCoefficient Q Cc hh n k₀)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n k₀)) m α t X z v u)) ∧
      ∀ r ≤ K, ∀ s ≤ arrayFastOrder k L D, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => subCoeff (rawFluxCoefficient Q Cc hh n k₀)
            (cellMeanCoeff (rawFluxCoefficient Q Cc hh n k₀)) m α t Y y v u) z) X‖ ≤
          ((1 + 2 ^ K) * rawEntryTotal K k L D H N CG Cw Cj) *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := by
  have hD := P.D_ge
  have hw := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u
  have hT := rawEntryTotal_nonneg K k L D H N CG Cw Cj
  obtain ⟨hRb, hRp, hRB⟩ := setting_rawEntry P Cc hseq hh hhh n hn hnR k₀ t ht m α v u
  have hslow : ∀ j ≤ K, ∀ X z, ‖iteratedFDeriv ℝ j
      (fun Y => rawFluxCoefficient Q Cc hh n k₀ m α t Y z v u) X‖ ≤
      rawEntryTotal K k L D H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := fun j hj X z =>
    (norm_mixed_jet_fast_zero j (fun X z => rawFluxCoefficient Q Cc hh n k₀ m α t X z v u)
      X z).symm.trans_le (hRB j hj 0 (Nat.zero_le _) X z)
  obtain ⟨hCb, hCB⟩ := cellMeanCoeff_entry_box_bound (rawFluxCoefficient Q Cc hh n k₀) α t v u
    K (arrayFastOrder k L D) (hRb.mono le_rfl (Nat.zero_le _)) hslow
  have hq : arrayFastOrder k L D ≤ max k (L + 2) + D := by unfold arrayFastOrder; omega
  have hRb' : IsBoxSmooth K (arrayFastOrder k L D)
      (fun X z => rawFluxCoefficient Q Cc hh n k₀ m α t X z v u) := hRb.mono le_rfl hq
  refine ⟨hRb'.sub hCb, ?_, ?_⟩
  · intro X s z
    exact congrArg (fun y => y - fieldCellMean
      (fun z' => rawFluxCoefficient Q Cc hh n k₀ m α t X z' v u)) (hRp X s z)
  · intro r hr s hs X z
    apply (norm_mixed_jet_sub_le (hRb'.mono hr hs) (hCb.mono hr hs) X z).trans
    have h2K : (2 : ℝ) ^ r ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hr
    calc
      _ ≤ rawEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u +
          2 ^ r * (rawEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) :=
        add_le_add (hRB r hr s (hs.trans hq) X z) (hCB r hr s X z)
      _ ≤ rawEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u +
          2 ^ K * (rawEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right h2K (mul_nonneg hT hw))
      _ = _ := by ring

include P in
/-- The entries of the scalar `T - fastDiv R`. -/
theorem setting_scalarEntry (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IsBoxSmooth K (arrayFastOrder k L D) (fun X z => subCoeff (tailLeftCoefficient Q Cc N hh n)
        (fastDivCoeff (rawFluxCoefficient Q Cc hh n)) m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => subCoeff (tailLeftCoefficient Q Cc N hh n)
        (fastDivCoeff (rawFluxCoefficient Q Cc hh n)) m α t X z v u)) ∧
      ∀ r ≤ K, ∀ s ≤ arrayFastOrder k L D, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => subCoeff (tailLeftCoefficient Q Cc N hh n)
            (fastDivCoeff (rawFluxCoefficient Q Cc hh n)) m α t Y y v u) z) X‖ ≤
          (tailEntryTotal K k L D H N CG Cw Cj + 2 * rawEntryTotal K k L D H N CG Cw Cj) *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := by
  have hD := P.D_ge
  obtain ⟨hTb, hTp, hTB⟩ := setting_tailEntry P Cc hseq hh hhh n hn hnR t ht m α v u
  have hR := fun kk : Fin 2 => setting_rawEntry P Cc hseq hh hhh n hn hnR kk t ht m α v u
  have hq : arrayFastOrder k L D + 1 ≤ max k (L + 2) + D := by unfold arrayFastOrder; omega
  obtain ⟨hFb, hFB⟩ := fastDiv_box_bound
    (fun kk X z => rawFluxCoefficient Q Cc hh n kk m α t X z v u)
    (fun kk => (hR kk).1.mono le_rfl hq)
    (fun kk r hr s hs X z => (hR kk).2.2 r hr s (hs.trans hq) X z)
  refine ⟨hTb.sub hFb, ?_, ?_⟩
  · intro X s z
    show tailLeftCoefficient Q Cc N hh n m α t X (z + AVenhance.latticeShift s) v u -
        ∑ kk : Fin 2, fastPartial kk
          (fun X' z' => rawFluxCoefficient Q Cc hh n kk m α t X' z' v u) X
          (z + AVenhance.latticeShift s) =
      tailLeftCoefficient Q Cc N hh n m α t X z v u -
        ∑ kk : Fin 2, fastPartial kk
          (fun X' z' => rawFluxCoefficient Q Cc hh n kk m α t X' z' v u) X z
    exact congrArg₂ (fun x y => x - y) (hTp X s z)
      (Finset.sum_congr rfl fun kk _ => fastPartial_isZ2Periodic kk _ X ((hR kk).2.1 X) s z)
  · intro r hr s hs X z
    apply (norm_mixed_jet_sub_le (hTb.mono hr hs) (hFb.mono hr hs) X z).trans
    calc
      _ ≤ tailEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u +
          2 * (rawEntryTotal K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) :=
        add_le_add (hTB r hr s hs X z) (hFB r hr s hs X z)
      _ = _ := by ring

end Setting

/-! ### The interface -/

/-- **The constructed centered tail arrays exist with uniform entry bounds.** -/
theorem arrays_statement_holds (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ArraysStatement N K k L D H CG Cw Cj := by
  refine ⟨arraysConstant K k L D H N CG Cw Cj, arraysConstant_nonneg K k L D H N CG Cw Cj, ?_⟩
  intro ι _ _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P Cc hseq
    hh hhh n hn1 hnR
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  have hD := P.D_ge
  have hN := P.N_ge
  have hn : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hsZ : 1 ≤ max (k + 1) (L + 2) := by omega
  have hw (v u : ι) := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u
  have hCm := arraysConstant_nonneg K k L D H N CG Cw Cj
  have hFle := flux_le_arraysConstant K k L D H N CG Cw Cj
  have hfle := scalar_le_arraysConstant K k L D H N CG Cw Cj
  -- Positive lifts annihilate constants (`cycle_lift_structure`, first assertion).
  have hconst : ∀ c0 : ∀ i, h i, ∀ hh', hh' ≤ H → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
      ∀ d, 1 ≤ d → d ≤ N → liftApply d (Cc hh' d) (fun _ _ => c0) t X z = 0 :=
    fun c0 hh' hhh' t ht X z d hd _ => congrFun (congrFun
      (liftSequence_constants_zero P _ _ Cc hseq c0 hh' hhh' d hd t ht) X) z
  -- Order-zero and above-order slices.
  have hR0 : ∀ kk, ∀ t ∈ Set.Icc t₀ t₁, ∀ (α : DerivativeWord2 0) X z v u,
      rawFluxCoefficient Q Cc hh n kk 0 α t X z v u = 0 :=
    fun kk t ht α X z v u => setting_rawFluxCoefficient_order_zero P (K + D + 2)
      (max (k + 1) (L + 2)) hsZ Cc hseq hconst hh hhh n hn2 kk α t ht X z v u
  have hT0 : ∀ t ∈ Set.Icc t₀ t₁, ∀ (α : DerivativeWord2 0) X z v u,
      tailLeftCoefficient Q Cc N hh n 0 α t X z v u = 0 :=
    fun t ht α X z v u => setting_tailLeftCoefficient_zero_order P (K + D + 2)
      (max (k + 1) (L + 2)) (by omega) (by omega) Cc hseq hh hhh n hn hnR α t ht X z v u
  have hRhi : ∀ kk m, n < m → ∀ α t X z v u,
      rawFluxCoefficient Q Cc hh n kk m α t X z v u = 0 :=
    fun kk m hm α t X z v u => rawFluxCoefficient_above_order Q Cc hh n hn kk m hm α t X z v u
  have hThi : ∀ m, n < m → ∀ α t X z v u, tailLeftCoefficient Q Cc N hh n m α t X z v u = 0 :=
    fun m hm α t X z v u => tailLeftCoefficient_above_order Q Cc N hh n hn m hm α t X z v u
  -- Symmetry.
  have hFperm : ∀ kk m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
      zero0 (subCoeff (rawFluxCoefficient Q Cc hh n kk)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk))) m (β ∘ σ) =
      zero0 (subCoeff (rawFluxCoefficient Q Cc hh n kk)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk))) m β :=
    fun kk m β σ => zero0_perm _ m (subCoeff_perm (rawFluxCoefficient_perm Q Cc hh n kk m)
      (cellMeanCoeff_perm (rawFluxCoefficient_perm Q Cc hh n kk m))) β σ
  have hfperm : ∀ m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
      zero0 (subCoeff (tailLeftCoefficient Q Cc N hh n)
        (fastDivCoeff (rawFluxCoefficient Q Cc hh n))) m (β ∘ σ) =
      zero0 (subCoeff (tailLeftCoefficient Q Cc N hh n)
        (fastDivCoeff (rawFluxCoefficient Q Cc hh n))) m β :=
    fun m β σ => zero0_perm _ m (subCoeff_perm (tailLeftCoefficient_perm Q Cc N hh n m)
      (fastDivCoeff_perm (fun kk => rawFluxCoefficient_perm Q Cc hh n kk m))) β σ
  -- Support.
  have hFsupp : ∀ kk m α t X z v u, (m = 0 ∨ 2 * N + D < m) →
      zero0 (subCoeff (rawFluxCoefficient Q Cc hh n kk)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk))) m α t X z v u = 0 := by
    intro kk m α t X z v u hm
    rcases hm with hm0 | hm
    · subst hm0
      exact zero0_zero _ α t X z v u
    · rw [zero0_of_ne _ (by omega)]
      show rawFluxCoefficient Q Cc hh n kk m α t X z v u -
        fieldCellMean (fun z' => rawFluxCoefficient Q Cc hh n kk m α t X z' v u) = 0
      simp only [hRhi kk m (by omega), fieldCellMean_zero, sub_zero]
  have hfsupp : ∀ m α t X z v u, (m = 0 ∨ 2 * N + D < m) →
      zero0 (subCoeff (tailLeftCoefficient Q Cc N hh n)
        (fastDivCoeff (rawFluxCoefficient Q Cc hh n))) m α t X z v u = 0 := by
    intro m α t X z v u hm
    rcases hm with hm0 | hm
    · subst hm0
      exact zero0_zero _ α t X z v u
    · rw [zero0_of_ne _ (by omega)]
      have hRz : ∀ kk X' z', rawFluxCoefficient Q Cc hh n kk m α t X' z' v u = 0 :=
        fun kk X' z' => hRhi kk m (by omega) α t X' z' v u
      show tailLeftCoefficient Q Cc N hh n m α t X z v u - ∑ kk : Fin 2, fastPartial kk
        (fun X' z' => rawFluxCoefficient Q Cc hh n kk m α t X' z' v u) X z = 0
      simp [hThi m (by omega) α t X z v u, hRz, fastPartial]
  -- Actions.
  have hRbox : ∀ kk, ∀ t ∈ Set.Icc t₀ t₁, ∀ m α v u, IsBoxSmooth K (max k (L + 2) + D)
      (fun X z => rawFluxCoefficient Q Cc hh n kk m α t X z v u) :=
    fun kk t ht m α v u => (setting_rawEntry P Cc hseq hh hhh n hn hnR kk t ht m α v u).1
  have hact : ∀ kk a₀, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
      liftApply (2 * N + D) (rawFluxCoefficient Q Cc hh n kk) (fun _ => a₀) t X z =
        constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z kk :=
    fun kk a₀ ha₀ t ht X z => setting_rawFluxCoefficient_action P (K + D + 2)
      (max (k + 1) (L + 2)) hsZ Cc hseq hh hhh n hn hnR kk a₀ ha₀ t ht X z
  have hLbox : ∀ kk a₀, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁,
      IsBoxSmooth 0 1 (liftApply (2 * N + D) (rawFluxCoefficient Q Cc hh n kk) (fun _ => a₀) t) :=
    fun kk a₀ ha₀ t ht => liftApply_box_reserve (2 * N + D) 0 1 _ (fun _ => a₀) t
      (ha₀.of_le (by exact_mod_cast le_top))
      (fun m _ α v u => (hRbox kk t ht m α v u).mono (Nat.zero_le _) (by omega))
  have hFact : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁,
      ∀ X z, ∀ kk, liftApply (2 * N + D) (zero0 (subCoeff (rawFluxCoefficient Q Cc hh n kk)
          (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk)))) (fun _ => a₀) t X z =
        constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z kk -
          fieldCellMean
            (fun z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z' kk) := by
    intro a₀ ha₀ t ht X z kk
    have hcont : Continuous
        (fun z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z' kk) := by
      have he : (fun z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z' kk) =
          liftApply (2 * N + D) (rawFluxCoefficient Q Cc hh n kk) (fun _ => a₀) t X :=
        funext fun z' => (hact kk a₀ ha₀ t ht X z').symm
      rw [he]
      exact ((hLbox kk a₀ ha₀ t ht).1 X).continuous
    have h0 : ∀ (α : DerivativeWord2 0) v u, subCoeff (rawFluxCoefficient Q Cc hh n kk)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk)) 0 α t X z v u = 0 := by
      intro α v u
      show rawFluxCoefficient Q Cc hh n kk 0 α t X z v u -
        fieldCellMean (fun z' => rawFluxCoefficient Q Cc hh n kk 0 α t X z' v u) = 0
      simp only [hR0 kk t ht α, fieldCellMean_zero, sub_zero]
    rw [liftApply_zero0 (2 * N + D) _ (fun _ => a₀) t X z h0, liftApply_subCoeff]
    funext v
    have hfun : (fun z' => liftApply (2 * N + D) (rawFluxCoefficient Q Cc hh n kk)
        (fun _ => a₀) t X z' v) =
        fun z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z' kk v :=
      funext fun z' => congrFun (hact kk a₀ ha₀ t ht X z') v
    rw [Pi.sub_apply, Pi.sub_apply, liftApply_cellMeanCoeff (2 * N + D)
      (rawFluxCoefficient Q Cc hh n kk) (fun _ => a₀) t X z v
      (fun m α u => ((hRbox kk t ht m α v u).1 X).continuous), hact kk a₀ ha₀ t ht X z, hfun,
      fieldCellMean_pi_apply _ hcont v]
  have hfact : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁,
      ∀ X z, liftApply (2 * N + D) (zero0 (subCoeff (tailLeftCoefficient Q Cc N hh n)
          (fastDivCoeff (rawFluxCoefficient Q Cc hh n)))) (fun _ => a₀) t X z =
        liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z -
          ∑ kk : Fin 2, fastPartial kk (fun X' z' =>
            constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X' z' kk) X z := by
    intro a₀ ha₀ t ht X z
    have hR0' : ∀ kk (α : DerivativeWord2 0) X' z' v u,
        rawFluxCoefficient Q Cc hh n kk 0 α t X' z' v u = 0 :=
      fun kk α X' z' v u => hR0 kk t ht α X' z' v u
    have h0 : ∀ (α : DerivativeWord2 0) v u, subCoeff (tailLeftCoefficient Q Cc N hh n)
        (fastDivCoeff (rawFluxCoefficient Q Cc hh n)) 0 α t X z v u = 0 := by
      intro α v u
      show tailLeftCoefficient Q Cc N hh n 0 α t X z v u - ∑ kk : Fin 2, fastPartial kk
        (fun X' z' => rawFluxCoefficient Q Cc hh n kk 0 α t X' z' v u) X z = 0
      simp [hT0 t ht α X z v u, hR0', fastPartial]
    have hfield : ∀ kk, (fun X' z' =>
        constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X' z' kk) =
        liftApply (2 * N + D) (rawFluxCoefficient Q Cc hh n kk) (fun _ => a₀) t :=
      fun kk => funext fun X' => funext fun z' => (hact kk a₀ ha₀ t ht X' z').symm
    rw [liftApply_zero0 (2 * N + D) _ (fun _ => a₀) t X z h0, liftApply_subCoeff,
      setting_tailLeftCoefficient_apply P (K + D + 2) (max (k + 1) (L + 2)) (by omega)
        (by omega) Cc hseq hh hhh n hn hnR a₀ ha₀ t ht X z]
    funext v
    rw [Pi.sub_apply, Pi.sub_apply, liftApply_fastDivCoeff (2 * N + D)
      (rawFluxCoefficient Q Cc hh n) (fun _ => a₀) t X z v
      (fun kk m α v' u => ((hRbox kk t ht m α v' u).1 X).of_le
        (by exact_mod_cast (show 1 ≤ max k (L + 2) + D by omega))),
      Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun kk _ => ?_
    rw [hfield kk]
    exact fastPartial_postcomposition (ContinuousLinearMap.proj v) _
      (hLbox kk a₀ ha₀ t ht) kk X z
  -- Entry packages.
  have Fentry : ∀ kk, ∀ t ∈ Set.Icc t₀ t₁, ∀ m (α : DerivativeWord2 m) v u,
      IsBoxSmooth K (arrayFastOrder k L D) (fun X z => zero0 (subCoeff
        (rawFluxCoefficient Q Cc hh n kk) (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk)))
          m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => zero0 (subCoeff
        (rawFluxCoefficient Q Cc hh n kk) (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk)))
          m α t X z v u)) ∧
      ∀ r ≤ K, ∀ s ≤ arrayFastOrder k L D, ∀ X z, ‖iteratedFDeriv ℝ r (fun Y =>
        iteratedFDeriv ℝ s (fun y => zero0 (subCoeff (rawFluxCoefficient Q Cc hh n kk)
          (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk))) m α t Y y v u) z) X‖ ≤
        arraysConstant K k L D H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := by
    intro kk t ht m α v u
    refine zero0_entry _ α t v u _ (mul_nonneg hCm (hw v u)) fun _ => ?_
    obtain ⟨hb, hp, hB⟩ := setting_fluxEntry P Cc hseq hh hhh n hn hnR kk t ht m α v u
    exact ⟨hb, hp, fun r hr s hs X z =>
      (hB r hr s hs X z).trans (mul_le_mul_of_nonneg_right hFle (hw v u))⟩
  have fentry : ∀ t ∈ Set.Icc t₀ t₁, ∀ m (α : DerivativeWord2 m) v u,
      IsBoxSmooth K (arrayFastOrder k L D) (fun X z => zero0 (subCoeff
        (tailLeftCoefficient Q Cc N hh n) (fastDivCoeff (rawFluxCoefficient Q Cc hh n)))
          m α t X z v u) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => zero0 (subCoeff
        (tailLeftCoefficient Q Cc N hh n) (fastDivCoeff (rawFluxCoefficient Q Cc hh n)))
          m α t X z v u)) ∧
      ∀ r ≤ K, ∀ s ≤ arrayFastOrder k L D, ∀ X z, ‖iteratedFDeriv ℝ r (fun Y =>
        iteratedFDeriv ℝ s (fun y => zero0 (subCoeff (tailLeftCoefficient Q Cc N hh n)
          (fastDivCoeff (rawFluxCoefficient Q Cc hh n))) m α t Y y v u) z) X‖ ≤
        arraysConstant K k L D H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := by
    intro t ht m α v u
    refine zero0_entry _ α t v u _ (mul_nonneg hCm (hw v u)) fun _ => ?_
    obtain ⟨hb, hp, hB⟩ := setting_scalarEntry P Cc hseq hh hhh n hn hnR t ht m α v u
    exact ⟨hb, hp, fun r hr s hs X z =>
      (hB r hr s hs X z).trans (mul_le_mul_of_nonneg_right hfle (hw v u))⟩
  -- The two cases of the scalar cutoff.
  by_cases hend : constructedScalarTailEnd N D hh < n
  · have hh0 : hh = 0 := by
      by_contra hne
      have he : constructedScalarTailEnd N D hh = 2 * N + D := by
        simp [constructedScalarTailEnd, hne]
      omega
    have hend' : 2 * N + 2 ≤ n := by
      have he : constructedScalarTailEnd N D hh = 2 * N + 1 := by
        simp [constructedScalarTailEnd, hh0]
      omega
    refine ⟨0, fun kk => zero0 (subCoeff (rawFluxCoefficient Q Cc hh n kk)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk))),
      fun _ _ _ => rfl, hFperm, fun _ _ _ _ _ _ _ _ => rfl, hFsupp,
      fun _ _ _ _ _ _ _ _ => rfl, ?_, ?_, ?_⟩
    · intro a₀ ha₀ t ht X z
      refine ⟨fun kk => hFact a₀ ha₀ t ht X z kk, ?_⟩
      have hzero : liftApply (2 * N + D) (0 : LiftCoeff ι h) (fun _ => a₀) t X z = 0 :=
        congrFun (congrFun (congrFun (liftApply_of_coeff_zero (2 * N + D) 0
          (fun _ _ _ _ _ _ _ => rfl) (fun _ => a₀)) t) X) z
      rw [hzero, hh0]
      exact (diagonal_tail_sub_rawFlux_div_zero P (K + D + 2) (max (k + 1) (L + 2))
        (by omega) (by omega) Cc hseq n hend' a₀ ha₀ t ht X z).symm
    · intro t ht m α v u
      exact ⟨IsBoxSmooth.zero, fun _ _ _ => rfl,
        fun kk => ⟨(Fentry kk t ht m α v u).1, (Fentry kk t ht m α v u).2.1⟩⟩
    · intro t ht m α v u r hr s hs X z
      refine ⟨?_, fun kk => (Fentry kk t ht m α v u).2.2 r hr s hs X z⟩
      simp only [Pi.zero_apply, iteratedFDeriv_fun_zero, norm_zero]
      exact mul_nonneg hCm (hw v u)
  · refine ⟨zero0 (subCoeff (tailLeftCoefficient Q Cc N hh n)
        (fastDivCoeff (rawFluxCoefficient Q Cc hh n))),
      fun kk => zero0 (subCoeff (rawFluxCoefficient Q Cc hh n kk)
        (cellMeanCoeff (rawFluxCoefficient Q Cc hh n kk))),
      hfperm, hFperm, hfsupp, hFsupp, fun hlt => absurd hlt hend, ?_, ?_, ?_⟩
    · intro a₀ ha₀ t ht X z
      exact ⟨fun kk => hFact a₀ ha₀ t ht X z kk, hfact a₀ ha₀ t ht X z⟩
    · intro t ht m α v u
      exact ⟨(fentry t ht m α v u).1, (fentry t ht m α v u).2.1,
        fun kk => ⟨(Fentry kk t ht m α v u).1, (Fentry kk t ht m α v u).2.1⟩⟩
    · intro t ht m α v u r hr s hs X z
      exact ⟨(fentry t ht m α v u).2.2 r hr s hs X z,
        fun kk => (Fentry kk t ht m α v u).2.2 r hr s hs X z⟩

end AVRegularity.CycleComparison.TailPresentation
end
end
