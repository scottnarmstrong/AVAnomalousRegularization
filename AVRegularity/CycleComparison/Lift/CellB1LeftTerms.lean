-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.TransversePrimitiveBoxRegularity
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse
import AVRegularity.CycleEvolution.CellTimeFourierConvergence
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered slow derivatives of a finite differential operator retain a finite left-term representation. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftTermsSlowWord {m : ℕ} (α : DerivativeWord2 m) (l : List (LeftTerm E F)) :
    List (LeftTerm E F) := covariantLeftTermList 1 (List.ofFn α) l m

theorem leftTermsSlowWord_order {m : ℕ} (α : DerivativeWord2 m) (l : List (LeftTerm E F))
    (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n) (c : LeftTerm E F)
    (hc : c ∈ leftTermsSlowWord α l) : c.order ≤ n + m :=
  covariantLeftTermList_order 1 (List.ofFn α) l n hl m c hc

theorem leftTermsSlowWord_box {m : ℕ} (α : DerivativeWord2 m) (l : List (LeftTerm E F))
    (p q : ℕ) (hl : ∀ c ∈ l, IsBoxSmooth (p + m) q c.coeff)
    (c : LeftTerm E F) (hc : c ∈ leftTermsSlowWord α l) : IsBoxSmooth p q c.coeff := by
  apply covariantLeftTermList_box 1 (List.ofFn α) l m p q (by simp)
    (fun d hd => ?_) c hc
  simpa only [List.length_ofFn, Nat.add_sub_cancel] using hl d hd

theorem leftTermsSlowWord_apply {m : ℕ} (α : DerivativeWord2 m) (l : List (LeftTerm E F))
    (hl : ∀ c ∈ l, IsBoxSmooth m 0 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (leftTermsSlowWord α l) f X z =
      orderedDerivative α (fun Y => leftTermsApply l f Y z) X := by
  have he := covariantLeftTermList_apply 1 (List.ofFn α) l f hf m
    (fun c hc => by simpa only [List.length_ofFn, Nat.sub_self] using hl c hc)
  have htop : covariantListCoefficients 1 (List.ofFn α) (leftTermsApply l f) m =
      slowListDerivative (List.ofFn α) (leftTermsApply l f) := by
    simpa only [List.length_ofFn] using covariantListCoefficients_top (List.ofFn α) (leftTermsApply l f)
  rw [htop] at he
  exact (congrFun (congrFun he X) z).trans (slowListDerivative_word α _ X z)

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The fixed-order metric-difference decay constants are nonnegative. -/

theorem metricDifferenceKernelSourceConstant_nonneg (p q : ℕ) (M Md κ : ℝ) (S : ℕ → ℝ)
    (hM : 0 ≤ M) (hMd : 0 ≤ Md) (hκ : 0 < κ) (hS : ∀ j ≤ q, 0 ≤ S j) :
    0 ≤ metricDifferenceKernelSourceConstant p q M Md κ S := by
  unfold metricDifferenceKernelSourceConstant
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (metricDifferenceSourceBudget_nonneg p (q - j) Md S hMd
          (fun r hr => hS r (hr.trans (Nat.sub_le _ _))))
    · positivity
  · positivity

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Degree j in the literal source needs j slow input derivatives and the complementary D-j fast reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceCoefficientArray_box_reserve (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (p q j : ℕ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth (p + 1) (q + 1) (fun X z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth (p + j) (q + D - j) Φ) :
    IsBoxSmooth p q (sourceCoefficientArray edge η t Φ j) := by
  have he : sourceCoefficientArray edge η t Φ j = fun X z => ∑ k : Fin 2,
      covariantCoefficientStep η k (sourceFluxCoefficientArray edge η t Φ k) j X z := rfl
  rw [he]
  apply IsBoxSmooth.sum
  intro k _
  apply covariantCoefficientStep_box_reserve
  · apply sourceFluxCoefficientArray_box_reserve
    · intro v u d γ hγ α
      exact (hΓ v u d γ hγ α).mono (by omega) le_rfl
    · exact hΦ.mono le_rfl (by omega)
  · intro hj
    apply sourceFluxCoefficientArray_box_reserve
    · intro v u d γ hγ α
      exact (hΓ v u d γ hγ α).mono le_rfl (by omega)
    · exact hΦ.mono (by omega) (by omega)
end

/-! Componentwise source-flux fields retain the exact rectangular word reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxComponentCoefficient_box_reserve (edge : ConstituentEdges D h)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (p q j : ℕ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p q (γ.coeff α t))
    (hΦ : ∀ u, IsBoxSmooth (p + j) (q + (D - 1) - j) (fun X z => Φ X z u))
    (v : ι) : IsBoxSmooth p q (sourceFluxComponentCoefficient edge η t Φ k j v) := by
  have hf : IsBoxSmooth (p + j) (q + (D - 1) - j) Φ :=
    isBoxSmooth_pi (p + j) (q + (D - 1) - j) Φ hΦ
  have he := sourceFluxCoefficientArray_component_eq edge η t Φ k j
    (hf.mono (by omega) (by omega)) v
  rw [← he]
  exact (sourceFluxCoefficientArray_box_reserve edge η t Φ k p q j hΓ hf).clm_comp
    (ContinuousLinearMap.proj v)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every reserved slow word derivative of the literal inverse is a differentiated time integral. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseModeResponse_orderedDerivative_parameter (n : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (f t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) :
    orderedDerivative α
      (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b) =
      fun X => ∫ s, orderedDerivative α (clampedDuhamelField rate g f a b hab s) X
        ∂volume.restrict (Ioc a b) := by
  have hd := clamped_duhamel_reserve_data n g hm hs M lam rate κ a b
    hM hlam hrate hκ hab hb hgl f hmf hf S hS hfB
  rw [transverseModeResponse_eq_clamped_integral rate g f a b hab]
  exact orderedDerivative_parameter_integral (volume.restrict (Ioc a b)) n
    (clampedDuhamelField rate g f a b hab) hd.1 hd.2.1
    (fun j => duhamelSlowJetMajorant n M κ S j * lam ^ j) hd.2.2 q hq α

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! One constituent flux word has an explicit finite differential representation. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def constituentLeftTerms (η : ℝ) (w : List (Fin 2)) (j : ℕ)
    (l : List (LeftTerm E F)) (T : F →L[ℝ] G) (a : Vec 2 → Vec 2 → ℝ) :
    List (LeftTerm E G) :=
  ((covariantLeftTermList η w l j).map (fun c => c.postcompose T)).map (fun c => c.fieldSmul a)

theorem constituentLeftTerms_apply (η : ℝ) (w : List (Fin 2)) (j : ℕ)
    (l : List (LeftTerm E F)) (T : F →L[ℝ] G) (a : Vec 2 → Vec 2 → ℝ)
    (hl : ∀ c ∈ l, IsBoxSmooth j (w.length - j) c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    leftTermsApply (constituentLeftTerms η w j l T a) f = fun X z =>
      a X z • T (covariantListCoefficients η w (leftTermsApply l f) j X z) := by
  unfold constituentLeftTerms
  rw [leftTermsApply_map_fieldSmul, leftTermsApply_map_postcompose,
    covariantLeftTermList_apply η w l f hf j hl]

theorem constituentLeftTerms_box (η : ℝ) (w : List (Fin 2)) (j p q : ℕ)
    (hj : j ≤ w.length) (l : List (LeftTerm E F))
    (T : F →L[ℝ] G) (a : Vec 2 → Vec 2 → ℝ)
    (hl : ∀ c ∈ l, IsBoxSmooth (p + j) (q + w.length - j) c.coeff)
    (ha : IsBoxSmooth p q a) (c : LeftTerm E G)
    (hc : c ∈ constituentLeftTerms η w j l T a) : IsBoxSmooth p q c.coeff := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have hb := covariantLeftTermList_box η w l j p q hj hl e he
  exact (e.postcompose T).fieldSmul_box a p q (e.postcompose_box T p q hb) ha
end

/-! The height-zero mean flux adds the molecular metric only at degree two. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def diagonalMeanFluxCoefficient (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) (k : Fin 2) : LiftCoeff ι h :=
  fun m α t X z v u =>
    weightedLiftCoefficientMean (Cc 0 (n - 1))
      (fun t z => Real.sqrt Q.η * Q.v t z k) m α t X z v u +
    if n = 2 then metricFluxCoefficient Q.η Q.G k m α t X z v u else 0
end

/-! Single slow coordinate derivatives specialize the reusable ordered left-term calculus. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftTermsSlowPartial (k : Fin 2) (l : List (LeftTerm E F)) : List (LeftTerm E F) :=
  leftTermsSlowWord (fun _ : Fin 1 => k) l

theorem leftTermsSlowPartial_order (k : Fin 2) (l : List (LeftTerm E F))
    (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n) (c : LeftTerm E F)
    (hc : c ∈ leftTermsSlowPartial k l) : c.order ≤ n + 1 :=
  leftTermsSlowWord_order (fun _ : Fin 1 => k) l n hl c hc

theorem leftTermsSlowPartial_box (k : Fin 2) (l : List (LeftTerm E F))
    (p q : ℕ) (hl : ∀ c ∈ l, IsBoxSmooth (p + 1) q c.coeff)
    (c : LeftTerm E F) (hc : c ∈ leftTermsSlowPartial k l) : IsBoxSmooth p q c.coeff :=
  leftTermsSlowWord_box (fun _ : Fin 1 => k) l p q hl c hc

theorem leftTermsSlowPartial_apply (k : Fin 2) (l : List (LeftTerm E F))
    (hl : ∀ c ∈ l, IsBoxSmooth 1 0 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    leftTermsApply (leftTermsSlowPartial k l) f = slowPartial k (leftTermsApply l f) := by
  funext X z
  rw [leftTermsSlowPartial, leftTermsSlowWord_apply (fun _ : Fin 1 => k) l hl f hf X z]
  simp only [orderedDerivative, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil]
  rfl
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! An explicit fixed-data metric budget, chosen before scales and component families. -/

def metricParameterBudget (p : ℕ) (CG : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), max (CG r) 0

theorem metricParameterBudget_nonneg (p : ℕ) (CG : ℕ → ℝ) : 0 ≤ metricParameterBudget p CG :=
  Finset.sum_nonneg (fun r _ => le_max_right (CG r) 0)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_clamped_diagonal_metric_fixed_data (p : ℕ) (hp : p ≤ qs) (i : Fin 2) :
    let g := fun t X => Q.G (Set.projIcc a b P.window t) X i i
    let M := metricParameterBudget p CG
    0 ≤ M ∧
      (∀ X, Measurable (fun t => g t X)) ∧
      (∀ t, ContDiff ℝ (p : ℕ∞) (g t)) ∧
      (∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r) ∧
      (∀ t X, (3 / 4 : ℝ) ≤ g t X) := by
  dsimp only
  refine ⟨metricParameterBudget_nonneg p CG, ?_, ?_, ?_, ?_⟩
  · intro X
    exact (P.G_meas X i i).comp
      (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val
  · intro t
    exact (P.G_smooth _ (Set.projIcc a b P.window t).2 i i).of_le (by exact_mod_cast hp)
  · intro r hr t X
    apply (setting_metric_entry_scaled_jet_bound P r (hr.trans hp) _
      (Set.projIcc a b P.window t).2 X i i).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by
      rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le) r)
    exact Finset.single_le_sum (fun v _ => le_max_right (CG v) 0)
      (Finset.mem_range.mpr (by omega))
  · intro t X
    exact (metric_diagonal_bounds _ (3 / 4) (5 / 4)
      (P.G_ellip _ (Set.projIcc a b P.window t).2 X) i).1

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The explicit source array equals every literal normalized parameter derivative. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceCoefficientArray_above_degree (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (j : ℕ) (hj : D < j) :
    sourceCoefficientArray edge η t Φ j = fun _ _ => 0 := by
  funext X z
  change (∑ k : Fin 2,
    covariantCoefficientStep η k (sourceFluxCoefficientArray edge η t Φ k) j X z) = 0
  apply Finset.sum_eq_zero
  intro k _
  have h0 := sourceFluxCoefficientArray_above_degree edge η t Φ k j (by omega)
  have h1 := sourceFluxCoefficientArray_above_degree edge η t Φ k (j - 1) (by omega)
  have he : covariantCoefficientStep η k (sourceFluxCoefficientArray edge η t Φ k) j X z =
      fastPartial k (sourceFluxCoefficientArray edge η t Φ k j) X z +
        if j = 0 then 0 else Real.sqrt η •
          slowPartial k (sourceFluxCoefficientArray edge η t Φ k (j - 1)) X z := rfl
  rw [he, h0, h1]
  simp only [fastPartial_zero, slowPartial_zero, smul_zero, ite_self, add_zero]

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceCoeff_eq_sourceCoefficientArray (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : GoodField D Φ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z)) (j : ℕ) :
    sourceCoeff edge η j t Φ = sourceCoefficientArray edge η t Φ j := by
  funext X z
  have he : (fun ε => sourceOp edge η ε t Φ X z) =
      fun ε => ∑ i ∈ Finset.range (D + 1),
        ε ^ i • sourceCoefficientArray edge η t Φ i X z :=
    funext fun ε => sourceOp_polynomial_identity edge hD η ε t Φ hΦ hΓ X z
  change ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
    (fun ε => sourceOp edge η ε t Φ X z) 0 = _
  rw [he]
  exact normalized_polynomial_coefficient D j _ (fun i hi => by
    rw [sourceCoefficientArray_above_degree edge hD η t Φ i hi])

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Slow inverse jets gain the reciprocal Fourier rate, uniformly in the time window. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseModeResponse_orderedDerivative_parameter_norm_le (n : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 < rate) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (f t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) (X : Vec 2) :
    ‖orderedDerivative α
      (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b) X‖ ≤
      duhamelSlowJetMajorant n M κ S q * lam ^ q * (2 / (rate * κ)) := by
  let μ := volume.restrict (Ioc a b)
  let B := duhamelSlowJetMajorant n M κ S q * lam ^ q
  have hB : 0 ≤ B := mul_nonneg
    (duhamelSlowJetMajorant_nonneg n q M κ S hM hκ (fun j hj => hS j (hj.trans hq)))
    (pow_nonneg hlam q)
  have hd := clamped_duhamel_reserve_data n g hm hs M lam rate κ a b
    hM hlam hrate.le hκ hab hb hgl f hmf hf S hS hfB
  rw [transverseModeResponse_orderedDerivative_parameter n g hm hs M lam rate κ a b
    hM hlam hrate.le hκ hab hb hgl f hmf hf S hS hfB q hq α]
  have hc : Continuous (fun s : ℝ => B * Real.exp (-(rate * κ / 2) * (b - s))) := by fun_prop
  have hi : Integrable (fun s => B * Real.exp (-(rate * κ / 2) * (b - s))) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hc.intervalIntegrable a b)
  have hbound : ∀ᵐ s ∂μ,
      ‖orderedDerivative α (clampedDuhamelField rate g f a b hab s) X‖ ≤
        B * Real.exp (-(rate * κ / 2) * (b - s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsmem
    have hsb : s ≤ b := hsmem.2
    have he : clampedDuhamelField rate g f a b hab s =
        fun Y => transverseModeKernel rate (fun t => g t Y) s b • f s Y := by
      funext Y
      change transverseModeKernel rate (fun t => g t Y) (projIcc a b hab s) b •
        f (projIcc a b hab s) Y = _
      rw [projIcc_of_mem hab (show s ∈ Icc a b from ⟨hsmem.1.le, hsmem.2⟩)]
    apply (norm_orderedDerivative_le ((hd.2.1 s).of_le (by exact_mod_cast hq)) α X).trans
    rw [he]
    have hh := transverseModeKernel_source_scaled_jet_decay n q hq g hm hs
      M lam rate κ s b hM hlam hrate.le hκ hsb hb (fun t _ Y => hgl t Y)
      (f s) (hf s) S hS (fun j hj Y => hfB j hj s Y) X
    simpa only [B, duhamelSlowJetMajorant, mul_assoc, mul_left_comm, mul_comm] using hh
  calc
    _ ≤ ∫ s, B * Real.exp (-(rate * κ / 2) * (b - s)) ∂μ :=
      norm_integral_le_of_norm_le hi hbound
    _ = ∫ s in a..b, B * Real.exp (-(rate * κ / 2) * (b - s)) :=
      (intervalIntegral.integral_of_le hab).symm
    _ = B * ∫ s in a..b, Real.exp (-(rate * κ / 2) * (b - s)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ B * (1 / (rate * κ / 2)) := mul_le_mul_of_nonneg_left
      (integral_decayKernel_le _ (by positivity) a b) hB
    _ = _ := by dsimp [B]; ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The literal metric-response difference is one measurable bounded parameter integral. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def clampedMetricDifferenceField (rate : ℝ) (g : ℝ → Vec 2 → ℝ) (f : ℝ → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b) : ℝ → Vec 2 → E :=
  clampedDuhamelField rate g f a b hab - clampedDuhamelField rate (fun _ _ => 1) f a b hab

theorem clamped_metric_difference_reserve_data (p : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hf : ∀ t, ContDiff ℝ (p : ℕ∞) (f t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ p, 0 ≤ S j)
    (hfB : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j) :
    (∀ X, Measurable (fun s => clampedMetricDifferenceField rate g f a b hab s X)) ∧
    (∀ s, ContDiff ℝ (p : ℕ∞) (clampedMetricDifferenceField rate g f a b hab s)) ∧
    (∀ q ≤ p, ∀ s X, ‖iteratedFDeriv ℝ q (clampedMetricDifferenceField rate g f a b hab s) X‖ ≤
      (duhamelSlowJetMajorant p M κ S q + duhamelSlowJetMajorant p 1 κ S q) * lam ^ q) ∧
    (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b -
      transverseModeResponse rate (fun _ => 1) (fun t => f t X) a b) =
      fun X => ∫ s, clampedMetricDifferenceField rate g f a b hab s X ∂volume.restrict (Ioc a b) := by
  have hjI : ∀ j ≤ p, ∀ (t : ℝ) (X : Vec 2),
      ‖iteratedFDeriv ℝ j (fun _ : Vec 2 => (1 : ℝ)) X‖ ≤ 1 * lam ^ j := by
    intro j _ t X
    simpa only [abs_one] using scalarConstant_scaled_jet_le 1 lam hlam j X
  have hdG := clamped_duhamel_reserve_data p g hm hs M lam rate κ a b
    hM hlam hrate hκ hab hb hgl f hmf hf S hS hfB
  have hdI := clamped_duhamel_reserve_data p (fun _ _ => 1) (fun _ => measurable_const)
    (fun _ => contDiff_const) 1 lam rate κ a b zero_le_one hlam hrate hκ hab hjI
    (fun _ _ => hκ1) f hmf hf S hS hfB
  refine ⟨fun X => (hdG.1 X).sub (hdI.1 X), fun s => (hdG.2.1 s).sub (hdI.2.1 s), ?_, ?_⟩
  · intro q hq s X
    have he := parameter_difference_jet_bound p q hq _ _ (hdG.2.1 s) (hdI.2.1 s)
      _ _ (hdG.2.2 q hq s) (hdI.2.2 q hq s) X
    exact he.trans_eq (by ring)
  · have he := parameter_integral_sub_eq (volume.restrict (Ioc a b))
      (clampedDuhamelField rate g f a b hab) (clampedDuhamelField rate (fun _ _ => 1) f a b hab)
      hdG.1 hdI.1 (duhamelSlowJetMajorant p M κ S 0) (duhamelSlowJetMajorant p 1 κ S 0)
      (fun s X => by simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hdG.2.2 0 (by omega) s X)
      (fun s X => by simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hdI.2.2 0 (by omega) s X)
    rw [← transverseModeResponse_eq_clamped_integral rate g f a b hab,
      ← transverseModeResponse_eq_clamped_integral rate (fun _ _ => 1) f a b hab] at he
    exact he.symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Common ambient rectangular reserves justify the literal source derivatives and their sharp degree-wise reserve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sourceCoeff_box_reserve_of_ambient_inputs
    (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (p q j : ℕ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth (p + 1) (q + 1) (fun X z => γ.coeff α t X z))
    (hΓper : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X,
      AVenhance.IsZ2Periodic (fun z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth (max D (p + j)) (max D (q + D - j)) Φ)
    (hΦper : ∀ X, AVenhance.IsZ2Periodic (Φ X)) :
    IsBoxSmooth p q (sourceCoeff edge η j t Φ) := by
  have hgood : GoodField D Φ :=
    ⟨hΦ.contDiff_uncurry (Nat.le_max_left _ _) (Nat.le_max_left _ _), hΦper⟩
  have hΓgood : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z) := by
    intro v u d γ hγ α
    exact ⟨(hΓ v u d γ hγ α).contDiff_uncurry (by omega) (by omega),
      hΓper v u d γ hγ α⟩
  rw [sourceCoeff_eq_sourceCoefficientArray edge hD η t Φ hgood hΓgood j]
  exact sourceCoefficientArray_box_reserve edge hD η t Φ p q j hΓ
    (hΦ.mono (Nat.le_max_right _ _) (Nat.le_max_right _ _))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Every genuine Taylor source coefficient is a continuous periodic field during active pulses. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sourceCoeff_good_zero (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : GoodField D Φ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z)) (j : ℕ) :
    GoodField 0 (sourceCoeff edge η j t Φ) := by
  rw [sourceCoeff_eq_sourceCoefficientArray edge hD η t Φ hΦ hΓ j]
  change GoodField 0 (fun X z => ∑ k : Fin 2,
    covariantCoefficientStep η k (sourceFluxCoefficientArray edge η t Φ k) j X z)
  apply GoodField.sum
  intro k _
  have hg (i : ℕ) := sourceFluxCoefficientArray_good edge hD η t Φ hΦ hΓ k i
  have he : covariantCoefficientStep η k (sourceFluxCoefficientArray edge η t Φ k) j =
      fun X z => fastPartial k (sourceFluxCoefficientArray edge η t Φ k j) X z +
        if j = 0 then 0 else Real.sqrt η •
          slowPartial k (sourceFluxCoefficientArray edge η t Φ k (j - 1)) X z := rfl
  rw [he]
  by_cases hj : j = 0
  · simpa only [ite_eq_left hj, add_zero] using (hg j).fastPartial k
  · simpa only [ite_eq_right hj] using
      ((hg j).fastPartial k).add (((hg (j - 1)).slowPartial k).smul (Real.sqrt η))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Removing a slow exponential preserves the literal source-flux rectangular reserve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceFluxComponent_box_reserve (edge : ConstituentEdges D h)
    (η t lam : ℝ) (A : Vec 2 →L[ℝ] ℝ) (k : Fin 2) (p q j : ℕ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p q (γ.coeff α t))
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth (p + j) (q + (D - 1) - j) (fun X z => f X z u))
    (v : ι) : IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      sourceFluxComponentCoefficient edge η t
        (fun Y y => Real.exp ((lam • A) Y) • f Y y) k j v X z) := by
  have hexp := isBoxSmooth_slow_field (p + j) (q + (D - 1) - j)
    (fun Y => Real.exp ((lam • A) Y)) (Real.contDiff_exp.comp (lam • A).contDiff)
  have hΦ (u : ι) : IsBoxSmooth (p + j) (q + (D - 1) - j)
      (fun X z => (Real.exp ((lam • A) X) • f X z) u) := by
    exact isBoxSmooth_bilinear hexp (hf u)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h u →L[ℝ] h u)
  have hb := sourceFluxComponentCoefficient_box_reserve edge η t _ k p q j hΓ hΦ v
  have hinv := isBoxSmooth_slow_field p q (fun Y => Real.exp (-((lam • A) Y)))
    (Real.contDiff_exp.comp ((lam • A).contDiff.neg))
  simpa only [Real.exp_neg] using! isBoxSmooth_bilinear hinv hb
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Centered transverse cell fields have centered scalar profiles. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem transverse_profile_fourier_centered (par : Fin 2) (I : Set ℝ)
    (f : ℝ → Vec 2 → Vec 2 → E) (hf : IsTransverseOn par I f)
    (t : ℝ) (ht : t ∈ I) (X : Vec 2)
    (hc : Continuous (f t X)) (hm : fieldCellMean (f t X) = 0)
    (l : E →L[ℝ] ℝ) :
    unitProfileFourierCoeff (fun x => ((l (f t X (x • basisVec par.rev)) : ℝ) : ℂ)) 0 = 0 := by
  let A := Complex.ofRealCLM.comp l
  have hprof : Continuous (fun x : ℝ => A (f t X (x • basisVec par.rev))) :=
    A.continuous.comp (hc.comp (continuous_id.smul continuous_const))
  rw [unitProfileFourierCoeff_zero_eq_integral]
  change (∫ x in (0 : ℝ)..1, A (f t X (x • basisVec par.rev))) = 0
  rw [← integral_coordinate_eq_intervalIntegral par.rev _ hprof]
  have he : (fun z : Vec 2 => A (f t X (z par.rev • basisVec par.rev))) =
      fun z => A (f t X z) := by
    funext z
    rw [← transverse_profile_representation par I f hf t ht X z]
  rw [he]
  have hi : IntegrableOn (f t X) AVenhance.unitCube := by
    exact (AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell hc).congr_set_ae
      AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.symm
  rw [A.integral_comp_comm hi]
  change A (fieldCellMean (f t X)) = 0
  rw [hm, map_zero]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! A classical periodic weak jet with the same trace represents the actual public cell solution. -/

theorem cellSolution_classical_representative
    (I : Set ℝ) (C : CellCoefficients) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution I C src F D)
    (hI : MeasurableSet I) (hE : ∀ t ∈ I, HasPeriodicOrderedWeakJet (E t))
    (hm : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => E p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (he : ∀ t ∈ I, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue E t) :
    IsCellSolution I C src F E := by
  have hjet : ∀ᵐ t ∂volume.restrict I, ∀ a,
      D t a =ᵐ[volume.restrict AVenhance.unitCube] E t a := by
    filter_upwards [hD.2.1, ae_restrict_mem hI] with t hDt ht
    exact cellPeriodicWeakJet_congr_value (D t) (E t) hDt (hE t ht) (he t ht)
  have hgrad : ∀ᵐ t ∂volume.restrict I,
      cellGradient (D t) =ᵐ[volume.restrict AVenhance.unitCube] cellGradient (E t) := by
    filter_upwards [hjet] with t ht
    have hg := ae_all_iff.mpr (fun j : Fin 2 => ht ⟨⟨1, by decide⟩, fun _ => j⟩)
    filter_upwards [hg] with x hx
    exact PiLp.ext hx
  refine ⟨hD.1, ?_, ?_, hm, ?_, ?_, ?_⟩
  · exact (ae_restrict_mem hI).mono (fun t ht => hE t ht)
  · intro t ht
    exact ⟨(hE t ht).2.1 (valueIndex2 1), (hE t ht).1 (valueIndex2 1)⟩
  · intro t₀ ht₀
    apply (hD.2.2.2.2.1 t₀ ht₀).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply lintegral_congr_ae
    filter_upwards [he t ht, he t₀ ht₀] with x hx hx₀
    rw [hx, hx₀]
  · intro a ha b hb
    have hsub : Icc a b ⊆ I := fun t ht => hD.1.out ha hb ht
    have hg := ae_mono (Measure.restrict_mono hsub le_rfl) hgrad
    have hn : (fun t => cellL2Norm (cellGradient (D t)) ^ 2) =ᵐ[volume.restrict (Icc a b)]
        fun t => cellL2Norm (cellGradient (E t)) ^ 2 := by
      filter_upwards [hg] with t ht
      rw [cellL2Norm, cellL2Norm, eLpNorm_congr_ae ht]
    rw [← lintegral_congr_ae hn]
    exact hD.2.2.2.2.2.1 a ha b hb
  · intro s hs t ht hst ψ
    have hsub : Ioc s t ⊆ I := fun r hr => hD.1.out hs ht ⟨hr.1.le, hr.2⟩
    have hj : ∀ᵐ r ∂volume.restrict (Ioc s t), ∀ a,
        D r a =ᵐ[volume.restrict AVenhance.unitCube] E r a :=
      ae_mono (Measure.restrict_mono hsub le_rfl) hjet
    apply cellWeakIdentity_state_congr_sections C s t _ _ _ _ _ _ _ _ _ _ src F
      (he s hs) (he t ht)
    · exact hj.mono (fun _ hr => hr (valueIndex2 1))
    · exact hj.mono (fun _ hr j => hr ⟨⟨1, by decide⟩, fun _ => j⟩)
    · exact hD.2.2.2.2.2.2 s hs t ht hst ψ

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The genuine paired mean flux separates coefficient and molecular metric differences. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

omit [Fintype ι] in
theorem diagonalMeanFluxCoefficient_paired_difference
    (Q : LiftOperatorData ι h D) (J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) (k : Fin 2)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι)
    (hw : Continuous (fun y => Real.sqrt Q.η * Q.v t y k))
    (hc : Continuous (fun y => Cc 0 (n - 1) m α t X y v u))
    (hi : Continuous (fun y => Ci 0 (n - 1) m α t X y v u)) :
    diagonalMeanFluxCoefficient Q Cc n k m α t X z v u -
      diagonalMeanFluxCoefficient (⟨Q.η, J, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
        Ci n k m α t X z v u =
    weightedLiftCoefficientMean
      (fun d β s Y y i j => Cc 0 (n - 1) d β s Y y i j - Ci 0 (n - 1) d β s Y y i j)
      (fun s y => Real.sqrt Q.η * Q.v s y k) m α t X z v u +
    if n = 2 then metricFluxCoefficient Q.η Q.G k m α t X z v u -
      metricFluxCoefficient Q.η J k m α t X z v u else 0 := by
  unfold diagonalMeanFluxCoefficient
  rw [weightedLiftCoefficientMean_sub _ _ _ m α t X z v u hw hc hi]
  split_ifs <;> abel

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original perturbation premise supplies all slow jets of the clamped diagonal difference. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_clamped_metric_difference_fixed_data
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (p : ℕ) (hp : p ≤ qs) (i : Fin 2) :
    let d := fun t X => Q.G (Set.projIcc a b P.window t) X i i - 1
    (∀ X, Measurable (fun t => d t X)) ∧
    (∀ t, ContDiff ℝ (p : ℕ∞) (d t)) ∧
    (∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (d t) X‖ ≤
      metricParameterBudget p CGI * g * lam ^ r) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact ((P.G_meas X i i).comp
      (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val).sub measurable_const
  · intro t
    exact ((P.G_smooth _ (Set.projIcc a b P.window t).2 i i).sub contDiff_const).of_le
      (by exact_mod_cast hp)
  · intro r hr t X
    have he := setting_metric_difference_entry_scaled_jet_bound P g hg CGI hGI r (hr.trans hp)
      (Set.projIcc a b P.window t) (Set.projIcc a b P.window t).2 X i i
    simp only at he
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by
      rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le) r)
    apply mul_le_mul_of_nonneg_right _ hg
    exact Finset.single_le_sum (fun j _ => le_max_right (CGI j) 0)
      (Finset.mem_range.mpr (by omega))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Actual kernel-source differences have full slow jets with an integrable, scale-graded perturbation bound. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseModeKernel_metric_difference_source_jet_bound
    (p q : ℕ) (hq : q ≤ p) (g : ℝ → Vec 2 → ℝ)
    (hm : ∀ X, Measurable (fun t => g t X)) (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M Md eps lam rate κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hrate : 0 ≤ rate) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hdb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (fun Y => g t Y - 1) X‖ ≤ Md * eps * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : Vec 2 → E) (hf : ContDiff ℝ (p : ℕ∞) f) (S : ℕ → ℝ)
    (hS : ∀ j ≤ p, 0 ≤ S j) (hfB : ∀ j ≤ p, ∀ X, ‖iteratedFDeriv ℝ j f X‖ ≤ S j * lam ^ j)
    (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y =>
      (transverseModeKernel rate (fun t => g t Y) a b - transverseModeKernel rate (fun _ => 1) a b) • f Y) X‖ ≤
      ((2 : ℝ) ^ q * metricDifferenceKernelSourceConstant p q M Md κ S) * eps *
        Real.exp (-(rate * κ / 4) * (b - a)) * lam ^ q := by
  let d := fun t Y => g t Y - 1
  have hdm : ∀ X, Measurable (fun t => d t X) := fun X => (hm X).sub measurable_const
  have hds : ∀ t, ContDiff ℝ (p : ℕ∞) (d t) := fun t => (hs t).sub contDiff_const
  have hdi := transverseMetricDifferenceExponent_contDiff p d hdm hds
    (fun j => Md * eps * lam ^ j) hdb rate a b
  let F := fun θ Y => transverseModeKernel rate
    (fun t => scalarMetricInterpolation (clampedMetricInterpolationParameter θ) g t Y) a b •
      (transverseMetricDifferenceExponent rate d a b Y • f Y)
  let C := fun j => metricDifferenceKernelSourceConstant p j M Md κ S * eps *
    Real.exp (-(rate * κ / 4) * (b - a)) * lam ^ j
  have hi (Y : Vec 2) : IntervalIntegrable (fun t => g t Y) volume a b := by
    have hi : IntegrableOn (fun t => g t Y) (Icc a b) := by
      apply (integrable_const M).mono' (hm Y).aestronglyMeasurable
      exact ae_of_all _ (fun t => by simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hb 0 (by omega) t Y)
    have hi' : IntegrableOn (fun t => g t Y) (uIcc a b) := by simpa only [uIcc_of_le hab] using hi
    exact hi'.intervalIntegrable
  have hFm (Y : Vec 2) : Measurable (fun θ => F θ Y) := by
    have hc := transverseModeKernel_clamped_interpolation_continuous rate (fun t => g t Y) a b (hi Y)
    exact (hc.smul continuous_const).measurable
  have hFs (θ : ℝ) : ContDiff ℝ (p : ℕ∞) (F θ) := by
    have hθ := clampedMetricInterpolationParameter_mem θ
    have hg := transverseModeKernel_parameter_contDiff p
      (scalarMetricInterpolation (clampedMetricInterpolationParameter θ) g)
      (fun Y => measurable_const.add ((hm Y).const_mul _))
      (scalarMetricInterpolation_contDiff _ p g hs)
      (fun j => (1 + M) * lam ^ j)
      (scalarMetricInterpolation_scaled_jet_le _ hθ p g hs M lam hM hlam hb) rate a b
    exact hg.smul (hdi.smul hf)
  have hFb : ∀ j ≤ p, ∀ θ Y, ‖iteratedFDeriv ℝ j (F θ) Y‖ ≤ C j := by
    intro j hj θ Y
    exact metricDifferenceKernelSource_decay p j hj (clampedMetricInterpolationParameter θ)
      (clampedMetricInterpolationParameter_mem θ) g d hm hdm hs hds M Md eps lam rate κ a b
      hM hMd heps hlam hrate hκ hκ1 hab hb hdb hgl f hf S hS hfB Y
  have he := transverseModeKernel_difference_source_eq_integral rate g a b hi f
  rw [he]
  have hh := parameter_intervalIntegral_iteratedFDeriv_norm_le p F hFm hFs C hFb q hq X 0 1 zero_le_one
  apply hh.trans_eq
  dsimp [C]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The full slow Fréchet jet of the inverse has the same reciprocal-rate gain. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseModeResponse_iteratedFDeriv_parameter_norm_le (n : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 < rate) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (f t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ n, 0 ≤ S j)
    (hfB : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j)
    (q : ℕ) (hq : q ≤ n) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q
      (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b) X‖ ≤
      (2 : ℝ) ^ q * (duhamelSlowJetMajorant n M κ S q * lam ^ q * (2 / (rate * κ))) := by
  have hc : ContDiff ℝ (q : ℕ∞)
      (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b) :=
    (transverseModeResponse_parameter_contDiff n g hm hs M lam rate κ a b
      hM hlam hrate.le hκ hab hb hgl f hmf hf S hS hfB).of_le (by exact_mod_cast hq)
  apply (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words hc X).trans
  calc
    _ ≤ ∑ α : DerivativeWord2 q,
        duhamelSlowJetMajorant n M κ S q * lam ^ q * (2 / (rate * κ)) :=
      Finset.sum_le_sum (fun α _ => transverseModeResponse_orderedDerivative_parameter_norm_le
        n g hm hs M lam rate κ a b hM hlam hrate hκ hab hb hgl f hmf hf S hS hfB q hq α X)
    _ = _ := by simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered composition of differential operators is synthesized from differentiated left coefficients. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def leftTermComposition (a : LeftTerm F G) (l : List (LeftTerm E F)) : List (LeftTerm E G) :=
  (leftTermsSlowWord a.word l).map (fun c => c.fieldPostcompose a.coeff)

theorem leftTermComposition_order (a : LeftTerm F G) (l : List (LeftTerm E F))
    (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n) (c : LeftTerm E G)
    (hc : c ∈ leftTermComposition a l) : c.order ≤ n + a.order := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact leftTermsSlowWord_order a.word l n hl d hd

theorem leftTermComposition_apply (a : LeftTerm F G) (l : List (LeftTerm E F))
    (hl : ∀ c ∈ l, IsBoxSmooth a.order 0 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (leftTermComposition a l) f X z =
      a.coeff X z (orderedDerivative a.word (fun Y => leftTermsApply l f Y z) X) := by
  rw [leftTermComposition, leftTermsApply_map_fieldPostcompose]
  exact congrArg (a.coeff X z) (leftTermsSlowWord_apply a.word l hl f hf X z)
end

/-! Metric divergence of a slow differential action is again a finite left-term action. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftTermsMetricSlowDerivative (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2)
    (l : List (LeftTerm E F)) : List (LeftTerm E F) :=
  leftTermsSlowPartial i ((leftTermsSlowPartial j l).map
    (fun c => c.fieldSmul (fun X _ => G X i j)))

theorem leftTermsMetricSlowDerivative_order (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2)
    (l : List (LeftTerm E F)) (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n)
    (c : LeftTerm E F) (hc : c ∈ leftTermsMetricSlowDerivative G i j l) : c.order ≤ n + 2 := by
  have hinner (d : LeftTerm E F) (hd : d ∈ (leftTermsSlowPartial j l).map
      (fun c => c.fieldSmul (fun X _ => G X i j))) : d.order ≤ n + 1 := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact leftTermsSlowPartial_order j l n hl e he
  have h := leftTermsSlowPartial_order i _ (n + 1) hinner c hc
  simpa only [Nat.add_assoc] using h

theorem leftTermsMetricSlowDerivative_apply (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2)
    (l : List (LeftTerm E F)) (hG : ContDiff ℝ 1 (fun X => G X i j))
    (hl : ∀ c ∈ l, IsBoxSmooth 2 0 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    leftTermsApply (leftTermsMetricSlowDerivative G i j l) f =
      slowPartial i (fun X z => G X i j • slowPartial j (leftTermsApply l f) X z) := by
  have hmult (d : LeftTerm E F) (hd : d ∈ (leftTermsSlowPartial j l).map
      (fun c => c.fieldSmul (fun X _ => G X i j))) : IsBoxSmooth 1 0 d.coeff := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact e.fieldSmul_box _ 1 0 (leftTermsSlowPartial_box j l 1 0 hl e he)
      (isBoxSmooth_slow_field 1 0 _ hG)
  rw [leftTermsMetricSlowDerivative, leftTermsSlowPartial_apply i _ hmult f hf,
    leftTermsApply_map_fieldSmul, leftTermsSlowPartial_apply j l
      (fun c hc => (hl c hc).mono (by omega) le_rfl) f hf]
end

/-! The literal outer source coefficient can be evaluated componentwise under its exact reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceComponentCoefficientArray (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (j : ℕ) (v : ι) : Vec 2 → Vec 2 → h v :=
  fun X z => ∑ k : Fin 2, covariantCoefficientStep η k
    (fun i => sourceFluxComponentCoefficient edge η t Φ k i v) j X z

theorem sourceCoefficientArray_component_eq (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (j : ℕ) (hj : j ≤ D)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth 1 1 (γ.coeff α t))
    (hΦ : IsBoxSmooth j (D - j) Φ) (v : ι) :
    (fun X z => sourceCoefficientArray edge η t Φ j X z v) =
      sourceComponentCoefficientArray edge η t Φ j v := by
  let L : (∀ i, h i) →L[ℝ] h v := ContinuousLinearMap.proj v
  funext X z
  change (∑ k : Fin 2, covariantCoefficientStep η k
    (sourceFluxCoefficientArray edge η t Φ k) j X z) v = _
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hfast : IsBoxSmooth 0 1 (sourceFluxCoefficientArray edge η t Φ k j) :=
    sourceFluxCoefficientArray_box_reserve edge η t Φ k 0 1 j
      (fun v u d γ hm α => (hΓ v u d γ hm α).mono (by omega) le_rfl)
      (hΦ.mono (by omega) (by omega))
  have hslow : j ≠ 0 → IsBoxSmooth 1 0
      (sourceFluxCoefficientArray edge η t Φ k (j - 1)) := by
    intro hne
    apply sourceFluxCoefficientArray_box_reserve
    · intro v u d γ hm α
      exact (hΓ v u d γ hm α).mono le_rfl (by omega)
    · exact hΦ.mono (by omega) (by omega)
  have he i (hi : i = j ∨ i = j - 1) : (fun Y y => L (sourceFluxCoefficientArray edge η t Φ k i Y y)) =
      sourceFluxComponentCoefficient edge η t Φ k i v := by
    apply sourceFluxCoefficientArray_component_eq
    rcases hi with rfl | rfl
    · exact hΦ.mono le_rfl (by omega)
    · exact hΦ.mono (by omega) (by omega)
  have hh := covariantCoefficientStep_postcomposition η k
    (sourceFluxCoefficientArray edge η t Φ k) j L hfast hslow X z
  simpa only [covariantCoefficientStep, L, ContinuousLinearMap.proj_apply, ← he j (Or.inl rfl),
    ← he (j - 1) (Or.inr rfl)] using! hh.symm
end

/-! The mixed metric divergence has its literal two finite differential actions. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftTermsMetricCrossDerivative (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2)
    (l : List (LeftTerm E F)) : List (LeftTerm E F) :=
  ((leftTermsFastPartial i (leftTermsSlowPartial j l)).map
    (fun c => c.fieldSmul (fun X _ => G X i j))) ++
  leftTermsSlowPartial i ((leftTermsFastPartial j l).map
    (fun c => c.fieldSmul (fun X _ => G X i j)))

theorem leftTermsMetricCrossDerivative_order (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2)
    (l : List (LeftTerm E F)) (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n)
    (c : LeftTerm E F) (hc : c ∈ leftTermsMetricCrossDerivative G i j l) : c.order ≤ n + 1 := by
  rcases List.mem_append.mp hc with hfirst | hsecond
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfirst
    exact leftTermsFastPartial_order i _ (n + 1)
      (leftTermsSlowPartial_order j l n hl) d hd
  · apply leftTermsSlowPartial_order i _ n ?_ c hsecond
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact leftTermsFastPartial_order j l n hl e he

theorem leftTermsMetricCrossDerivative_apply (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2)
    (l : List (LeftTerm E F)) (hG : ContDiff ℝ 1 (fun X => G X i j))
    (hl : ∀ c ∈ l, IsBoxSmooth 1 1 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    leftTermsApply (leftTermsMetricCrossDerivative G i j l) f = fun X z =>
      G X i j • fastPartial i (slowPartial j (leftTermsApply l f)) X z +
        slowPartial i (fun Y y => G Y i j • fastPartial j (leftTermsApply l f) Y y) X z := by
  have hslow (d : LeftTerm E F) (hd : d ∈ leftTermsSlowPartial j l) : IsBoxSmooth 0 1 d.coeff :=
    leftTermsSlowPartial_box j l 0 1 hl d hd
  have hmult (d : LeftTerm E F) (hd : d ∈ (leftTermsFastPartial j l).map
      (fun c => c.fieldSmul (fun X _ => G X i j))) : IsBoxSmooth 1 0 d.coeff := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact e.fieldSmul_box _ 1 0 (leftTermsFastPartial_box j l 1 0 hl e he)
      (isBoxSmooth_slow_field 1 0 _ hG)
  rw [leftTermsMetricCrossDerivative, leftTermsApply_append, leftTermsApply_map_fieldSmul,
    leftTermsFastPartial_apply i _ hslow f hf,
    leftTermsSlowPartial_apply j l (fun c hc => (hl c hc).mono le_rfl (by omega)) f hf,
    leftTermsSlowPartial_apply i _ hmult f hf, leftTermsApply_map_fieldSmul,
    leftTermsFastPartial_apply j l (fun c hc => (hl c hc).mono (by omega) le_rfl) f hf]
end

/-! The literal second cross operator has differential order two on finite left terms. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def cellB2LeftTerms (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ)
    (l : List (LeftTerm E F)) : List (LeftTerm E F) :=
  (Finset.univ.toList : List (Fin 2)).flatMap fun i =>
    (Finset.univ.toList : List (Fin 2)).flatMap fun j =>
      (leftTermsMetricSlowDerivative G i j l).map (fun c => c.smul (-η))

theorem cellB2LeftTerms_order (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ)
    (l : List (LeftTerm E F)) (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n)
    (c : LeftTerm E F) (hc : c ∈ cellB2LeftTerms η G l) : c.order ≤ n + 2 := by
  obtain ⟨i, _, j, _, d, hd, rfl⟩ := by
    simpa only [cellB2LeftTerms, List.mem_flatMap, List.mem_map] using hc
  exact leftTermsMetricSlowDerivative_order G i j l n hl d hd

theorem cellB2LeftTerms_apply (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (l : List (LeftTerm E F))
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => G t X i j))
    (hl : ∀ c ∈ l, IsBoxSmooth 2 0 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (cellB2LeftTerms η (G t) l) f X z = cellB2 η G t (leftTermsApply l f) X z := by
  unfold cellB2LeftTerms
  rw [leftTermsApply_finset_flatMap]
  simp_rw [leftTermsApply_finset_flatMap, leftTermsApply_map_smul,
    leftTermsMetricSlowDerivative_apply (G t) _ _ l (hG _ _) hl f hf]
  simp only [cellB2, Finset.smul_sum, neg_smul, Finset.sum_neg_distrib]
end

/-! Ordered composition of two finite differential actions. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def leftTermsComposition (a : List (LeftTerm F G)) (l : List (LeftTerm E F)) :
    List (LeftTerm E G) := a.flatMap (fun c => leftTermComposition c l)

theorem leftTermsComposition_order (a : List (LeftTerm F G)) (l : List (LeftTerm E F))
    (m n : ℕ) (ha : ∀ c ∈ a, c.order ≤ m) (hl : ∀ c ∈ l, c.order ≤ n)
    (c : LeftTerm E G) (hc : c ∈ leftTermsComposition a l) : c.order ≤ m + n := by
  obtain ⟨d, hd, hdc⟩ := List.mem_flatMap.mp hc
  have := leftTermComposition_order d l n hl c hdc
  have := ha d hd
  omega

theorem leftTermsComposition_apply (a : List (LeftTerm F G)) (l : List (LeftTerm E F))
    (hl : ∀ c ∈ a, ∀ d ∈ l, IsBoxSmooth c.order 0 d.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (leftTermsComposition a l) f X z =
      leftTermsApply a (fun Y => leftTermsApply l f Y z) X z := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    change leftTermsApply (leftTermComposition c l ++ leftTermsComposition a l) f X z = _
    rw [leftTermsApply_append]
    dsimp only
    rw [leftTermComposition_apply c l
      (fun d hd => hl c (by simp) d hd) f hf,
      ih (fun d hd e he => hl d (by simp only [List.mem_cons]; exact Or.inr hd) e he)]
    rfl
end

/-! Finite test calibration of an arbitrary symmetric lift array. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def calibratedLiftCoefficientEntry (c : LiftCoeff ι h) (n m : ℕ)
    (α : DerivativeWord2 m) (lam : ℝ) (u v : ι) (ξ : h u) : ℝ → Vec 2 → Vec 2 → h v :=
  fun t X z => ∑ j : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α lam j •
    normalizedLiftTestField c n
      (lam • ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) u v ξ t X z

theorem calibratedLiftCoefficientEntry_eq (c : LiftCoeff ι h) (n m : ℕ) (hm : m ≤ n)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (u v : ι) (ξ : h u) (t : ℝ) (X z : Vec 2) :
    calibratedLiftCoefficientEntry c n m α lam u v ξ t X z = c m α t X z v u ξ :=
  liftCalibration_synthesis n m hm c lam hlam hc α t X z v u ξ

theorem calibratedLiftCoefficientEntry_box (c : LiftCoeff ι h) (n m p q : ℕ)
    (α : DerivativeWord2 m) (lam : ℝ) (u v : ι) (ξ : h u) (t : ℝ)
    (hbox : ∀ A : Vec 2 →L[ℝ] ℝ,
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t)) :
    IsBoxSmooth p q (calibratedLiftCoefficientEntry c n m α lam u v ξ t) :=
  IsBoxSmooth.sum Finset.univ (fun j _ => (hbox ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))).const_smul _)
end

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The first cross operator is a finite differential action of order one on left coefficients. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def cellB1LeftTerms (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (v : Vec 2 → Vec 2)
    (l : List (LeftTerm E F)) : List (LeftTerm E F) :=
  ((Finset.univ.toList : List (Fin 2)).flatMap fun k =>
    (leftTermsSlowPartial k l).map (fun c => c.fieldSmul (fun _ z => Real.sqrt η * v z k))) ++
  (Finset.univ.toList : List (Fin 2)).flatMap fun i =>
    (Finset.univ.toList : List (Fin 2)).flatMap fun j =>
      (leftTermsMetricCrossDerivative G i j l).map (fun c => c.smul (-Real.sqrt η))

theorem cellB1LeftTerms_order (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (v : Vec 2 → Vec 2)
    (l : List (LeftTerm E F)) (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n)
    (c : LeftTerm E F) (hc : c ∈ cellB1LeftTerms η G v l) : c.order ≤ n + 1 := by
  rcases List.mem_append.mp hc with hfirst | hsecond
  · obtain ⟨k, _, d, hd, rfl⟩ := by
      simpa only [List.mem_flatMap, List.mem_map] using hfirst
    exact leftTermsSlowPartial_order k l n hl d hd
  · obtain ⟨i, _, j, _, d, hd, rfl⟩ := by
      simpa only [List.mem_flatMap, List.mem_map] using hsecond
    exact leftTermsMetricCrossDerivative_order G i j l n hl d hd

theorem cellB1LeftTerms_apply (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (l : List (LeftTerm E F))
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => G t X i j))
    (hl : ∀ c ∈ l, IsBoxSmooth 1 1 c.coeff)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (cellB1LeftTerms η (G t) (v t) l) f X z =
      cellB1 η G v t (leftTermsApply l f) X z := by
  unfold cellB1LeftTerms
  rw [leftTermsApply_append]
  dsimp only
  rw [leftTermsApply_finset_flatMap, leftTermsApply_finset_flatMap]
  simp_rw [leftTermsApply_finset_flatMap, leftTermsApply_map_fieldSmul,
    leftTermsSlowPartial_apply _ l (fun c hc => (hl c hc).mono le_rfl (by omega)) f hf,
    leftTermsApply_map_smul, leftTermsMetricCrossDerivative_apply (G t) _ _ l (hG _ _) hl f hf]
  simp only [cellB1, Finset.smul_sum, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

end AVRegularity.CycleComparison.Lift
end
end
