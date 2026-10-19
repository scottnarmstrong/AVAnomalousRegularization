-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.LiftMeanEntrywise

/-! The mean letters are measurable in time on the window for each slow position.
The drift part is a cell mean
of measurable, cell-continuous fields; the source part is recovered from finitely many
exponential tests of its literal action, which is a cell mean of measurable source-flux
coefficients. -/

section
theorem measurable_Icc_of_projIcc {F : Type*} [MeasurableSpace F] {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → F) (hg : Measurable (fun s => g (Set.projIcc a b hab s))) :
    Measurable (fun t : Set.Icc a b => g t) := by
  have he : (fun t : Set.Icc a b => g t) =
      (fun s => g (Set.projIcc a b hab s)) ∘ Subtype.val := by
    funext t
    simp only [Function.comp_apply, Set.projIcc_val]
  rw [he]
  exact hg.comp measurable_subtype_coe

section Metric
variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem metricFluxCoefficient_parameter_measurable (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (τ : ℝ → ℝ)
    (hG : ∀ X i j, Measurable (fun s => G (τ s) X i j)) (k : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (X z : Vec 2) (v u : ι) :
    Measurable (fun s => metricFluxCoefficient (h := h) η G k m α (τ s) X z v u) := by
  match m, α with
  | 0, α =>
    show Measurable (fun _ : ℝ => (0 : h u →L[ℝ] h v))
    exact measurable_const
  | 1, α =>
    show Measurable (fun s => (-η * G (τ s) X k (α 0)) • blockIdentityEntry h v u)
    exact (measurable_const.mul (hG X k (α 0))).smul_const _
  | m + 2, α =>
    show Measurable (fun _ : ℝ => (0 : h u →L[ℝ] h v))
    exact measurable_const

end Metric

section Coefficient
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The averaged source-flux coefficients of the positive letter, with their left-term list
read at the current time. -/
def sourceFluxMeanLetterCoeff (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (k₀ : Fin 2) : LiftCoeff ι h :=
  fun m α t X z v u => sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t X z v u

theorem sourceFluxMeanLetterCoeff_perm (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (k₀ : Fin 2) (m : ℕ) (β : DerivativeWord2 m)
    (σ : Equiv.Perm (Fin m)) :
    sourceFluxMeanLetterCoeff Q Cc hh n k₀ m (β ∘ σ) =
      sourceFluxMeanLetterCoeff Q Cc hh n k₀ m β := by
  funext t X z v u
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    (sourceFluxMeanCoefficient_perm Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m β σ) t) X) z) v) u

/-- The literal action reads the letter coefficients at the current time only. -/
theorem liftApply_sourceFluxMeanLetterCoeff (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (k₀ : Fin 2) (f : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply (n - 1) (sourceFluxMeanLetterCoeff Q Cc hh n k₀) f t X z v =
      liftApply (n - 1) (sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀)
        f t X z v := by
  simp only [liftApply, sourceFluxMeanLetterCoeff]

end Coefficient

section Setting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_weightedDrift_clamped_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hh : ℕ) (hhh : hh ≤ H) (q : ℕ)
    (hqR : q ≤ N + D) (k₀ : Fin 2) (m : ℕ) (hm : m ≤ q) (α : DerivativeWord2 m)
    (X z : Vec 2) (v u : ι) :
    Measurable (fun s => weightedLiftCoefficientMean (Cc hh q)
      (fun t y => Real.sqrt Q.η * Q.v t y k₀) m α (Set.projIcc a b P.window s) X z v u) := by
  have hproj : Measurable (fun s : ℝ => (Set.projIcc a b P.window s : ℝ)) :=
    (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhh q hqR
  change Measurable (fun s => fieldCellMean (fun y =>
    (Real.sqrt Q.η * Q.v (Set.projIcc a b P.window s) y k₀) •
      Cc hh q m α (Set.projIcc a b P.window s) X y v u))
  apply fieldCellMean_parameter_measurable
  · intro y
    exact (measurable_const.mul (((measurable_pi_apply k₀).comp (P.v_meas y)).comp hproj)).smul
      (measurable_of_all_real_duals _ (fun l => state.coefficient.measurable m hm α v u l X y))
  · intro s
    exact (setting_normalized_drift_contDiff_one P _ (Set.projIcc a b P.window s).2
      k₀).continuous.smul
      ((hseq.2.2.2.2.2.1 hh hhh q m α v u _ (Set.projIcc a b P.window s).2).1.1 X).continuous

include P in
theorem setting_diagonalMeanFlux_clamped_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (X : Vec 2) (v u : ι) :
    Measurable (fun s =>
      diagonalMeanFluxCoefficient Q Cc n k₀ m α (Set.projIcc a b P.window s) X 0 v u) := by
  have hproj : Measurable (fun s : ℝ => (Set.projIcc a b P.window s : ℝ)) :=
    (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val
  have hw := setting_weightedDrift_clamped_measurable P sX sZ hsZ Cc hseq P₀ hreserve
    0 (Nat.zero_le H) (n - 1) (by omega) k₀ m hm α X 0 v u
  by_cases hn2 : n = 2
  · simp only [diagonalMeanFluxCoefficient, ite_eq_left hn2]
    exact hw.add (metricFluxCoefficient_parameter_measurable Q.η Q.G
      (fun s => (Set.projIcc a b P.window s : ℝ)) (fun X i j => (P.G_meas X i j).comp hproj)
      k₀ m α X 0 v u)
  · simp only [diagonalMeanFluxCoefficient, ite_eq_right hn2, add_zero]
    exact hw

include P in
theorem setting_sourceFluxMeanLetterCoeff_test_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u) (X z : Vec 2) (v : ι) :
    Measurable (fun s => liftApply (n - 1) (sourceFluxMeanLetterCoeff Q Cc hh n k₀)
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b P.window s) X z v) := by
  have hproj : Measurable (fun s : ℝ => (Set.projIcc a b P.window s : ℝ)) :=
    (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun Y => Real.exp ((lam • A) Y) • Pi.single u ξ) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const
  have hcbox (τ : ℝ) (hτ : τ ∈ Set.Icc a b) : ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j) (fun X z => Cc (hh - 1) (n - 1 - j) m α τ X z u u') := by
    intro j hj m hm α u u'
    have hjn : j ≤ n - 1 := le_trans hj (min_le_right _ _)
    have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
      P₀ hreserve (hh - 1) (by omega) (n - 1 - j) (by omega)
    have hres := ambient_flux_predecessor_reserve P₀ (max k (L + 2)) D H (N + D)
      hh n j hhpos hhh hn hnR hjn
    exact (state.coefficient.box m hm α u u' τ hτ).mono
      (show j ≤ ambientDegreeSlowReserve P₀ (N + D) (n - 1 - j) by omega) hres.2
  have hΓbox (τ : ℝ) (hτ : τ ∈ Set.Icc a b) : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 0 0 (fun X z => γ.coeff α τ X z k₀) := by
    intro v u d γ hγ α
    exact ((P.coeff_smooth v u d γ hγ α τ hτ).mono (Nat.zero_le _) (Nat.zero_le _)).clm_comp
      (ContinuousLinearMap.proj k₀ : Vec 2 →L[ℝ] ℝ)
  have he : (fun s => liftApply (n - 1) (sourceFluxMeanLetterCoeff Q Cc hh n k₀)
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b P.window s) X z v) =
      fun s => fieldCellMean (fun y => ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        sourceFluxComponentCoefficient Q.edge Q.η (Set.projIcc a b P.window s)
          (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
            (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b P.window s))
          k₀ j v X y) := by
    funext s
    rw [liftApply_sourceFluxMeanLetterCoeff]
    exact sourceFluxMeanCoefficient_apply Q.edge Q.η _ (n - 1) (Cc (hh - 1)) k₀
      (hcbox _ (Set.projIcc a b P.window s).2) (hΓbox _ (Set.projIcc a b P.window s).2) _ hf
      X z v
  rw [he]
  apply fieldCellMean_parameter_measurable
  · intro y
    apply Finset.measurable_sum
    intro j hj
    have hjn : j ≤ n - 1 := by have hr := Finset.mem_range.mp hj; omega
    have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
      P₀ hreserve (hh - 1) (by omega) (n - 1 - j) (by omega)
    have hres := ambient_flux_predecessor_reserve P₀ (max k (L + 2)) D H (N + D)
      hh n j hhpos hhh hn hnR hjn
    exact sourceFluxComponentCoefficient_parameter_measurable Q.edge Q.η
      (fun s => (Set.projIcc a b P.window s : ℝ))
      (fun s => liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b P.window s)) j
      (fun X' z' w => (measurable_pi_apply w).comp
        (state.coefficient.raw_test_measurable A u ξ X' z'))
      (fun s w => ((state.coefficient.raw_test_box A u ξ _
        (Set.projIcc a b P.window s).2).clm_comp (ContinuousLinearMap.proj w)).mono
          (by omega) (by omega))
      (fun v' u' d γ hγ α X' z' => (P.coeff_meas v' u' d γ hγ α X' z').comp hproj) k₀ v X y
  · intro s
    apply continuous_finsetSum
    intro j hj
    have hjn : j ≤ n - 1 := by have hr := Finset.mem_range.mp hj; omega
    have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
      P₀ hreserve (hh - 1) (by omega) (n - 1 - j) (by omega)
    have hres := ambient_flux_predecessor_reserve P₀ (max k (L + 2)) D H (N + D)
      hh n j hhpos hhh hn hnR hjn
    have hb := sourceFluxComponentCoefficient_box_reserve Q.edge Q.η
      (Set.projIcc a b P.window s : ℝ)
      (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b P.window s))
      k₀ 0 0 j
      (fun v' u' d γ hγ α => (P.coeff_smooth v' u' d γ hγ α _
        (Set.projIcc a b P.window s).2).mono (Nat.zero_le _) (Nat.zero_le _))
      (fun w => ((state.coefficient.raw_test_box A u ξ _
        (Set.projIcc a b P.window s).2).clm_comp (ContinuousLinearMap.proj w)).mono
          (by omega) (by omega)) v
    exact (hb.1 X).continuous

include P in
theorem setting_sourceFluxMeanLetterCoeff_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (X : Vec 2) (v u : ι) :
    Measurable (fun s =>
      sourceFluxMeanLetterCoeff Q Cc hh n k₀ m α (Set.projIcc a b P.window s) X 0 v u) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  apply measurable_of_all_real_duals
  intro l
  apply liftCoefficient_dual_measurable_of_finite_tests (n - 1) m hm
    (sourceFluxMeanLetterCoeff Q Cc hh n k₀) lam hlam.ne'
    (sourceFluxMeanLetterCoeff_perm Q Cc hh n k₀ m) α a b P.window X 0 v u l
  intro ξ l' j s
  have he : (s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ)) =
      lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) := smul_comm _ _ _
  simp only [he]
  exact l'.continuous.measurable.comp
    ((setting_sourceFluxMeanLetterCoeff_test_measurable P sX sZ hsZ Cc hseq P₀ hreserve
      hh hhpos hhh n hn hnR k₀ ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u ξ X 0
      v).const_smul _)

include P in
theorem setting_positiveMeanFlux_clamped_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (X : Vec 2) (v u : ι) :
    Measurable (fun s =>
      positiveMeanFluxCoefficient Q Cc hh n k₀ m α (Set.projIcc a b P.window s) X 0 v u) := by
  have hw := setting_weightedDrift_clamped_measurable P sX sZ hsZ Cc hseq P₀ hreserve
    hh hhh (n - 1) (by omega) k₀ m hm α X 0 v u
  have hs := setting_sourceFluxMeanLetterCoeff_measurable P sX sZ hsZ Cc hseq P₀ hreserve
    hh hhpos hhh n hn hnR k₀ m hm α X v u
  exact hw.sub (hs.const_smul (Real.sqrt Q.η))

include P in
/-- Clause (c) for the positive letter. -/
theorem setting_positiveMeanLetter_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2) :
    Measurable (fun t : Set.Icc a b => positiveMeanLetter Q Cc hh n d α t X k₀ v u) := by
  refine measurable_Icc_of_projIcc P.window
    (fun τ => positiveMeanLetter Q Cc hh n d α τ X k₀ v u) ?_
  by_cases hd : 2 ≤ d ∧ d ≤ n
  · simp only [positiveMeanLetter, truncatedMeanCoefficient, ite_eq_left hd]
    exact setting_positiveMeanFlux_clamped_measurable P sX sZ hsZ Cc hseq P₀ hreserve
      hh hhpos hhh n hn hnR k₀ (d - 1) (by omega) α X v u
  · simp only [positiveMeanLetter, truncatedMeanCoefficient, ite_eq_right hd]
    exact measurable_const

include P in
/-- Clause (c) for the source-degree-zero letter. -/
theorem setting_diagonalMeanLetter_measurable (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2) :
    Measurable (fun t : Set.Icc a b => diagonalMeanLetter Q Cc n d α t X k₀ v u) := by
  refine measurable_Icc_of_projIcc P.window
    (fun τ => diagonalMeanLetter Q Cc n d α τ X k₀ v u) ?_
  by_cases hd : 2 ≤ d ∧ d ≤ n
  · simp only [diagonalMeanLetter, truncatedMeanCoefficient, ite_eq_left hd]
    exact setting_diagonalMeanFlux_clamped_measurable P sX sZ hsZ Cc hseq P₀ hreserve
      n hn hnR k₀ (d - 1) (by omega) α X v u
  · simp only [diagonalMeanLetter, truncatedMeanCoefficient, ite_eq_right hd]
    exact measurable_const

end Setting
end

/-! The source-degree-zero mean letter is scalar diagonal, `L_n^{(0)} = M_n I`:
its drift part averages the scalar lifts `C_{n-1}^{(0)} = T I`,
and its molecular part is the scalar metric times the identity. -/

section
section Metric
variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem metricFluxCoefficient_scalar (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) :
    ∃ s : ℝ, ∀ v u : ι,
      metricFluxCoefficient (h := h) η G k m α t X z v u = s • blockIdentityEntry h v u := by
  match m, α with
  | 0, α => exact ⟨0, fun v u => by rw [metricFluxCoefficient_zero, zero_smul]⟩
  | 1, α => exact ⟨-η * G t X k (α 0), fun v u => metricFluxCoefficient_one η G k α t X z v u⟩
  | m + 2, α => exact ⟨0, fun v u => by rw [zero_smul]; rfl⟩

end Metric

section Weighted
variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

theorem weightedLiftCoefficientMean_scalar (c : LiftCoeff ι h) (w : ℝ → Vec 2 → ℝ) (m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2)
    (hc : ∀ y, ∃ s : ℝ, ∀ v u, c m α t X y v u = s • blockIdentityEntry h v u) :
    ∃ s : ℝ, ∀ v u,
      weightedLiftCoefficientMean c w m α t X z v u = s • blockIdentityEntry h v u := by
  choose sf hsf using hc
  refine ⟨fieldCellMean (fun y => w t y * sf y), fun v u => ?_⟩
  have he : (fun y => w t y • c m α t X y v u) =
      fun y => (w t y * sf y) • blockIdentityEntry h v u := by
    funext y
    rw [hsf y v u, smul_smul]
  change fieldCellMean (fun y => w t y • c m α t X y v u) = _
  rw [he]
  exact integral_smul_const _ _

end Weighted

section Setting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_diagonalMeanLetter_scalar (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    ∃ s : ℝ, ∀ v u,
      diagonalMeanLetter Q Cc n d α t X k₀ v u = s • blockIdentityEntry h v u := by
  obtain ⟨s₁, hs₁⟩ := weightedLiftCoefficientMean_scalar (Cc 0 (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k₀) (d - 1) α t X 0
    (fun y => setting_gradeZero_scalar P sX sZ hsZ Cc hseq (n - 1) (d - 1) α t ht X y)
  obtain ⟨s₂, hs₂⟩ := metricFluxCoefficient_scalar (ι := ι) (h := h) Q.η Q.G k₀ (d - 1) α t X 0
  refine ⟨s₁ + if n = 2 then s₂ else 0, fun v u => ?_⟩
  rw [show diagonalMeanLetter Q Cc n d α t X k₀ v u =
      diagonalMeanFluxCoefficient Q Cc n k₀ (d - 1) α t X 0 v u from
    truncatedMeanCoefficient_eq n d hd hdn _ α t X k₀ v u]
  change weightedLiftCoefficientMean (Cc 0 (n - 1)) (fun t z => Real.sqrt Q.η * Q.v t z k₀)
      (d - 1) α t X 0 v u +
    (if n = 2 then metricFluxCoefficient Q.η Q.G k₀ (d - 1) α t X 0 v u else 0) = _
  by_cases hn2 : n = 2
  · rw [ite_eq_left hn2, ite_eq_left hn2, hs₁ v u, hs₂ v u, add_smul]
  · rw [ite_eq_right hn2, ite_eq_right hn2, hs₁ v u, add_zero, add_zero]

include P in
/-- Clause (f): the source-degree-zero letter is a scalar multiple of the identity. -/
theorem setting_diagonalMeanLetter_scalar_diagonal (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (n : ℕ) :
    ∃ Ls : (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ,
      ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2),
        ∀ t ∈ Set.Icc a b, ∀ X,
          (∀ v, diagonalMeanLetter Q Cc n d α t X k₀ v v =
            Ls d α t X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
          (∀ v u, v ≠ u → diagonalMeanLetter Q Cc n d α t X k₀ v u = 0) := by
  have hex : ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (t : ℝ) (X : Vec 2) (k₀ : Fin 2),
      ∃ s : ℝ, 2 ≤ d → d ≤ n → t ∈ Set.Icc a b → ∀ v u,
        diagonalMeanLetter Q Cc n d α t X k₀ v u = s • blockIdentityEntry h v u := by
    intro d α t X k₀
    by_cases hc : 2 ≤ d ∧ d ≤ n ∧ t ∈ Set.Icc a b
    · obtain ⟨s, hs⟩ := setting_diagonalMeanLetter_scalar P sX sZ hsZ Cc hseq n d hc.1 hc.2.1
        α k₀ t hc.2.2 X
      exact ⟨s, fun _ _ _ => hs⟩
    · exact ⟨0, fun h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ hc⟩
  choose Ls hLs using hex
  refine ⟨Ls, fun d hd hdn α k₀ t ht X => ⟨fun v => ?_, fun v u hvu => ?_⟩⟩
  · rw [hLs d α t X k₀ hd hdn ht v v, blockIdentityEntry_self]
  · rw [hLs d α t X k₀ hd hdn ht v u, blockIdentityEntry_ne h v u hvu, smul_zero]

end Setting
end

/-! The mean letters are invariant under every slow translation that leaves the metric and the
source coefficients invariant. The source-degree-zero letter is pointwise in the invariant lift
coefficients; the positive letter is identified by its literal action through symmetric coefficient
uniqueness. -/

section
section Metric
variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem metricFluxCoefficient_slowShift (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (T : Vec 2) (hG : ∀ t X i j, G t (X + T) i j = G t X i j) (m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    metricFluxCoefficient (h := h) η G k m α t (X + T) z v u =
      metricFluxCoefficient η G k m α t X z v u := by
  match m, α with
  | 0, α => rfl
  | 1, α => rw [metricFluxCoefficient_one, metricFluxCoefficient_one, hG]
  | m + 2, α => rfl

end Metric

section Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- Clause (g) for the source-degree-zero letter. -/
theorem setting_diagonalMeanLetter_slowShift (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (n : ℕ) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    diagonalMeanLetter Q Cc n d α t (X + T) k₀ v u = diagonalMeanLetter Q Cc n d α t X k₀ v u := by
  have hinv := setting_liftSequence_slowShift_invariant P sX sZ Cc hseq T hG hc
  have hw : weightedLiftCoefficientMean (Cc 0 (n - 1)) (fun t z => Real.sqrt Q.η * Q.v t z k₀)
      (d - 1) α t (X + T) 0 v u =
      weightedLiftCoefficientMean (Cc 0 (n - 1)) (fun t z => Real.sqrt Q.η * Q.v t z k₀)
        (d - 1) α t X 0 v u := by
    change fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) •
        Cc 0 (n - 1) (d - 1) α t (X + T) z v u) =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Cc 0 (n - 1) (d - 1) α t X z v u)
    simp only [hinv 0 (Nat.zero_le H) (n - 1) (d - 1) α t ht X]
  simp only [diagonalMeanLetter, truncatedMeanCoefficient, diagonalMeanFluxCoefficient, hw,
    metricFluxCoefficient_slowShift Q.η Q.G k₀ T hG]

end Diagonal

section Positive
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- Clause (g) for the positive-source-degree letter. -/
theorem setting_positiveMeanLetter_slowShift (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (T : Vec 2) (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    positiveMeanLetter Q Cc hh n d α t (X + T) k₀ v u =
      positiveMeanLetter Q Cc hh n d α t X k₀ v u := by
  by_cases hd : 2 ≤ d ∧ d ≤ n
  · rw [show positiveMeanLetter Q Cc hh n d α t (X + T) k₀ v u =
        positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) α t (X + T) 0 v u from
      truncatedMeanCoefficient_eq n d hd.1 hd.2 _ α t (X + T) k₀ v u,
      show positiveMeanLetter Q Cc hh n d α t X k₀ v u =
        positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) α t X 0 v u from
      truncatedMeanCoefficient_eq n d hd.1 hd.2 _ α t X k₀ v u]
    have hinv := setting_liftSequence_slowShift_invariant P sX sZ Cc hseq T hG hc
    have hperm : ∀ (β : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
        positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) (β ∘ σ) =
          positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) β :=
      setting_positive_mean_flux_coefficient_perm sX sZ Cc hseq hh hhh n k₀ (d - 1)
    have hperm' : ∀ (β : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
        slowShiftCoeff T (positiveMeanFluxCoefficient Q Cc hh n k₀) (d - 1) (β ∘ σ) =
          slowShiftCoeff T (positiveMeanFluxCoefficient Q Cc hh n k₀) (d - 1) β := by
      intro β σ
      show (fun s Y y =>
          positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) (β ∘ σ) s (Y + T) y) =
        fun s Y y => positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) β s (Y + T) y
      rw [hperm β σ]
    symm
    refine symmetric_lift_coefficient_eq_of_operator_eq (n - 1) (d - 1) (by omega)
      (positiveMeanFluxCoefficient Q Cc hh n k₀)
      (slowShiftCoeff T (positiveMeanFluxCoefficient Q Cc hh n k₀)) hperm hperm' t X 0 v u ?_ α
    intro a₀ ha₀
    have ha₁ : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => a₀ (Y - T)) :=
      ha₀.comp (contDiff_id.sub contDiff_const)
    have hshift : ∀ Y, (fun (_ : ℝ) => a₀) t Y =
        (fun (_ : ℝ) (Y' : Vec 2) => a₀ (Y' - T)) t (Y + T) := by
      intro Y
      simp only [add_sub_cancel_right]
    have hcong (p q : ℕ) (hp : p ≤ H) : liftApply q (slowShiftSequence T Cc p q) (fun _ => a₀) t =
        liftApply q (Cc p q) (fun _ => a₀) t :=
      liftApply_congr_at_time q _ _ _ t (fun m β Y y w j => hinv p hp q m β t ht Y y w j)
    have h1 (z : Vec 2) : liftApply (n - 1) (Cc hh (n - 1)) (fun _ Y => a₀ (Y - T)) t (X + T) z =
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t X z := by
      rw [← liftApply_slowShift (n - 1) (Cc hh (n - 1)) (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t
        hshift X z]
      exact congrFun (congrFun (hcong hh (n - 1) hhh) X) z
    have h2 (ε : ℝ) (X' z' : Vec 2) :
        liftPolyField Cc N ε (hh - 1) (fun _ Y => a₀ (Y - T)) t (X' + T) z' =
          liftPolyField Cc N ε (hh - 1) (fun _ => a₀) t X' z' := by
      rw [← liftPolyField_slowShift Cc N ε (hh - 1) (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t
        hshift X' z']
      simp only [liftPolyField, hcong (hh - 1) _ (by omega)]
    have h3 (z : Vec 2) : sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ Y => a₀ (Y - T)) t) k₀ (X + T) z =
        sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => a₀) t) k₀ X z := by
      have hΦ : (fun ε X' z' =>
          liftPolyField Cc N ε (hh - 1) (fun _ Y => a₀ (Y - T)) t (X' + T) z') =
          fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => a₀) t := by
        funext ε X' z'
        exact h2 ε X' z'
      rw [← sourceFluxCoeff_slowShift Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ Y => a₀ (Y - T)) t) T
        (fun v u d γ hγ α X z => hc v u d γ hγ α t X z) k₀ X z, hΦ]
    rw [liftApply_slowShift (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k₀)
        (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t hshift X 0,
      setting_positive_mean_flux_coefficient_apply P sX sZ hsZ Cc hseq P₀ hreserve hh hhpos hhh
        n hn hnR a₀ ha₀ k₀ t ht X 0 v,
      setting_positive_mean_flux_coefficient_apply P sX sZ hsZ Cc hseq P₀ hreserve hh hhpos hhh
        n hn hnR _ ha₁ k₀ t ht (X + T) 0 v]
    simp only [h1, h3]
  · simp only [positiveMeanLetter, truncatedMeanCoefficient, ite_eq_right hd]

end Positive
end

/-! Entrywise path-product bounds for the lift means: the explicit divergence-form letter of `L_n^{(hh)}` is word
symmetric, `C^{K+1}` in the slow variable, measurable in time, presents the mean, obeys the
pointwise bound `‖D_X^j b_{d,α}‖ ≤ C ((A_phys)^hh)_{vu} λ^{n-d+j}`, is scalar diagonal at source
degree zero, and is invariant under data-invariant slow translations. -/

section
section Setting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The seven properties of the explicit mean letter `meanLetter Q Cc hh n`. -/
theorem setting_meanLetter_entrywise (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) :
    (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
      meanLetter Q Cc hh n d (α ∘ σ) = meanLetter Q Cc hh n d α) ∧
    (∀ d α k₀ v u, ∀ t ∈ Set.Icc a b,
      ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun X => meanLetter Q Cc hh n d α t X k₀ v u)) ∧
    (∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
      Measurable (fun t : Set.Icc a b => meanLetter Q Cc hh n d α t X k₀ v u)) ∧
    (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc a b, ∀ X,
      liftMean Q Cc (fun _ => a₀) hh n t X =
        meanApply n (meanLetter Q Cc hh n) (fun _ => a₀) t X) ∧
    (∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
      ∀ j, j ≤ K + 1 → ∀ t ∈ Set.Icc a b, ∀ X,
        ‖iteratedFDeriv ℝ j (fun X' => meanLetter Q Cc hh n d α t X' k₀ v u) X‖ ≤
          ambientMeanGradeConstant K N k L D H CG Cw Cj *
            ((Matrix.of fun v' u' => edge v' u' / Real.sqrt (π u' / π v')) ^ hh) v u *
              lam ^ (n - d + j)) ∧
    (hh = 0 → ∃ Ls : (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ,
      ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2),
        ∀ t ∈ Set.Icc a b, ∀ X,
          (∀ v, meanLetter Q Cc hh n d α t X k₀ v v =
            Ls d α t X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
          (∀ v u, v ≠ u → meanLetter Q Cc hh n d α t X k₀ v u = 0)) ∧
    (∀ T : Vec 2, (∀ t X i j, Q.G t (X + T) i j = Q.G t X i j) →
      (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
        γ.coeff α t (X + T) z = γ.coeff α t X z) →
      ∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
        ∀ t ∈ Set.Icc a b, ∀ X, meanLetter Q Cc hh n d α t (X + T) k₀ v u =
          meanLetter Q Cc hh n d α t X k₀ v u) := by
  have hres : K + (N + D) ≤ qs := by have := setting_ambient_output_supported P; omega
  have hX : 2 ≤ K + D + 2 := by omega
  have hZ : 2 ≤ max (k + 1) (L + 2) := by omega
  have hsZ : 1 ≤ max (k + 1) (L + 2) := by omega
  by_cases hh0 : hh = 0
  · subst hh0
    obtain ⟨ha, hb, hd, he⟩ := setting_diagonalMeanLetter_core P _ _ hX hZ Cc hseq K hres
      n hn hnR
    obtain ⟨Ls, hLs⟩ := setting_diagonalMeanLetter_scalar_diagonal P _ _ hsZ Cc hseq n
    rw [meanLetter_zero]
    refine ⟨ha, hb, ?_, hd, ?_, fun _ => ⟨Ls, hLs⟩, ?_⟩
    · intro d α k₀ v u X
      exact setting_diagonalMeanLetter_measurable P _ _ hsZ Cc hseq K hres n hn hnR
        d α k₀ v u X
    · intro d hd hdn α k₀ v u j hj t ht X
      exact he d hd hdn α k₀ v u j hj t ht X
    · intro T hG hc d α k₀ v u t ht X
      exact setting_diagonalMeanLetter_slowShift P _ _ Cc hseq n T hG hc d α k₀ v u t ht X
  · obtain ⟨ha, hb, hd, he⟩ := setting_positiveMeanLetter_core P _ _ hX hZ Cc hseq K hres
      hh (by omega) hhh n hn hnR
    rw [meanLetter_of_ne_zero Q Cc hh0]
    refine ⟨ha, hb, ?_, hd, ?_, fun h0 => absurd h0 hh0, ?_⟩
    · intro d α k₀ v u X
      exact setting_positiveMeanLetter_measurable P _ _ hsZ Cc hseq K hres hh (by omega) hhh
        n hn hnR d α k₀ v u X
    · intro d hd hdn α k₀ v u j hj t ht X
      exact he d hd hdn α k₀ v u j hj t ht X
    · intro T hG hc d α k₀ v u t ht X
      exact setting_positiveMeanLetter_slowShift P _ _ hsZ Cc hseq K hres hh (by omega) hhh
        n hn hnR T hG hc d α k₀ v u t ht X

include P in
theorem setting_lift_mean_entrywise (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) :
    ∃ Lb : MeanCoeff ι h,
      (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
        Lb d (α ∘ σ) = Lb d α) ∧
      (∀ d α k₀ v u, ∀ t ∈ Set.Icc a b,
        ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun X => Lb d α t X k₀ v u)) ∧
      (∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
        Measurable (fun t : Set.Icc a b => Lb d α t X k₀ v u)) ∧
      (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc a b, ∀ X,
        liftMean Q Cc (fun _ => a₀) hh n t X = meanApply n Lb (fun _ => a₀) t X) ∧
      (∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
        ∀ j, j ≤ K + 1 → ∀ t ∈ Set.Icc a b, ∀ X,
          ‖iteratedFDeriv ℝ j (fun X' => Lb d α t X' k₀ v u) X‖ ≤
            ambientMeanGradeConstant K N k L D H CG Cw Cj *
              ((Matrix.of fun v' u' => edge v' u' / Real.sqrt (π u' / π v')) ^ hh) v u *
                lam ^ (n - d + j)) ∧
      (hh = 0 → ∃ Ls : (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ,
        ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2),
          ∀ t ∈ Set.Icc a b, ∀ X,
            (∀ v, Lb d α t X k₀ v v = Ls d α t X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
            (∀ v u, v ≠ u → Lb d α t X k₀ v u = 0)) ∧
      (∀ T : Vec 2, (∀ t X i j, Q.G t (X + T) i j = Q.G t X i j) →
        (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
          γ.coeff α t (X + T) z = γ.coeff α t X z) →
        ∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
          ∀ t ∈ Set.Icc a b, ∀ X, Lb d α t (X + T) k₀ v u = Lb d α t X k₀ v u) :=
  ⟨meanLetter Q Cc hh n, setting_meanLetter_entrywise P Cc hseq hh hhh n hn hnR⟩

end Setting
end

end AVRegularity.CycleComparison.LiftMeanEntrywise
end
