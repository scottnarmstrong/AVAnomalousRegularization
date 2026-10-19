-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.TailConstructed.RawFluxOrderZero
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction

/-! Normalized exponential tests of the raw-flux array at the tail degrees: box smoothness through
the tail test reserves and the mixed bound `K_raw(A) · (env^hh)_{vu} · |ξ| · λ^(n+r)`. The cross part
spends one slow derivative on the degree-`n-1` lift; the source part of word length `l` uses the
degree-`n-l` lift of the preceding grade, whose budget carries one more envelope factor. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.TailConstructed

theorem finiteLiftSymbolBudget_mono {m n : ℕ} (hmn : m ≤ n) (A : Vec 2 →L[ℝ] ℝ) :
    finiteLiftSymbolBudget m A ≤ finiteLiftSymbolBudget n A :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun _ _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The explicit test budget of the raw-flux array; it depends only on the fixed orders, the
fixed data constants and the test direction. -/
def rawFluxTestBudget (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  (normalizedCrossFluxMixedConstant (K + D + 2) (max k (L + 2) + D) A
      (metricParameterBudget (K + D + 2 + 1) CG) 1 +
    ∑ l ∈ Finset.range D,
      normalizedSourceUniformConstant D (K + D + 2) (max k (L + 2) + D) l A Cj) *
    finiteLiftSymbolBudget (2 * N + D) A * tailRawCoefficientBudget K k L D H N CG Cw Cj

theorem rawFluxTestBudget_nonneg (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (A : Vec 2 →L[ℝ] ℝ) : 0 ≤ rawFluxTestBudget K k L D H N CG Cw Cj A := by
  unfold rawFluxTestBudget
  have h1 := normalizedCrossFluxMixedConstant_nonneg (K + D + 2) (max k (L + 2) + D) A
    (metricParameterBudget (K + D + 2 + 1) CG) 1 (metricParameterBudget_nonneg _ CG) zero_le_one
  have h2 : 0 ≤ ∑ l ∈ Finset.range D,
      normalizedSourceUniformConstant D (K + D + 2) (max k (L + 2) + D) l A Cj :=
    Finset.sum_nonneg fun l _ => normalizedSourceUniformConstant_nonneg _ _ _ _ _ _
  have h3 := finiteLiftSymbolBudget_nonneg (2 * N + D) A
  have h4 := tailRawCoefficientBudget_nonneg K k L D H N CG Cw Cj
  positivity

theorem budget_weaken_left_le {c L₁ L₂ m x y : ℝ} (hc : 0 ≤ c) (hL : L₁ ≤ L₂) (hm : 0 ≤ m)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : (c * (L₁ * m * x)) * y ≤ (c * L₂ * m * x) * y := by
  have h : 0 ≤ c * m * x * y := mul_nonneg (mul_nonneg (mul_nonneg hc hm) hx) hy
  calc
    (c * (L₁ * m * x)) * y = (c * m * x * y) * L₁ := by ring
    _ ≤ (c * m * x * y) * L₂ := mul_le_mul_of_nonneg_left hL h
    _ = (c * L₂ * m * x) * y := by ring

theorem budget_weaken_right_le {c L₁ L₂ m x y : ℝ} (hc : 0 ≤ c) (hL : L₁ ≤ L₂) (hm : 0 ≤ m)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : (L₁ * c * m * x) * y ≤ (c * L₂ * m * x) * y := by
  have h : 0 ≤ c * m * x * y := mul_nonneg (mul_nonneg (mul_nonneg hc hm) hx) hy
  calc
    (L₁ * c * m * x) * y = (c * m * x * y) * L₁ := by ring
    _ ≤ (c * m * x * y) * L₂ := mul_le_mul_of_nonneg_left hL h
    _ = (c * L₂ * m * x) * y := by ring

section Fields
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The normalized cross part of the raw flux on an exponential test. -/
def normalizedRawCrossField (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (k₀ : Fin 2) (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) :
    Vec 2 → Vec 2 → h v :=
  fun Y y => (Real.exp (A Y))⁻¹ • crossFluxField Q.η (Q.G t) k₀
    (fun Z w => liftApply (n - 1) (Cc hh (n - 1))
      (fun _ Z' => Real.exp (A Z') • Pi.single u ξ) t Z w v) Y y

theorem normalizedRawCrossField_eq (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (k₀ : Fin 2) (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) :
    normalizedRawCrossField Q Cc hh n k₀ A u v ξ t = fun Y y => (Real.exp (A Y))⁻¹ •
      crossFluxField Q.η (Q.G t) k₀ (fun Z w => liftApply (n - 1) (Cc hh (n - 1))
        (fun _ Z' => Real.exp (A Z') • Pi.single u ξ) t Z w v) Y y := rfl

/-- The normalized source part of word length `l` of the raw flux on an exponential test. -/
def normalizedRawSourceField (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n l : ℕ) (k₀ : Fin 2) (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) :
    Vec 2 → Vec 2 → h v :=
  fun Y y => (Real.exp (A Y))⁻¹ • sourceFluxComponentCoefficient Q.edge Q.η t
    (liftApply (n - l) (Cc (hh - 1) (n - l))
      (fun _ Z' => Real.exp (A Z') • Pi.single u ξ) t) k₀ l v Y y

end Fields

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
/-- The normalized test field of the raw-flux array splits into its cross and source parts. -/
theorem setting_rawFlux_normalized_test_split
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (k₀ : Fin 2)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) (Y y : Vec 2) :
    normalizedLiftTestField (rawFluxCoefficient Q Cc hh n k₀) n A u v ξ t Y y =
      normalizedRawCrossField Q Cc hh n k₀ A u v ξ t Y y -
        (if hh = 0 then 0 else ∑ l ∈ Finset.range (min (D - 1) n + 1),
          normalizedRawSourceField Q Cc hh n l k₀ A u v ξ t Y y) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z => Real.exp (A Z) • (Pi.single u ξ : ∀ i, h i)) :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have hΦ : IsBoxSmooth 1 0
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ Z => Real.exp (A Z) • Pi.single u ξ) t) :=
    liftApply_box_reserve (n - 1) 1 0 (Cc hh (n - 1)) _ t (hf.of_le (by simp))
      (fun m _ α v' u' => setting_tailRaw_coefficient_box P sX sZ hsZ Cc hseq 1 0
        (by omega) (by omega) hh hhh (n - 1) m α v' u' t ht)
  simp only [normalizedRawCrossField, normalizedRawSourceField]
  rw [setting_rawFluxCoefficient_normalized_test_eq P sX sZ hsZ Cc hseq hh hhh n hn k₀
    A u v ξ t ht Y y, constructedLiftTailRawFlux_apply Q Cc N hh n _ t Y y k₀ v hΦ
      (setting_metric_contDiff_one P t ht), smul_sub]
  by_cases hh0 : hh = 0
  · rw [ite_eq_left hh0, ite_eq_left hh0, smul_zero]
  · rw [ite_eq_right hh0, ite_eq_right hh0, setting_sourceFluxCoeff_component_sum P sX sZ hsZ Cc hseq
      hh hh0 hhh n _ hf k₀ t ht Y y v, Finset.smul_sum]

include P in
/-- The `v`-component of the degree-`n-1` lift of an exponential test is box smooth one slow
order beyond the tail test reserve. -/
theorem setting_rawCross_lift_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth (K + D + 2 + 1) (max k (L + 2) + D)
      (fun Z w => liftApply (n - 1) (Cc hh (n - 1))
        (fun _ Z' => Real.exp ((lam • A) Z') • Pi.single u ξ) t Z w v) := by
  have hD := P.D_ge
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun Z => Real.exp ((lam • A) Z) • (Pi.single u ξ : ∀ i, h i)) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const
  exact liftApply_component_box_reserve (n - 1) (K + D + 2 + 1) (max k (L + 2) + D)
    (Cc hh (n - 1)) (fun _ Z' => Real.exp ((lam • A) Z') • Pi.single u ξ) t v
    (hf.of_le (by simp))
    (fun m _ α u' => setting_tailRaw_coefficient_box P sX sZ hsZ Cc hseq
      (K + D + 2 + 1) (max k (L + 2) + D) (by omega) (by omega) hh hhh (n - 1) m α v u' t ht)

include P in
/-- Box smoothness of the normalized cross part. -/
theorem setting_rawCross_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (k₀ : Fin 2)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth (K + D + 2) (max k (L + 2) + D)
      (normalizedRawCrossField Q Cc hh n k₀ (lam • A) u v ξ t) := by
  have hPq : K + D + 2 + 1 ≤ qs := by
    have := setting_tail_ambient_supported P
    have := P.N_ge
    omega
  rw [normalizedRawCrossField_eq]
  exact exponential_normalization_box_reserve (K + D + 2) (max k (L + 2) + D) (lam • A) _
    (crossFluxField_box Q.η (Q.G t) k₀ _ (K + D + 2) (max k (L + 2) + D)
      (setting_rawCross_lift_box P sX sZ hsZ Cc hseq hh hhh n A u v ξ t ht)
      (fun i j => setting_metric_entry_box P (K + D + 2 + 1) (max k (L + 2) + D) hPq t ht i j))

include P in
/-- The graded bound of the normalized cross part. -/
theorem setting_rawCross_bound
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (k₀ : Fin 2)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (r : ℕ) (hr : r ≤ K + D + 2) (s : ℕ) (hs : s ≤ max k (L + 2) + D) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (normalizedRawCrossField Q Cc hh n k₀ (lam • A) u v ξ t Y) z) X‖ ≤
      (normalizedCrossFluxMixedConstant (K + D + 2) (max k (L + 2) + D) A
          (metricParameterBudget (K + D + 2 + 1) CG) 1 *
        finiteLiftSymbolBudget (2 * N + D) A *
        (tailRawCoefficientBudget K k L D H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖) *
        lam ^ (n + r) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hPq : K + D + 2 + 1 ≤ qs := by
    have := setting_tail_ambient_supported P
    have := P.N_ge
    omega
  have hD := P.D_ge
  have data := setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq (K + D + 2 + 1)
    (max k (L + 2) + D) (by omega) (by omega) hh hhh (n - 1)
  have hβw : 0 ≤ tailRawCoefficientBudget K k L D H N CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u := data.nonneg v u
  have hNc := normalizedCrossFluxMixedConstant_nonneg (K + D + 2) (max k (L + 2) + D) A
    (metricParameterBudget (K + D + 2 + 1) CG) 1 (metricParameterBudget_nonneg _ CG) zero_le_one
  have hmono := finiteLiftSymbolBudget_mono (show n - 1 ≤ 2 * N + D by omega) A
  have hb := normalizedCrossFlux_lift_test_grading (n - 1) (K + D + 2) (max k (L + 2) + D)
    Q.η lam (metricParameterBudget (K + D + 2 + 1) CG)
    (tailRawCoefficientBudget K k L D H N CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)
    P.η_le hlam.le (metricParameterBudget_nonneg _ CG) hβw A (Q.G t) k₀ t
    (Cc hh (n - 1)) v u ξ (fun m hm α => data.box m hm α v u t ht)
    (fun i j => setting_metric_entry_box P (K + D + 2 + 1) (max k (L + 2) + D) hPq t ht i j) X
    (fun i j a' ha' b' _ y => setting_metric_mixed_uniform_bound P (K + D + 2 + 1) a' b' hPq ha'
      t ht X y i j)
    (fun m hm α a' ha' b' hb' y => data.bound m hm α v u a' ha' b' hb' t ht X y) r s hr hs z
  have hexp : (n - 1 + 1) + r = n + r := by omega
  rw [hexp] at hb
  rw [normalizedRawCrossField_eq]
  refine hb.trans ?_
  exact budget_weaken_left_le hNc hmono hβw (norm_nonneg ξ) (pow_nonneg hlam.le (n + r))

include P in
/-- Box smoothness and the graded bound of the normalized cross part. -/
theorem setting_rawCross_box_and_bound
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (k₀ : Fin 2)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth (K + D + 2) (max k (L + 2) + D)
        (normalizedRawCrossField Q Cc hh n k₀ (lam • A) u v ξ t) ∧
      ∀ r ≤ K + D + 2, ∀ s ≤ max k (L + 2) + D, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (normalizedRawCrossField Q Cc hh n k₀ (lam • A) u v ξ t Y) z) X‖ ≤
          (normalizedCrossFluxMixedConstant (K + D + 2) (max k (L + 2) + D) A
              (metricParameterBudget (K + D + 2 + 1) CG) 1 *
            finiteLiftSymbolBudget (2 * N + D) A *
            (tailRawCoefficientBudget K k L D H N CG Cw Cj *
              finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖) *
            lam ^ (n + r) :=
  ⟨setting_rawCross_box P sX sZ hsZ Cc hseq hh hhh n k₀ A u v ξ t ht,
    fun r hr s hs X z => setting_rawCross_bound P sX sZ hsZ Cc hseq hh hhh n hn hnR k₀
      A u v ξ t ht r hr s hs X z⟩

include P in
/-- Box smoothness and the graded bound of the normalized source part of word length `l`. -/
theorem setting_rawSource_box_and_bound
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hh0 : hh ≠ 0) (hhh : hh ≤ H) (n : ℕ) (hnR : n ≤ 2 * N + D) (l : ℕ)
    (hl : l ≤ min (D - 1) n) (k₀ : Fin 2)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth (K + D + 2) (max k (L + 2) + D)
        (normalizedRawSourceField Q Cc hh n l k₀ (lam • A) u v ξ t) ∧
      ∀ r ≤ K + D + 2, ∀ s ≤ max k (L + 2) + D, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (normalizedRawSourceField Q Cc hh n l k₀ (lam • A) u v ξ t Y) z) X‖ ≤
          (normalizedSourceUniformConstant D (K + D + 2) (max k (L + 2) + D) l A Cj *
            finiteLiftSymbolBudget (2 * N + D) A *
            (tailRawCoefficientBudget K k L D H N CG Cw Cj *
              finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖) *
            lam ^ (n + r) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hPq : K + D + 2 ≤ qs := by
    have := setting_tail_ambient_supported P
    omega
  have hQq : max k (L + 2) + D ≤ qf := by
    rw [P.qf_eq]
    omega
  have data := setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq (K + D + 2 + l)
    (max k (L + 2) + D + (D - 1) - l) (by omega) (by omega) (hh - 1) (by omega) (n - l)
  refine ⟨setting_ambient_sourceFlux_lift_box P Cc (hh - 1) (n - l) (K + D + 2)
    (max k (L + 2) + D) l _ _ hPq hQq le_rfl le_rfl _ data A k₀ t ht v u ξ, ?_⟩
  intro r hr s hs X z
  have hb := setting_ambient_sourceFlux_lift_bound P Cc (hh - 1) (n - l) (K + D + 2)
    (max k (L + 2) + D) l _ _ hPq hQq le_rfl le_rfl _ data A k₀ t ht v u ξ r s hr hs X z
  have h1 : 1 ≤ hh := Nat.one_le_iff_ne_zero.mpr hh0
  have hln : l ≤ n := le_trans hl (min_le_right _ _)
  simp only [finiteMatrixProduct_edge_scalar_power, Nat.sub_add_cancel h1,
    Nat.sub_add_cancel hln] at hb
  exact hb.trans (budget_weaken_right_le
    (normalizedSourceUniformConstant_nonneg _ _ _ _ _ _)
    (finiteLiftSymbolBudget_mono (show n - l ≤ 2 * N + D by omega) A)
    (mul_nonneg (tailRawCoefficientBudget_nonneg K k L D H N CG Cw Cj)
      (finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg)
        hh v u))
    (norm_nonneg ξ) (pow_nonneg hlam.le _))

include P in
/-- **Normalized test bounds of the raw-flux array.** For every tail degree, every grade up to
`H`, every slow order `p ≤ K + D + 2` and fast order `q ≤ max k (L+2) + D`, the normalized
exponential test fields of the raw-flux array are box smooth and graded at degree `n`, with the
explicit budget `rawFluxTestBudget` and the `hh`-th power of the physical envelope matrix. -/
theorem setting_rawFlux_normalized_test_box_and_bound
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (k₀ : Fin 2)
    (p q : ℕ) (hp : p ≤ K + D + 2) (hq : q ≤ max k (L + 2) + D)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q
        (normalizedLiftTestField (rawFluxCoefficient Q Cc hh n k₀) n (lam • A) u v ξ t) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (normalizedLiftTestField (rawFluxCoefficient Q Cc hh n k₀) n (lam • A) u v ξ t Y)
            z) X‖ ≤
          (rawFluxTestBudget K k L D H N CG Cw Cj A *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) *
            lam ^ (n + r) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hD := P.D_ge
  obtain ⟨hcb, hcB⟩ := setting_rawCross_box_and_bound P sX sZ hsZ Cc hseq hh hhh n hn hnR k₀
    A u v ξ t ht
  have hβw : 0 ≤ tailRawCoefficientBudget K k L D H N CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u :=
    mul_nonneg (tailRawCoefficientBudget_nonneg K k L D H N CG Cw Cj)
      (finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg)
        hh v u)
  have hΛ := finiteLiftSymbolBudget_nonneg (2 * N + D) A
  have hS : 0 ≤ ∑ l ∈ Finset.range D,
      normalizedSourceUniformConstant D (K + D + 2) (max k (L + 2) + D) l A Cj :=
    Finset.sum_nonneg fun l _ => normalizedSourceUniformConstant_nonneg _ _ _ _ _ _
  by_cases hh0 : hh = 0
  · have he : normalizedLiftTestField (rawFluxCoefficient Q Cc hh n k₀) n (lam • A) u v ξ t =
        normalizedRawCrossField Q Cc hh n k₀ (lam • A) u v ξ t := by
      funext Y y
      rw [setting_rawFlux_normalized_test_split P sX sZ hsZ Cc hseq hh hhh n hn k₀ (lam • A)
        u v ξ t ht Y y, ite_eq_left hh0, sub_zero]
    rw [he]
    refine ⟨hcb.mono hp hq, fun r hr s hs X z =>
      (hcB r (hr.trans hp) s (hs.trans hq) X z).trans ?_⟩
    have hc : 0 ≤ finiteLiftSymbolBudget (2 * N + D) A *
        (tailRawCoefficientBudget K k L D H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖ * lam ^ (n + r) :=
      mul_nonneg (mul_nonneg (mul_nonneg hΛ hβw) (norm_nonneg ξ)) (pow_nonneg hlam.le _)
    exact (le_add_of_nonneg_right (mul_nonneg hS hc)).trans_eq
      (by unfold rawFluxTestBudget; ring)
  · have he : normalizedLiftTestField (rawFluxCoefficient Q Cc hh n k₀) n (lam • A) u v ξ t =
        fun Y y => normalizedRawCrossField Q Cc hh n k₀ (lam • A) u v ξ t Y y -
          ∑ l ∈ Finset.range (min (D - 1) n + 1),
            normalizedRawSourceField Q Cc hh n l k₀ (lam • A) u v ξ t Y y := by
      funext Y y
      rw [setting_rawFlux_normalized_test_split P sX sZ hsZ Cc hseq hh hhh n hn k₀ (lam • A)
        u v ξ t ht Y y, ite_eq_right hh0]
    have hsrc (l : ℕ) (hl : l ∈ Finset.range (min (D - 1) n + 1)) :=
      setting_rawSource_box_and_bound P sX sZ hsZ Cc hseq hh hh0 hhh n hnR l
        (by have := Finset.mem_range.mp hl; omega) k₀ A u v ξ t ht
    have hsb : IsBoxSmooth (K + D + 2) (max k (L + 2) + D) (fun Y y =>
        ∑ l ∈ Finset.range (min (D - 1) n + 1),
          normalizedRawSourceField Q Cc hh n l k₀ (lam • A) u v ξ t Y y) :=
      IsBoxSmooth.sum _ fun l hl => (hsrc l hl).1
    rw [he]
    refine ⟨(hcb.sub hsb).mono hp hq, ?_⟩
    intro r hr s hs X z
    have hr' : r ≤ K + D + 2 := hr.trans hp
    have hs' : s ≤ max k (L + 2) + D := hs.trans hq
    have hcy : 0 ≤ finiteLiftSymbolBudget (2 * N + D) A *
        (tailRawCoefficientBudget K k L D H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖ * lam ^ (n + r) :=
      mul_nonneg (mul_nonneg (mul_nonneg hΛ hβw) (norm_nonneg ξ)) (pow_nonneg hlam.le _)
    have hsum := (norm_mixed_jet_finset_sum_le (Finset.range (min (D - 1) n + 1)) r s
      (fun l => normalizedRawSourceField Q Cc hh n l k₀ (lam • A) u v ξ t)
      (fun l hl => ((hsrc l hl).1).mono hr' hs') X z).trans
      (Finset.sum_le_sum fun l hl => (hsrc l hl).2 r hr' s hs' X z)
    have hT : ∑ l ∈ Finset.range (min (D - 1) n + 1),
        (normalizedSourceUniformConstant D (K + D + 2) (max k (L + 2) + D) l A Cj *
          finiteLiftSymbolBudget (2 * N + D) A *
          (tailRawCoefficientBudget K k L D H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖) *
          lam ^ (n + r) ≤
        (∑ l ∈ Finset.range D,
          normalizedSourceUniformConstant D (K + D + 2) (max k (L + 2) + D) l A Cj) *
          (finiteLiftSymbolBudget (2 * N + D) A *
            (tailRawCoefficientBudget K k L D H N CG Cw Cj *
              finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖ *
            lam ^ (n + r)) := by
      rw [Finset.sum_mul]
      calc
        _ = ∑ l ∈ Finset.range (min (D - 1) n + 1),
            normalizedSourceUniformConstant D (K + D + 2) (max k (L + 2) + D) l A Cj *
              (finiteLiftSymbolBudget (2 * N + D) A *
                (tailRawCoefficientBudget K k L D H N CG Cw Cj *
                  finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * ‖ξ‖ *
                lam ^ (n + r)) :=
          Finset.sum_congr rfl fun l _ => by ring
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega))
          (fun l _ _ => mul_nonneg (normalizedSourceUniformConstant_nonneg _ _ _ _ _ _) hcy)
    apply (norm_mixed_jet_sub_le (hcb.mono hr' hs') (hsb.mono hr' hs') X z).trans
    apply (add_le_add (hcB r hr' s hs' X z) (hsum.trans hT)).trans
    apply le_of_eq
    unfold rawFluxTestBudget
    ring

end Setting

end AVRegularity.CycleComparison.TailConstructed
