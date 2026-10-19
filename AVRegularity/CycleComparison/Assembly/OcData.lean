-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleComparison.ActualMeans.Transfer
import AVRegularity.CycleComparison.ActualMeans.PulseFlux
import AVRegularity.CycleComparison.LiftSetting.Main
public import AVRegularity.CycleComparison.ActualMeans.KernelRegular
import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.Statements.Intermediate.CycleOutput.IsLiftPartition
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber

section
section
/-! From pointwise bounds on the derivative arrays of a family of coefficient letters to the
normalized coefficient seminorms of `cycle_comparison` (clause 3): the dimensional conversion
`ℓ⁻² d_*ⁿ = B d_*^{n-2}` and the grading at the radii `E` and `R`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity.CycleComparison.Assembly

/-- The grading inequality: for `d_* ≤ R ≤ E` and `2 ≤ d ≤ n`,
`R^j · B d_*^{n-2} E^{-(n+j-d)} ≤ B R^{d-2}`. -/
theorem scale_term_le {B dstar R E : ℝ} (hB : 0 ≤ B) (hd : 0 ≤ dstar) (hR : 0 < R)
    (hdR : dstar ≤ R) (hRE : R ≤ E) {d n : ℕ} (hd2 : 2 ≤ d) (hdn : d ≤ n) (j : ℕ) :
    R ^ j * (B * dstar ^ (n - 2) * E⁻¹ ^ (n + j - d)) ≤ B * R ^ (d - 2) := by
  have hE : 0 < E := lt_of_lt_of_le hR hRE
  have h1 : dstar ^ (n - 2) ≤ R ^ (n - 2) := pow_le_pow_left₀ hd hdR _
  have h2 : R ^ (n + j - d) * E⁻¹ ^ (n + j - d) ≤ 1 := by
    rw [← mul_pow]
    refine pow_le_one₀ (mul_nonneg hR.le (inv_nonneg.2 hE.le)) ?_
    rw [← div_eq_mul_inv]
    exact (div_le_one hE).2 hRE
  have e1 : R ^ j * R ^ (n - 2) = R ^ (n + j - d) * R ^ (d - 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc R ^ j * (B * dstar ^ (n - 2) * E⁻¹ ^ (n + j - d))
      ≤ R ^ j * (B * R ^ (n - 2) * E⁻¹ ^ (n + j - d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 hB) (pow_nonneg (inv_nonneg.2 hE.le) _))
          (pow_nonneg hR.le _)
    _ = B * R ^ (d - 2) * (R ^ (n + j - d) * E⁻¹ ^ (n + j - d)) := by
        calc R ^ j * (B * R ^ (n - 2) * E⁻¹ ^ (n + j - d))
            = B * (R ^ j * R ^ (n - 2)) * E⁻¹ ^ (n + j - d) := by ring
          _ = B * (R ^ (n + j - d) * R ^ (d - 2)) * E⁻¹ ^ (n + j - d) := by rw [e1]
          _ = B * R ^ (d - 2) * (R ^ (n + j - d) * E⁻¹ ^ (n + j - d)) := by ring
    _ ≤ B * R ^ (d - 2) * 1 :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hB (pow_nonneg hR.le _))
    _ = B * R ^ (d - 2) := mul_one _

section Seminorm

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A normalized coefficient seminorm from pointwise bounds on the derivative arrays. -/
theorem coefficientSeminorm_mul_inv_le {R S w : ℝ} (hR : 0 < R) (hS : 0 < S) (hw : 0 ≤ w)
    (K' : ℕ) (t₀ t₁ : ℝ) (A : ℝ → Vec 2 → X →L[ℝ] Y)
    (h : ∀ j, j ≤ K' → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      R ^ j * ‖coefficientDerivativeArray (A t) j x‖ ≤ w * S) :
    coefficientSeminorm R K' t₀ t₁ A * (ENNReal.ofReal S)⁻¹ ≤
      ENNReal.ofReal (((K' : ℝ) + 1) * w) := by
  have hterm : ∀ j ∈ Finset.range (K' + 1),
      ENNReal.ofReal (R ^ j / (j.factorial : ℝ)) *
        (⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2,
          (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞)) ≤ ENNReal.ofReal (w * S) := by
    intro j hj
    have hjK : j ≤ K' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hRj : 0 < R ^ j := pow_pos hR j
    have hfac : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have hsup : (⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2,
        (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞)) ≤ ENNReal.ofReal (w * S / R ^ j) := by
      refine iSup₂_le fun t ht => iSup_le fun x => ?_
      rw [← enorm_eq_nnnorm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ hRj, mul_comm]
      exact h j hjK t ht x
    refine (mul_le_mul' le_rfl hsup).trans ?_
    rw [← ENNReal.ofReal_mul (div_nonneg hRj.le (by positivity))]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : R ^ j / (j.factorial : ℝ) * (w * S / R ^ j) = w * S / (j.factorial : ℝ) := by
      field_simp
    rw [e]
    exact div_le_self (mul_nonneg hw hS.le) hfac
  have hsum : coefficientSeminorm R K' t₀ t₁ A ≤
      ENNReal.ofReal (((K' : ℝ) + 1) * w * S) := by
    unfold coefficientSeminorm
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast (K' + 1), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    ring
  have hS0 : ENNReal.ofReal S ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hS
  refine (mul_le_mul' hsum le_rfl).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) hw), mul_assoc,
    ENNReal.mul_inv_cancel hS0 ENNReal.ofReal_ne_top, mul_one]

end Seminorm

/-- **The means bound from the transfer bound.** If the derivative arrays of the letters `CE d`
are bounded by `w ∑_{n ≥ d} B d_*^{n-2} E^{-(n+j-d)}` on the window, then both normalized sums of
clause 3 of `cycle_comparison` are bounded by `2 N'² (K'+1) w`. -/
theorem means_seminorm_le {N' : ℕ} {X : Finset.Icc 2 N' → Type*}
    [∀ d, NormedAddCommGroup (X d)] [∀ d, NormedSpace ℝ (X d)] {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {B dstar ρ E w : ℝ} (hB : 0 < B)
    (hd : 0 ≤ dstar) (hρ : 0 < ρ) (hdρ : dstar ≤ ρ) (hρE : ρ ≤ E) (hw : 0 ≤ w)
    (K' : ℕ) (t₀ t₁ : ℝ) (CE : ∀ d : Finset.Icc 2 N', ℝ → Vec 2 → X d →L[ℝ] Y)
    (hT : ∀ (d : Finset.Icc 2 N') (j : ℕ), j ≤ K' → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (CE d t) j x‖ ≤
        w * ∑ n ∈ Finset.Icc d.1 N', B * dstar ^ (n - 2) * E⁻¹ ^ (n + j - d.1)) :
    (∑ d : Finset.Icc 2 N', coefficientSeminorm E K' t₀ t₁ (CE d) *
        (ENNReal.ofReal (B * E ^ (d.1 - 2)))⁻¹) +
      ∑ d : Finset.Icc 2 N', coefficientSeminorm ρ K' t₀ t₁ (CE d) *
        (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹ ≤
      ENNReal.ofReal (2 * (N' : ℝ) ^ 2 * ((K' : ℝ) + 1) * w) := by
  have hE : 0 < E := lt_of_lt_of_le hρ hρE
  -- one radius `R` with `d_* ≤ R ≤ E`
  have hone : ∀ R : ℝ, 0 < R → dstar ≤ R → R ≤ E →
      ∑ d : Finset.Icc 2 N', coefficientSeminorm R K' t₀ t₁ (CE d) *
        (ENNReal.ofReal (B * R ^ (d.1 - 2)))⁻¹ ≤
      ENNReal.ofReal ((N' : ℝ) ^ 2 * ((K' : ℝ) + 1) * w) := by
    intro R hR hdR hRE
    have hterm : ∀ d : Finset.Icc 2 N', coefficientSeminorm R K' t₀ t₁ (CE d) *
        (ENNReal.ofReal (B * R ^ (d.1 - 2)))⁻¹ ≤
        ENNReal.ofReal (((K' : ℝ) + 1) * ((N' : ℝ) * w)) := by
      intro d
      have hd2 := Finset.mem_Icc.1 d.2
      refine coefficientSeminorm_mul_inv_le hR (mul_pos hB (pow_pos hR _))
        (mul_nonneg (Nat.cast_nonneg _) hw) K' t₀ t₁ (CE d) fun j hj t ht x => ?_
      calc R ^ j * ‖coefficientDerivativeArray (CE d t) j x‖
          ≤ R ^ j * (w * ∑ n ∈ Finset.Icc d.1 N', B * dstar ^ (n - 2) * E⁻¹ ^ (n + j - d.1)) :=
            mul_le_mul_of_nonneg_left (hT d j hj t ht x) (pow_nonneg hR.le _)
        _ = w * ∑ n ∈ Finset.Icc d.1 N',
              R ^ j * (B * dstar ^ (n - 2) * E⁻¹ ^ (n + j - d.1)) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by ring
        _ ≤ w * ∑ _n ∈ Finset.Icc d.1 N', B * R ^ (d.1 - 2) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) hw
            exact scale_term_le hB.le hd hR hdR hRE hd2.1 (Finset.mem_Icc.1 hn).1 j
        _ ≤ w * ((N' : ℝ) * (B * R ^ (d.1 - 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ hw
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
            refine mul_le_mul_of_nonneg_right ?_
              (mul_nonneg hB.le (pow_nonneg hR.le _))
            exact_mod_cast (by omega : N' + 1 - d.1 ≤ N')
        _ = (N' : ℝ) * w * (B * R ^ (d.1 - 2)) := by ring
    refine (Finset.sum_le_sum fun d _ => hterm d).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast (N' + 1 - 2),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc : ((N' + 1 - 2 : ℕ) : ℝ) ≤ (N' : ℝ) := by exact_mod_cast (by omega : N' + 1 - 2 ≤ N')
    have hX : 0 ≤ ((K' : ℝ) + 1) * ((N' : ℝ) * w) :=
      mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) hw)
    calc ((N' + 1 - 2 : ℕ) : ℝ) * (((K' : ℝ) + 1) * ((N' : ℝ) * w))
        ≤ (N' : ℝ) * (((K' : ℝ) + 1) * ((N' : ℝ) * w)) := mul_le_mul_of_nonneg_right hc hX
      _ = (N' : ℝ) ^ 2 * ((K' : ℝ) + 1) * w := by ring
  have h1 := hone E hE (hdρ.trans hρE) le_rfl
  have h2 := hone ρ hρ hdρ hρE
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end AVRegularity.CycleComparison.Assembly
end
end

section
/-! Classical representatives of vector-valued torus Sobolev fields (`H^{r+2}(𝕋²; 𝗁) ⊂ C^r`,
`𝗁` finite dimensional), componentwise in an orthonormal basis from the scalar case
`torusHk_classicalRep_exists`. This gives the classical representative `aRep` of the retained
coarse field in clause 6 of `cycle_comparison` (the coarse responses are genuine second-order
energy solutions, on which the lift acts classically). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleComparison.Assembly

/-- The jet of order `m ≤ K` of a torus Sobolev field is a.e. its `L²` jet. -/
theorem torusJetOrder_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K m : ℕ} (V : TorusHk K E)
    (hmK : m ≤ K) (w : DerivativeWord2 m) :
    torusJetOrder V m w =ᵐ[volume.restrict AVenhance.unitCube]
      (V.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩ : Vec 2 → E) := by
  have e : torusJetOrder V m w = V.toFunction.jet ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩ := by
    funext x
    simp [torusJetOrder, hmK]
  rw [e]
  exact periodicJetRepresentative_ae V.val _

/-- **Classical representatives of vector-valued fields.** -/
theorem torusHk_classicalRep_exists_vec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (K r : ℕ) (hr : r + 2 ≤ K) (W : TorusHk K E) : ∃ a : Vec 2 → E, IsClassicalRep W a r := by
  have hrK : r ≤ K := by omega
  set bs := stdOrthonormalBasis ℝ E with hbs
  set Wc : Fin (Module.finrank ℝ E) → TorusHk K ℝ := fun i =>
    CoupledEnergy.Variational.mapTorusHk (innerSL ℝ (bs i)) W with hWc
  choose ac hac using fun i => Providers.torusHk_classicalRep_exists K r hr (Wc i)
  set L : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.proj i : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ).smulRight (bs i)
    with hL_def
  have hL : ∀ c : Fin (Module.finrank ℝ E) → ℝ, L c = ∑ i, c i • bs i := by
    intro c
    simp only [hL_def, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
  have hgr : ContDiff ℝ (r : ℕ∞) (fun x i => ac i x) := contDiff_pi.2 fun i => (hac i).2.1
  refine ⟨fun x => L (fun i => ac i x), hrK, L.contDiff.comp hgr, ?_, fun m hm w => ?_⟩
  · intro n x
    show L (fun i => ac i (x + AVenhance.latticeShift n)) = L (fun i => ac i x)
    congr 1
    funext i
    exact (hac i).2.2.1 n x
  · have hmK : m ≤ K := hm.trans hrK
    have hg : ContDiff ℝ (m : ℕ∞) (fun x i => ac i x) := hgr.of_le (by exact_mod_cast hm)
    have hda := orderedDerivative_clm_comp L w hg
    have hdi : ∀ i, orderedDerivative w (ac i) =
        fun x => orderedDerivative w (fun x i => ac i x) x i := fun i =>
      orderedDerivative_clm_comp (ContinuousLinearMap.proj i) w hg
    set j : JetIndex2 K := ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩ with hj
    have htor : ∀ V : TorusHk K ℝ,
        torusJetOrder V m w =ᵐ[volume.restrict AVenhance.unitCube] (V.val j : Vec 2 → ℝ) :=
      fun V => torusJetOrder_ae V hmK w
    have htorW : torusJetOrder W m w =ᵐ[volume.restrict AVenhance.unitCube]
        (W.val j : Vec 2 → E) := torusJetOrder_ae W hmK w
    have hWi : ∀ i, ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
        torusJetOrder (Wc i) m w x = inner ℝ (bs i) ((W.val j : Vec 2 → E) x) := by
      intro i
      filter_upwards [htor (Wc i), CoupledEnergy.Variational.mapTorusHk_jet_ae
        (innerSL ℝ (bs i)) W j] with x h1 h2
      rw [h1, hWc, h2, innerSL_apply_apply]
    filter_upwards [htorW, ae_all_iff.2 hWi, ae_all_iff.2 fun i => (hac i).2.2.2 m hm w]
      with x h1 h2 h3
    calc torusJetOrder W m w x = (W.val j : Vec 2 → E) x := h1
      _ = ∑ i, inner ℝ (bs i) ((W.val j : Vec 2 → E) x) • bs i := (bs.sum_repr' _).symm
      _ = ∑ i, orderedDerivative w (ac i) x • bs i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← h2 i, h3 i]
      _ = L (fun i => orderedDerivative w (ac i) x) := (hL _).symm
      _ = orderedDerivative w (fun x => L (fun i => ac i x)) x := by
          rw [hda]
          congr 1
          funext i
          rw [hdi i]

end AVRegularity.CycleComparison.Assembly
end
end

section
/-! Clause 3 of `cycle_comparison` for the Eulerian edge letters `ceLetter`: an entrywise
envelope `M λ_s^{n-d+i}` of the chart-frame letters gives the normalized coefficient seminorms at
the radii `E` and `R = ρ`. The dimensions are `c = ℓ²`, `ε_c = d_*/ρ`, `d_* = ℓ√B`, `λ_s = ρ/E`, and the
chart scale is `E`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Assembly

open AVRegularity.CycleComparison.ActualMeans

/-- The dimensional conversion `ℓ⁻² d_*ⁿ = B d_*^{n-2}` for `d_* = ℓ√B`, `n ≥ 2`. -/
theorem dimensional_conversion {ℓ B dstar ρ : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hd : dstar = ℓ * Real.sqrt B) {n : ℕ} (hn : 2 ≤ n) :
    (ℓ ^ 2)⁻¹ * (dstar / ρ * ρ) ^ n = B * dstar ^ (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h1 : dstar / ρ * ρ = dstar := div_mul_cancel₀ _ hρ.ne'
  have h2 : dstar ^ 2 = ℓ ^ 2 * B := by
    rw [hd, mul_pow, Real.sq_sqrt hB]
  rw [h1, Nat.add_sub_cancel, pow_add, h2]
  field_simp

/-- **Clause 3 for the edge letters.** -/
theorem ceLetter_means_bound (N D Kt : ℕ) (Cχ : ℕ → ℝ) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (ℓ B dstar ρ E T₀ T₁ : ℝ)
      (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
      (r : ℕ) (v u : ι) (Mb : ℝ),
      0 < ℓ → 0 < B → 0 < ρ → dstar = ℓ * Real.sqrt B → dstar ≤ ρ → ρ ≤ E → 0 ≤ Mb →
      (∀ k ∈ kset, ∀ t, 0 ≤ ϖ k t) → (∀ t ∈ Set.Icc T₀ T₁, ∑ k ∈ kset, ϖ k t = 1) →
      (∀ k ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (chart k t)) →
      (∀ k ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (label k t)) →
      (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
        ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
        ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * E⁻¹ ^ (p - 1) ∧
        ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * E⁻¹ ^ (p - 1)) →
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
          ContDiff ℝ (Kt : ℕ∞) (fun X => Lb k r n d α s X k₀ v u)) →
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ i, i ≤ Kt →
          ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            ‖iteratedFDeriv ℝ i (fun X' => Lb k r n d α s X' k₀ v u) X‖ ≤
              Mb * (ρ / E) ^ (n - d + i)) →
      ∀ K' : ℕ, K' ≤ Kt →
        (∑ d : Finset.Icc 2 (N + D), coefficientSeminorm E K' T₀ T₁
            (ceLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lb r v u d) *
            (ENNReal.ofReal (B * E ^ (d.1 - 2)))⁻¹) +
          ∑ d : Finset.Icc 2 (N + D), coefficientSeminorm ρ K' T₀ T₁
            (ceLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lb r v u d) *
            (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹ ≤
          ENNReal.ofReal (2 * ((N + D : ℕ) : ℝ) ^ 2 * ((K' : ℝ) + 1) * (Ct * Mb)) := by
  obtain ⟨Ct, hCt, htr⟩ := ceLetter_transfer N D Kt Cχ
  refine ⟨Ct, hCt, ?_⟩
  intro ι h _ _ kset ϖ ℓ B dstar ρ E T₀ T₁ chart label s₀ s₁ Lb r v u Mb hℓ hB hρ hd hdρ hρE hMb
    hϖ0 hϖ1 hchart hlabel hjets hLbC hLjet K' hK'
  have hE : 0 < E := lt_of_lt_of_le hρ hρE
  have hdstar : 0 ≤ dstar := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg _)
  refine means_seminorm_le hB hdstar hρ hdρ hρE (mul_nonneg hCt hMb) K' T₀ T₁
    (fun d => ceLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lb r v u d) ?_
  intro d j hj t ht x
  have hd2 := Finset.mem_Icc.1 d.2
  have hsum : ∑ k ∈ kset, |ϖ k t| = 1 := by
    rw [← hϖ1 t ht]
    exact Finset.sum_congr rfl fun k hk => abs_of_nonneg (hϖ0 k hk t)
  have h1 := htr kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (ρ / E) E chart label s₀ s₁ Lb r v u Mb t
    (pow_pos hℓ 2) hρ (div_nonneg hdstar hρ.le) hE rfl hMb
    (fun k hk => hchart k hk t) (fun k hk => hlabel k hk t)
    (fun k hk hwin p hp1 hpN y => hjets k hk t ht hwin p hp1 hpN y) hLbC hLjet d j
    (hj.trans hK') x
  refine h1.trans (le_of_eq ?_)
  rw [hsum, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn2 : 2 ≤ n := hd2.1.trans (Finset.mem_Icc.1 hn).1
  rw [dimensional_conversion hℓ hB.le hρ hd hn2]

end AVRegularity.CycleComparison.Assembly
end
end

section
/-! Clause 4 of `cycle_comparison` for the Eulerian diagonal letter `adLetter`: the normalized
size `α_R = ∑_d 𝒜_{R,N}(AD_d)/(B R^{d-2})` of the diagonal perturbation relative to the
reference flux: higher diagonal means cost `C ε_c^{n-2}`, hence
`α_R ≤ C(g_m + d_sw + ∑_{n=3}^{N'+1} ε_c^{n-2})`.

From the transfer bound `adLetter_transfer`, at the radius `R = ρ ≤ E`:
* the letters of order `n ≥ 3` cost `ℓ⁻² d_*ⁿ E^{-(n-d)}/(B R^{d-2}) ≤ ε_c` each;
* the order two costs `(θ + C_J g)/B`, where `θ` bounds `B L₂₂ + 𝖩` on the lift windows and
  `C_J g` is the Piola deformation of the reference flux. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleComparison.Assembly

open AVRegularity.CycleComparison.ActualMeans

/-- The grading of a higher order: `x^{n-2} E^{-(n-d)} ≤ (x/R) R^{d-2}` for `x ≤ R ≤ E`,
`2 ≤ d ≤ n`, `3 ≤ n`. -/
theorem diag_power_le {x R E : ℝ} (hx : 0 ≤ x) (hR : 0 < R) (hxR : x ≤ R) (hRE : R ≤ E)
    {d n : ℕ} (hd2 : 2 ≤ d) (hdn : d ≤ n) (hn3 : 3 ≤ n) :
    x ^ (n - 2) * E⁻¹ ^ (n - d) ≤ x / R * R ^ (d - 2) := by
  have hE : 0 < E := lt_of_lt_of_le hR hRE
  have hxE : x * E⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hE).2 (hxR.trans hRE)
  have hxE0 : 0 ≤ x * E⁻¹ := mul_nonneg hx (inv_nonneg.2 hE.le)
  rcases Nat.lt_or_ge d 3 with hd | hd
  · obtain rfl : d = 2 := by omega
    rw [← mul_pow, Nat.sub_self, pow_zero, mul_one]
    calc (x * E⁻¹) ^ (n - 2) ≤ x * E⁻¹ := pow_le_of_le_one hxE0 hxE (by omega)
      _ ≤ x * R⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hR hRE) hx
      _ = x / R := (div_eq_mul_inv x R).symm
  · obtain ⟨a, rfl⟩ : ∃ a, n = d + a := ⟨n - d, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, d = b + 3 := ⟨d - 3, by omega⟩
    have e1 : b + 3 + a - 2 = a + b + 1 := by omega
    have e2 : b + 3 + a - (b + 3) = a := by omega
    have e3 : b + 3 - 2 = b + 1 := by omega
    rw [e1, e2, e3]
    have h1 : (x * E⁻¹) ^ a ≤ 1 := pow_le_one₀ hxE0 hxE
    have h2 : x ^ b ≤ R ^ b := pow_le_pow_left₀ hx hxR b
    have e4 : x / R * R ^ (b + 1) = R ^ b * x := by
      calc x / R * R ^ (b + 1) = R ^ b * x * (R⁻¹ * R) := by
            rw [div_eq_mul_inv, pow_succ]
            ring
        _ = R ^ b * x := by rw [inv_mul_cancel₀ hR.ne', mul_one]
    rw [e4]
    calc x ^ (a + b + 1) * E⁻¹ ^ a = (x * E⁻¹) ^ a * (x ^ b * x) := by ring
      _ ≤ 1 * (R ^ b * x) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hx) (by positivity) zero_le_one
      _ = R ^ b * x := one_mul _

/-- One order of the diagonal letter, normalized at the radius `R = ρ`. -/
theorem diag_order_term_le {ℓ B dstar ρ E : ℝ} (hℓ : 0 < ℓ) (hB : 0 < B) (hρ : 0 < ρ)
    (hd : dstar = ℓ * Real.sqrt B) (hdρ : dstar ≤ ρ) (hρE : ρ ≤ E) {d n : ℕ} (hd2 : 2 ≤ d)
    (hdn : d ≤ n) :
    (if n = 2 then 0 else (ℓ ^ 2)⁻¹ * (dstar / ρ * ρ) ^ n * E⁻¹ ^ (n - d)) ≤
      dstar / ρ * (B * ρ ^ (d - 2)) := by
  have hdstar : 0 ≤ dstar := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg _)
  by_cases hn : n = 2
  · rw [ite_eq_left hn]
    positivity
  · rw [ite_eq_right hn, dimensional_conversion hℓ hB.le hρ hd (by omega)]
    have h := diag_power_le hdstar hρ hdρ hρE hd2 hdn (by omega)
    calc B * dstar ^ (n - 2) * E⁻¹ ^ (n - d) = B * (dstar ^ (n - 2) * E⁻¹ ^ (n - d)) := by ring
      _ ≤ B * (dstar / ρ * ρ ^ (d - 2)) := mul_le_mul_of_nonneg_left h hB.le
      _ = dstar / ρ * (B * ρ ^ (d - 2)) := by ring

/-- `ℓ⁻² ε_c² ρ² = B` for `ε_c = d_*/ρ`, `d_* = ℓ√B`. -/
theorem order_two_factor {ℓ B dstar ρ : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hd : dstar = ℓ * Real.sqrt B) : (ℓ ^ 2)⁻¹ * (dstar / ρ) ^ 2 * ρ ^ 2 = B := by
  have h := dimensional_conversion hℓ hB hρ hd (n := 2) le_rfl
  rw [mul_pow, Nat.sub_self, pow_zero, mul_one, ← mul_assoc] at h
  exact h

/-- **Clause 4 for the diagonal letter.** -/
theorem adLetter_means_bound (N D Kt : ℕ) (Cχ : ℕ → ℝ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (ℓ B dstar ρ E T₀ T₁ : ℝ)
      (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
      (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
      (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A₃ θ g CJ : ℝ),
      2 ≤ N + D → 0 < ℓ → 0 < B → 0 < ρ → dstar = ℓ * Real.sqrt B → dstar ≤ ρ → ρ ≤ E →
      0 ≤ A₃ → 0 ≤ θ → 0 ≤ g → 0 ≤ CJ →
      (∀ k ∈ kset, ∀ t, 0 ≤ ϖ k t) → (∀ t ∈ Set.Icc T₀ T₁, ∑ k ∈ kset, ϖ k t = 1) →
      (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, ϖ k t ≠ 0 → (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k)) →
      (∀ k ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (chart k t)) →
      (∀ k ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (label k t)) →
      (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
        ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
        ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * E⁻¹ ^ (p - 1) ∧
        ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * E⁻¹ ^ (p - 1)) →
      (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
        ∀ a b : Fin 2, ScaledJet Kt E
          (fun y => jacMatrix (chart k t) y a b - (if a = b then 1 else 0)) g) →
      (∀ t ∈ Set.Icc T₀ T₁, ∀ a b, |Jm t a b| ≤ CJ) →
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
          ContDiff ℝ (Kt : ℕ∞) (Lsc k n d α l s)) →
      (∀ k ∈ kset, ∀ n, 3 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ i, i ≤ Kt →
          ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            ‖iteratedFDeriv ℝ i (Lsc k n d α l s) X‖ ≤ A₃ * (ρ / E) ^ (n - d + i)) →
      (∀ k ∈ kset, ∀ (α : DerivativeWord2 1) (l : Fin 2), ∀ i, i ≤ Kt →
        ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
          ‖iteratedFDeriv ℝ i
            (fun X' => B * Lsc k 2 2 α l s X' + Jm (ℓ ^ 2 * s) l (α 0)) X‖ ≤
              θ * (ρ / E) ^ i) →
      ∀ K' : ℕ, K' ≤ Kt →
        ∑ d : Finset.Icc 2 (N + D), coefficientSeminorm ρ K' T₀ T₁
            (adLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lsc Jm d) *
            (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹ ≤
          ENNReal.ofReal (Ca * ((N + D : ℕ) : ℝ) * ((K' : ℝ) + 1) *
            (A₃ * ((N + D : ℕ) : ℝ) * (dstar / ρ) + (θ + CJ * g) / B)) := by
  obtain ⟨C, hC, htr⟩ := adLetter_transfer N D Kt Cχ
  refine ⟨C, hC, ?_⟩
  intro kset ϖ ℓ B dstar ρ E T₀ T₁ chart label s₀ s₁ Lsc Jm A₃ θ g CJ hM hℓ hB hρ hd hdρ hρE hA
    hθ hg hCJ hϖ0 hϖ1 hsupp hchart hlabel hjets hdev hJb hLC hL3 hL2 K' hK'
  have hE : 0 < E := lt_of_lt_of_le hρ hρE
  have hdstar : 0 ≤ dstar := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg _)
  have hεc : 0 ≤ dstar / ρ := div_nonneg hdstar hρ.le
  have h2 := order_two_factor hℓ hB.le hρ hd
  set w : ℝ := C * (A₃ * ((N + D : ℕ) : ℝ) * (dstar / ρ) + (θ + CJ * g) / B) with hw_def
  have hw : 0 ≤ w := mul_nonneg hC (add_nonneg (by positivity)
    (div_nonneg (add_nonneg hθ (mul_nonneg hCJ hg)) hB.le))
  -- one degree
  have hterm : ∀ d : Finset.Icc 2 (N + D),
      coefficientSeminorm ρ K' T₀ T₁
          (adLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lsc Jm d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹ ≤ ENNReal.ofReal (((K' : ℝ) + 1) * w) := by
    intro d
    have hd2 := Finset.mem_Icc.1 d.2
    refine coefficientSeminorm_mul_inv_le hρ (mul_pos hB (pow_pos hρ _)) hw K' T₀ T₁ _
      fun j hj t ht x => ?_
    have hT := htr kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (ρ / E) E chart label s₀ s₁ Lsc Jm A₃ θ g CJ t hM
      (pow_pos hℓ 2) hρ hεc hE rfl hA hθ hg hCJ (fun k hk => hϖ0 k hk t) (hϖ1 t ht)
      (fun k hk => hsupp k hk t ht) (fun k hk => hchart k hk t) (fun k hk => hlabel k hk t)
      (fun k hk hwin => hjets k hk t ht hwin) (fun k hk hwin => hdev k hk t ht hwin) (hJb t ht)
      hLC hL3
      (fun k hk α l i hi s hs X => by
        rw [h2]
        exact hL2 k hk α l i hi s hs X)
      d j (hj.trans hK') x
    have hρj : ρ ^ j ≤ E ^ j := pow_le_pow_left₀ hρ.le hρE j
    have hS : ∑ n ∈ Finset.Icc d.1 (N + D),
        (if n = 2 then 0 else (ℓ ^ 2)⁻¹ * (dstar / ρ * ρ) ^ n * E⁻¹ ^ (n - d.1)) ≤
          ((N + D : ℕ) : ℝ) * (dstar / ρ * (B * ρ ^ (d.1 - 2))) := by
      calc ∑ n ∈ Finset.Icc d.1 (N + D),
            (if n = 2 then 0 else (ℓ ^ 2)⁻¹ * (dstar / ρ * ρ) ^ n * E⁻¹ ^ (n - d.1))
          ≤ ∑ _n ∈ Finset.Icc d.1 (N + D), dstar / ρ * (B * ρ ^ (d.1 - 2)) :=
            Finset.sum_le_sum fun n hn =>
              diag_order_term_le hℓ hB hρ hd hdρ hρE hd2.1 (Finset.mem_Icc.1 hn).1
        _ = ((Finset.Icc d.1 (N + D)).card : ℝ) * (dstar / ρ * (B * ρ ^ (d.1 - 2))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((N + D : ℕ) : ℝ) * (dstar / ρ * (B * ρ ^ (d.1 - 2))) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [Nat.card_Icc]
            exact_mod_cast (by omega : N + D + 1 - d.1 ≤ N + D)
    have hJ : (if d.1 = 2 then θ + CJ * g else 0) ≤ (θ + CJ * g) / B * (B * ρ ^ (d.1 - 2)) := by
      by_cases hd2' : d.1 = 2
      · rw [ite_eq_left hd2', hd2', Nat.sub_self, pow_zero, mul_one,
          div_mul_cancel₀ _ hB.ne']
      · rw [ite_eq_right hd2']
        exact mul_nonneg (div_nonneg (add_nonneg hθ (mul_nonneg hCJ hg)) hB.le)
          (mul_nonneg hB.le (pow_nonneg hρ.le _))
    calc ρ ^ j * ‖coefficientDerivativeArray
          (adLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lsc Jm d t) j x‖
        ≤ E ^ j * ‖coefficientDerivativeArray
          (adLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lsc Jm d t) j x‖ :=
          mul_le_mul_of_nonneg_right hρj (norm_nonneg _)
      _ ≤ C * (A₃ * (∑ n ∈ Finset.Icc d.1 (N + D),
            if n = 2 then 0 else (ℓ ^ 2)⁻¹ * (dstar / ρ * ρ) ^ n * E⁻¹ ^ (n - d.1)) +
            if d.1 = 2 then θ + CJ * g else 0) := hT
      _ ≤ C * (A₃ * (((N + D : ℕ) : ℝ) * (dstar / ρ * (B * ρ ^ (d.1 - 2)))) +
            (θ + CJ * g) / B * (B * ρ ^ (d.1 - 2))) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hS hA) hJ) hC
      _ = w * (B * ρ ^ (d.1 - 2)) := by
          rw [hw_def]
          ring
  refine (Finset.sum_le_sum fun d _ => hterm d).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast (N + D + 1 - 2), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : ((N + D + 1 - 2 : ℕ) : ℝ) ≤ ((N + D : ℕ) : ℝ) := by
    exact_mod_cast (by omega : N + D + 1 - 2 ≤ N + D)
  calc ((N + D + 1 - 2 : ℕ) : ℝ) * (((K' : ℝ) + 1) * w)
      ≤ ((N + D : ℕ) : ℝ) * (((K' : ℝ) + 1) * w) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) hw)
    _ = C * ((N + D : ℕ) : ℝ) * ((K' : ℝ) + 1) *
          (A₃ * ((N + D : ℕ) : ℝ) * (dstar / ρ) + (θ + CJ * g) / B) := by
        rw [hw_def]
        ring

end AVRegularity.CycleComparison.Assembly
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Assembly

/-! The pulse data of the construction as data of the means stage: slow `ρ⁻¹ℤ²`-periodicity of
the material metric and of the lifted source coefficients (torus compatibility, one of the chart
and quiet hypotheses), and the partition facts of
`IsLiftPartition` in the form used by the stage. -/

/-- `ρ • (X + ρ⁻¹ • s) = ρ • X + s`. -/
theorem smul_add_inv_smul {ρ : ℝ} (hρ : ρ ≠ 0) (X s : Vec 2) :
    ρ • (X + ρ⁻¹ • s) = ρ • X + s := by
  rw [smul_add, smul_smul, mul_inv_cancel₀ hρ, one_smul]

/-- The material metric of a renewal chart is `ℤ²`-periodic. -/
theorem ocMaterialMetric_latticeShift (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (t : ℝ) (p : Fin 2 → ℤ) (y : Vec 2) :
    ocMaterialMetric α q Λ m φ hφ l t (y + latticeShift p) =
      ocMaterialMetric α q Λ m φ hφ l t y := by
  unfold ocMaterialMetric
  rw [ActualMeans.jacMatrix_shift (latticeShift p)
    (fun y' => Charts.ocChart_latticeShift hφ α q Λ m l t p y') y]

/-- The metric of the lift data of a pulse is periodic in the slow variable. -/
theorem pulseLiftData_G_shift {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (ν B : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (lam : ℝ) (k : ℤ)
    (edge : ConstituentEdges D h) (p : Fin 2 → ℤ) (t : ℝ) (X : Vec 2) (i j : Fin 2) :
    (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).G t (X + ρ⁻¹ • latticeShift p) i j =
      (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).G t X i j := by
  show ocMaterialMetric α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * t)
      (ρ • (X + ρ⁻¹ • latticeShift p)) i j =
    ocMaterialMetric α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * t)
      (ρ • X) i j
  rw [smul_add_inv_smul hρ, ocMaterialMetric_latticeShift]

section Family

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The lifted source coefficients of a torus-compatible family are periodic in the slow
variable. -/
theorem liftEdges_fiber_coeff_shift {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p}
    {E ρ : ℝ} (hρ : ρ ≠ 0) (htorus : IsTorusCompatible F actual E) (c : ℝ)
    (p : P) (s : Fin 2 → ℤ) {v u : ι} {d : Finset.Icc 2 D}
    {γ : Constituent d.1 (h u) (h v)}
    (hγ : γ ∈ liftEdges c (ρ / E) (F.fiber p (actual p)) v u d)
    (w : DerivativeWord2 (d.1 - 1)) (t : ℝ) (X z : Vec 2) :
    γ.coeff w t (X + ρ⁻¹ • latticeShift s) z = γ.coeff w t X z := by
  obtain ⟨γ₀, -, -, hc⟩ := LiftSetting.mem_liftEdges_fiber hγ
  rw [hc]
  have hper := htorus.2 p (c * t) v u γ₀ d.1 w z s (ρ • X)
  have e1 : (ρ / E) • (X + ρ⁻¹ • latticeShift s) = E⁻¹ • (ρ • X + latticeShift s) := by
    rw [← smul_add_inv_smul hρ X (latticeShift s), smul_smul, div_eq_inv_mul]
  have e2 : (ρ / E) • X = E⁻¹ • (ρ • X) := by
    rw [smul_smul, div_eq_inv_mul]
  show F.flux p (actual p) v u γ₀ d.1 w (c * t) ((ρ / E) • (X + ρ⁻¹ • latticeShift s)) z =
    F.flux p (actual p) v u γ₀ d.1 w (c * t) ((ρ / E) • X) z
  rw [e1, e2]
  exact hper

end Family

/-- The partition facts used by the means stage. -/
theorem partition_stage_facts {kset : Finset ℤ} {ϖ : ℤ → ℝ → ℝ} {win : ℤ → Set ℝ}
    {quiet I : Set ℝ} {τ Cpart : ℝ} (hpart : IsLiftPartition kset ϖ win quiet I τ Cpart) :
    (∀ k ∈ kset, ∀ t, 0 ≤ ϖ k t) ∧ (∀ k ∈ kset, Measurable (ϖ k)) ∧
      (∀ t ∈ I, ∑ k ∈ kset, ϖ k t = 1) ∧ (∀ k ∈ kset, ∀ t, ϖ k t ≠ 0 → t ∈ win k) :=
  ⟨hpart.1, fun k hk => (hpart.2.1 k hk).continuous.measurable, hpart.2.2.1, hpart.2.2.2.1⟩

/-- A time of a pulse window and of the observation window is, in cell time, in the clipped
lift window. -/
theorem cellTime_mem_liftWindow {c a b tp tz t : ℝ} (hc : 0 < c) (ht : t ∈ Set.Icc a b)
    (htI : t ∈ Set.Icc tp tz) : c⁻¹ * t ∈ Set.Icc (max a tp / c) (min b tz / c) := by
  have e : c⁻¹ * t = t / c := by rw [div_eq_inv_mul]
  rw [e]
  exact ⟨div_le_div_of_nonneg_right (max_le ht.1 htI.1) hc.le,
    div_le_div_of_nonneg_right (le_min ht.2 htI.2) hc.le⟩

/-- A cell time of the clipped lift window is a time of the pulse window and of the observation
window. -/
theorem mem_window_of_cellTime {c a b tp tz t : ℝ} (hc : 0 < c)
    (ht : c⁻¹ * t ∈ Set.Icc (max a tp / c) (min b tz / c)) :
    t ∈ Set.Icc a b ∩ Set.Icc tp tz := by
  have h := LiftSetting.mul_mem_inter_of_mem_Icc hc ht
  rwa [mul_inv_cancel_left₀ hc.ne'] at h

end AVRegularity.CycleComparison.Assembly
end
end
