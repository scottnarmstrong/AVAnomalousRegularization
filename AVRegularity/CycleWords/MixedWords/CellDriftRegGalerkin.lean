-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.MixedWordsB1Transfer
import AVRegularity.CycleWords.MixedWords.B1WSourceL2
import AVRegularity.CycleWords.ConstructedFullGalerkinAllOrderEnergy
public import AVRegularity.CycleWords.CellEnergyJointH1Trace

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Smallness-free estimates of the reduced transverse equation on a transverse window

A transverse weak solution of the full fibre equation of a shear drift (no perpendicular
component) solves the reduced scalar-multiplier equation
(`cellTransverse_actual_reduced_weak_curve`). So the smallness-free regularity
`TransverseRegularityStatement` gives growth, smoothing and the deviation from `1` for it
(`transverse_full_regularity`). On the buffered window of a region the package's extension
`ext p` is the actual drift (`ext_agree`), hence smooth with jets bounded by `K.Cvj`
(`ext_window_contDiff`, `ext_window_jets`); it is a shear for all times (`ext_perp_zero`,
`ext_parallel_invariant`). -/

/-- **Transverse regularity for transverse full-equation curves of a smooth shear drift.** -/
theorem transverse_full_regularity (hR : TransverseRegularityStatement) (j : ℕ) (ρ Cw : ℝ)
    (J : ℕ → ℝ) (hρ : 0 ≤ ρ) (hCw : 0 ≤ Cw) (hJ : ∀ l, 0 ≤ J l) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
      {w : ℝ → Vec 2 → Vec 2} (hw : IsCellDrift w)
      (_hww : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw) (ξ : Fin 2 → ℂ)
      (e : Fin 2), (∀ t x, w t x e.rev = 0) →
      a ≤ b → 0 ≤ η → η ≤ 1 → (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ ρ →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (w t)) →
      (∀ (l : ℕ) t, t ∈ Set.Icc a b → ∀ x,
        ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • w t x) x‖ ≤ J l) →
    ∀ (V : ℝ) (hb : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
      (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun t =>
        cellDualDerivative ⟨fun t _ => G t, w, fun k => (Real.sqrt η : ℂ) * ξ k, 0⟩
          hG V hw.1 hb t (slice t) 0 0) →
      (∀ t ∈ Set.Icc a b, cellTransverseProjection e (u t) = u t) →
      (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b, t ≤ a + 1 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t ∧ ‖w'‖ ≤ C * ‖w₀‖) ∧
      (∀ t ∈ Set.Icc a b, a + 1 ≤ t → t ≤ a + 2 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t ∧ ‖w'‖ ≤ C * ‖u a‖) ∧
      (u a = cellConstantCLM 1 → ∀ t ∈ Set.Icc a b, t ≤ a + 2 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t - cellConstantCLM 1 ∧
          ‖w'‖ ≤ C * fibreNorm ξ) := by
  obtain ⟨C, hC, h⟩ := hR j ρ Cw J hρ hCw hJ
  refine ⟨C, hC, ?_⟩
  intro a b η G hG w hw hww ξ e hperp hab hη0 hη hreal hξ hcont hjets V hb u slice hu hfix
  have hred := cellTransverse_actual_reduced_weak_curve η Cw hCw G hG hw hww V hb e hperp ξ 0
    u slice hu (ae_restrict_of_forall_mem measurableSet_Icc hfix)
  exact h a b η hCw G hG hw hww ξ hab hη0 hη hreal hξ hcont hjets u slice hred

variable {K : ScalarConstants} {η t₀ S ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {reg : BlockRegions}

/-- The extension of a region has no perpendicular component. -/
theorem ext_perp_zero (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (p : Fin reg.P) (t : ℝ)
    (x : Vec 2) : pkg.ext p t x (reg.orient p).rev = 0 := by
  obtain ⟨V, hV⟩ := pkg.ext_shear p
  rw [hV t x]
  have hne : ∀ e : Fin 2, e.rev ≠ e := by decide
  simp [basisVec_apply, hne (reg.orient p)]

/-- The extension of a region is invariant along its orientation. -/
theorem ext_parallel_invariant (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (p : Fin reg.P)
    (t : ℝ) (z : Vec 2) (s : ℝ) :
    pkg.ext p t (z + s • basisVec (reg.orient p)) = pkg.ext p t z := by
  obtain ⟨V, hV⟩ := pkg.ext_shear p
  exact shear_drift_parallel_invariant (pkg.ext p) (reg.orient p) V hV t z s

/-- On the buffered window the extension is smooth. -/
theorem ext_window_contDiff (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (p : Fin reg.P)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) :
    ∀ t ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer),
      ContDiff ℝ (⊤ : ℕ∞) (pkg.ext p t) := by
  intro t ht
  have he : pkg.ext p t = v t := funext fun z => pkg.ext_agree p t ht z
  rw [he]
  exact hvs t

/-- On the buffered window the extension has the jets of the actual drift. -/
theorem ext_window_jets (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (p : Fin reg.P)
    (hvj : ∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) :
    ∀ (l : ℕ) t, t ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • pkg.ext p t x) x‖ ≤ K.Cvj l := by
  intro l t ht x
  have he : (fun x => Real.sqrt η • pkg.ext p t x) = fun x => Real.sqrt η • v t x :=
    funext fun z => by rw [pkg.ext_agree p t ht z]
  rw [he]
  exact hvj l t x

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # steps of the polynomial regularity of the cell equation with a smooth drift (statements)

Statements only.  Every `Step` below is a `Prop`; the module of the proof is named in its docstring.
The drift `v` is a general divergence-free drift whose jets of order `≤ J` on `[a, b]` are at most
`P ≥ 1` (`P = 1 + L` in the final statement); `peFactor η` of the constructed chain is replaced by
`P`.  The cell coefficients are `⟨fun s _ => G s, v, θ, 0⟩` (no potential, `κ = 0`).

Chain (as for the constructed drift, with the drift replaced by the jet hypothesis):
`GalerkinEnergy` → `GalerkinWindow` → `GalerkinSmoothing` (with `GalerkinContraction` for the zeroth
bound) → `WeakShort`, `WeakSmoothing` (with `WeakContraction`) → `cellDriftRegularity`. -/

/-- Smoothness and jet bounds of order `≤ J` of the drift on `[a, b]`. -/
def DriftJets (v : ℝ → Vec 2 → Vec 2) (a b P : ℝ) (J : ℕ) : Prop :=
  (∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) ∧
    ∀ l : ℕ, l ≤ J → ∀ t ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ P

/-- Universal native price of a multiplier with jets `≤ 1` on `TorusHk K` (copy of
`constructedEntryUniversalNativePrice` with the spatial jet price `1`). -/
def cellDriftNativePrice (K : ℕ) : ℝ :=
  (∑ l : Fin (K + 1), factorialRootWeight 1 l.val *
      ((Fintype.card (DerivativeWord2 l.val) : ℝ) * ‖realScalarMultiplierMap‖)) *
    Real.sqrt (factorialWeightMax 1 K) / Real.sqrt (factorialWeightMin 1 K)

/-- Order price (the coefficient of `P ^ 2` in the growth of the order-`K` energy), shift `≤ R`,
no potential. -/
def cellDriftOrderPrice : ℕ → ℝ → ℝ
  | 0, R => 528 * R ^ 2 + 6 * R + 1 / 2
  | K + 1, R => 528 * R ^ 2 + 1 / 4 + 4 * (2 * cellDriftNativePrice (K + 1) *
      (1 + R * (1 + ‖torusHigherScalarCLM (K + 1) Complex.I‖))) ^ 2 + 1 / 2

/-- Common window price for the orders `≤ J`. -/
def cellDriftWindowPrice (J : ℕ) (R : ℝ) : ℝ :=
  1 + ∑ K : Fin (J + 1), cellDriftOrderPrice K.val R

/-- Common smoothing time: `1 / ((J + 1) M P²)`. -/
def cellDriftSmoothingTime (J : ℕ) (R P : ℝ) : ℝ :=
  1 / (((J : ℝ) + 1) * cellDriftWindowPrice J R * P ^ 2)

/-- **Step 1.** Order-`K` Galerkin energy inequality with growth `cellDriftOrderPrice K R * P²`:
copy of `constructedFullGalerkin_all_order_energy`, the drift multiplier bounded by jets `≤ P`. -/
def GalerkinEnergy : Prop :=
  ∀ (K N : ℕ) (R P : ℝ), 0 ≤ R → 1 ≤ P →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (a b t : ℝ) (_ : t ∈ Icc a b)
    (_ : DriftJets v a b P K) (θ : Fin 2 → ℂ) (_ : ∀ i, ‖θ i‖ ≤ R)
    (u : CellGalerkinSpace (E := ℂ) N),
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K (cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G s, v, θ, 0⟩ hG V hv.1 hb t) u)) (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      cellDriftOrderPrice K R * P ^ 2 * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2

/-- **Step 2 (from Step 1).** Short window for all orders `K ≤ J`: copy of
`constructedFullGalerkin_native_window`. -/
def GalerkinWindow : Prop :=
  ∀ (J N : ℕ) (R P : ℝ), 0 ≤ R → 1 ≤ P →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ) (_ : ∀ i, ‖θ i‖ ≤ R)
    {a b : ℝ} (_ : a ≤ b) (_ : DriftJets v a b P J) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (_ : StrongTimeRegularity a b y (fun t => cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G s, v, θ, 0⟩ hG V hv.1 hb t) (y t)))
    (_ : cellDriftWindowPrice J R * P ^ 2 * (b - a) ≤ 1),
    ∀ K ≤ J,
      ‖cellGalerkinNativeLiftCLM N K (y b)‖ ^ 2 ≤
        Real.exp 1 * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 ∧
      (∫ t in a..b, ‖cellGalerkinNativeLiftCLM N (K + 1) (y t)‖ ^ 2) ≤
        (2 * Real.exp 1) * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2

/-- **Step 3.** `L²` contraction of the Galerkin curve for a real shift:
`cellDualDerivative_real_energy` and `cellGalerkinOperator_pairing`. -/
def GalerkinContraction : Prop :=
  ∀ (N : ℕ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    {a b : ℝ} (_ : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (_ : StrongTimeRegularity a b y (fun t => cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t) (y t))),
    ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ ‖cellGalerkinValue N (y a)‖ ^ 2

/-- **Step 4 (from Steps 2 and 3).** Time-weighted smoothing on a common frequency disc: copy of
`constructedFullGalerkin_native_smoothing` with the zeroth bound `B` from Step 3. -/
def GalerkinSmoothing : Prop :=
  ∀ (J N : ℕ) (R P : ℝ), 0 ≤ R → 1 ≤ P →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (_ : Real.sqrt (vecDot θ θ) ≤ R)
    {a b : ℝ} (_ : a ≤ b) (_ : DriftJets v a b P J) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (_ : StrongTimeRegularity a b y (fun t => cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t) (y t)))
    (δ : ℝ) (_ : 0 < δ) (_ : cellDriftWindowPrice J R * P ^ 2 * δ ≤ 1) (t : ℝ)
    (_ : a + J * δ ≤ t) (_ : t ≤ b),
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * ‖cellGalerkinValue N (y a)‖ ^ 2

/-- **Step 5.** The weak curve on a short window keeps `H^J`: copy of
`constructedActualWeak_native_short_propagation`. -/
def WeakShort : Prop :=
  ∀ (J : ℕ) (R P : ℝ), 0 ≤ R → 1 ≤ P →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (_ : Real.sqrt (vecDot θ θ) ≤ R)
    {a b : ℝ} (_ : a < b) (_ : DriftJets v a b P J)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (_ : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0))
    (initial : TorusHk J ℂ) (_ : U a = torusHkValueCLM initial)
    (_ : cellDriftWindowPrice J R * P ^ 2 * (b - a) ≤ 1),
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤ Real.exp 1 * ‖initial‖ ^ 2

/-- **Step 6.** Polynomial smoothing of the weak curve from `L²`: copy of
`constructedActualWeak_native_polynomial_smoothing`, the zeroth bound by contraction. -/
def WeakSmoothing : Prop :=
  ∀ (J : ℕ) (R P : ℝ), 0 ≤ R → 1 ≤ P →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (_ : Real.sqrt (vecDot θ θ) ≤ R)
    {a b : ℝ} (_ : a < b) (_ : DriftJets v a b P J)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (_ : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0))
    (_ : b - a ≤ 1) (t : ℝ) (_ : t ∈ Icc a b)
    (_ : a + J * cellDriftSmoothingTime J R P ≤ t),
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧
      ‖W‖ ^ 2 ≤ (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * cellDriftWindowPrice J R * P ^ 2) ^ J *
        ‖U a‖ ^ 2

/-- **Step 7.** `L²` contraction of the weak curve: `CellWeakHilbertCurve.energy_strongTime` and
`cellDualDerivative_real_energy`. -/
def WeakContraction : Prop :=
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    {a b : ℝ} (_ : a ≤ b) (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (_ : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)),
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → ‖U t‖ ≤ ‖U s‖

/-- **Step 8.** (G) and (S) from the weak steps: contraction on
`[a, t - τ]`, then smoothing on `[t - τ, t]` with `τ = J * cellDriftSmoothingTime`; for
`t - a` below the short window, Step 5 directly.  `P = 1 + L`. -/
def DriftRegAssembly : Prop := WeakShort → WeakSmoothing → WeakContraction → CellDriftRegularityStatement

/-! # the `L²` contraction of a weak curve with a real shift

`CellWeakHilbertCurve.energy_increment` on `[s, t]` and `cellDualDerivative_real_energy`
(the transport does no work, the metric is coercive, the real shift is skew). -/

/-- Step 7: the weak curve is `L²` nonincreasing. -/
theorem cellDriftWeakContraction : WeakContraction := by
  intro G hG v hv V hb θ a b hab U slice h s hs t ht hst
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have he := (h.mono hsub).energy_increment hst
  have hint : (∫ r in s..t, 2 * inner ℝ (cellDualDerivative
      ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb r (slice r) 0 0) (slice r)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hst]
    apply integral_nonpos
    intro r
    beta_reduce
    have hr := cellDualDerivative_real_energy (G := fun s _ => G s) hG hv V hb
      (fun k => (θ k : ℂ)) (fun j => Complex.conj_ofReal (θ j)) r (slice r)
    have hn : 0 ≤ (1 / 2) * ∑ j, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice r)‖ ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    show _ ≤ (0 : ℝ)
    linarith
  have h2 : ‖U t‖ ^ 2 ≤ ‖U s‖ ^ 2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- Step 3: the Galerkin curve of a real shift is `L²` nonincreasing. -/
theorem cellDriftGalerkinContraction : GalerkinContraction := by
  intro N G hG v hv V hb θ a b hab y hy
  have hg := (hy.map (cellGalerkinValue N)).norm_sq_le_gronwall hab 0 le_rfl 0
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun _ => by simp only [Pi.zero_apply, le_refl])) (by
      apply Filter.Eventually.of_forall
      intro t
      simp only [Pi.zero_apply, zero_mul, zero_add]
      rw [real_inner_comm, cellGalerkinOperator_pairing]
      have hp : cellGeneratorForm ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
          (y t).val (y t).val =
          inner ℝ (cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
            (y t).val 0 0) (y t).val := by
        rw [cellDualDerivative_pairing]
        change _ = _ + cellSourceFunctional (fun k => (θ k : ℂ)) 0 0 (y t).val
        have hz : cellSourceFunctional (fun k => (θ k : ℂ)) 0 0 (y t).val = 0 :=
          cellSourceFunctional_zero _ _
        rw [hz, add_zero]
      have hr := cellDualDerivative_real_energy (G := fun s _ => G s) hG hv V hb
        (fun k => (θ k : ℂ)) (fun j => Complex.conj_ofReal (θ j)) t (y t).val
      have hn : 0 ≤ (1 / 2) * ∑ j, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (y t).val‖ ^ 2 :=
        mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      change 2 * cellGeneratorForm _ hG V hv.1 hb t (y t).val (y t).val ≤ 0
      linarith)
  intro t ht
  simpa only [Pi.zero_apply, intervalIntegral.integral_zero, add_zero, zero_mul, Real.exp_zero,
    mul_one] using hg t ht

theorem cellDriftOrderPrice_nonneg (K : ℕ) (R : ℝ) (hR : 0 ≤ R) : 0 ≤ cellDriftOrderPrice K R := by
  cases K with
  | zero => unfold cellDriftOrderPrice; positivity
  | succ K =>
    unfold cellDriftOrderPrice
    positivity

theorem cellDriftOrderPrice_le_window {J K : ℕ} (hK : K ≤ J) (R : ℝ) (hR : 0 ≤ R) :
    cellDriftOrderPrice K R ≤ cellDriftWindowPrice J R := by
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin (J + 1) => cellDriftOrderPrice i.val R)
    (fun i _ => cellDriftOrderPrice_nonneg i.val R hR)
    (Finset.mem_univ (⟨K, by omega⟩ : Fin (J + 1)))
  exact hs.trans (le_add_of_nonneg_left (by norm_num))

theorem DriftJets.of_le {v : ℝ → Vec 2 → Vec 2} {a b P : ℝ} {J K : ℕ}
    (h : DriftJets v a b P J) (hK : K ≤ J) : DriftJets v a b P K :=
  ⟨h.1, fun l hl => h.2 l (hl.trans hK)⟩

theorem cellDriftWindowPrice_one_le (J : ℕ) (R : ℝ) (hR : 0 ≤ R) : 1 ≤ cellDriftWindowPrice J R := by
  have hn : ∀ K : ℕ, 0 ≤ cellDriftOrderPrice K R := fun K => cellDriftOrderPrice_nonneg K R hR
  have : 0 ≤ ∑ K : Fin (J + 1), cellDriftOrderPrice K.val R :=
    Finset.sum_nonneg fun K _ => hn K.val
  unfold cellDriftWindowPrice
  linarith

theorem DriftJets.mono {v : ℝ → Vec 2 → Vec 2} {a b a' b' P : ℝ} {J : ℕ}
    (h : DriftJets v a b P J) (ha : a ≤ a') (hb : b' ≤ b) : DriftJets v a' b' P J :=
  ⟨fun t ht => h.1 t ⟨ha.trans ht.1, ht.2.trans hb⟩,
    fun l hl t ht x => h.2 l hl t ⟨ha.trans ht.1, ht.2.trans hb⟩ x⟩


/-- A real shift has coordinates of norm at most `R` when `√(θ·θ) ≤ R`. -/
theorem cellDrift_theta_le {θ : Vec 2} {R : ℝ} (h : Real.sqrt (vecDot θ θ) ≤ R) (i : Fin 2) :
    ‖(fun k => (θ k : ℂ)) i‖ ≤ R := by
  have h0 : θ i ^ 2 ≤ vecDot θ θ := by
    unfold vecDot
    have : ∀ k : Fin 2, 0 ≤ θ k * θ k := fun k => mul_self_nonneg _
    have hs := Finset.single_le_sum (fun k _ => this k) (Finset.mem_univ i)
    simpa [sq] using hs
  have h1 : |θ i| ≤ Real.sqrt (vecDot θ θ) := Real.abs_le_sqrt h0
  simpa [Complex.norm_real] using h1.trans h

/-! # (G) and (S) from the weak steps

For `t - a ≤ τ`, `τ = 1 / (M P²)`, the short window (Step 5); otherwise the smoothing step on
`[t - τ, t]` (Step 6) after the `L²` contraction on `[a, t - τ]` (Step 7).  `P = 1 + L`. -/

theorem cellDriftValue_norm_le {k : ℕ} (U : TorusHk k ℂ) : ‖torusHkValueCLM U‖ ≤ ‖U‖ :=
  PiLp.norm_apply_le U.val (valueIndex2 k)

theorem cellDriftAssembly_aux (r s n p : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hn : 0 ≤ n) (hp : 1 ≤ p) :
    r * n ≤ (r + s + 1) * p * n ∧ (s * p) * n ≤ (r + s + 1) * p * n ∧ n ≤ (r + s + 1) * p * n := by
  have h0 : 0 ≤ p := by linarith
  have h1 : (r + s + 1) * 1 ≤ (r + s + 1) * p := mul_le_mul_of_nonneg_left hp (by linarith)
  have h2 : (r + s + 1) * 1 * n ≤ (r + s + 1) * p * n := mul_le_mul_of_nonneg_right h1 hn
  have h3 : s * p ≤ (r + s + 1) * p := mul_le_mul_of_nonneg_right (by linarith) h0
  refine ⟨?_, mul_le_mul_of_nonneg_right h3 hn, ?_⟩
  · nlinarith [mul_nonneg hs hn, mul_nonneg hr hn]
  · nlinarith [mul_nonneg hs hn, mul_nonneg hr hn]

/-- Steps 5-7 give the statement (Step 8). -/
theorem cellDriftAssembly : DriftRegAssembly := by
  intro hS hSm hC j ρ hρ
  have hM := cellDriftWindowPrice_one_le j ρ hρ
  set M := cellDriftWindowPrice j ρ with hMdef
  set X : ℝ := Real.exp 1 * (2 * Real.exp 1) * ((j : ℝ) + 1) * M with hXdef
  have hX : 0 ≤ X := by
    have := Real.exp_pos 1
    positivity
  have hsqe : 0 ≤ Real.sqrt (Real.exp 1) := Real.sqrt_nonneg _
  have hsqX : 0 ≤ Real.sqrt (X ^ j) := Real.sqrt_nonneg _
  refine ⟨Real.sqrt (Real.exp 1) + Real.sqrt (X ^ j) + 1, j, by positivity, ?_⟩
  intro a b L G hG v hv V hb θ hab hL hθ hsm hjet u slice hu
  set P : ℝ := 1 + L with hPdef
  have hP : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hPj : 1 ≤ P ^ j := one_le_pow₀ hP
  have hJ : DriftJets v a b P j :=
    ⟨hsm, fun l hl t ht x => (hjet l t (by omega) ht x).trans (by linarith)⟩
  have hMP : 1 ≤ M * P ^ 2 := by nlinarith
  have hMP0 : 0 < M * P ^ 2 := by linarith
  set τ : ℝ := 1 / (M * P ^ 2) with hτdef
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := (div_le_one hMP0).mpr hMP
  have hCt := hC G hG hv V hb θ hab u slice hu
  have hT : (j : ℝ) * cellDriftSmoothingTime j ρ P ≤ τ := by
    unfold cellDriftSmoothingTime
    rw [hτdef, ← hMdef]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hMP0]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < (j : ℝ) + 1) hMP0]
  have hsmooth : ∀ t ∈ Icc a b, a + τ ≤ t →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧ ‖w‖ ≤ (Real.sqrt (X ^ j) * P ^ j) * ‖u a‖ := by
    intro t ht hat
    have hlt : t - τ < t := by linarith
    have hsub : Icc (t - τ) t ⊆ Icc a b := Icc_subset_Icc (by linarith) ht.2
    obtain ⟨W, hW1, hW2⟩ := hSm j ρ P hρ hP G hG hv V hb θ hθ hlt (hJ.mono (by linarith) ht.2)
      u slice (hu.mono hsub) (by linarith) t ⟨hlt.le, le_rfl⟩ (by linarith)
    refine ⟨W, hW1, ?_⟩
    have hc : ‖u (t - τ)‖ ≤ ‖u a‖ := hCt a ⟨le_rfl, hab⟩ (t - τ) ⟨by linarith, by linarith [ht.2]⟩ (by linarith)
    have hsq : (Real.sqrt (X ^ j) * P ^ j) ^ 2 = (Real.exp 1 * (2 * Real.exp 1) * ((j : ℝ) + 1) * M * P ^ 2) ^ j := by
      rw [mul_pow, Real.sq_sqrt (pow_nonneg hX j), ← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
    have h2 : ‖W‖ ^ 2 ≤ ((Real.sqrt (X ^ j) * P ^ j) * ‖u a‖) ^ 2 := by
      rw [mul_pow, hsq]
      exact hW2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc 2) (by positivity))
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h2
  constructor
  · intro w₀ hw₀ t ht htle
    rcases lt_or_ge τ (t - a) with hlong | hshort
    · obtain ⟨w, hw1, hw2⟩ := hsmooth t ht (by linarith)
      refine ⟨w, hw1, hw2.trans ?_⟩
      have hua : ‖u a‖ ≤ ‖w₀‖ := by rw [← hw₀]; exact cellDriftValue_norm_le w₀
      calc (Real.sqrt (X ^ j) * P ^ j) * ‖u a‖ ≤ (Real.sqrt (X ^ j) * P ^ j) * ‖w₀‖ :=
            mul_le_mul_of_nonneg_left hua (by positivity)
        _ ≤ _ := by exact (cellDriftAssembly_aux _ _ _ _ hsqe hsqX (norm_nonneg w₀) hPj).2.1
    · rcases eq_or_lt_of_le ht.1 with hta | hta
      · refine ⟨w₀, ?_, ?_⟩
        · rw [hw₀, ← hta]
        · exact (cellDriftAssembly_aux _ _ _ _ hsqe hsqX (norm_nonneg w₀) hPj).2.2
      · have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
        have hprice : M * P ^ 2 * (t - a) ≤ 1 := by
          have := (le_div_iff₀ hMP0).mp (show t - a ≤ 1 / (M * P ^ 2) from hshort)
          linarith
        obtain ⟨W, hW1, hW2⟩ := hS j ρ P hρ hP G hG hv V hb θ hθ hta (hJ.mono le_rfl ht.2) u slice
          (hu.mono hsub) w₀ hw₀.symm hprice
        refine ⟨W, hW1, ?_⟩
        have h2 : ‖W‖ ^ 2 ≤ (Real.sqrt (Real.exp 1) * ‖w₀‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Real.exp_pos 1).le]
          exact hW2
        have h3 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h2
        refine h3.trans ?_
        exact (cellDriftAssembly_aux _ _ _ _ hsqe hsqX (norm_nonneg w₀) hPj).1
  · intro t ht h1 _
    obtain ⟨w, hw1, hw2⟩ := hsmooth t ht (by linarith)
    refine ⟨w, hw1, hw2.trans ?_⟩
    exact (cellDriftAssembly_aux _ _ _ _ hsqe hsqX (norm_nonneg (u a)) hPj).2.1

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords.Assembly

/-! # the transport entry as a multiplier of `TorusHk K`, with jet bounds `≤ P`

Copy of the construction of `constructedDriftEntryNativeCLM` (the coefficient jets, the native
multiplier and its polynomial price), with the concrete drift `ocCellDrift` replaced by a
drift `w` with `‖D^l w(t)‖ ≤ P` for all `t` and `l ≤ K`.  The bound is `cellDriftNativePrice K * P`. -/

/-- Global (in time) smoothness and jet bounds of order `≤ K`. -/
def GlobalJets (w : ℝ → Vec 2 → Vec 2) (P : ℝ) (K : ℕ) : Prop :=
  (∀ t, ContDiff ℝ (⊤ : ℕ∞) (w t)) ∧ ∀ l : ℕ, l ≤ K → ∀ t x, ‖iteratedFDeriv ℝ l (w t) x‖ ≤ P

/-- The transport entry as a pointwise real multiplier. -/
def cdrEntryCoeff (w : ℝ → Vec 2 → Vec 2) (i : Fin 2) (t : ℝ) (x : Vec 2) : ℂ →L[ℝ] ℂ :=
  realScalarMultiplierMap (w t x i)

/-- The unit jet price of the entry multiplier. -/
def cdrEntryJet (n : ℕ) : ℝ := (Fintype.card (DerivativeWord2 n) : ℝ) * ‖realScalarMultiplierMap‖

theorem cdrEntryJet_nonneg (n : ℕ) : 0 ≤ cdrEntryJet n := by
  unfold cdrEntryJet
  positivity

theorem cdrEntryCoeff_contDiff {w : ℝ → Vec 2 → Vec 2} {P : ℝ} {K : ℕ} (hJ : GlobalJets w P K)
    (i : Fin 2) (t : ℝ) (n : ℕ) : ContDiff ℝ (n : ℕ) (cdrEntryCoeff w i t) := by
  have hv : ContDiff ℝ (n : ℕ) (w t) := (hJ.1 t).of_le (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  exact realScalarMultiplierMap.contDiff.comp ((contDiff_apply ℝ ℝ i).comp hv)

theorem cdrEntryCoeff_periodic {w : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift w) (i : Fin 2) (t : ℝ) :
    IsZ2Periodic (cdrEntryCoeff w i t) := by
  intro k x
  unfold cdrEntryCoeff
  rw [hv.2.2.1 t k x]

theorem cdrComponent_jet_le {w : ℝ → Vec 2 → Vec 2} {P : ℝ} {K : ℕ} (hJ : GlobalJets w P K)
    (i : Fin 2) (t : ℝ) {n : ℕ} (hn : n ≤ K) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y => w t y i) x‖ ≤ P := by
  have hv : ContDiff ℝ (n : ℕ) (w t) := (hJ.1 t).of_le (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  let g : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hg : ‖g‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun y => by simpa [g] using norm_le_pi_norm y i)
  have hj := g.norm_iteratedFDeriv_comp_left (x := x) hv.contDiffAt le_rfl
  have hc : (fun y => w t y i) = g ∘ (w t) := rfl
  rw [hc]
  exact hj.trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans
    (by rw [one_mul]; exact hJ.2 n hn t x))

theorem cdrEntryCoeff_array_bound {w : ℝ → Vec 2 → Vec 2} {P : ℝ} {K : ℕ} (hJ : GlobalJets w P K)
    (i : Fin 2) (t : ℝ) {n : ℕ} (hn : n ≤ K) (x : Vec 2) :
    ‖coefficientDerivativeArray (cdrEntryCoeff w i t) n x‖ ≤ cdrEntryJet n * P := by
  have hv : ContDiff ℝ (n : ℕ) (fun y => w t y i) := by
    simpa only [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp
      ((hJ.1 t).of_le (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)))
  have hb := realScalarMultiplier_jet_array_bound _ n hv x
  exact hb.trans (by
    unfold cdrEntryJet
    exact mul_le_mul_of_nonneg_left (cdrComponent_jet_le hJ i t hn x) (by positivity))

/-- The entry multiplier on `TorusHk K`. -/
def cdrEntryCLM (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ} (hJ : GlobalJets w P K)
    (hv : IsCellDrift w) (i : Fin 2) (t : ℝ) : TorusHk K ℂ →L[ℝ] TorusHk K ℂ :=
  KernelEnergy.torusMultiplierCLM (cdrEntryCoeff w i t) (cdrEntryCoeff_contDiff hJ i t K)
    (cdrEntryCoeff_periodic hv i t) (fun l => cdrEntryJet l.val * P)
    (fun l x => cdrEntryCoeff_array_bound hJ i t (Nat.lt_succ_iff.mp l.2) x) 1 (by norm_num)

theorem cdrEntryCLM_norm_le (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ} (hJ : GlobalJets w P K)
    (hv : IsCellDrift w) (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    ‖cdrEntryCLM K hJ hv i t U‖ ≤ cellDriftNativePrice K * P * ‖U‖ := by
  have h := KernelEnergy.torusMultiplier_norm_bound (cdrEntryCoeff w i t)
    (cdrEntryCoeff_contDiff hJ i t K) (cdrEntryCoeff_periodic hv i t) (fun l => cdrEntryJet l.val * P)
    (fun l x => cdrEntryCoeff_array_bound hJ i t (Nat.lt_succ_iff.mp l.2) x) 1 (by norm_num) U
  refine h.trans (le_of_eq ?_)
  unfold cellDriftNativePrice cdrEntryJet
  simp only [← mul_assoc, ← Finset.sum_mul]
  ring

theorem cdrEntryCLM_value (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ} (hJ : GlobalJets w P K)
    (hv : IsCellDrift w) (V : ℝ) (hb : ∀ t x, ∑ j, w t x j ^ 2 ≤ V ^ 2)
    (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    torusHkValueCLM (cdrEntryCLM K hJ hv i t U) =
      cellDriftEntryCLM ⟨0, w, 0, 0⟩ V hv.1 hb t i (torusHkValueCLM U) := by
  apply Lp.ext
  have hl := torusMulCoefficient_value_ae U (cdrEntryCoeff w i t)
    (cdrEntryCoeff_contDiff hJ i t K) (cdrEntryCoeff_periodic hv i t)
    (A := fun l => cdrEntryJet l.val * P)
    (fun l x => cdrEntryCoeff_array_bound hJ i t (Nat.lt_succ_iff.mp l.2) x)
  have hr := cellDriftEntryCLM_ae ⟨0, w, 0, 0⟩ V hv.1 hb t i (torusHkValueCLM U)
  filter_upwards [hl, hr] with x hl hr
  exact hl.trans hr.symm

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # higher-order energy of the full generator with a drift of jets `≤ P`

Copies of `constructedHigherAdvectionCLM`, `constructedHigherFullGeneratorCLM`,
`constructedHigherAdvectionCLM_adjacent_polynomial_bound`,
`constructedHigherFullGeneratorCLM_pairing` and `constructedHigherFullGenerator_smooth_energy`, with
`ocCellDrift` replaced by a drift `w` with `GlobalJets w P K` and `peFactor` by `P`. -/

/-- The transport term on `TorusHk (K + 2)`. -/
def cdrAdvectionCLM (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ} (hJ : GlobalJets w P K)
    (hv : IsCellDrift w) (θ : Fin 2 → ℂ) (t : ℝ) : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  ∑ i : Fin 2, (cdrEntryCLM K hJ hv i t).comp (torusHigherShiftedFirstCLM K θ i)

theorem cdrAdvectionCLM_value (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ} (hJ : GlobalJets w P K)
    (hv : IsCellDrift w) (V : ℝ) (hb : ∀ t x, ∑ j, w t x j ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (cdrAdvectionCLM K hJ hv θ t U) =
      ∑ i : Fin 2, cellDriftEntryCLM ⟨0, w, 0, 0⟩ V hv.1 hb t i
        (cellShiftedDerivativeCLM θ i
          (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U))) := by
  simp only [cdrAdvectionCLM, Fin.sum_univ_two, add_apply,
    ContinuousLinearMap.comp_apply, map_add, cdrEntryCLM_value K hJ hv V hb,
    torusHigherShiftedFirstCLM_value]

/-- The full generator on `TorusHk (K + 2)`. -/
def cdrFullGeneratorCLM (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ} (hJ : GlobalJets w P K)
    (hv : IsCellDrift w) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) :
    TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  torusHigherStrongDiffusionCLM K G θ t - cdrAdvectionCLM K hJ hv θ t +
    (torusHigherScalarCLM K (κ t)).comp (truncateTorusHk (by omega : K ≤ K + 2))

/-- Price of the transport term against one higher reserve (without the factor `P`). -/
def cdrAdvPrice (K : ℕ) (R : ℝ) : ℝ :=
  2 * cellDriftNativePrice K * (1 + R * (1 + ‖torusHigherScalarCLM K Complex.I‖))

theorem cdrAdvectionCLM_adjacent_bound (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hP : 0 ≤ P) (hv : IsCellDrift w)
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R) (t : ℝ) (U : TorusHk (K + 2) ℂ) :
    ‖cdrAdvectionCLM K hJ hv θ t U‖ ≤
      (cdrAdvPrice K R * P) * ‖truncateTorusHk (by omega : K + 1 ≤ K + 2) U‖ := by
  have hp : 0 ≤ cellDriftNativePrice K * P := by
    have h : 0 ≤ cellDriftNativePrice K := by
      unfold cellDriftNativePrice
      refine div_nonneg (mul_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg
        (by unfold factorialRootWeight; positivity) (cdrEntryJet_nonneg l.val)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    exact mul_nonneg h hP
  have hi (i : Fin 2) :
      ‖(cdrEntryCLM K hJ hv i t) (torusHigherShiftedFirstCLM K θ i U)‖ ≤
      (cellDriftNativePrice K * P) *
        ((1 + R * (1 + ‖torusHigherScalarCLM K Complex.I‖)) *
          ‖truncateTorusHk (by omega : K + 1 ≤ K + 2) U‖) :=
    (cdrEntryCLM_norm_le K hJ hv i t _).trans
      (mul_le_mul_of_nonneg_left (torusHigherShiftedFirstCLM_adjacent_bound K θ R hθ i U) hp)
  simp only [cdrAdvectionCLM, Fin.sum_univ_two, add_apply, ContinuousLinearMap.comp_apply]
  exact ((norm_add_le _ _).trans (add_le_add (hi 0) (hi 1))).trans_eq
    (by unfold cdrAdvPrice; ring)

theorem cdrFullGeneratorCLM_pairing (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hv : IsCellDrift w)
    (V : ℝ) (hb : ∀ t x, ∑ j, w t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) (z : TorusHk 1 ℂ) :
    inner ℝ (torusHkValueCLM (cdrFullGeneratorCLM K hJ hv G θ κ t U))
      (torusHkValueCLM z) =
    cellGeneratorForm ⟨fun t _ => G t, w, θ, κ⟩ hG V hv.1 hb t
      (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U)) z := by
  let C : CellCoefficients := ⟨fun t _ => G t, w, θ, κ⟩
  let u := truncateTorusHk (by omega : 2 ≤ K + 2) U
  have hd : cellDiffusionForm C hG t (cellH2BaseCLM u) z =
      inner ℝ (cellConstantMetricStrongDiffusionCLM G θ t u) (torusHkValueCLM z) := by
    have he := congrArg Complex.re (cellConstantMetricStrongDiffusionCLM_pair G hG θ t u z)
    rw [cellComplexDiffusionForm_real_part C hG, cellComplexPair_re] at he
    exact he
  simp only [cdrFullGeneratorCLM, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, torusHigherStrongDiffusionCLM_value,
    cdrAdvectionCLM_value K hJ hv V hb,
    torusHigherScalarCLM_value, inner_add_left, inner_sub_left, Fin.sum_univ_two]
  change _ = cellGeneratorForm C hG V hv.1 hb t (cellH2BaseCLM u) z
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  rw [hd]
  rfl

/-- Order growth (without potential contribution unless `k > 0`). -/
def cdrGrowth (K : ℕ) (R P k : ℝ) : ℝ :=
  528 * R ^ 2 + 1 / 4 + 4 * (cdrAdvPrice K R * P) ^ 2 +
    2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)

theorem cdrFullGenerator_smooth_energy (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hP : 0 ≤ P) (hv : IsCellDrift w)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : IsZ2Periodic f) :
    2 * inner ℝ
        (cdrFullGeneratorCLM K hJ hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * finiteSmoothHigherGradientEnergy K f hf hp ≤
      cdrGrowth K R P k *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  let U := finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let W := finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let B := ‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖
  let A := cdrAdvPrice K R * P
  have ha := cdrAdvectionCLM_adjacent_bound K hJ hP hv θ R hθ t W
  rw [finiteSmoothPeriodicHk_truncate (K := K + 1) (L := K + 2) (by omega) f hf hp] at ha
  have hy := real_inner_transport_young
    (cdrAdvectionCLM K hJ hv θ t W) U A B ha
  have hb := finiteSmoothHigher_adjacent_energy_le K f hf hp
  have hd := finiteSmoothHigherDiffusion_energy K f hf hp G hG θ t
  have ht : (∑ i : Fin 2, ‖θ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hc : |inner ℝ (torusHigherScalarCLM K (κ t) U) U| ≤
      (k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2 := by
    exact ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (((torusHigherScalarCLM K (κ t)).le_opNorm U).trans
          (mul_le_mul_of_nonneg_right (torusHigherScalarCLM_norm_le K (κ t) k hk) (norm_nonneg U)))
        (norm_nonneg U))).trans_eq (by ring)
  have hdt := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖U‖)
  have hat := neg_le_abs (inner ℝ (cdrAdvectionCLM K hJ hv θ t W) U)
  have hct := le_abs_self (inner ℝ (torusHigherScalarCLM K (κ t) U) U)
  simp only [cdrFullGeneratorCLM, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_sub_left]
  rw [finiteSmoothPeriodicHk_truncate (K := K) (L := K + 2) (by omega) f hf hp]
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U -
    inner ℝ (cdrAdvectionCLM K hJ hv θ t W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤ _
  change 2 * inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U + _ ≤ _ at hd
  change B ^ 2 ≤ ‖U‖ ^ 2 + _ at hb
  unfold cdrGrowth
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U -
    inner ℝ (cdrAdvectionCLM K hJ hv θ t W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤
    (528 * R ^ 2 + 1 / 4 + 4 * A ^ 2 + 2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2
  nlinarith

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # the common short window from the order-`K` energy inequality (Step 2)

Copy of `constructedFullGalerkin_native_window` with `GalerkinEnergy` as a hypothesis. -/

theorem cellDriftGalerkinWindow (hE : GalerkinEnergy) : GalerkinWindow := by
  intro J N R P hR hP G hG v hv V hb θ hθ a b hab hJ y hy hshort K hK
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  let : NormedAddCommGroup (TorusHk (K + 1) ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk (K + 1) ℂ) := inferInstance
  have hM := cellDriftOrderPrice_le_window hK R hR
  have hA : 0 ≤ cellDriftWindowPrice J R * P ^ 2 :=
    mul_nonneg (zero_le_one.trans (cellDriftWindowPrice_one_le J R hR)) (sq_nonneg _)
  apply finiteObservable_short_window_bounds hab hy (cellGalerkinNativeLiftCLM N K)
    (cellGalerkinNativeLiftCLM N (K + 1)) _ hA hshort
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro t ht
  have he := hE K N R P hR hP G hG hv V hb a b t ht (hJ.of_le hK) θ hθ (y t)
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hM (sq_nonneg P)) (sq_nonneg _))

/-! # Galerkin smoothing from the short window (Step 4)

Copy of `constructedFullGalerkin_native_smoothing`, the window lemma being a hypothesis
(`GalerkinWindow`) and the zeroth bound coming from the `L²` contraction (`GalerkinContraction`). -/

theorem cellDriftGalerkinSmoothing (hW : GalerkinWindow) (hC : GalerkinContraction) :
    GalerkinSmoothing := by
  intro J N R P hR hP G hG v hv V hb θ hθ a b hab hJ y hy δ hδ hshort t ht htb
  have hρ := cellDrift_theta_le hθ
  let E := fun K s => ‖cellGalerkinNativeLiftCLM N K (y s)‖ ^ 2
  have hcontinuous : ContinuousOn y (Icc a b) := by
    simpa only [uIcc_of_le hab] using hy.ac.continuousOn
  have hlocal (s d : ℝ) (has : a ≤ s) (hsd : s ≤ d) (hdb : d ≤ b) (hds : d - s ≤ δ) :
      ∀ K ≤ J, E K d ≤ Real.exp 1 * E K s ∧
        (∫ u in s..d, E (K + 1) u) ≤ (2 * Real.exp 1) * E K s := by
    have hsub : uIcc s d ⊆ uIcc a b := by
      rw [uIcc_of_le hsd, uIcc_of_le hab]
      intro x hx
      exact ⟨has.trans hx.1, hx.2.trans hdb⟩
    have hM : 0 ≤ cellDriftWindowPrice J R * P ^ 2 := by
      have := cellDriftWindowPrice_one_le J R hR
      positivity
    have hsmall : cellDriftWindowPrice J R * P ^ 2 * (d - s) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hds hM).trans hshort
    exact hW J N R P hR hP G hG hv V hb (fun k => (θ k : ℂ)) hρ hsd (hJ.mono has hdb) y
      (hy.mono hsub) hsmall
  apply continuous_energy_short_window_polynomial_price E (2 * Real.exp 1) (Real.exp 1)
    (‖cellGalerkinValue N (y a)‖ ^ 2) a b δ J
    hδ (by positivity) (Real.exp_pos 1).le
    (fun K _ => ((cellGalerkinNativeLiftCLM N K).continuous.comp_continuousOn hcontinuous).norm.pow 2)
    (fun s hs => by
      simpa only [E, cellGalerkinNativeLiftCLM_zero_norm_sq] using
        hC N G hG hv V hb θ hab y hy s hs)
    (sq_nonneg _)
    (fun K hK s has hsb => (hlocal s (s + δ) has (by linarith only [hδ]) hsb
      (by simp only [add_sub_cancel_left, le_refl]) K (by omega)).2)
    (fun K _ hK s d has hsd hdb hds => (hlocal s d has hsd hdb hds K hK).1) t ht htb

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the order-`K` Galerkin energy inequality with a drift of jets `≤ P` (Step 1)

Copies of `constructedFullGalerkinOperator_higher_readout`,
`constructedFullGalerkinOperator_higher_lift`, `constructedFullGalerkinOperator_higher_energy` and
`constructedFullGalerkin_all_order_energy`, for a drift `w` with `GlobalJets w P K`; then the
local statement `GalerkinEnergy` by replacing `v` by its clamp to `[a, b]` in time (which agrees
with `v` at the given `t ∈ [a, b]`, `cellDriftEntryCLM_congr_at_time`). -/

theorem cdrGalerkinOperator_readout (K N : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hv : IsCellDrift w)
    (V : ℝ) (hb : ∀ t x, ∑ j, w t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinOperator N (cellGeneratorB
      ⟨fun t _ => G t, w, θ, κ⟩ hG V hv.1 hb t) u =
    cellGalerkinL2Initial N (torusHkValueCLM
      (cdrFullGeneratorCLM K hJ hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) := by
  apply cellGalerkinMass_injective N
  apply LinearMap.ext
  intro z
  change inner ℝ (cellGalerkinValue N (cellGalerkinOperator N _ u)) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N _)) (cellGalerkinValue N z)
  rw [cellGalerkinOperator_pairing, cellGalerkinL2Initial_pairing]
  change cellGeneratorForm
      ⟨fun t _ => G t, w, θ, κ⟩ hG V hv.1 hb t u.val z.val =
    inner ℝ (torusHkValueCLM
      (cdrFullGeneratorCLM K hJ hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) (torusHkValueCLM z.val)
  rw [cdrFullGeneratorCLM_pairing K hJ hv V hb G hG θ κ t _ z.val]
  have he := rangeSmoothFourierLift_truncate (by omega : 1 ≤ K + 2) N u
  have hbase : cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) = u.val := by
    exact he
  rw [hbase]

theorem cdrGalerkinOperator_lift {K : ℕ} (hK : 1 ≤ K) (N : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hv : IsCellDrift w)
    (V : ℝ) (hb : ∀ t x, ∑ j, w t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, w, θ, κ⟩ hG V hv.1 hb t) u) =
    galerkinProj N (cdrFullGeneratorCLM K hJ hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) := by
  rw [cdrGalerkinOperator_readout K N hJ hv V hb G hG θ κ t u,
    cellGalerkinL2Initial_higher_lift]

/-- Order price with potential bound `k`. -/
def cdrOrderPrice (K : ℕ) (R k : ℝ) : ℝ :=
  528 * R ^ 2 + 1 / 4 + 4 * (cdrAdvPrice K R) ^ 2 + 2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)

theorem cdrGrowth_le (K : ℕ) (R P k : ℝ) (hP : 1 ≤ P) (hk : 0 ≤ k) :
    cdrGrowth K R P k ≤ cdrOrderPrice K R k * P ^ 2 := by
  have hp2 : 1 ≤ P ^ 2 := one_le_pow₀ hP
  have hc : 0 ≤ 528 * R ^ 2 + 1 / 4 + 2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖) := by
    positivity
  have he := mul_le_mul_of_nonneg_left hp2 hc
  unfold cdrGrowth cdrOrderPrice
  nlinarith only [he]

theorem cdrFullGenerator_smooth_adjacent_energy (K : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hP : 1 ≤ P) (hv : IsCellDrift w)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    2 * inner ℝ
        (cdrFullGeneratorCLM K hJ hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
        ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤
      cdrOrderPrice K R k * P ^ 2 *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  have he := cdrFullGenerator_smooth_energy K hJ (zero_le_one.trans hP) hv G hG θ R hθ κ t k hk f hf hp
  have hg := finiteSmoothHigherGradientEnergy_native_identity K f hf hp
  have hprice := mul_le_mul_of_nonneg_right
    (cdrGrowth_le K R P k hP ((norm_nonneg _).trans hk))
    (sq_nonneg ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖)
  apply le_trans ?_ hprice
  nlinarith only [he, hg]

theorem cdrGalerkinOperator_higher_energy {K : ℕ} (hK : 1 ≤ K) (N : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hP : 1 ≤ P) (hv : IsCellDrift w)
    (V : ℝ) (hb : ∀ t x, ∑ j, w t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, w, θ, κ⟩ hG V hv.1 hb t) u))
      (rangeSmoothFourierLiftCLM hK N u) +
      (1 / 2) * (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
        ‖cellGalerkinValue N u‖ ^ 2) ≤
      cdrOrderPrice K R k * P ^ 2 * ‖rangeSmoothFourierLiftCLM hK N u‖ ^ 2 := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  have hl := cdrGalerkinOperator_lift hK N hJ hv V hb G hG θ κ t u
  have hi := torusHigherProjection_retained_inner K N
    (cdrFullGeneratorCLM K hJ hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))
    (rangeSmoothFourierLiftCLM hK N u) (rangeSmoothFourierLift_fixed hK N u)
  have hpair := (congrArg (fun z : TorusHk K ℂ =>
    inner ℝ z (rangeSmoothFourierLiftCLM hK N u)) hl).trans hi
  have he := cellGalerkinSmoothEnergyTransfer hK N u
    (cdrFullGeneratorCLM K hJ hv G θ κ t)
    (cdrOrderPrice K R k * P ^ 2)
    (cdrFullGenerator_smooth_adjacent_energy K hJ hP hv G hG θ R hθ κ t k hk
      (cellGalerkinSmoothValue N u) (cellGalerkinSmoothValue_contDiff N u) (cellGalerkinSmoothValue_periodic N u))
  exact (congrArg (fun x : ℝ => 2 * x + (1 / 2) *
    (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
      ‖cellGalerkinValue N u‖ ^ 2)) hpair).le.trans he


theorem cdr_absorb_aux (O Oc E P : ℝ) (h : Oc = O + 1 / 2) (hp2 : 1 ≤ P ^ 2) (hE : 0 ≤ E) :
    (O * P ^ 2 + 1 / 2) * E ≤ Oc * P ^ 2 * E := by
  subst h
  have := mul_nonneg (sub_nonneg.mpr hp2) hE
  nlinarith [this]

theorem cdr_zeroth_growth_le (R P : ℝ) (hR : 0 ≤ R) (hP : 1 ≤ P) (θ : Fin 2 → ℂ)
    (hθ : ∀ i, ‖θ i‖ ≤ R) :
    cellFullZerothGrowth 1 (2 * P) θ 0 ≤ cellDriftOrderPrice 0 R * P ^ 2 := by
  have hs : (∑ j : Fin 2, ‖θ j‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hf : fibreNorm θ ≤ 3 / 2 * R := by
    unfold fibreNorm
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg R]
  have hP0 : 0 ≤ P := by linarith
  have h1 : 2 * P * fibreNorm θ ≤ 2 * P * (3 / 2 * R) := mul_le_mul_of_nonneg_left hf (by positivity)
  have h2 : (∑ j : Fin 2, ‖(Real.sqrt 1 : ℂ) * θ j‖ ^ 2) ≤ 2 * R ^ 2 := by
    simpa only [Real.sqrt_one, Complex.ofReal_one, one_mul] using hs
  unfold cellFullZerothGrowth cellDriftOrderPrice
  have hp2 : 1 ≤ P ^ 2 := one_le_pow₀ hP
  have hq : P ≤ P ^ 2 := by nlinarith
  have e1 : 528 * R ^ 2 ≤ 528 * R ^ 2 * P ^ 2 := by
    have := mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ 528 * R ^ 2)
    linarith
  have e2 : R * P ≤ R * P ^ 2 := mul_le_mul_of_nonneg_left hq hR
  have e3 : (528 * R ^ 2 + 6 * R + 1 / 2) * P ^ 2 =
      528 * R ^ 2 * P ^ 2 + 6 * (R * P ^ 2) + 1 / 2 * P ^ 2 := by ring
  rw [e3]
  have e4 : 2 * P * (3 / 2 * R) = 3 * (R * P) := by ring
  simp only [Real.sqrt_one, Complex.ofReal_one, one_mul, add_zero]
  linarith

theorem cdr_drift_sq_le {w : ℝ → Vec 2 → Vec 2} {P : ℝ} {K : ℕ} (hJ : GlobalJets w P K)
    (hP : 1 ≤ P) (t : ℝ) (x : Vec 2) :
    Real.sqrt 1 * Real.sqrt (∑ i, w t x i ^ 2) ≤ 2 * P := by
  have h0 : ‖w t x‖ ≤ P := by
    have := hJ.2 0 (Nat.zero_le K) t x
    simpa only [norm_iteratedFDeriv_zero] using this
  have hi : ∀ i, w t x i ^ 2 ≤ P ^ 2 := fun i => by
    have := (norm_le_pi_norm (w t x) i).trans h0
    rw [Real.norm_eq_abs] at this
    exact sq_le_sq' (by linarith [abs_le.mp this]) (abs_le.mp this).2
  rw [Real.sqrt_one, one_mul, Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  simp only [Fin.sum_univ_two]
  nlinarith [hi 0, hi 1]

theorem cdrGalerkin_all_order_energy (K N : ℕ) {w : ℝ → Vec 2 → Vec 2} {P : ℝ}
    (hJ : GlobalJets w P K) (hP : 1 ≤ P) (hv : IsCellDrift w)
    (V : ℝ) (hb : ∀ t x, ∑ j, w t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hθ : ∀ i, ‖θ i‖ ≤ R) (t : ℝ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K (cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G s, w, θ, 0⟩ hG V hv.1 hb t) u)) (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      cellDriftOrderPrice K R * P ^ 2 * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2 := by
  cases K with
  | zero =>
    change _ + (1 / 2) * ‖cellGalerkinNativeLiftCLM N 1 u‖ ^ 2 ≤ _
    have he := cellFullGalerkin_zeroth_adjacent_energy N 1 (2 * P) (by linarith) G hG hv
      (cdr_drift_sq_le hJ hP) V hb θ 0 t 0 (by simp) u
    simp only [Real.sqrt_one, Complex.ofReal_one, one_mul] at he
    have hg := cdr_zeroth_growth_le R P hR hP θ hθ
    have hn := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖cellGalerkinValue N u‖)
    simp only [torusH0_inner_value, cellGalerkinNativeLiftCLM_value, cellGalerkinNativeLiftCLM_one,
      cellGalerkinNativeLiftCLM_zero_norm_sq]
    refine le_trans ?_ hn
    simpa only [Real.sqrt_one, Complex.ofReal_one, one_mul] using he
  | succ j =>
    have he := cdrGalerkinOperator_higher_energy (by omega : 1 ≤ j + 1) N hJ hP hv V hb G hG
      θ R hθ 0 t 0 (by simp) u
    have hv' := pow_le_pow_left₀ (norm_nonneg (cellGalerkinValue N u))
      (cellGalerkinRangeHigher_value_norm_le (by omega : 1 ≤ j + 1) N u) 2
    have hp := energyGradientDifference_absorb hv' he
    simp only [cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ j + 1),
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ (j + 1) + 1)]
    refine hp.trans ?_
    have hp2 : 1 ≤ P ^ 2 := one_le_pow₀ hP
    have hE := sq_nonneg ‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ j + 1) N u‖
    have hO : 0 ≤ cdrOrderPrice (j + 1) R 0 := by
      unfold cdrOrderPrice
      positivity
    have hOP : cellDriftOrderPrice (j + 1) R = cdrOrderPrice (j + 1) R 0 + 1 / 2 := by
      unfold cellDriftOrderPrice cdrOrderPrice cdrAdvPrice
      ring
    exact cdr_absorb_aux _ _ _ _ hOP hp2 hE


/-- The time-clamp of a cell drift is a cell drift. -/
theorem cdr_clamp_isCellDrift {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (a b : ℝ) :
    IsCellDrift (fun s => v (max a (min s b))) := by
  obtain ⟨hm, ⟨M, hM⟩, hp, hd⟩ := hv
  refine ⟨?_, ⟨M, fun s z => hM _ z⟩, fun s => hp _, fun s φ => hd _ φ⟩
  have hc : Measurable (fun p : ℝ × Vec 2 => (max a (min p.1 b), p.2)) :=
    ((measurable_const.max (measurable_fst.min measurable_const))).prodMk measurable_snd
  exact hm.comp hc

/-- **Step 1.** The order-`K` Galerkin energy inequality with growth `cellDriftOrderPrice K R * P²`. -/
theorem cellDriftGalerkinEnergy : GalerkinEnergy := by
  intro K N R P hR hP G hG v hv V hb a b t ht hJ θ hθ u
  have hab : a ≤ b := ht.1.trans ht.2
  have hcl : ∀ s, max a (min s b) ∈ Icc a b := fun s =>
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hw := cdr_clamp_isCellDrift hv a b
  have hb' : ∀ s x, ∑ i, (fun s => v (max a (min s b))) s x i ^ 2 ≤ V ^ 2 := fun s x => hb _ x
  have hJw : GlobalJets (fun s => v (max a (min s b))) P K :=
    ⟨fun s => hJ.1 _ (hcl s), fun l hl s x => hJ.2 l hl _ (hcl s) x⟩
  have hvw : v t = (fun s => v (max a (min s b))) t := by
    simp only [min_eq_left ht.2, max_eq_right ht.1]
  have hform : cellGeneratorForm ⟨fun s _ => G s, v, θ, 0⟩ hG V hv.1 hb t =
      cellGeneratorForm ⟨fun s _ => G s, fun s => v (max a (min s b)), θ, 0⟩ hG V hw.1 hb' t := by
    unfold cellGeneratorForm
    simp only [cellDriftEntryCLM_congr_at_time (fun s _ => G s) v (fun s => v (max a (min s b)))
      θ 0 V hv.1 hw.1 hb hb' t hvw]
    rfl
  have hgen : cellGeneratorB ⟨fun s _ => G s, v, θ, 0⟩ hG V hv.1 hb t =
      cellGeneratorB ⟨fun s _ => G s, fun s => v (max a (min s b)), θ, 0⟩ hG V hw.1 hb' t := by
    unfold cellGeneratorB
    rw [hform]
  rw [hgen]
  exact cdrGalerkin_all_order_energy K N hJw hP hw V hb' G hG θ R hR hθ t u

end AVRegularity.CycleWords.Assembly
end
