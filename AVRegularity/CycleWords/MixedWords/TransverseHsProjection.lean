-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransverseLocalAdjoint
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleWords.MixedWords.B1WSourceL2
public import AVRegularity.CycleWords.Assembly.SeamNorms
import AVRegularity.CycleWords.MixedWords.TransverseRegGrowth

section
@[expose] public noncomputable section
section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Reversed (adjoint) curves on a region window

The adjoint fibre problem of the transverse estimate is the forward problem of the time-reversed coefficients
`G(-τ)`, `-v(-τ)`, `-θ` on `[-t, -s]` (`IsRevCurve`). Its curves exist from every datum
(`revCurve_exists`), form a linear space
(`revCurve_smul_sub`), and stay transverse for a shear (`revCurve_transverse`). On the window of
a region they are curves of the reduced equation at the frequency `-ξ`, so
`TransverseRegularityStatement` gives their growth, smoothing and deviation from `1`
(`revCurve_regularity`), with constants after `j, ρ, C_w, J` only. -/

section
/-- The standing hypotheses of the local transverse problem at a real frequency. -/
structure TransverseLocalHyp (K : ScalarConstants) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ) : Prop where
  hη0 : 0 ≤ η
  hη : η ≤ 1
  hCg : 0 ≤ K.Cg
  hCw : 0 ≤ K.Cw
  hG : IsCellMetric (fun t _ => G t)
  hv : IsCellDrift v
  hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0
  hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw
  hreal : ∀ i, (ξ i).im = 0
  hξ : fibreNorm ξ < K.ξ0
  hsep : (2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16

/-- The window hypotheses of a region: a shear along `e`, smooth with jets `J` on `[A, B]`. -/
structure TransverseWindowHyp (η : ℝ) (v : ℝ → Vec 2 → Vec 2) (e : Fin 2) (A B : ℝ)
    (J : ℕ → ℝ) : Prop where
  ht : ∀ (t : ℝ) (z : Vec 2) (s : ℝ), v t (z + s • basisVec e) = v t z
  hperp : ∀ t x, v t x e.rev = 0
  hvs : ∀ t ∈ Icc A B, ContDiff ℝ (⊤ : ℕ∞) (v t)
  hvj : ∀ (l : ℕ) t, t ∈ Icc A B → ∀ x,
    ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- The bound of the reversed drift. -/
theorem rev_bound {V : ℝ} (hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := fun s x => by
  simpa only [Pi.neg_apply, neg_sq] using hV (-s) x

/-- A curve of the time-reversed (adjoint) fibre equation. -/
def IsRevCurve (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) (a b : ℝ) (u : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ) : Prop :=
  CellWeakHilbertCurve a b u slice (fun τ =>
    cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
      fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse H.hG) V
      (cellDrift_timeReverse H.hv).1 hb' τ (slice τ) 0 0)

/-- Reversed curves exist from every datum. -/
theorem revCurve_exists (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a b : ℝ} (hab : a ≤ b)
    (init : ComplexCellL2) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      IsRevCurve H V hb' a b u slice ∧ u a = init := by
  obtain ⟨u, slice, hu, hu0⟩ := cellActual_exists_Hilbert hab
    ⟨fun s _ => G (-s), fun s x => -v (-s) x,
      fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse H.hG)
    V 0 (cellDrift_timeReverse H.hv).1 hb' measurable_const (fun _ => by simp)
    (fun _ _ => 0) (fun _ _ => 0) measurable_const measurable_const (by simp [cellL2Norm])
    (by simp [cellL2Norm]) init
  refine ⟨u, slice, ?_, hu0⟩
  unfold IsRevCurve
  simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
    show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hu

/-- A scalar multiple minus a reversed curve is a reversed curve. -/
theorem revCurve_smul_sub (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a b : ℝ}
    {u u' : ℝ → ComplexCellL2} {slice slice' : ℝ → TorusHk 1 ℂ}
    (hu : IsRevCurve H V hb' a b u slice) (hu' : IsRevCurve H V hb' a b u' slice') (c : ℂ) :
    IsRevCurve H V hb' a b (fun τ => cellScalarCLM c (u τ) - u' τ)
      (fun τ => cellH1Scalar c (slice τ) - slice' τ) := by
  have h1 := CellWeakHilbertCurve.homogeneous_complex_scalar (fun s _ => G (-s))
    (cellMetric_timeReverse H.hG) (fun s x => -v (-s) x) V (cellDrift_timeReverse H.hv).1 hb'
    (fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j)) hu c
  have h2 := h1.sub hu'
  have h3 : (fun τ => cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse H.hG) V
        (cellDrift_timeReverse H.hv).1 hb' τ (cellH1Scalar c (slice τ)) 0 0 -
      cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse H.hG) V
        (cellDrift_timeReverse H.hv).1 hb' τ (slice' τ) 0 0) =
      fun τ => cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse H.hG) V
        (cellDrift_timeReverse H.hv).1 hb' τ (cellH1Scalar c (slice τ) - slice' τ) 0 0 :=
    funext fun τ => cellDualDerivative_sub_zero _ _ V _ hb' τ _ _
  rw [h3] at h2
  exact h2

/-- Reversed curves of a shear stay transverse. -/
theorem revCurve_transverse (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) (e : Fin 2)
    (ht : ∀ (t : ℝ) (z : Vec 2) (s : ℝ), v t (z + s • basisVec e) = v t z) {a b : ℝ}
    (hab : a ≤ b) {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (hu : IsRevCurve H V hb' a b u slice)
    (hi : cellTransverseProjection e (u a) = u a) :
    ∀ τ ∈ Icc a b, cellTransverseProjection e (u τ) = u τ := by
  have ht' : ∀ (τ : ℝ) (z : Vec 2) (r : ℝ),
      (fun s x => -v (-s) x) τ (z + r • basisVec e) = (fun s x => -v (-s) x) τ z := by
    intro τ z r
    simp only [ht (-τ) z r]
  exact cellActualWeak_transverse_invariant hab (fun s => G (-s))
    (cellMetric_timeReverse H.hG) (fun s x => -v (-s) x) _ 0 (cellDrift_timeReverse H.hv) V 0
    hb' (fun _ => by simp) e ht' (fun _ => 0) (fun _ => 0) u slice hu
    (fun _ => map_zero _) (fun _ _ => map_zero _) hi

/-- Changing the shift of a homogeneous curve along an equality. -/
theorem curve_theta_congr {a b V : ℝ} {G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {w : ℝ → Vec 2 → Vec 2} (hG' : IsCellMetric G')
    (hw : Measurable (fun p : ℝ × Vec 2 => w p.1 p.2)) (hb : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    {θ₁ θ₂ : Fin 2 → ℂ} (hθ : θ₁ = θ₂) {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun τ =>
      cellDualDerivative ⟨G', w, θ₁, 0⟩ hG' V hw hb τ (slice τ) 0 0)) :
    CellWeakHilbertCurve a b u slice (fun τ =>
      cellDualDerivative ⟨G', w, θ₂, 0⟩ hG' V hw hb τ (slice τ) 0 0) := by
  subst hθ
  exact h

/-- **Transverse regularity for reversed curves on the window of a region.** -/
theorem revCurve_regularity (hR : TransverseRegularityStatement) (j : ℕ) (ρ : ℝ) (J : ℕ → ℝ)
    (hρ : 0 ≤ ρ) (hJ : ∀ l, 0 ≤ J l) (hCw : 0 ≤ K.Cw) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
      (H : TransverseLocalHyp K η G v ξ) (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
      (e : Fin 2) (A B : ℝ), TransverseWindowHyp η v e A B J → fibreNorm ξ ≤ ρ →
    ∀ a b : ℝ, a ≤ b → -B ≤ a → b ≤ -A →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' a b u slice →
      cellTransverseProjection e (u a) = u a →
      (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b, t ≤ a + 1 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t ∧ ‖w'‖ ≤ C * ‖w₀‖) ∧
      (∀ t ∈ Set.Icc a b, a + 1 ≤ t → t ≤ a + 2 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t ∧ ‖w'‖ ≤ C * ‖u a‖) ∧
      (u a = cellConstantCLM 1 → ∀ t ∈ Set.Icc a b, t ≤ a + 2 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t - cellConstantCLM 1 ∧
          ‖w'‖ ≤ C * fibreNorm ξ) := by
  obtain ⟨C, hC, h⟩ := transverse_full_regularity hR j ρ K.Cw J hρ hCw hJ
  refine ⟨C, hC, ?_⟩
  intro η G v ξ H V hb' e A B W hξρ a b hab haB hbA u slice hu hi
  have hθ : (fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j)) =
      fun k => (Real.sqrt η : ℂ) * (fun k => -(ξ k)) k :=
    funext fun k => by simp only [mul_neg]
  have hfull := curve_theta_congr (cellMetric_timeReverse H.hG) (cellDrift_timeReverse H.hv).1
    hb' hθ hu
  have hmem : ∀ t ∈ Icc a b, -t ∈ Icc A B := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hww : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, (-v (-t) x) i ^ 2) ≤ K.Cw := fun t x => by
    simpa only [Pi.neg_apply, neg_sq] using H.hw (-t) x
  have hjets : ∀ (l : ℕ) t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • (fun s x => -v (-s) x) t x) x‖ ≤ J l := by
    intro l t ht x
    have hf : (fun x => Real.sqrt η • (fun s x => -v (-s) x) t x) =
        -(fun x => Real.sqrt η • v (-t) x) := funext fun x => by simp only [smul_neg,
          Pi.neg_apply]
    rw [hf, iteratedFDeriv_neg_apply, norm_neg]
    exact W.hvj l (-t) (hmem t ht) x
  have hres := h a b η (fun s => G (-s)) (cellMetric_timeReverse H.hG)
    (cellDrift_timeReverse H.hv)
    hww (fun k => -(ξ k)) e (fun t x => by simp only [Pi.neg_apply, W.hperp, neg_zero]) hab
    H.hη0 H.hη (fun i => by simp only [Complex.neg_im, H.hreal i, neg_zero])
    (by rw [fibreNorm_neg]; exact hξρ) (fun t ht => (W.hvs (-t) (hmem t ht)).neg) hjets V hb'
    u slice hfull (revCurve_transverse H V hb' e W.ht hab hu hi)
  rw [fibreNorm_neg] at hres
  exact hres
end

/-! # Sharp fast decay: reversed curves of two drifts that agree on a time interval

The dual derivative of a reversed curve at a time depends only on the coefficients at that time,
and not on the bound `V` of the drift. So a reversed curve of the actual drift on a time interval
where the drift equals the pulse extension is a reversed curve of the extension. -/

/-- A coefficient multiplier does not depend on the bound used to define it. -/
theorem sharpEntry_congr (c : Vec 2 → ℂ)
    (hc₁ hc₂ : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hb₁ : ∀ x, ‖c x‖ ≤ M₁)
    (hb₂ : ∀ x, ‖c x‖ ≤ M₂) :
    cellCoefficientCLM c hc₁ M₁ hM₁ hb₁ = cellCoefficientCLM c hc₂ M₂ hM₂ hb₂ := by
  refine ContinuousLinearMap.ext fun u => ?_
  refine Lp.ext ?_
  filter_upwards [cellCoefficientCLM_ae c hc₁ M₁ hM₁ hb₁ u,
    cellCoefficientCLM_ae c hc₂ M₂ hM₂ hb₂ u] with x h1 h2
  rw [h1, h2]

/-- The drift entry at a time depends on the drift at that time only. -/
theorem sharpDriftEntry_congr {C₁ C₂ : CellCoefficients} (V₁ V₂ : ℝ)
    (hv₁ : Measurable (fun p : ℝ × Vec 2 => C₁.v p.1 p.2))
    (hv₂ : Measurable (fun p : ℝ × Vec 2 => C₂.v p.1 p.2))
    (hb₁ : ∀ t z, ∑ i, C₁.v t z i ^ 2 ≤ V₁ ^ 2) (hb₂ : ∀ t z, ∑ i, C₂.v t z i ^ 2 ≤ V₂ ^ 2)
    (t : ℝ) (h : C₁.v t = C₂.v t) (j : Fin 2) :
    cellDriftEntryCLM C₁ V₁ hv₁ hb₁ t j = cellDriftEntryCLM C₂ V₂ hv₂ hb₂ t j := by
  unfold cellDriftEntryCLM
  have hf : (fun x => (C₁.v t x j : ℂ)) = fun x => (C₂.v t x j : ℂ) := by rw [h]
  have key : ∀ (c₁ c₂ : Vec 2 → ℂ), c₁ = c₂ →
      ∀ (hc₁ : AEStronglyMeasurable c₁ (volume.restrict AVenhance.unitCube))
        (hc₂ : AEStronglyMeasurable c₂ (volume.restrict AVenhance.unitCube))
        (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hb₁ : ∀ x, ‖c₁ x‖ ≤ M₁)
        (hb₂ : ∀ x, ‖c₂ x‖ ≤ M₂),
      cellCoefficientCLM c₁ hc₁ M₁ hM₁ hb₁ = cellCoefficientCLM c₂ hc₂ M₂ hM₂ hb₂ := by
    intro c₁ c₂ e
    subst e
    exact fun hc₁ hc₂ M₁ M₂ hM₁ hM₂ hb₁ hb₂ => sharpEntry_congr _ hc₁ hc₂ M₁ M₂ hM₁ hM₂ hb₁ hb₂
  exact key _ _ hf _ _ _ _ _ _ _ _

/-- The dual derivative at a time depends on the drift at that time only (zero source). -/
theorem sharpDual_congr_time (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ)
    (v v' : ℝ → Vec 2 → Vec 2) (hG : IsCellMetric G) (V V' : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hv' : Measurable (fun p : ℝ × Vec 2 => v' p.1 p.2))
    (hb' : ∀ t x, ∑ i, v' t x i ^ 2 ≤ V' ^ 2) (t : ℝ) (h : v t = v' t) (u : TorusHk 1 ℂ) :
    cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t u 0 0 =
      cellDualDerivative ⟨G, v', θ, 0⟩ hG V' hv' hb' t u 0 0 := by
  have h1 : ∀ j, cellDriftEntryCLM ⟨G, v, θ, 0⟩ V hv hb t j =
      cellDriftEntryCLM ⟨G, v', θ, 0⟩ V' hv' hb' t j :=
    fun j => sharpDriftEntry_congr V V' hv hv' hb hb' t h j
  unfold cellDualDerivative cellGeneratorForm
  simp only [h1]
  rfl

/-- Reversed curves of two drifts that agree on the time interval are the same curves. -/
theorem sharpRevCurve_congr {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v₁ v₂ : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ} (H₁ : TransverseLocalHyp K η G v₁ ξ)
    (H₂ : TransverseLocalHyp K η G v₂ ξ) (V₁ V₂ : ℝ)
    (hb₁ : ∀ s x, ∑ i, (-v₁ (-s) x) i ^ 2 ≤ V₁ ^ 2)
    (hb₂ : ∀ s x, ∑ i, (-v₂ (-s) x) i ^ 2 ≤ V₂ ^ 2) {a b : ℝ}
    (hagree : ∀ τ ∈ Icc a b, v₁ (-τ) = v₂ (-τ))
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} (hu : IsRevCurve H₁ V₁ hb₁ a b u slice) :
    IsRevCurve H₂ V₂ hb₂ a b u slice := by
  unfold IsRevCurve at hu ⊢
  refine hu.dual_congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
  exact sharpDual_congr_time _ _ _ _ _ V₁ V₂ _ _ _ _ τ
    (by show (fun x => -v₁ (-τ) x) = fun x => -v₂ (-τ) x; rw [hagree τ hτ]) _

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! **(C1): the solution from the constant `1`**, and `transverseRegularity`.

`‖u(t) - 1‖_{H^j} ≤ C |ξ|` for `a ≤ t ≤ a + 2` when `u(a) = 1`, with `C` from `j, ρ, C_w, J` (no
smallness of `|ξ|`). Galerkin at order `K = j + 1`: `z = y - 1` solves `z' = T z + T 1` with
`z(a) = 0`, and the forcing is `O(|ξ|)` in `H^K`: on the constant, the twisted diffusion is the
scalar `-θGθ` (`|θGθ| ≤ 8|ξ|² ≤ 8ρ|ξ|`), and the potential has the multiplier price
`P_K(J)·|ξ|`. Grönwall with `Γ_K + 1`; then `transverseReg_transfer` and truncation to order `j`.

For `ξ = 0` the forcing vanishes and `u ≡ 1`; for `a = b` one has `w = 0`; for `j = 0` the
truncation starts from order `1`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE

namespace AVRegularity.CycleWords

theorem transverseRegMultiplierPrice_mul_right (K : ℕ) (B : Fin (K + 1) → ℝ) (s : ℝ) :
    transverseRegMultiplierPrice K (fun l => B l * s) = transverseRegMultiplierPrice K B * s := by
  unfold transverseRegMultiplierPrice
  have h : ∑ l : Fin (K + 1), factorialRootWeight 1 l.val * (B l * s) =
      (∑ l : Fin (K + 1), factorialRootWeight 1 l.val * B l) * s := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h]
  ring

/-- The `H^K` size of the forcing on the constant, per unit of `|ξ|`. -/
def transverseRegConstSource (K : ℕ) (ρ : ℝ) (J : ℕ → ℝ) : ℝ :=
  (8 * ρ + transverseRegMultiplierPrice K (transverseRegJetPrice K 1 J)) *
    ‖torusHigherConstant K 1‖

/-- The twisted diffusion of the constant is the scalar `-θGθ`. -/
theorem transverseRegDiffusion_constant (K : ℕ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Fin 2 → ℂ) (t : ℝ) :
    torusHigherStrongDiffusionCLM K G θ t (torusHigherConstant (K + 2) 1) =
      torusHigherScalarCLM K (-(∑ i : Fin 2, ∑ k : Fin 2, (G t i k : ℂ) * θ i * θ k))
        (torusHigherConstant K 1) := by
  have h2 (i k : Fin 2) : torusHigherSecondCLM K i k (torusHigherConstant (K + 2) 1) = 0 := by
    have h : derivativeTorusHk (K := K + 1) (fun _ : Fin 1 => i) (torusHigherConstant (K + 2) 1) = 0 :=
      torusHigherConstant_derivative (fun _ : Fin 1 => i) one_pos 1
    change derivativeTorusHk (K := K) (fun _ : Fin 1 => k)
      (derivativeTorusHk (K := K + 1) (fun _ : Fin 1 => i) (torusHigherConstant (K + 2) 1)) = 0
    rw [h, map_zero]
  have h1 (i : Fin 2) : torusHigherFirstCLM K i (torusHigherConstant (K + 2) 1) = 0 := by
    change derivativeTorusHk (K := K) (fun _ : Fin 1 => i)
      (truncateTorusHk (by omega : K + 1 ≤ K + 2) (torusHigherConstant (K + 2) 1)) = 0
    rw [torusHigherConstant_truncate]
    exact torusHigherConstant_derivative (fun _ : Fin 1 => i) one_pos 1
  simp only [torusHigherStrongDiffusionCLM, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    h2, h1, map_zero, Finset.sum_const_zero, zero_add, torusHigherConstant_truncate]

/-- The transverse source on the constant `1`: the diffusion gives `-θGθ`, the potential its
multiplier price. Generic in the order-`K` coefficient data. -/
theorem transverseRegSource_constant_norm_le (K : ℕ) (a b η : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hcK : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t)) (AK : Fin (K + 1) → ℝ) (hAK : ∀ l, 0 ≤ AK l)
    (hbK : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ AK l)
    (t P ρ : ℝ) (hξ : fibreNorm ξ ≤ ρ)
    (hP : transverseRegMultiplierPrice K AK ≤ P * fibreNorm ξ) :
    ‖torusHigherTransverseWindowSourceCLM K a b η G hv ξ hcK AK hAK hbK 0 t
        (torusHigherConstant (K + 2) 1)‖ ≤
      (8 * ρ + P) * ‖torusHigherConstant K 1‖ * fibreNorm ξ := by
  have htr : truncateTorusHk (by omega : K ≤ K + 2) (torusHigherConstant (K + 2) 1) =
      torusHigherConstant K 1 := torusHigherConstant_truncate _ 1
  have hM := (transverseRegMultiplier_norm_le K a b η hv ξ hcK AK hAK hbK t
    (torusHigherConstant K 1)).trans
    (mul_le_mul_of_nonneg_right hP (norm_nonneg (torusHigherConstant K 1)))
  have hq := scaledMetricQuad_norm_le η hη0 hη G hG ξ t
  have hξ2 : fibreNorm ξ ^ 2 ≤ ρ * fibreNorm ξ := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hξ (fibreNorm_nonneg ξ)
  simp only [torusHigherTransverseWindowSourceCLM, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, htr, transverseRegDiffusion_constant]
  refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
  simp only [torusHigherScalarCLM_norm, norm_neg, Complex.norm_I, one_mul, Pi.zero_apply,
    norm_zero, zero_mul, add_zero]
  have e1 := mul_le_mul_of_nonneg_right hq (norm_nonneg (torusHigherConstant K 1))
  have e2 := mul_le_mul_of_nonneg_right hξ2 (norm_nonneg (torusHigherConstant K 1))
  linarith only [e1, e2, hM]

/-- The retained constant lifts to the constant at every order. -/
theorem transverseRegRangeLift_constant (K N : ℕ) :
    rangeSmoothFourierLiftCLM (E := ℂ) (by omega : 1 ≤ K + 2) N (cellGalerkinConstant N 1) =
      torusHigherConstant (K + 2) 1 := by
  apply TorusHk.ext_value
  change torusHkValueCLM (rangeSmoothFourierLiftCLM (E := ℂ) (by omega : 1 ≤ K + 2) N
    (cellGalerkinConstant N 1)) = torusHkValueCLM (torusHigherConstant (K + 2) 1)
  rw [cellGalerkinRangeHigher_value, cellGalerkinConstant_value, torusHigherConstant_value]

/-- The finite transverse operator on the constant reads the source of the constant. Generic in the
order-`K` coefficient data. -/
theorem transverseRegGalerkin_constant_lift (K N : ℕ) (hK : 1 ≤ K) (a b η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hcK : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t)) (AK : Fin (K + 1) → ℝ) (hAK : ∀ l, 0 ≤ AK l)
    (hbK : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ AK l)
    (t : ℝ) (ht : t ∈ Icc a b) :
    cellGalerkinNativeLiftCLM N K
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0 t (cellGalerkinConstant N 1)) =
      galerkinProj N (torusHigherTransverseWindowSourceCLM K a b η G hv ξ hcK AK hAK hbK 0 t
        (torusHigherConstant (K + 2) 1)) := by
  rw [cellGalerkinNativeLiftCLM_eq_range hK, cellTransverseGalerkinOperator_higher_value N a b η G
    hv ξ hc A hA hb 0 Cw hCw hw K hcK AK hAK hbK t ht, cellGalerkinL2Initial_higher_lift hK N,
    transverseRegRangeLift_constant K N]
  rfl

/-- The jet budget's multiplier price is linear in `|ξ|`. -/
theorem transverseRegJetBudget_price (K : ℕ) (J : ℕ → ℝ) (ξ : Fin 2 → ℂ) :
    transverseRegMultiplierPrice K (normalizedDriftJetBudget K (fun l => J l.val) ξ) =
      transverseRegMultiplierPrice K (transverseRegJetPrice K 1 J) * fibreNorm ξ := by
  rw [← transverseRegMultiplierPrice_mul_right]
  congr 1
  funext l
  simp only [normalizedDriftJetBudget, transverseRegJetPrice, mul_one]

/-- **The forcing on the constant is `O(|ξ|)` in `H^K`**, `K ≥ 1`, with no smallness. -/
theorem transverseRegGalerkin_constant_source (K N : ℕ) (hK : 1 ≤ K) {a b η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖cellGalerkinNativeLiftCLM N K
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0 t (cellGalerkinConstant N 1))‖ ≤
      transverseRegConstSource K ρ J * fibreNorm ξ := by
  have hJ0 : ∀ l, 0 ≤ J l := fun l => (norm_nonneg _).trans (hj l t ht 0)
  have hcK : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t) :=
    fun t ht => (hfull t ht).of_le (by exact_mod_cast le_top)
  have hAK := normalizedDriftJetBudget_nonneg K (fun l => J l.val) ξ (fun l => hJ0 l.val)
  have hbK := normalizedDriftJetBudget_window_bound K a b η v ξ hcK (fun l => J l.val)
    (fun l t ht x => hj l.val t ht x)
  have hl := transverseRegGalerkin_constant_lift K N hK a b η G hv ξ hc A hA hb Cw hCw hw hcK _
    hAK hbK t ht
  have hS := transverseRegSource_constant_norm_le K a b η hη0 hη G hG hv ξ hcK _ hAK hbK t _ ρ hξ
    (transverseRegJetBudget_price K J ξ).le
  exact (congrArg norm hl).trans_le ((galerkinProj_norm_le N _).trans hS)

/-- **(C1) for the finite transverse system** from the constant, at order `K ≥ 1`. -/
theorem transverseRegGalerkin_constant_bound (K N : ℕ) (hK : 1 ≤ K) {a b η : ℝ} (hab : a ≤ b)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (ξ : Fin 2 → ℂ) (ρ : ℝ) (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 (cellGalerkinL2Initial N (cellConstantCLM 1)) a b (extendCurve hab y))
    (t : ℝ) (ht : t ∈ Icc a b) (ht2 : t ≤ a + 2) :
    ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y t - cellGalerkinConstant N 1)‖ ^ 2 ≤
      2 * Real.exp (2 * (transverseRegGamma K ρ Cw J + 1)) *
        (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2 := by
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξ
  have hJ0 : ∀ l, 0 ≤ J l := fun l => (norm_nonneg _).trans (hj l t ht 0)
  have hΓ := transverseRegGamma_nonneg K ρ Cw hρ J hJ0
  have hΓ1 : 0 ≤ transverseRegGamma K ρ Cw J + 1 := by linarith only [hΓ]
  have hs := transverseRegGalerkin_strongTime N hab G hG hv ξ hc A hA hb _ y hy
  have hcst : StrongTimeRegularity a b
      (fun _ : ℝ => cellGalerkinNativeLiftCLM N K (cellGalerkinConstant N 1)) (fun _ => 0) :=
    ⟨contDiffOn_const.absolutelyContinuousOnInterval, ae_of_all _ fun s => hasDerivAt_const s _⟩
  have hz := ((hs.map (cellGalerkinNativeLiftCLM N K)).sub hcst).mono
    (by rw [uIcc_of_le ht.1, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl ht.2)
  have hwb := (strongTime_scalar_norm_energy hz).scalar_weighted_bound ht.1
    (-(transverseRegGamma K ρ Cw J + 1)) (fun _ => (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2)
    (fun _ => 0) intervalIntegrable_const intervalIntegrable_const (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs'
      have hsI : s ∈ Icc a b := ⟨hs'.1, hs'.2.trans ht.2⟩
      have hsub : cellGalerkinNativeLiftCLM N K (extendCurve hab y s) -
          cellGalerkinNativeLiftCLM N K (cellGalerkinConstant N 1) =
          cellGalerkinNativeLiftCLM N K (extendCurve hab y s - cellGalerkinConstant N 1) :=
        (map_sub _ _ _).symm
      rw [Set.indicator_of_mem hsI, sub_zero, hsub]
      have hsplit : cellGalerkinNativeLiftCLM N K (cellTransverseGalerkinOperator N a b η G hv ξ hc
          A hA hb 0 s (extendCurve hab y s)) =
          cellGalerkinNativeLiftCLM N K (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0 s
            (extendCurve hab y s - cellGalerkinConstant N 1)) +
          cellGalerkinNativeLiftCLM N K (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0 s
            (cellGalerkinConstant N 1)) := by
        rw [← map_add, ← map_add, sub_add_cancel]
      rw [hsplit, inner_add_left]
      have he : 2 * inner ℝ (cellGalerkinNativeLiftCLM N K (cellTransverseGalerkinOperator N a b η G
            hv ξ hc A hA hb 0 s (extendCurve hab y s - cellGalerkinConstant N 1)))
            (cellGalerkinNativeLiftCLM N K (extendCurve hab y s - cellGalerkinConstant N 1)) +
          (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1)
            (extendCurve hab y s - cellGalerkinConstant N 1)‖ ^ 2 ≤
          transverseRegGamma K ρ Cw J *
            ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y s - cellGalerkinConstant N 1)‖ ^ 2 :=
        transverseRegGalerkin_energy K N a b η hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J hj
          hc A hA hb s hsI (extendCurve hab y s - cellGalerkinConstant N 1)
      have hF := transverseRegGalerkin_constant_source K N hK hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull
        J hj hc A hA hb s hsI
      have hF2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
      have hcross := real_inner_le_norm
        (cellGalerkinNativeLiftCLM N K (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0 s
          (cellGalerkinConstant N 1)))
        (cellGalerkinNativeLiftCLM N K (extendCurve hab y s - cellGalerkinConstant N 1))
      have hamgm := two_mul_le_add_sq
        ‖cellGalerkinNativeLiftCLM N K (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0 s
          (cellGalerkinConstant N 1))‖
        ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y s - cellGalerkinConstant N 1)‖
      have hd := sq_nonneg
        ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y s - cellGalerkinConstant N 1)‖
      linarith only [he, hF2, hcross, hamgm, hd])
  have h0 : extendCurve hab y a = cellGalerkinConstant N 1 :=
    transverseRegGalerkin_initial N hab G hv ξ hc A hA hb _ y hy
  simp only [h0, sub_self, norm_zero, mul_zero, intervalIntegral.integral_zero, add_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hwb
  have hint : (∫ s in a..t, Real.exp (-(transverseRegGamma K ρ Cw J + 1) * (s - a)) *
      (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2) ≤
      2 * (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2 := by
    have hcw : Continuous (fun s => Real.exp (-(transverseRegGamma K ρ Cw J + 1) * (s - a)) *
        (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).mul
        continuous_const
    have hm : (∫ s in a..t, Real.exp (-(transverseRegGamma K ρ Cw J + 1) * (s - a)) *
        (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2) ≤
        ∫ _ in a..t, (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2 :=
      intervalIntegral.integral_mono_on ht.1 (hcw.intervalIntegrable _ _) intervalIntegrable_const
        (fun s hs => mul_le_of_le_one_left (sq_nonneg _) (Real.exp_le_one_iff.mpr (by
          have := mul_nonneg hΓ1 (sub_nonneg.2 hs.1)
          linarith only [this])))
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (by linarith only [ht2]) (sq_nonneg _))
  have hsplit := (transverseReg_exp_split (Γ := transverseRegGamma K ρ Cw J + 1) (s := t - a)
    (X := ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y t) -
      cellGalerkinNativeLiftCLM N K (cellGalerkinConstant N 1)‖ ^ 2) (I := 0)
    (Y := 2 * (transverseRegConstSource K ρ J * fibreNorm ξ) ^ 2)
    (sq_nonneg _) le_rfl (by simpa only [mul_zero, add_zero] using hwb.trans hint)).1
  rw [map_sub]
  have hm := mul_le_mul_of_nonneg_left (by linarith only [ht2] : t - a ≤ 2) hΓ1
  have he : Real.exp ((transverseRegGamma K ρ Cw J + 1) * (t - a)) ≤
      Real.exp (2 * (transverseRegGamma K ρ Cw J + 1)) :=
    Real.exp_le_exp.mpr (by linarith only [hm])
  exact hsplit.trans ((mul_le_mul_of_nonneg_right he
    (mul_nonneg (by norm_num) (sq_nonneg _))).trans_eq (by ring))

end AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

/-- **(C1)**: the solution from `1` differs from `1` by `O(|ξ|)` in `H^j` on `[a, a + 2]`. -/
theorem transverseRegConstant : TransverseRegConstantStatement := by
  intro j ρ Cw J hρ _ hJ
  have hQ : 0 ≤ 2 * Real.exp (2 * (transverseRegGamma (j + 1) ρ Cw J + 1)) *
      transverseRegConstSource (j + 1) ρ J ^ 2 := by positivity
  refine ⟨2 * Real.exp (2 * (transverseRegGamma (j + 1) ρ Cw J + 1)) *
    transverseRegConstSource (j + 1) ρ J ^ 2 + 1, by linarith only [hQ], ?_⟩
  intro W hi t ht ht2
  rcases eq_or_lt_of_le W.hab with hab | hab'
  · have hta : t = W.a := le_antisymm (ht.2.trans hab.ge) ht.1
    refine ⟨0, ?_, ?_⟩
    · rw [map_zero, hta, hi, sub_self]
    · rw [norm_zero]
      exact mul_nonneg (by linarith only [hQ]) (fibreNorm_nonneg _)
  · have hc0 := transverseRegWindow_contDiff_zero W
    obtain ⟨w, hwv, hwb⟩ := transverseReg_transfer (j + 1) hab' W.hη0 W.hη1 W.G W.hG W.hv W.ξ ρ
      W.hfreq Cw W.hCw W.hw W.hsmooth J W.hjets hc0 _
      (normalizedDriftJetBudget_nonneg 0 (fun l => J l.val) W.ξ (fun l => hJ l.val))
      (normalizedDriftJetBudget_window_bound 0 W.a W.b W.η W.v W.ξ hc0 (fun l => J l.val)
        (fun l t ht x => W.hjets l.val t ht x))
      W.u W.slice W.curve (cellConstantCLM 1)
      (2 * Real.exp (2 * (transverseRegGamma (j + 1) ρ Cw J + 1)) *
        transverseRegConstSource (j + 1) ρ J ^ 2 * fibreNorm W.ξ ^ 2)
      (mul_nonneg hQ (sq_nonneg _)) t ht
      (fun N y hy => ⟨cellGalerkinNativeLiftCLM N (j + 1)
          (extendCurve hab'.le y t - cellGalerkinConstant N 1),
        by rw [cellGalerkinNativeLiftCLM_value, map_sub, cellGalerkinConstant_value],
        (transverseRegGalerkin_constant_bound (j + 1) N (by omega) hab'.le W.hη0 W.hη1 W.G W.hG
          W.hv W.ξ ρ W.hfreq Cw W.hCw W.hw W.hsmooth J W.hjets hc0 _ _ _ y (hi ▸ hy) t ht
          ht2).trans_eq (by ring)⟩)
    refine ⟨truncateTorusHk (by omega : j ≤ j + 1) w, hwv, ?_⟩
    refine (truncateTorusHk_norm_le _ w).trans (transverseReg_le_of_sq (norm_nonneg _)
      (fibreNorm_nonneg _) (by linarith only [hQ]) (hwb.trans ?_))
    exact mul_le_mul_of_nonneg_right (by linarith only) (sq_nonneg _)

/-- **Smallness-free regularity of the reduced transverse equation** (`H^j` layer). -/
theorem transverseRegularity : TransverseRegularityStatement :=
  transverseRegularity_of_ingredients transverseRegGrowth transverseRegSmoothing
    transverseRegConstant

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Finite Fourier readouts and the divergence-source kernel, with bounds independent of the cutoff. -/

local instance quietForcedKernelMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

/-- The zero Fourier mode is the actual constant-one cell class. -/
theorem quietFourier_mode_zero : scalarTorusToCell (mFourierLp 2 (0 : Fin 2 → ℤ)) =
    cellConstantCLM 1 := by
  apply Lp.ext
  rw [scalarTorusToCell_mode]
  filter_upwards [(cellComplexFourierMode_memLp 0).coeFn_toLp, cellConstantCLM_ae 1] with x hx hc
  rw [hx, hc, cellComplexFourierMode_eq]
  rw [mFourier_zero]
  rfl

/-- Removing the mean deletes exactly the zero Fourier coefficient. -/
theorem quietFourier_q0_coefficient (u : ComplexCellL2) (n : Fin 2 → ℤ) :
    cellComplexPair (cellQ0CLM u) (scalarTorusToCell (mFourierLp 2 n)) =
      if n = 0 then 0 else cellComplexPair u (scalarTorusToCell (mFourierLp 2 n)) := by
  by_cases hn : n = 0
  · subst n
    simp only [quietFourier_mode_zero, cellComplexPair_one, cellQ0CLM_mean_zero, ite_true]
  rw [ite_eq_right hn]
  have ho := (orthonormal_iff_ite.mp (mFourierBasis (d := Fin 2)).orthonormal) n 0
  simp only [coe_mFourierBasis] at ho
  have hi := scalarTorusToCellComplex.inner_map_map (mFourierLp 2 n) (mFourierLp 2 0)
  simp only [scalarTorusToCellComplex_eq, quietFourier_mode_zero] at hi
  have hz : inner ℂ (scalarTorusToCell (mFourierLp 2 n)) (cellConstantCLM 1) = 0 := by
    rw [hi, ho, ite_eq_right hn]
  have hc : cellConstantCLM (cellMeanCLM u) =
      (cellMeanCLM u) • (cellConstantCLM 1) := by
    apply Lp.ext
    filter_upwards [cellConstantCLM_ae (cellMeanCLM u), Lp.coeFn_smul (cellMeanCLM u) (cellConstantCLM 1),
      cellConstantCLM_ae 1] with x h₁ h₂ h₃
    rw [h₁, h₂, Pi.smul_apply, h₃, smul_eq_mul, mul_one]
  change cellComplexPair (u - cellConstantCLM (cellMeanCLM u)) _ = _
  rw [cellComplexPair_eq_inner, cellComplexPair_eq_inner, inner_sub_right, hc,
    inner_smul_right, hz, mul_zero, sub_zero]

/-- The multiplier on the mean-free subspace. -/
def quietFourierCutMultiplier (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Vec 2)
    (n : Fin 2 → ℤ) (a b : ℝ) : ℂ :=
  if n = 0 then 0 else quietFourierMultiplier G θ n a b

/-- The cutoff multiplier has the sharp quiet spectral gap at every index. -/
theorem quietFourier_cut_gap (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (n : Fin 2 → ℤ) {a b : ℝ} (hab : a ≤ b) :
    ‖quietFourierCutMultiplier G θ n a b‖ ≤ Real.exp (-(Real.pi ^ 2 / 2) * (b - a)) := by
  by_cases hn : n = 0
  · simp only [quietFourierCutMultiplier, ite_eq_left hn, norm_zero]
    exact (Real.exp_pos _).le
  · simpa only [quietFourierCutMultiplier, ite_eq_right hn] using
      quietFourier_multiplier_gap G hG θ hθ n hn hab

/-- The scalar ODE coefficient is the negative real-frequency metric symbol. -/
theorem quietFourier_symbol_eq (G : Matrix (Fin 2) (Fin 2) ℝ) (y : Vec 2) :
    -(∑ j, ∑ k, (G j k : ℂ) * (y j : ℂ) * (y k : ℂ)) =
      -fibreQuad G (fun j => (y j : ℂ)) := by
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The forced mean-free Fourier equation with its zero mode removed. -/
theorem quietFourier_q0_evolution {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 (F t)))
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) (n : Fin 2 → ℤ) :
    cellComplexPair (cellQ0CLM (u b)) (scalarTorusToCell (mFourierLp 2 n)) =
      quietFourierCutMultiplier G θ n a b *
        cellComplexPair (cellQ0CLM (u a)) (scalarTorusToCell (mFourierLp 2 n)) +
      ∫ t in a..b, quietFourierCutMultiplier G θ n t b *
        (Complex.I * ∑ j, (quietFourierFrequency θ n j : ℂ) *
          cellComplexPair (F t j) (scalarTorusToCell (mFourierLp 2 n))) := by
  by_cases hn : n = 0
  · simp only [quietFourier_q0_coefficient, quietFourierCutMultiplier, ite_eq_left hn,
      zero_mul, intervalIntegral.integral_zero, add_zero]
  · have he := quietFourier_evolution hab G hG hv V hb θ u slice F hF h hquiet n
    dsimp only at he
    simpa only [quietFourier_symbol_eq, intervalIntegral.integral_neg, quietFourierMultiplier,
      quietFourierCutMultiplier, ite_eq_right hn, quietFourier_q0_coefficient] using he

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CycleWords AVRegularity.CoupledEnergy.Galerkin
open AVRegularity
namespace AVRegularity.CycleWords.Assembly

/-! The quiet `H^s` decay: the mean-free part of a forced-free quiet cell curve
contracts in every `H^s` at the rate `π²/2`, with factor one. -/

local instance quietHsDecayMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

/-- Two Fourier-coefficient-equal `L²` classes on the torus coincide. -/
theorem quietHs_ext_coeff (x y : ScalarTorusL2)
    (h : ∀ n, mFourierCoeff x n = mFourierCoeff y n) : x = y := by
  apply (mFourierBasis (d := Fin 2)).repr.injective
  apply Subtype.ext
  funext n
  change (mFourierBasis (d := Fin 2)).repr x n = (mFourierBasis (d := Fin 2)).repr y n
  rw [mFourierBasis_repr, mFourierBasis_repr]
  exact h n

/-- A drift that vanishes at time `t` acts by zero. -/
theorem quietHs_drift_zero (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (hz : ∀ x, C.v t x = 0) (j : Fin 2) :
    cellDriftEntryCLM C V hv hb t j = 0 := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [zero_apply]
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae C V hv hb t j u,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube)] with x hx h0
  rw [hx, h0, hz x]
  simp

/-- The dual derivative only sees the drift through its values at the given time. -/
theorem quietHs_dual_congr (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (v v' : ℝ → Vec 2 → Vec 2) (hG : IsCellMetric G) (V V' : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hv' : Measurable (fun p : ℝ × Vec 2 => v' p.1 p.2))
    (hb' : ∀ t x, ∑ i, v' t x i ^ 2 ≤ V' ^ 2) (t : ℝ) (hz : ∀ x, v t x = 0)
    (hz' : ∀ x, v' t x = 0) (u : TorusHk 1 ℂ) :
    cellDualDerivative ⟨G, v, θ, κ⟩ hG V hv hb t u 0 0 =
      cellDualDerivative ⟨G, v', θ, κ⟩ hG V' hv' hb' t u 0 0 := by
  have h1 := quietHs_drift_zero ⟨G, v, θ, κ⟩ V hv hb t hz
  have h2 := quietHs_drift_zero ⟨G, v', θ, κ⟩ V' hv' hb' t hz'
  unfold cellDualDerivative cellGeneratorForm
  simp only [h1, h2]
  rfl

/-- **Quiet `H^s` decay.** -/
theorem quietHsDecay : QuietHsDecayStatement := by
  intro C hG V hv hb a₁ b₁ u slice hab hv0 hGc hκ hθ h s w₀ hw₀
  rcases C with ⟨CG, Cv, Cθ, Cκ⟩
  obtain ⟨G₀, rfl⟩ : ∃ G₀ : ℝ → Matrix (Fin 2) (Fin 2) ℝ, CG = fun t _ => G₀ t :=
    ⟨fun t => CG t 0, funext fun t => funext fun x => hGc t x 0⟩
  obtain ⟨θ₀, rfl⟩ : ∃ θ₀ : Vec 2, Cθ = fun j => (θ₀ j : ℂ) :=
    ⟨fun j => (Cθ j).re, funext fun j => Complex.ext (by simp) (by simpa using (hθ j).1)⟩
  have hθ₀ : ∀ j, |θ₀ j| ≤ Real.pi := fun j => by simpa using (hθ j).2
  obtain rfl : Cκ = 0 := funext hκ
  have hv0' : IsCellDrift (fun (_ : ℝ) (_ : Vec 2) => (0 : Vec 2)) :=
    ⟨measurable_const, ⟨0, by simp⟩, fun _ _ _ => rfl, fun t φ => by simp⟩
  have hb0 : ∀ (t : ℝ) (x : Vec 2), ∑ i, (0 : Vec 2) i ^ 2 ≤ (0 : ℝ) ^ 2 := by simp
  have h' : CellWeakHilbertCurve a₁ b₁ u slice (fun τ => cellDualDerivative
      ⟨fun t _ => G₀ t, fun _ _ => 0, fun j => (θ₀ j : ℂ), 0⟩ hG 0 hv0'.1 hb0 τ (slice τ) 0 0) := by
    refine h.dual_congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact quietHs_dual_congr _ _ _ _ _ hG V 0 hv hb hv0'.1 hb0 τ (hv0 τ hτ) (fun _ => rfl) _
  have hF : ∀ j : Fin 2, MemLp (fun t : ℝ => (fun (_ : ℝ) (_ : Fin 2) => (0 : ComplexCellL2)) t j) 2
      (volume.restrict (Icc a₁ b₁)) := fun j => MemLp.zero
  have hcoef : ∀ n, mFourierCoeff (scalarCellToTorus (cellQ0CLM (u b₁))) n =
      quietFourierCutMultiplier G₀ θ₀ n a₁ b₁ *
        mFourierCoeff (scalarCellToTorus (cellQ0CLM (u a₁))) n := by
    intro n
    have he := quietFourier_q0_evolution hab G₀ hG hv0' 0 hb0 θ₀ u slice
      (fun _ _ => 0) hF h' (fun t _ x => rfl) n
    simp only [cellComplexPair_zero_left, mul_zero, Finset.sum_const_zero,
      intervalIntegral.integral_zero, add_zero] at he
    rw [scalarCellToTorus_fourierCoeff_pair, scalarCellToTorus_fourierCoeff_pair]
    exact he
  have hM : 0 ≤ Real.exp (-(Real.pi ^ 2 / 2) * (b₁ - a₁)) := (Real.exp_pos _).le
  obtain ⟨w, hwc, hwn⟩ := quietHs_multiplier s (fun n => quietFourierCutMultiplier G₀ θ₀ n a₁ b₁)
    _ hM (fun n => quietFourier_cut_gap G₀ hG θ₀ hθ₀ n hab) w₀
  refine ⟨w, ?_, hwn⟩
  have hx : scalarCellToTorus (torusHkValueCLM w) = scalarCellToTorus (cellQ0CLM (u b₁)) :=
    quietHs_ext_coeff _ _ (fun n => by rw [hwc n, hcoef n, hw₀])
  rw [← scalarTorusToCell_scalarCellToTorus (torusHkValueCLM w), hx,
    scalarTorusToCell_scalarCellToTorus]

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CycleWords AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! The transverse projection on `H^s`: the Fourier multiplier `1_{n_e = 0}`. -/

local instance transverseHsMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

/-- The Fourier coefficient of the value of a Sobolev element. -/
def transverseHsCoeff {s : ℕ} (U : TorusHk s ℂ) (n : Fin 2 → ℤ) : ℂ :=
  mFourierCoeff (scalarCellToTorus (torusHkValueCLM U)) n

theorem transverseHs_ext {s : ℕ} (w₁ w₂ : TorusHk s ℂ)
    (h : ∀ n, transverseHsCoeff w₁ n = transverseHsCoeff w₂ n) : w₁ = w₂ := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  have hc : scalarCellToTorus (w₁.val a) = scalarCellToTorus (w₂.val a) :=
    quietHs_ext_coeff _ _ (fun n => by
      rw [quietHs_jet_coeff w₁ n a, quietHs_jet_coeff w₂ n a]
      exact congrArg _ (h n))
  rw [← scalarTorusToCell_scalarCellToTorus (w₁.val a), hc, scalarTorusToCell_scalarCellToTorus]

theorem transverseHsCoeff_add {s : ℕ} (U V : TorusHk s ℂ) (n : Fin 2 → ℤ) :
    transverseHsCoeff (U + V) n = transverseHsCoeff U n + transverseHsCoeff V n := by
  unfold transverseHsCoeff
  rw [map_add, scalarCellToTorus_fourierCoeff_add]

theorem transverseHsCoeff_smul {s : ℕ} (c : ℝ) (U : TorusHk s ℂ) (n : Fin 2 → ℤ) :
    transverseHsCoeff (c • U) n = (c : ℂ) * transverseHsCoeff U n := by
  unfold transverseHsCoeff
  have h : c • torusHkValueCLM U = cellScalarCLM (c : ℂ) (torusHkValueCLM U) := by
    rw [cellScalarCLM_smul]
    exact (Complex.coe_smul c _).symm
  rw [map_smul, h, scalarCellToTorus_fourierCoeff_scalar]

theorem transverseHs_exists (e : Fin 2) (s : ℕ) (U : TorusHk s ℂ) :
    ∃ w : TorusHk s ℂ, (∀ n, transverseHsCoeff w n =
      (if n e = 0 then 1 else 0) * transverseHsCoeff U n) ∧ ‖w‖ ≤ 1 * ‖U‖ := by
  refine quietHs_multiplier s (fun n => if n e = 0 then 1 else 0) 1 zero_le_one
    (fun n => ?_) U
  split_ifs <;> simp

theorem transverseHsProjection : TransverseHsProjectionStatement := by
  intro e s
  choose Pf hPc hPn using transverseHs_exists e s
  let L : TorusHk s ℂ →ₗ[ℝ] TorusHk s ℂ :=
    { toFun := Pf
      map_add' := fun U V => transverseHs_ext _ _ (fun n => by
        rw [hPc, transverseHsCoeff_add, transverseHsCoeff_add, hPc, hPc]; ring)
      map_smul' := fun c U => transverseHs_ext _ _ (fun n => by
        rw [hPc, RingHom.id_apply, transverseHsCoeff_smul, transverseHsCoeff_smul, hPc]; ring) }
  refine ⟨L.mkContinuous 1 (fun U => hPn U), fun U => ?_, fun U => ?_⟩
  · change torusHkValueCLM (Pf U) = _
    rw [← scalarTorusToCell_scalarCellToTorus (torusHkValueCLM (Pf U)),
      cellTransverseProjection_apply]
    congr 1
    apply quietHs_ext_coeff
    intro n
    have h1 := hPc U n
    unfold transverseHsCoeff at h1
    rw [h1, scalarTorusTransverseProjection_fourierCoeff]
    split_ifs <;> simp
  · change ‖Pf U‖ ≤ ‖U‖
    simpa using hPn U

end AVRegularity.CycleWords.Assembly
end
end
end
