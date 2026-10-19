-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
public import AVRegularity.Definitions.Construction.ResidualOps
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
public import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees

section
section
/-! Expose the all-order diagonal regularity already established by the native bounded Cauchy argument. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem contextCertified_native_flux_diagonal_contDiff
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} (hG : G.IsContextCertified k)
    (hpar : G.IsSlotTransverse) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2) (lam : ℝ) (n : ℕ) :
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1,
      ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
        G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (lam • X) c) := by
  obtain ⟨θ, f, F, hθ, hHol, hsize, hsem, hbound⟩ :=
    contextCertified_exists_native_complex_bound hG hi hj hb hε p v u γ d I c hm hm2
  let S := (1 + compReserve k v.1 / 4) * (1 / 100) * D.eps (G.level - 1)
  let T := (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (G.level - 1)
  have hS : 0 < S := by dsimp [S]; positivity
  have hST : S ≤ T := by
    dsimp [S, T]
    apply mul_le_mul_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith only [hm2]
  let A : ℕ → ℝ := fun j => ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * bw)) ^ j) *
    ‖lam • (ContinuousLinearMap.proj (transverseIndex p.1) : Vec 2 →L[ℝ] ℝ)‖ ^ j
  have hA (j : ℕ) : 0 ≤ A j := by dsimp [A]; positivity
  obtain ⟨_B, _hB, hdiag⟩ := base_fast_diagonal_exists_jet_bounds S T hS hST lam A hA n
  intro t ht
  apply contDiff_iff_contDiffAt.mpr
  intro Y
  let Fb : (Fin 2 → ℂ) → Vec 2 → ℂ := fun Z z => F p ⟨G.level - 1, [p.1]⟩ 0 t
    (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ)))
  have hd (z : Vec 2) : DifferentiableOn ℂ (fun Z => Fb Z z)
      {Z | (∑ a, |(Z a).im|) < T} :=
    native_holomorphic_base_slice D bw hb j₀ G.level p.1 f (F p) hHol t ht
      (fun a => (z a : ℂ)) (fun _ => Complex.ofReal_im _)
  have hfast (Z : Fin 2 → ℂ) (hZ : (∑ a, |(Z a).im|) < S) (z : Vec 2) :=
    native_complex_fast_affine_regular_and_jets G hi hj hb hε hpar p v u γ d I c f F hHol
      t ht (fun ctx X z => hsem ctx t ht X z) (compReserve k v.1) hm hm2 k.Lstar θ hθ hsize
      Z hZ z lam n
  obtain ⟨hreg, _hnorm⟩ := hdiag Fb hd (fun Z hZ z => (hfast Z hZ z).1) θ hθ
    (fun Z hZ z => hbound t ht z Z hZ)
    (fun Z hZ z => (hfast Z hZ z).2) Y (lam • Y)
  let sf : Vec 2 → ℝ := fun X =>
    G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (lam • X) c
  let H : Vec 2 → ℂ := fun X => Fb (fun a => ((Y + X) a : ℂ)) (lam • Y + lam • X)
  have he : (fun X : Vec 2 => sf (Y + X)) = Complex.reCLM ∘ H := by
    funext X
    have hh := native_flux_holomorphic_realization G hi hj p v u γ d I c f (F p) hHol t ht
      (fun ctx X z => hsem ctx t ht X z) (Y + X) (lam • Y + lam • X)
    have hh' : H X = (sf (Y + X) : ℂ) := by
      simpa only [sf, Fb, H, smul_add] using hh
    exact (congrArg Complex.re hh').symm
  have hreal : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec 2 => sf (Y + X)) 0 := by
    rw [he]
    exact Complex.reCLM.contDiff.contDiffAt.comp (f := H) 0 hreg
  have hreal' : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec 2 => sf (Y + X)) (Y - Y) := by
    rw [sub_self]
    exact hreal
  have hsub : ContDiffAt ℝ (n : ℕ∞) (fun X : Vec 2 => X - Y) Y :=
    contDiffAt_id.sub contDiffAt_const
  have hh := hreal'.comp (f := fun X : Vec 2 => X - Y) Y hsub
  simpa only [Function.comp_def, ← add_sub_assoc, add_sub_cancel_left] using hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The actual dimensional coefficient has every finite diagonal spatial order from its context certificate. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_dimensional_diagonal_contDiff
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e : ℝ) (n : ℕ) (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) :
    ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
      G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t X (e⁻¹ • X) c) := by
  obtain ⟨_, f, _, _, _, _, he, _⟩ :=
    contextCertified_exists_native_complex_bound hG hi hj hb hε p v u γ d I c hm hm2
  have heq : (fun X : Vec 2 => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
      v u γ d I t X (e⁻¹ • X) c) =
      fun X => (ν * e ^ (d - 2)) *
        G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (e⁻¹ • X) c := by
    funext X
    exact actual_native_dimFlux_eq G hi hj p (hnat.2.2.1 p) v u γ d I c t f
      (fun ctx X z => he ctx t ht X z) hε.ne' ν e X (e⁻¹ • X)
  rw [heq]
  exact (contextCertified_native_flux_diagonal_contDiff hG hpar hi hj hb hε p v u γ d I c
    hm hm2 e⁻¹ n t ht).const_smul (ν * e ^ (d - 2))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The reference mean controls normalized fresh ellipses uniformly after relaxation.
Two short transported Jacobians then bound each actual fresh axis. -/
@[expose] public noncomputable section
open Homogenization Filter Topology
namespace AVRegularity.Construction.Preservation.FullLift

/-- Uniform pointwise diagonal bounds relative to the coarser reference mean. -/
theorem uniform_normalized_fresh_flux_bound
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∃ R : ℝ, 0 < R ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ b, m₀ ≤ b + 1 → b + 1 ≤ D.term → ∀ t i,
      Real.sqrt ((D.κ b)⁻¹ *
        ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) t i i) ≤ R := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hb⟩ := CycleReference.bandChain_memory_scale hα₀ hα₁ hs₀ hs₁ hq hζ
  have hc := CycleReference.core_coercivity_constant_range.1
  let c : ℝ := (1 - Real.exp (-2)) / 96
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  have h128 := hΛ₀.trans hΛ
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have ht := Buffer.preparation_parent_power_tendsto_zero hq.1 h128 (mul_pos (by norm_num : (0:ℝ) < 4) hδ)
  have hlim : Tendsto (fun m : ℕ => C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  obtain ⟨mf, hmf⟩ := eventually_atTop.1 (hlim.eventually
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1 / 6)))
  refine ⟨Real.sqrt c⁻¹, Real.sqrt_pos.2 (inv_pos.2 hc), max mf 2, by omega, ?_⟩
  intro D hDα hDq hDΛ hDζ hband b hbm hbterm t i
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hκ := CycleReference.bandChain_pos hΛD hζD hband hbterm
  have hκb := CycleReference.bandChain_pos hΛD hζD hband (by omega : b ≤ D.term)
  have hband' : IsOCBandChain α q Λ ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ] using hband
  have hmem := (hb Λ hΛ D.term (by omega) D.κ hband' (b + 1) (by omega) hbterm).1
  have hinv := CycleReference.inverse_memory_rate_time_le (q := D.q) (m := b + 1) hΛD hκ
    (Construction.Stream.ocTau_pos (α := D.α) (q := D.q) hΛD (m := b + 1))
  have hsmall : (ocMu D.q D.Λ (b + 1) (D.κ (b + 1)) *
      ocTau D.α D.q D.Λ (b + 1))⁻¹ ≤ (6:ℝ)⁻¹ := by
    have hs := hmem.trans (hmf (b + 1) (by omega))
    simpa only [hDα, hDq, hDΛ, one_div] using hinv.trans (by
      simpa only [hDα, hDq, hDΛ, one_div] using hs)
  have hμτ : 0 < ocMu D.q D.Λ (b + 1) (D.κ (b + 1)) *
      ocTau D.α D.q D.Λ (b + 1) := mul_pos
    (CycleReference.ocMu_pos hΛD hκ) (Construction.Stream.ocTau_pos hΛD)
  have hrelax : 6 ≤ ocMu D.q D.Λ (b + 1) (D.κ (b + 1)) *
      ocTau D.α D.q D.Λ (b + 1) := (inv_le_inv₀ hμτ (by norm_num)).1 hsmall
  have hlo := (CycleReference.refFlux_mean_core_bounds hΛD hζD hκ hrelax).1
  have hstep := hband.2 (b + 1) (by omega) hbterm
  simp only [Nat.add_sub_cancel] at hstep
  rw [← hstep] at hlo
  have hentry : ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) t i i ≤
      D.κ (b + 1) + ocHStar D.α D.q D.Λ (b + 1) (D.κ (b + 1)) :=
    (le_abs_self _).trans (CycleReference.refFlux_entry_norm_le hΛD hζD hκ i i)
  apply Real.sqrt_le_sqrt
  have hce : c * ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) t i i ≤ D.κ b :=
    (mul_le_mul_of_nonneg_left hentry hc.le).trans hlo
  have he : ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) t i i ≤ c⁻¹ * D.κ b := by
    exact (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hce) |>.trans_eq (by ring)
  calc
    (D.κ b)⁻¹ * _ ≤ (D.κ b)⁻¹ * (c⁻¹ * D.κ b) := mul_le_mul_of_nonneg_left he (inv_pos.2 hκb).le
    _ = c⁻¹ := by field_simp

private theorem norm_le_two_of_deviation (L : Vec 2 →L[ℝ] Vec 2) (h : ‖L - 1‖ ≤ 1) :
    ‖L‖ ≤ 2 := by
  have ht := norm_le_norm_sub_add L (1 : Vec 2 →L[ℝ] Vec 2)
  have h1 : ‖(1 : Vec 2 →L[ℝ] Vec 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith only [ht, h, h1]

/-- Uniform upper bounds on the full fresh axes, not only their spanning columns. -/
theorem uniform_fresh_axes_norm_bound
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∃ Γ : ℝ, 0 < Γ ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ b, m₀ ≤ b + 1 → b + 1 ≤ D.term →
    ∀ S : KernelSpec, IsFreshAxes D b S.H₁ S.H₂ → ∀ t, ‖S.H₁ t‖ ≤ Γ ∧ ‖S.H₂ t‖ ≤ Γ := by
  obtain ⟨Λ₀, hΛ₀, hb⟩ := uniform_normalized_fresh_flux_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  have h128 := hΛ₀.trans hΛ
  obtain ⟨R, hR, mf, hmf, hb⟩ := hb Λ hΛ
  obtain ⟨ms, hms, hs⟩ := uniform_sampled_flow_derivative_deviation α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ h128 1 zero_lt_one le_rfl
  obtain ⟨mc, _hmc, hc⟩ := uniform_quiet_margin_flow_derivative_deviation α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ h128 1 zero_lt_one le_rfl
  refine ⟨8 * R, mul_pos (by norm_num) hR, max mf (max ms mc), by omega, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq hband b hbm hbterm S haxes t
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  obtain ⟨l, ht⟩ := exists_fresh_quiet_margin D b hΛD t
  obtain ⟨tH, tV, lH, lV, hsample, hmat⟩ := haxes l
  let s₀ := ((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)
  have ht' : |t - s₀| ≤ ocTauPP D.α D.q D.Λ (b + 1) := by
    have he : ((l : ℝ) + 3 / 2) * ocTauPP D.α D.q D.Λ (b + 1) = s₀ + ocTauPP D.α D.q D.Λ (b + 1) := by dsimp [s₀]; ring
    rw [he] at ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have htup : t ≤ s₀ + ocTauPP D.α D.q D.Λ (b + 1) := ht.2.le
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using htup)
  have hG := norm_le_two_of_deviation _ (hc D hDα hDq hDΛ hseq b (by omega) s₀ t ht' 0)
  have hS := hs D hDα hDq hDΛ hseq b (by omega) s₀ tH tV lH lV hsample
  have hbound (H : Vec 2 →L[ℝ] Vec 2) (ti : ℝ) (li : ℤ)
      (hH : H = (Matrix.toLin' (jacMatrix (fun y => D.flowOf b t y s₀) 0 *
        sampledEllipse D b s₀ ti li)).toContinuousLinearMap)
      (hder : ‖sampledFlowDerivative D b s₀ ti li - 1‖ ≤ 1) : ‖H‖ ≤ 8 * R := by
    have hcol (i : Fin 2) : ‖H (basisVec i)‖ ≤ 4 * R := by
      rw [hH]
      change ‖Matrix.toLin' _ (basisVec i)‖ ≤ _
      rw [transported_sampledEllipse_apply_basis, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hscale := hb D hDα hDq hDΛ hDζ hband b (by omega) hbterm ti i
      have hinner := (sampledFlowDerivative D b s₀ ti li).le_opNorm (basisVec i)
      have hbn : ‖(basisVec i : Vec 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
      rw [hbn, mul_one] at hinner
      have hinner' := hinner.trans (norm_le_two_of_deviation _ hder)
      have houter := (fderiv ℝ (fun y => D.flowOf b t y s₀) 0).le_opNorm
        (sampledFlowDerivative D b s₀ ti li (basisVec i))
      have houter' : ‖fderiv ℝ (fun y => D.flowOf b t y s₀) 0
          (sampledFlowDerivative D b s₀ ti li (basisVec i))‖ ≤ 4 :=
        houter.trans ((mul_le_mul hG hinner' (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
      exact (mul_le_mul hscale houter' (norm_nonneg _) hR.le).trans_eq (by ring)
    exact (AVenhance.timeIncrement_clm_norm_le_two_basis (by positivity) (hcol 0) (hcol 1)).trans_eq (by ring)
  obtain ⟨hH₁, hH₂⟩ := hmat t ht
  exact ⟨hbound (S.H₁ t) tH lH hH₁ hS.1, hbound (S.H₂ t) tV lV hH₂ hS.2⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The native context certificate gives all-order dimensional diagonal bounds without a higher envelope premise. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_dimensional_diagonal_all_order_bounds
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (A : Set ℝ) (hAP : A ⊆ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e : ℝ) (n : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t ∈ A, ∀ j ≤ n, ∀ Y : Vec 2,
        ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
            v u γ d I t X (e⁻¹ • X) c) Y‖ ≤ C j := by
  obtain ⟨C, hC, hbound⟩ := contextCertified_native_flux_diagonal_bounds
    hG hpar hi hj hb hε p v u γ d I c hm hm2 e⁻¹ n
  obtain ⟨_, f, _, _, _, _, he, _⟩ :=
    contextCertified_exists_native_complex_bound hG hi hj hb hε p v u γ d I c hm hm2
  refine ⟨fun j => ‖ν * e ^ (d - 2)‖ * C j,
    fun j => mul_nonneg (norm_nonneg _) (hC j), ?_⟩
  intro t ht j hjn Y
  let sf : Vec 2 → ℝ := fun X => G.fam.flux p
    (nativeStageContext G hi hj p X) v u γ d I t 0 (e⁻¹ • X) c
  have hreg := native_dimensional_diagonal_contDiff hG hpar hnat hi hj hb hε p v u γ d I c
    hm hm2 ν e n t (hAP ht)
  have heq : (fun X : Vec 2 => G.fam.dimFlux ν e (D.eps (G.level - 1)) p
      (G.actual p) v u γ d I t X (e⁻¹ • X) c) =
      fun X => (ν * e ^ (d - 2)) * sf X := by
    funext X
    exact actual_native_dimFlux_eq G hi hj p (hnat.2.2.1 p) v u γ d I c t f
      (fun ctx X z => he ctx t (hAP ht) X z) hε.ne' ν e X (e⁻¹ • X)
  rw [heq] at hreg ⊢
  by_cases ha : ν * e ^ (d - 2) = 0
  · simp only [ha, zero_mul, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, le_refl]
  · have hsreg : ContDiff ℝ (n : ℕ∞) sf := by
      have hh := hreg.const_smul (ν * e ^ (d - 2))⁻¹
      simpa only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha, one_mul] using hh
    change ‖iteratedFDeriv ℝ j (fun X => (ν * e ^ (d - 2)) • sf X) Y‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hsreg.contDiffAt.of_le (by exact_mod_cast hjn)),
      norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound t (hAP ht) j hjn Y) (norm_nonneg _)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The named readoutEnergy in FullLiftClauses inherits the ordinary and marked word-menu bound,
including its prescribed truncation to any reserved order. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem actual_readoutEnergy_le {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hactual : IsActualSuccessor D P Mn G G')
    {m : ℕ} (hlevel : G.level = m) (hm : 1 ≤ m)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (law : BirthLaw)
    (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB) (hη0 : 0 ≤ law.eta0) (hiota : 0 ≤ law.iota)
    {K Naux : ℕ} (hKN : K ≤ Naux) (ρ a t : ℝ)
    (wout : CompIn G.comps → ℝ) (wr : CompIn (G'.retained m Mn.H Mn.J).comps → ℝ)
    (hweights : (wout = fun _ => 1) ∧ (wr = fun _ => 1) ∨
      wout = G.marker law ∧ wr = (G'.retained m Mn.H Mn.J).marker law)
    (u : ∀ c : CompIn (G'.retained m Mn.H Mn.J).comps, ℝ → TorusHk Naux (hr c.1.root))
    (uw : ∀ c : CompIn (G'.retained m Mn.H Mn.J).comps, ℝ → TorusHk (Naux + 1) (hr c.1.root))
    (hw : ∀ c, MemLp (uw c) 2 (volume.restrict (Set.Icc a t))) :
    readoutEnergy law G (G'.retained m Mn.H Mn.J) m law.eta0 ρ hKN wout a t u uw ≤
      ENNReal.ofReal (Real.sqrt ((wordsUpTo Mn.A (Mn.J + 1)).card + 1)) *
        strongEnergy ρ (D.κ (m - 1))
          (fun c => (G'.retained m Mn.H Mn.J).mass law c / wr c ^ 2) a t u uw := by
  rcases hweights with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [readoutEnergy, one_pow, div_one]
    apply (strongEnergy_truncate_le hKN ρ (D.κ (m - 1)) (G.mass law) a t _ _).trans
    exact actual_retained_readout_strongEnergy hactual hlevel hm hold hq hΛ law hcH hηB hη0
      ρ (D.κ (m - 1)) a t u uw hw
  · unfold readoutEnergy
    apply (strongEnergy_truncate_le hKN ρ (D.κ (m - 1))
      (fun v => G.mass law v / G.marker law v ^ 2) a t _ _).trans
    exact actual_retained_marked_readout_strongEnergy hactual hlevel hm hold hq hΛ law hcH hηB hη0 hiota
      ρ (D.κ (m - 1)) a t u uw hw

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Molecular and enhanced radii decrease toward finer levels. Consequently inherited
kernel widths remain within both budgets when the stage moves to its parent. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-- The ceiling in the renewal time preserves its scale monotonicity. -/
theorem renewal_time_step_le {α s q : ℝ} {Λ m : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    ocTauPP α q Λ m ≤ ocTauPP α q Λ (m - 1) := by
  have hp : 0 < 2 - (1 + α) + 2 * ocDelta α q := by
    have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
    linarith only [hα₁, hδ]
  have he := EntryScales.epsilon_antitone hq.1 hΛ (Nat.sub_le (m - 1) 1)
  have he0 := Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) (by omega : 1 ≤ Λ)
  have hexp := Real.rpow_le_rpow_of_nonpos he0 he (neg_nonpos.mpr hp.le)
  have hceil : (⌈ocEpsilon q Λ (m - 1 - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊ : ℝ) ≤
      (⌈ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊ : ℝ) :=
    Nat.cast_le.mpr (Nat.ceil_mono hexp)
  have hden : 0 < (⌈ocEpsilon q Λ (m - 1 - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊ : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr (Real.rpow_pos_of_pos
      (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _)
  exact div_le_div_of_nonneg_left (by positivity) hden hceil

/-- Both radii at the finer stage lie below the corresponding parent radii. -/
theorem radii_step_le {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (D : OCData) (hDα : D.α = α) (hDq : D.q = q) (hDΛ : D.Λ = Λ)
    (hband : IsOCBandChain α q Λ ζ D.term D.κ)
    (c₀ cr : ℝ) (hc₀ : 0 ≤ c₀) (hcr : 0 ≤ cr) (m : ℕ) (hm : 2 ≤ m) (hmt : m ≤ D.term) :
    rhoStar D c₀ m ≤ rhoStar D c₀ (m - 1) ∧ rhoEnh D cr m ≤ rhoEnh D cr (m - 1) := by
  have he := EntryScales.epsilon_antitone hq.1 hΛ (Nat.sub_le m 1)
  have hκ := CycleReference.bandChain_step_ge (by omega : 1 ≤ Λ) hζ hband (by omega : 1 ≤ m) hmt
  have hκ' := CycleReference.bandChain_step_ge (by omega : 1 ≤ Λ) hζ hband
    (by omega : 1 ≤ m - 1) (by omega : m - 1 ≤ D.term)
  have hκ0 := (CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hband hmt).le
  have hκ0' := (CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hband
    (by omega : m - 1 ≤ D.term)).le
  have hA : ocA α q Λ (m - 1) ≤ ocA α q Λ m := by
    exact Real.rpow_le_rpow_of_nonpos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ))
      he (by linarith only [hα₁])
  have hA0 : 0 < ocA α q Λ (m - 1) := Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _
  have hτ := renewal_time_step_le hα₀ hα₁ hs₀ hs₁ hq hΛ (m := m)
  constructor
  · unfold rhoStar OCData.eps
    rw [hDα, hDq, hDΛ]
    apply mul_le_mul_of_nonneg_left _ hc₀
    exact min_le_min he (Real.sqrt_le_sqrt (div_le_div₀ (hκ0.trans hκ) hκ hA0 hA))
  · unfold rhoEnh
    rw [hDα, hDq, hDΛ]
    apply mul_le_mul_of_nonneg_left _ hcr
    exact Real.sqrt_le_sqrt (mul_le_mul hκ' hτ
      (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ)).le
      (hκ0'.trans hκ'))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Native diagonal joint measurability follows directly from the context certificate. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_diagonal_joint_measurable
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1))
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2) (ν e : ℝ) :
    Measurable (fun z : Set.Icc a b × Vec 2 => G.fam.weight p z.1 •
      G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I
        z.1 z.2 (e⁻¹ • z.2)) := by
  have hp : (G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ G.level p.1 :=
    (hnat.1 p).2.1
  have hw : Measurable (G.fam.weight p) := by
    have he : G.fam.weight p = ocCutoff D.α D.q D.Λ G.level p.1 :=
      funext (hnat.2.1 p)
    rw [he]
    exact (CycleReference.ocCutoff_contDiff hΛ p.1).continuous.measurable
  have hz (t : ℝ) (ht : t ∉ ocPulseWindow D.α D.q D.Λ G.level p.1) :
      G.fam.weight p t = 0 := G.fam.weight_zero p t (hp ▸ ht)
  have hc (t : Set.Icc a b) : Continuous (fun X : Vec 2 => G.fam.weight p t •
      G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t X (e⁻¹ • X)) := by
    by_cases ht : (t : ℝ) ∈ ocPulseWindow D.α D.q D.Λ G.level p.1
    · exact (continuous_pi (fun c =>
        (native_dimensional_diagonal_contDiff hG hpar hnat hi hj hb hε p v u γ d I c
          hm hm2 ν e 0 t ht).continuous)).const_smul (G.fam.weight p t)
    · simp only [hz t ht, zero_smul]
      exact continuous_const
  have ht (X : Vec 2) : Measurable (fun t : Set.Icc a b => G.fam.weight p t •
      G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t X (e⁻¹ • X)) := by
    have hf := measurable_weighted_local_field measurableSet_Icc (G.fam.weight p)
      (fun t => G.fam.flux p (G.actual p) v u γ d I t
        ((D.eps (G.level - 1))⁻¹ • X) (e⁻¹ • X)) hw hz
      (contextCertified_flux_time_measurable_vec hG p (G.actual p) v u γ d I
        ((D.eps (G.level - 1))⁻¹ • X) (e⁻¹ • X))
    have hs : Measurable (fun t : Set.Icc a b => (ν * e ^ (d - 2)) •
        (G.fam.weight p t • G.fam.flux p (G.actual p) v u γ d I t
          ((D.eps (G.level - 1))⁻¹ • X) (e⁻¹ • X))) :=
      (hf.const_smul (ν * e ^ (d - 2))).comp measurable_subtype_coe
    simpa only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, smul_smul, mul_comm] using hs
  exact (measurable_uncurry_of_continuous_of_measurable hc ht).comp measurable_swap

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Construct the covariance value and gradient inputs from the given lifted field and original retained gradient. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem liftedField_covariance_energy_input_exists
    (G Gr : GenStage D hr Dm bw j₀) (m p Naux N H sX sZ k : ℕ)
    (hk : k + N + 2 * p ≤ Naux) (η tp tf : ℝ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ m)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (hYw : ∀ v, MemLp (Yw v) 2 (volume.restrict (Set.Icc tp tf)))
    (hcompat : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      truncateTorusHk (Nat.le_succ Naux) (Yw v t) = Y v t)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (hfield : IsLiftedField G Gr m p Naux N H sX sZ η tp tf Y CcT PZ a u)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((k + N + 1 : ℕ) : ℕ∞) (a t)) :
    let z := fun v t => truncateTorusHk hk
      (succReadout m (D.eps (m - 1)) η Naux (fun c => Y c t) v)
    let zw := fun v t => truncateTorusHk (Nat.succ_le_succ hk)
      (succReadout m (D.eps (m - 1)) η (Naux + 1) (fun c => Yw c t) v)
    ∃ (Z : ∀ v : CompIn G.comps, ℝ → TorusHk (k + N) (hr v.1.root))
      (Zw : ∀ v : CompIn G.comps, ℝ → TorusHk (k + N + 1) (hr v.1.root)),
      (∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Z v t) (fun x => a t x v) (k + N)) ∧
      (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
        IsClassicalRep (Zw v t) (fun x => a t x v) (k + N + 1)) ∧
      (∀ v, AEStronglyMeasurable (Zw v) (volume.restrict (Set.Icc tp tf))) ∧
      (∀ v, ∀ t ∈ Set.Icc tp tf, IsCovImage (covPolyP (covPrimitive D m t) p) (z v t) (Z v t)) ∧
      (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
        IsCovImage (covPolyP (covPrimitive D m t) p) (zw v t) (Zw v t)) ∧
      (∀ v, MemLp (zw v) 2 (volume.restrict (Set.Icc tp tf))) := by
  intro z zw
  have hK : k + N ≤ Naux - 2 * p := by omega
  let Z := fun v t => truncateTorusHk hK (PZ v t)
  have hZ (v : CompIn G.comps) (t : ℝ) (ht : t ∈ Set.Icc tp tf) :
      IsClassicalRep (Z v t) (fun x => a t x v) (k + N) :=
    classicalRep_truncate hK le_rfl (PZ v t) _
      (classicalRep_order_mono (PZ v t) _ (hfield.2.1 v t ht).2 hK)
  have hcov (v : CompIn G.comps) (t : ℝ) (ht : t ∈ Set.Icc tp tf) :
      IsCovImage (covPolyP (covPrimitive D m t) p) (z v t) (Z v t) :=
    covImage_truncate_input hk _ _ _ (covImage_truncate hK _ _ _ (hfield.2.1 v t ht).1)
  have hzw (v : CompIn G.comps) : MemLp (zw v) 2 (volume.restrict (Set.Icc tp tf)) :=
    memLp_truncated_succReadout (Nat.succ_le_succ hk) m (D.eps (m - 1)) η Yw hYw v
  have hex (v : CompIn G.comps) := smooth_covImage_gradient_window_exists tp tf
    (fun t => covPrimitive D m t)
    (fun i j => (native_covPrimitive_entry_continuous D m hΛ hζ hν i j).continuousOn)
    (z v) (zw v) (Z v) (fun t x => a t x v) (hZ v)
    (fun t ht => (ContinuousLinearMap.proj (R := ℝ) (φ := fun v : CompIn G.comps => hr v.1.root) v).contDiff.comp (ha t ht)) (hzw v).aestronglyMeasurable
    (readout_gradient_compatible_ae hk m (D.eps (m - 1)) η _ Y Yw hcompat v) (hcov v)
  choose Zw hZw using hex
  refine ⟨Z, Zw, hZ, ?_, ?_, hcov, ?_, hzw⟩
  · intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hZw v).1 t ht |>.1
  · exact fun v => (hZw v).2.2
  · exact fun v => (hZw v).2.1

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Before partition weighting, every actual native transported array has all spatial orders. -/

open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_raw_piece_all_order_smooth
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e : ℝ) (n r : ℕ) (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) :
    ContDiff ℝ (n : ℕ) (fun y => nativeArrayAssembly r (G.fam.identity v u γ).map
      (fun a A => transportedCoeff
        (naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t)
        (G.fam.identity v u γ).maxOrder
        (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
          (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
          (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)) r A y a)) := by
  let B := fun d (I : DerivativeWord2 (d - 1)) y =>
    G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
      (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
      (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
  have hflow : ContDiff ℝ (n : ℕ∞)
      (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t) :=
    (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) t).of_le (by simp)
  have hB d I c : ContDiff ℝ (n : ℕ) (fun y => B d I y c) :=
    (native_dimensional_diagonal_contDiff hG hpar hnat hi hj hb hε p v u γ d I c
      hm hm2 ν e n t ht).comp hflow
  apply nativeArrayAssembly_spatial_smooth r n (G.fam.identity v u γ).map
  intro a A
  exact transportedCoeff_spatial_smooth _
    (fun a b => (naturalPreparationJacobian_entry_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) a b).comp (contDiff_const.prodMk contDiff_id))
    (G.fam.identity v u γ).maxOrder n B hB r A a

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Joint measurability of the incoming native samples along its actual inverse flow. -/

section
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_sample_joint_measurable_of_context
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hcert : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1)) (ν e tS tZ : ℝ)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1))
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G.fam.weight p z.1 •
      G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I z.1
        (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)
        (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)) := by
  have hy : Continuous (fun z : Set.Icc tS tZ × Vec 2 =>
      D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1) := by
    exact (CycleReference.streamFlow_joint_smooth (D.hΦ (G.level - 1))).continuous.comp
      (continuous_const.prodMk (continuous_snd.prodMk
        (continuous_subtype_val.comp continuous_fst)))
  exact (native_weighted_diagonal_joint_measurable hcert hpar hnat hΛ hi hj hb hε tS tZ
    p v u γ d I hm hm2 ν e).comp
      (measurable_fst.prodMk hy.measurable)
end

/-! Joint measurability of the incoming stage's actual weighted Piola arrays. -/

section
open AVRegularity.Construction.Preservation.Buffer
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_piece_array_joint_measurable_of_context
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hcert : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1)) (ν e tS tZ : ℝ)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G.fam.weight p z.1 *
      transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material z.1).symm)
        (G.fam.identity v u γ).maxOrder
        (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I z.1
          (((G.fam.piece p).material z.1).symm z.2)
          (e⁻¹ • ((G.fam.piece p).material z.1).symm z.2)) r A z.2 a) := by
  let K := naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1)
  let B := fun d (I : DerivativeWord2 (d - 1)) (z : Set.Icc tS tZ × Vec 2) =>
    G.fam.weight p z.1 • G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I z.1
      (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)
      (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)
  have hB : ∀ d I i, Measurable (fun z => B d I z i) := by
    intro d I i
    exact (measurable_pi_apply i).comp
      (native_weighted_sample_joint_measurable_of_context hcert hpar hnat hΛ hi hj hb hε ν e tS tZ
        p v u γ d I hm hm2)
  have hm := transportedCoeff_joint_measurable tS tZ K
    (naturalPreparationJacobian_entry_smooth (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1))
    (G.fam.identity v u γ).maxOrder B hB r A a
  convert hm using 1
  funext z
  dsimp [B, K]
  rw [transportedCoeff_smul_native]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [native_inverse_jacobian_eq_natural hnat p z.1,
    native_inverse_material_eq_flow hnat p z.1]
  rfl
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Joint measurability of the incoming stage's literal Eulerian coefficients. -/

open AVRegularity.Construction.Preservation.Buffer
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_constituentPhysical_joint_measurable_of_context
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hcert : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1)) (ν e tS tZ : ℝ)
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve k v.1 ≤ 2)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      constituentPhysical G.fam ν e (D.eps (G.level - 1)) G.actual v u γ d z.1 z.2) := by
  let b := fun p (z : Set.Icc tS tZ × Vec 2) a (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material z.1).symm)
      (G.fam.identity v u γ).maxOrder
      (fun d' I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d' I z.1
        (((G.fam.piece p).material z.1).symm z.2)
        (e⁻¹ • ((G.fam.piece p).material z.1).symm z.2)) (d - 1) A z.2 a
  change Measurable (fun z : Set.Icc tS tZ × Vec 2 => ∑ᶠ p,
    G.fam.weight p z.1 • nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p z))
  refine measurable_piece_finsum_onWindow G.fam tS tZ
    (fun p z => G.fam.weight p z.1 •
      nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p z)) ?_ ?_
  · intro p
    have hm := nativeArrayAssembly_measurable (d - 1) (G.fam.identity v u γ).map
      (fun z a A => G.fam.weight p z.1 * b p z a A)
      (fun a A => native_weighted_piece_array_joint_measurable_of_context hcert hpar hnat hΛ hi hj
        hb hε ν e tS tZ p v u γ (hm v) (hm2 v) (d - 1) A a)
    convert hm using 1
    funext z
    exact ((nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map).map_smul
      (G.fam.weight p z.1) (b p z)).symm
  · intro p z hout
    rw [G.fam.weight_zero p z.1 hout]
    exact zero_smul ℝ (nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p z))

theorem native_physCoeff_joint_measurable_of_context
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hcert : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1)) (tS tZ : ℝ)
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve k v.1 ≤ 2)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G.physCoeff v u γ d z.1 z.2) :=
  native_constituentPhysical_joint_measurable_of_context hcert hpar hnat hΛ hi hj
    hb hε (D.kap G.level) (D.eps G.level) tS tZ hm hm2 v u γ d

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Actual dimensional native flux sampled by the stage flow has uniform spatial jets. -/

open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_sampled_all_order_bounds
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (A : Set ℝ) (hAP : A ⊆ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e : ℝ) (n : ℕ)
    (T : Set ℝ) (hT : IsCompact T)
    (hAT : A ⊆ T) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t ∈ A, ∀ j ≤ n, ∀ Y : Vec 2,
        ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
            v u γ d I t
            (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
              (D.slotAnchor G.level p.1) X t)
            (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
              (D.slotAnchor G.level p.1) X t) c) Y‖ ≤ C j := by
  obtain ⟨C, hC, hbnd⟩ := native_dimensional_diagonal_all_order_bounds hG hpar hnat
    hi hj hb hε p A hAP v u γ d I c hm hm2 ν e n
  apply native_flow_pullback_jet_bounds (D.hΦ (G.level - 1))
    (D.slotAnchor G.level p.1) T hT
    A hAT n
    (fun t X => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
      v u γ d I t X (e⁻¹ • X) c) _ C hC hbnd
  intro t ht
  exact native_dimensional_diagonal_contDiff hG hpar hnat hi hj hb hε p v u γ d I c
    hm hm2 ν e n t (hAP ht)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleReference AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual weighted native sample has uniform scalar budgets on the working window. -/

section
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_all_order_scalar_budgets
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) :
    ∃ MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ,
      (∀ d I, 0 ≤ MB d I) ∧
      (∀ t ∈ Set.Icc a b, ∀ d I c, ContDiff ℝ (n : ℕ)
        (fun X => nativeWeightedSampledFlux G ν e p v u γ d I t X c)) ∧
      ∀ t ∈ Set.Icc a b, ∀ d I c j, j ≤ n → ∀ X,
        ρ ^ j * ‖iteratedFDeriv ℝ j
          (fun Y => nativeWeightedSampledFlux G ν e p v u γ d I t Y c) X‖ ≤ MB d I := by
  let W := Set.Icc a b
  let A := W ∩ ocPulseWindow D.α D.q D.Λ G.level p.1
  let raw := fun d (I : DerivativeWord2 (d - 1)) t X =>
    G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
      (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) X t)
      (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
        (D.slotAnchor G.level p.1) X t)
  have hflow (t : ℝ) : ContDiff ℝ (n : ℕ∞)
      (fun X : Vec 2 => streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
        (D.slotAnchor G.level p.1) X t) :=
    ((streamFlow_joint_smooth (D.hΦ (G.level - 1))).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).of_le (by simp)
  have hraw (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (ht : t ∈ A) (c : Fin 2) :
      ContDiff ℝ (n : ℕ) (fun X => raw d I t X c) :=
    (native_dimensional_diagonal_contDiff hG hpar hnat hi hj hb hε p v u γ d I c
      hm hm2 ν e n t ht.2).comp (hflow t)
  have hz (t : ℝ) (ht : t ∉ A) (hW : t ∈ W) : G.fam.weight p t = 0 := by
    apply G.fam.weight_zero p t
    intro hout
    apply ht
    exact ⟨hW, by rw [← (hnat.1 p).2.1]; exact hout⟩
  have hreg (t : ℝ) (ht : t ∈ W) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
      ContDiff ℝ (n : ℕ) (fun X => nativeWeightedSampledFlux G ν e p v u γ d I t X c) := by
    change ContDiff ℝ (n : ℕ) (fun X => G.fam.weight p t • raw d I t X c)
    by_cases h : t ∈ A
    · exact (hraw d I t h c).const_smul _
    · simp only [hz t h ht, zero_smul]
      exact contDiff_const
  have hex (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
      ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ t ∈ W, ∀ j ≤ n, ∀ X,
        ‖iteratedFDeriv ℝ j (fun Y => nativeWeightedSampledFlux G ν e p v u γ d I t Y c) X‖ ≤ C j := by
    obtain ⟨C, hC, hbound⟩ := native_sampled_all_order_bounds hG hpar hnat hi hj hb hε
      p A (fun _ ht => ht.2) v u γ d I c hm hm2 ν e n
      W isCompact_Icc (fun _ ht => ht.1)
    refine ⟨C, hC, ?_⟩
    intro t ht j hjn X
    change ‖iteratedFDeriv ℝ j (fun Y => G.fam.weight p t • raw d I t Y c) X‖ ≤ C j
    by_cases h : t ∈ A
    · rw [iteratedFDeriv_const_smul_apply' ((hraw d I t h c).contDiffAt.of_le
        (by exact_mod_cast hjn)), norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (family_weight_abs_le_one G.fam p t) (norm_nonneg _)).trans
        (by rw [one_mul]; exact hbound t h j hjn X)
    · simp only [hz t h ht, zero_smul, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact hC j
  have hbudget (d : ℕ) (I : DerivativeWord2 (d - 1)) :=
    scalar_component_common_scaled_jet_budget W n ρ hρ
      (fun t X => nativeWeightedSampledFlux G ν e p v u γ d I t X) (hex d I)
  choose MB hMB hbudget using hbudget
  exact ⟨MB, hMB, hreg, fun t ht d I c j hjn X => hbudget d I t ht c j hjn X⟩
end

/-! The actual weighted physical constituent is smooth at every finite order from its context certificate. -/

section
open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_piece_all_order_smooth
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e : ℝ) (n r : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (n : ℕ) (fun x => G.fam.weight p t •
      nativeArrayAssembly r (G.fam.identity v u γ).map
        (fun i A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
          (G.fam.identity v u γ).maxOrder
          (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
            (((G.fam.piece p).material t).symm x)
            (e⁻¹ • ((G.fam.piece p).material t).symm x)) r A x i)) := by
  let KK := naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t
  let B := fun d I => nativeWeightedSampledFlux G ν e p v u γ d I t
  obtain ⟨_MB, _hMB, hB, _hBj⟩ := native_weighted_all_order_scalar_budgets hG hpar hnat
    hi hj hb hε a b p v u γ hm hm2 ν e 0 le_rfl n
  have he : (fun x => G.fam.weight p t • nativeArrayAssembly r (G.fam.identity v u γ).map
      (fun i A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
        (G.fam.identity v u γ).maxOrder
        (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
          (((G.fam.piece p).material t).symm x)
          (e⁻¹ • ((G.fam.piece p).material t).symm x)) r A x i)) =
      fun x => nativeArrayAssembly r (G.fam.identity v u γ).map
        (fun i A => transportedCoeff KK (G.fam.identity v u γ).maxOrder
          (fun d I => B d I x) r A x i) := by
    funext x
    rw [native_inverse_jacobian_eq_natural hnat p t, native_inverse_material_eq_flow hnat p t]
    exact (weighted_native_array_assembly KK (G.fam.identity v u γ).maxOrder r
      (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
        (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) x t)
        (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
          (D.slotAnchor G.level p.1) x t))
      (G.fam.weight p t) (G.fam.identity v u γ).map x).symm
  rw [he]
  apply nativeArrayAssembly_spatial_smooth r n (G.fam.identity v u γ).map
  intro i A
  exact transportedCoeff_spatial_smooth KK
    (fun i j => (naturalPreparationJacobian_entry_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) i j).comp (contDiff_const.prodMk contDiff_id))
    (G.fam.identity v u γ).maxOrder n B (hB t ht) r A i
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Genuine native coefficient jets give a finite seminorm for the actual physical coefficient. -/

open AVRegularity.Construction.Preservation.Buffer
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_physCoeff_all_order_smooth
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (n d : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (n : ℕ) (G.physCoeff v u γ d t) := by
  classical
  let A := fun p s x => G.fam.weight p s •
    nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map
      (fun i W => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material s).symm)
        (G.fam.identity v u γ).maxOrder
        (fun d' I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
          p (G.actual p) v u γ d' I s
          (((G.fam.piece p).material s).symm x)
          ((D.eps G.level)⁻¹ • ((G.fam.piece p).material s).symm x)) (d - 1) W x i)
  have he : G.physCoeff v u γ d t =
      fun x => ∑ p ∈ (G.fam.locally_finite a b).toFinset, A p t x := by
    funext x
    exact constituentPhysical_eq_window_sum G.fam (D.kap G.level) (D.eps G.level)
      (D.eps (G.level - 1)) G.actual a b t ht v u γ d x
  rw [he]
  exact ContDiff.sum (fun p _ => native_weighted_piece_all_order_smooth hG hpar hnat
    hi hj hb hε a b p v u γ hm hm2 (D.kap G.level) (D.eps G.level) n (d - 1) t ht)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleReference AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual weighted native piece has a finite coefficient seminorm. -/

open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_piece_all_order_seminorm_finite
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1))
    (n r : ℕ) :
    coefficientSeminorm ρ n a b (fun t x => G.fam.weight p t •
      nativeArrayAssembly r (G.fam.identity v u γ).map
        (fun i A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
          (G.fam.identity v u γ).maxOrder
          (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
            (((G.fam.piece p).material t).symm x)
            (e⁻¹ • ((G.fam.piece p).material t).symm x)) r A x i)) ≠ ⊤ := by
  let KK := fun t => naturalPreparationJacobian (D.hΦ (G.level - 1))
    (D.slotAnchor G.level p.1) t
  let B := fun t d I => nativeWeightedSampledFlux G ν e p v u γ d I t
  obtain ⟨MB, hMB, hB, hBj⟩ := native_weighted_all_order_scalar_budgets hG hpar hnat
    hi hj hb hε a b p v u γ hm hm2 ν e ρ hρ.le n
  let L := n + (G.fam.identity v u γ).maxOrder
  obtain ⟨C, hC, hKC⟩ := naturalPreparationJacobian_compact_scaled_jets
    (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) (Set.Icc a b) isCompact_Icc
    (D.eps (G.level - 1)) hε.le L
  have hK (t : ℝ) (_ht : t ∈ Set.Icc a b) (i j : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x => KK t x i j) :=
    (naturalPreparationJacobian_entry_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) i j).comp (contDiff_const.prodMk contDiff_id)
  have hf := native_transport_coefficientSeminorm_finite a b KK hK L
    (G.fam.identity v u γ).maxOrder n r C (D.eps (G.level - 1)) ρ hC hε hρ hρε
    le_rfl hKC B hB MB hMB
    (fun t ht d _ I i j hjn x => hBj t ht d I i j hjn x) (G.fam.identity v u γ).map
  apply ne_top_of_le_ne_top hf
  apply le_of_eq
  congr 1
  funext t x
  rw [native_inverse_jacobian_eq_natural hnat p t, native_inverse_material_eq_flow hnat p t]
  exact (weighted_native_array_assembly (KK t) (G.fam.identity v u γ).maxOrder r
    (fun d I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
      (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) x t)
      (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
        (D.slotAnchor G.level p.1) x t))
    (G.fam.weight p t) (G.fam.identity v u γ).map x).symm

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Positive transported piece budgets control the literal native physical seminorm. -/

section
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_physCoeff_seminorm_le_of_piece_jets
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (n d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (g : ℝ → OddSlot → Vec 2 →
      ((PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))))
    (hg : ∀ t p y, g t p y = nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map
      (fun a A => transportedCoeff
        (naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t)
        (G.fam.identity v u γ).maxOrder
        (fun d' I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
          p (G.actual p) v u γ d' I t
          (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) y t)
          ((D.eps G.level)⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
            (D.slotAnchor G.level p.1) y t)) (d - 1) A y a))
    (hgs : ∀ t ∈ Set.Icc a b, ∀ p, t ∈ (G.fam.piece p).output →
      ContDiff ℝ (n : ℕ) (g t p))
    (hjet : ∀ t ∈ Set.Icc a b, ∀ p, t ∈ (G.fam.piece p).output →
      ∀ j, j ≤ n → ∀ y, ρ ^ j * ‖iteratedFDeriv ℝ j (g t p) y‖ ≤ B j) :
    coefficientSeminorm ρ n a b (G.physCoeff v u γ d) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * B j / (j.factorial : ℝ)) := by
  apply pointwise_coefficient_seminorm_budget ρ hρ n a b (G.physCoeff v u γ d)
    (fun t ht => native_physCoeff_all_order_smooth hG hpar hnat hi hj hb hε a b
      v u γ hm hm2 n d t ht) B hB
  intro t ht j hjn x
  exact native_constituentPhysical_positive_jet_budget hnat a b
    (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) v u γ d j ρ (B j) hρ.le (hB j)
    ⟨t, ht⟩ (g t) (hg t)
    (fun p hp => (hgs t ht p hp).of_le (by exact_mod_cast hjn))
    (fun p hp y => hjet t ht p hp j hjn y) x
end

/-! Genuine native coefficient jets give a finite seminorm for the actual physical coefficient. -/

section
open AVRegularity.Construction.Preservation.Buffer
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_constituentPhysical_all_order_seminorm_finite
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1))
    (n d : ℕ) :
    coefficientSeminorm ρ n a b
      (constituentPhysical G.fam ν e (D.eps (G.level - 1)) G.actual v u γ d) ≠ ⊤ := by
  let A := fun p t x => G.fam.weight p t •
    nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map
      (fun i W => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
        (G.fam.identity v u γ).maxOrder
        (fun d' I => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d' I t
          (((G.fam.piece p).material t).symm x)
          (e⁻¹ • ((G.fam.piece p).material t).symm x)) (d - 1) W x i)
  have hf := coefficientSeminorm_sum_ne_top (G.fam.locally_finite a b).toFinset A ρ n a b
    (fun p _ t ht => native_weighted_piece_all_order_smooth hG hpar hnat hi hj hb hε a b
      p v u γ hm hm2 ν e n (d - 1) t ht)
    (fun p _ => native_weighted_piece_all_order_seminorm_finite hG hpar hnat hi hj hb
      hε a b p v u γ hm hm2 ν e ρ hρ hρε n (d - 1))
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) :
      constituentPhysical G.fam ν e (D.eps (G.level - 1)) G.actual v u γ d t =
        fun x => ∑ p ∈ (G.fam.locally_finite a b).toFinset, A p t x := by
    funext x
    exact constituentPhysical_eq_window_sum G.fam ν e (D.eps (G.level - 1)) G.actual
      a b t ht v u γ d x
  rw [AVRegularity.Construction.Preservation.Buffer.coefficientSeminorm_window_congr ρ n a b _ _ he]
  exact hf


theorem native_physCoeff_all_order_seminorm_finite
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b : ℝ)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1))
    (n d : ℕ) :
    coefficientSeminorm ρ n a b (G.physCoeff v u γ d) ≠ ⊤ :=
  native_constituentPhysical_all_order_seminorm_finite hG hpar hnat hi hj hb hε
    a b v u γ hm hm2 (D.kap G.level) (D.eps G.level) ρ hρ hρε n d
end

end AVRegularity.Construction.Preservation.FullLift
end
end
