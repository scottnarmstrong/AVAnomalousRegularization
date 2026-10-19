-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.StageEnvelopes.Cauchy.RealMixedJetTransfer
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.ComplexContext.DSlowCell
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
section
/-! The common all-history scalar estimate in real semantics. No stage, component count,
ambient source-order cap or time window enters its Cauchy constants. -/
@[expose] public noncomputable section
open Homogenization Set Filter Metric
open scoped Topology
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.ComplexContext

/-- One actual certified scalar context, evaluated at an inner real chain. -/
structure CarrierContext (b Δ : ℝ) where
  D : OCData
  CH : ℝ
  Υ : ℝ
  j₀ : ℕ
  i : ℕ
  env : ChainEnv D b CH Υ j₀
  p : OddSlot
  ch : RealChain
  mres : ℝ
  mcert : ℝ
  inner_nonneg : 0 ≤ mres
  reserve_gap : mres + Δ ≤ mcert
  cert_le_two : mcert ≤ 2
  chain : IsCarrierChain D b j₀ i p.1 mres ch
  f : GenSort.Sem .ctx
  F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ
  hol : IsHolExtension D b j₀ i p.1 f (F p)
  t : ℝ
  time_mem : t ∈ ocPulseWindow D.α D.q D.Λ i p.1
  L : ℕ
  θ : ℝ
  theta_nonneg : 0 ≤ θ
  modes : ctxSize D b j₀ i F mcert L ≤ ENNReal.ofReal θ

/-- Real semantics in the normalized physical slow displacement. -/
def CarrierContext.normalized {b Δ : ℝ} (c : CarrierContext b Δ) (X z : Vec 2) : ℝ :=
  c.f c.t (c.ch.recenter c.D (c.D.eps (c.ch.data.baseLevel + c.ch.children.length) • X)) z

/-- Uniform real mixed jets follow from the holomorphic recentering, the Fourier budget,
and real realization. This is pointwise at EVERY permitted time, not an essential supremum. -/
theorem context_exists_normalized_real_mixed_jet_bounds (b Δ : ℝ)
    (hb : 0 < b) (hΔ : 0 < Δ) (N : ℕ) :
    ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧ ∀ c : CarrierContext b Δ,
    ∀ (q : ℕ) (z : Vec 2),
      ContDiffAt ℝ (N : ℕ∞) (fun X => iteratedFDeriv ℝ q (c.normalized X) z) 0 ∧
      ∀ r ≤ N, ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (c.normalized X) z) 0‖ ≤
        B r * (((q.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ q) * c.θ) := by
  obtain ⟨B, hB, hbound⟩ := carrier_exists_normalized_mixed_jet_bounds b Δ hb hΔ N
  refine ⟨B, hB, ?_⟩
  intro c q z
  have hm2 : c.mres ≤ 2 := by have := c.reserve_gap.trans c.cert_le_two; linarith only [this, hΔ]
  have hadm : IsAdmissibleChain c.D b c.j₀ c.i c.p.1 c.ch := carrierChain_mono hb.le hm2 c.chain
  have hdd : AdmData c.D b c.j₀ c.i c.p.1 c.ch.data c.ch.children.length := ⟨c.ch, hadm, rfl, rfl⟩
  have hx := paramsC_mem_inner_carrier c.env.hΛ1 hb c.inner_nonneg c.chain 0
  let g : Vec 2 → Vec 2 → ℂ := fun X z => normalizedRecenteredCarrierFunction
    (D := c.D) (dd := c.ch.data) (c.F c.p c.ch.data c.ch.children.length c.t)
      (c.ch.paramsC 0) (ofRealVec X, ofRealVec z)
  have hjets := hbound c.D c.CH c.Υ c.j₀ c.i c.env c.p c.ch.data c.ch.children.length hdd
    c.f c.F c.hol c.t c.mres c.mcert c.time_mem c.inner_nonneg c.reserve_gap c.cert_le_two
    c.L c.θ c.theta_nonneg c.modes (c.ch.paramsC 0) hx q z
  have he : ∀ᶠ X : Vec 2 in 𝓝 0, ∀ z : Vec 2, g X z = (c.normalized X z : ℂ) :=
    normalized_recentered_carrier_agrees c.env hadm c.hol c.time_mem
  let U : Set (CVec × CVec) := ball 0 (b * Δ / 24) ×ˢ
    {z : CVec | |(z (transverseIndex (c.ch.data.slots.getLastD 0))).im| < (3 + c.mres / 4) * b}
  have hU : IsOpen U := isOpen_ball.prod (isOpen_lt
    ((Complex.continuous_im.comp (continuous_apply _)).abs) continuous_const)
  have hhol := (normalized_recentered_carrier_holomorphic c.env hdd.goodData.1 c.inner_nonneg
    hΔ (c.reserve_gap.trans c.cert_le_two) hx (c.hol.1 _ _ c.t c.time_mem)).1
  have hfast : ∀ᶠ X : Vec 2 in 𝓝 0, ContDiffAt ℝ (q : ℕ) (g X) z := by
    have hzero : ofRealVecCLM (0 : Vec 2) ∈ ball (0 : CVec) (b * Δ / 24) := by
      rw [map_zero]
      exact mem_ball_self (by positivity)
    have hX := ofRealVecCLM.continuous.continuousAt.eventually
      (isOpen_ball.mem_nhds hzero)
    filter_upwards [hX] with X hX
    have hphase : ofRealVec z ∈ {z : CVec |
        |(z (transverseIndex (c.ch.data.slots.getLastD 0))).im| < (3 + c.mres / 4) * b} := by
      simp only [mem_ofPred_eq, ofRealVec, Complex.ofReal_im, abs_zero]
      have hm := c.inner_nonneg
      positivity
    have hXZ : (ofRealVec X, ofRealVec z) ∈ U := ⟨hX, hphase⟩
    have hs : ContDiffAt ℝ (q : ℕ)
        (normalizedRecenteredCarrierFunction (D := c.D) (dd := c.ch.data)
          (c.F c.p c.ch.data c.ch.children.length c.t) (c.ch.paramsC 0))
        (ofRealVec X, ofRealVec z) :=
      ((hhol.contDiffAt (hU.mem_nhds hXZ)).restrict_scalars ℝ).of_le (by simp)
    have hmap : ContDiffAt ℝ (q : ℕ)
        (fun w : Vec 2 => (ofRealVec X, ofRealVecCLM w)) z :=
      (contDiff_const.prodMk ofRealVecCLM.contDiff).contDiffAt
    have hh := hs.comp (g := normalizedRecenteredCarrierFunction
      (D := c.D) (dd := c.ch.data)
      (c.F c.p c.ch.data c.ch.children.length c.t) (c.ch.paramsC 0))
      (f := fun w : Vec 2 => (ofRealVec X, ofRealVecCLM w)) z hmap
    exact hh
  have hreal := real_mixed_jet_le_complex N q c.normalized g z hfast
    (hjets.1.of_le (by simp)) he
  refine ⟨by exact_mod_cast hreal.1, ?_⟩
  intro r hr
  exact (real_mixed_jet_le_complex r q c.normalized g z hfast
    (hjets.1.of_le (by exact_mod_cast hr)) he).2.trans (hjets.2 r hr)

/-- Real semantics in the dimensional slow displacement. -/
def CarrierContext.physical {b Δ : ℝ} (c : CarrierContext b Δ) (Y z : Vec 2) : ℝ :=
  c.f c.t (c.ch.recenter c.D Y) z

/-- Undoing slow normalization costs exactly one inverse parent wavelength per derivative. -/
theorem context_exists_physical_real_mixed_jet_bounds (b Δ : ℝ)
    (hb : 0 < b) (hΔ : 0 < Δ) (N : ℕ) :
    ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧ ∀ c : CarrierContext b Δ,
    ∀ (q : ℕ) (z : Vec 2),
      ContDiffAt ℝ (N : ℕ∞) (fun Y => iteratedFDeriv ℝ q (c.physical Y) z) 0 ∧
      ∀ r ≤ N, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (c.physical Y) z) 0‖ ≤
        B r * (((q.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ q) * c.θ) /
          (c.D.eps (c.ch.data.baseLevel + c.ch.children.length)) ^ r := by
  obtain ⟨B, hB, hbound⟩ := context_exists_normalized_real_mixed_jet_bounds b Δ hb hΔ N
  refine ⟨B, hB, ?_⟩
  intro c q z
  let E : ℝ := c.D.eps (c.ch.data.baseLevel + c.ch.children.length)
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos c.env.hΛ1
  let L : Vec 2 →L[ℝ] Vec 2 := E⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)
  let J : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℝ :=
    fun X => iteratedFDeriv ℝ q (c.normalized X) z
  obtain ⟨hJ, hjet⟩ := hbound c q z
  have he : (fun Y => iteratedFDeriv ℝ q (c.physical Y) z) = J ∘ L := by
    funext Y
    have hf : c.physical Y = c.normalized (L Y) := by
      funext z
      simp only [CarrierContext.physical, CarrierContext.normalized, L,
        smul_apply, ContinuousLinearMap.id_apply,
        smul_smul, mul_inv_cancel₀ hE.ne', one_smul, E]
    rw [hf]
    rfl
  rw [he]
  have hzero : L 0 = 0 := map_zero L
  have hregular : ContDiffAt ℝ (N : ℕ∞) (J ∘ L) 0 := by
    exact (hzero.symm ▸ hJ).comp 0 L.contDiff.contDiffAt
  refine ⟨hregular, ?_⟩
  intro r hr
  have hJr : ContDiffAt ℝ (r : ℕ) J (L 0) := by
    rw [hzero]
    exact hJ.of_le (by exact_mod_cast hr)
  rw [iteratedFDeriv_comp_clm_at r J L 0 hJr, hzero]
  have hnormL : ‖L‖ ≤ E⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hE.le)
    intro X
    change ‖E⁻¹ • X‖ ≤ E⁻¹ * ‖X‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hE)]
  have hcost : 0 ≤ B r * (((q.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ q) * c.θ) :=
    mul_nonneg (hB r) (by have := c.theta_nonneg; positivity)
  apply ((iteratedFDeriv ℝ r J 0).norm_compContinuousLinearMap_le (fun _ : Fin r => L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (mul_le_mul (hjet r hr) (pow_le_pow_left₀ (norm_nonneg _) hnormL r)
    (by positivity) hcost).trans_eq (by rw [inv_pow]; rfl)

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! Assemble scalar coordinate estimates into genuine vector-valued mixed jets. Local
regularity suffices; no global extension of the guarded stage flux is required. -/
@[expose] public noncomputable section
open Homogenization Filter
open scoped Topology
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

/-- Coordinate projection on the value of a vector fast jet. -/
def coordinateFastJet (q : ℕ) (c : Fin 2) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) (Vec 2) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℝ :=
  ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) (Vec 2) ℝ
    (ContinuousLinearMap.proj c)

/-- Local scalar coordinate jets determine the vector jet and its regularity. -/
theorem vector_fast_jet_slow_regular (r q : ℕ) (f : Vec 2 → Vec 2 → Vec 2)
    (Y z : Vec 2)
    (hfast : ∀ᶠ X : Vec 2 in 𝓝 Y, ∀ c : Fin 2,
      ContDiffAt ℝ (q : ℕ) (fun w => f X w c) z)
    (hslow : ∀ c : Fin 2, ContDiffAt ℝ (r : ℕ)
      (fun X => iteratedFDeriv ℝ q (fun w => f X w c) z) Y) :
    ContDiffAt ℝ (r : ℕ) (fun X => iteratedFDeriv ℝ q (f X) z) Y := by
  let P := (ContinuousMultilinearMap.piₗᵢ (𝕜 := ℝ)
    (E := fun _ : Fin q => Vec 2) (E' := fun _ : Fin 2 => ℝ)).toContinuousLinearEquiv
  have he : (fun X => iteratedFDeriv ℝ q (f X) z) =ᶠ[𝓝 Y]
      (fun X => P (fun c => iteratedFDeriv ℝ q (fun w => f X w c) z)) := by
    filter_upwards [hfast] with X hX
    have hs : ContDiffAt ℝ (q : ℕ) (f X) z := contDiffAt_pi.mpr hX
    ext v c
    have hh := (ContinuousLinearMap.proj c : Vec 2 →L[ℝ] ℝ).iteratedFDeriv_comp_left hs le_rfl
    exact (congrArg (fun T => T v) hh).symm
  exact (P.contDiff.contDiffAt.comp Y (contDiffAt_pi.mpr hslow)).congr_of_eventuallyEq he

/-- No coordinate cardinality is hidden: the vector mixed jet is bounded by the sum of
its two scalar coordinate bounds, preserving the certificate's literal coordinate sum. -/
theorem vector_mixed_jet_norm_le_sum (r q : ℕ) (f : Vec 2 → Vec 2 → Vec 2) (Y z : Vec 2)
    (hfast : ∀ᶠ X : Vec 2 in 𝓝 Y, ContDiffAt ℝ (q : ℕ) (f X) z)
    (hslow : ContDiffAt ℝ (r : ℕ) (fun X => iteratedFDeriv ℝ q (f X) z) Y)
    (C : Fin 2 → ℝ) (hC : ∀ c, 0 ≤ C c)
    (hb : ∀ c, ‖iteratedFDeriv ℝ r
      (fun X => iteratedFDeriv ℝ q (fun w => f X w c) z) Y‖ ≤ C c) :
    ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (f X) z) Y‖ ≤ ∑ c, C c := by
  let T := iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (f X) z) Y
  have he (c : Fin 2) :
      (coordinateFastJet q c).compContinuousMultilinearMap T =
        iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (fun w => f X w c) z) Y := by
    have hh : (fun X => iteratedFDeriv ℝ q (fun w => f X w c) z) =ᶠ[𝓝 Y]
        ((coordinateFastJet q c) ∘ (fun X => iteratedFDeriv ℝ q (f X) z)) := by
      filter_upwards [hfast] with X hX
      exact (ContinuousLinearMap.proj c : Vec 2 →L[ℝ] ℝ).iteratedFDeriv_comp_left hX le_rfl
    rw [(hh.iteratedFDeriv ℝ r).eq_of_nhds,
      (coordinateFastJet q c).iteratedFDeriv_comp_left hslow le_rfl]
  have hsum : 0 ≤ ∑ c, C c := Finset.sum_nonneg (fun c _ => hC c)
  apply ContinuousMultilinearMap.opNorm_le_bound hsum
  intro v
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hsum (Finset.prod_nonneg
    (fun a _ => norm_nonneg (v a))))
  intro w
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hsum (Finset.prod_nonneg
    (fun a _ => norm_nonneg (v a)))) (Finset.prod_nonneg (fun a _ => norm_nonneg (w a))))).mpr
  intro c
  have hc : C c ≤ ∑ c, C c := Finset.single_le_sum (fun c _ => hC c) (Finset.mem_univ c)
  have hbound := ((iteratedFDeriv ℝ r
    (fun X => iteratedFDeriv ℝ q (fun w => f X w c) z) Y).le_opNorm v)
  have hvbound : ‖iteratedFDeriv ℝ r
      (fun X => iteratedFDeriv ℝ q (fun w => f X w c) z) Y‖ * (∏ a, ‖v a‖) ≤
      C c * ∏ a, ‖v a‖ := mul_le_mul_of_nonneg_right (hb c)
    (Finset.prod_nonneg (fun a _ => norm_nonneg (v a)))
  have hwbound := ((coordinateFastJet q c).compContinuousMultilinearMap T v).le_opNorm w
  have hcoord : ‖((coordinateFastJet q c).compContinuousMultilinearMap T) v‖ ≤
      C c * ∏ a, ‖v a‖ := by rw [he]; exact hbound.trans hvbound
  exact hwbound.trans ((mul_le_mul_of_nonneg_right hcoord
    (Finset.prod_nonneg (fun a _ => norm_nonneg (w a)))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc
        (Finset.prod_nonneg (fun a _ => norm_nonneg (v a))))
        (Finset.prod_nonneg (fun a _ => norm_nonneg (w a)))))

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end
end

section
section
/-! Local realization of the guarded stage flux on its actual inner carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter
open scoped Topology Classical
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.ComplexContext

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm j₀ : ℕ} {b : ℝ} {G : GenStage D hr Dm b j₀} {k : InvConsts}
  {v u : CompIn G.comps} {γ : G.fam.Γ v u} {d : ℕ} {I : DerivativeWord2 (d - 1)}

/-- The literal scalar witnesses of the context certificate, including its guarded realization. -/
structure StageScalarCertificate (G : GenStage D hr Dm b j₀) (k : InvConsts)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (θ : ℝ) where
  f : OddSlot → GenSort.Sem .ctx
  F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ
  hol : ∀ p, IsHolExtension D b j₀ G.level p.1 (f p) (F p)
  realize : ∀ p (ctx : StageCtx D b j₀ G.level p) t,
    t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ X z,
    G.fam.flux p ctx v u γ d I t X z c =
      if IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X))
      then f p t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0
  nonneg : 0 ≤ θ
  modes : ctxSize D b j₀ G.level F (compReserve k v.1) k.Lstar ≤ ENNReal.ofReal θ

/-- On an inner point the guarded coefficient agrees with the real semantics on a whole
slow neighborhood, uniformly in the final phase. -/
theorem stage_scalar_realization {c : Fin 2} {θ CH Υ mres : ℝ}
    (s : StageScalarCertificate G k v u γ d I c θ) (env : ChainEnv D b CH Υ j₀)
    (hm : mres ≤ 2) {p : OddSlot} {ctx : StageCtx D b j₀ G.level p}
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) {Y : Vec 2}
    (hch : IsCarrierChain D b j₀ G.level p.1 mres (ctx.1.recenter D Y)) :
    ∀ᶠ H : Vec 2 in 𝓝 0, ∀ z : Vec 2,
      G.fam.slowFlux (D.eps (G.level - 1)) p ctx v u γ d I t (Y + H) z c =
        s.f p t ((ctx.1.recenter D Y).recenter D H) z := by
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos env.hΛ1
  have hadm := carrierChain_mono env.hb0.le hm hch
  filter_upwards [recenter_admissible env hadm] with H hH z
  unfold ChartedFamily.slowFlux
  rw [s.realize p ctx t ht]
  simp only [smul_smul, mul_inv_cancel₀ hE.ne', one_smul]
  rw [← AVRegularity.Providers.GenSem.recenter_recenter D env.hζ ctx.1 Y H]
  exact ite_eq_left hH

/-- The raw guarded scalar is jointly smooth near every inner-domain point. This uses the
existing real holomorphic realization, without extending the field past its carrier. -/
theorem stage_scalar_smooth {c : Fin 2} {θ CH Υ mres : ℝ}
    (s : StageScalarCertificate G k v u γ d I c θ) (env : ChainEnv D b CH Υ j₀)
    (hm : mres ≤ 2) {p : OddSlot} {ctx : StageCtx D b j₀ G.level p}
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) {Y z : Vec 2}
    (hch : IsCarrierChain D b j₀ G.level p.1 mres (ctx.1.recenter D Y)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : Vec 2 × Vec 2 => G.fam.flux p ctx v u γ d I t w.1 w.2 c)
      ((D.eps (G.level - 1))⁻¹ • Y, z) := by
  let E := D.eps (G.level - 1)
  let U : Set (Vec 2 × Vec 2) :=
    {X | IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (E • X))} ×ˢ univ
  have hU : IsOpen U := ((AVRegularity.Providers.GenSem.isOpen_admissible_recenter
    D b j₀ G.level p.1 ctx.1).preimage (continuous_const_smul E)).prod isOpen_univ
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos env.hΛ1
  have hmem : (E⁻¹ • Y, z) ∈ U := by
    refine ⟨?_, mem_univ _⟩
    change IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (E • E⁻¹ • Y))
    rw [smul_smul, mul_inv_cancel₀ hE.ne', one_smul]
    exact carrierChain_mono env.hb0.le hm hch
  have hs := AVRegularity.Providers.GenSem.contDiffOn_holExtension_recenter env.hΛ1 env.hb0
    (s.hol p) ctx.1 E ht
  have he : Set.EqOn (fun w : Vec 2 × Vec 2 => G.fam.flux p ctx v u γ d I t w.1 w.2 c)
      (fun w => s.f p t (ctx.1.recenter D (E • w.1)) w.2) U := by
    intro w hw
    change G.fam.flux p ctx v u γ d I t w.1 w.2 c = _
    rw [s.realize p ctx t ht]
    exact ite_eq_left (show IsAdmissibleChain D b j₀ G.level p.1
      (ctx.1.recenter D (D.eps (G.level - 1) • w.1)) from hw.1)
  exact (hs.congr he).contDiffAt (hU.mem_nhds hmem)

/-- The scalar stage estimate is uniform over the ambient order cap, stage, output time and
history. Constants are precisely the common physical context constants. -/
theorem stage_exists_scalar_mixed_jet_bounds (b Δ : ℝ) (hb : 0 < b) (hΔ : 0 < Δ) (N : ℕ) :
    ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      (D : OCData) (Dm j₀ : ℕ) (G : GenStage D hr Dm b j₀) (k : InvConsts)
      (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
      (c : Fin 2) (θ CH Υ mres : ℝ),
      StageScalarCertificate G k v u γ d I c θ → ChainEnv D b CH Υ j₀ →
      0 ≤ mres → mres + Δ ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
      ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G.level p) (t : ℝ) (Y z : Vec 2),
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      IsCarrierChain D b j₀ G.level p.1 mres (ctx.1.recenter D Y) →
      ∀ q, ContDiffAt ℝ (N : ℕ∞)
        (fun H => iteratedFDeriv ℝ q
          (fun w => G.fam.slowFlux (D.eps (G.level - 1)) p ctx v u γ d I t H w c) z) Y ∧
      ∀ r ≤ N, ‖iteratedFDeriv ℝ r
        (fun H => iteratedFDeriv ℝ q
          (fun w => G.fam.slowFlux (D.eps (G.level - 1)) p ctx v u γ d I t H w c) z) Y‖ ≤
        B r * (((q.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ q) * θ) /
          (D.eps (G.level - 1)) ^ r := by
  obtain ⟨B, hB, hbound⟩ := context_exists_physical_real_mixed_jet_bounds b Δ hb hΔ N
  refine ⟨B, hB, ?_⟩
  intro hr _ _ D Dm j₀ G k v u γ d I c θ CH Υ mres s env hm hgap hm2 p ctx t Y z ht hch q
  let cc : CarrierContext b Δ :=
    { D := D, CH := CH, Υ := Υ, j₀ := j₀, i := G.level, env := env, p := p
      ch := ctx.1.recenter D Y, mres := mres, mcert := compReserve k v.1
      inner_nonneg := hm, reserve_gap := hgap, cert_le_two := hm2, chain := hch
      f := s.f p, F := s.F, hol := s.hol p, t := t, time_mem := ht, L := k.Lstar
      θ := θ, theta_nonneg := s.nonneg, modes := s.modes }
  let J : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℝ :=
    fun H => iteratedFDeriv ℝ q
      (fun w => G.fam.slowFlux (D.eps (G.level - 1)) p ctx v u γ d I t H w c) z
  have he : (fun H => J (Y + H)) =ᶠ[𝓝 0]
      (fun H => iteratedFDeriv ℝ q (cc.physical H) z) := by
    filter_upwards [stage_scalar_realization s env (by linarith only [hgap, hm2, hΔ]) ht hch]
      with H hH
    exact congrArg (fun f : Vec 2 → ℝ => iteratedFDeriv ℝ q f z) (funext hH)
  obtain ⟨hs, hj⟩ := hbound cc q z
  have hshift : ContDiffAt ℝ (N : ℕ∞) (fun H => J (Y + H)) 0 :=
    hs.congr_of_eventuallyEq he
  have hreg : ContDiffAt ℝ (N : ℕ∞) J Y := by
    have hh : ContDiffAt ℝ (N : ℕ∞) (fun H => J (Y + H)) (-Y + Y) := by
      simpa only [neg_add_cancel] using hshift
    simpa only [Function.comp_def, add_neg_cancel_left] using
      hh.comp Y (contDiffAt_const.add contDiffAt_id)
  have hparent : cc.ch.data.baseLevel + cc.ch.children.length = G.level - 1 := by
    have hh := hch.1
    change (ctx.1.recenter D Y).baseLevel + (ctx.1.recenter D Y).children.length + 1 = G.level at hh
    change (ctx.1.recenter D Y).baseLevel + (ctx.1.recenter D Y).children.length = G.level - 1
    omega
  refine ⟨hreg, ?_⟩
  intro r hr
  have hejet := (he.iteratedFDeriv ℝ r).eq_of_nhds
  rw [iteratedFDeriv_comp_add_left, add_zero] at hejet
  rw [hejet]
  simpa only [hparent] using hj r hr

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! The actual stage carrier estimate, assembled from the common Cauchy constants and the
literal scalar witness budget. Neither the ambient order cap nor the number of histories
enters the constants. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter
open scoped Topology Classical ENNReal
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

/-- Joint local regularity gives fast regularity on one slow neighborhood. -/
theorem eventually_fast_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℕ) {f : Vec 2 → Vec 2 → E} {Y z : Vec 2}
    (h : ContDiffAt ℝ (q : ℕ) (fun w : Vec 2 × Vec 2 => f w.1 w.2) (Y, z)) :
    ∀ᶠ X : Vec 2 in 𝓝 Y, ContDiffAt ℝ (q : ℕ) (f X) z := by
  have he := ((continuous_id.prodMk continuous_const).tendsto Y).eventually
    (h.eventually (by simp))
  filter_upwards [he] with X hX
  exact hX.comp z (contDiffAt_const.prodMk contDiffAt_id)

/-- Constant output scaling commutes with both genuine local derivatives. -/
theorem norm_mixed_jet_const_smul (r q : ℕ) (f : Vec 2 → Vec 2 → Vec 2)
    (Y z : Vec 2) (a : ℝ)
    (hfast : ∀ᶠ X : Vec 2 in 𝓝 Y, ContDiffAt ℝ (q : ℕ) (f X) z)
    (hslow : ContDiffAt ℝ (r : ℕ) (fun X => iteratedFDeriv ℝ q (f X) z) Y) :
    ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (fun w => a • f X w) z) Y‖ =
      |a| * ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (f X) z) Y‖ := by
  have he : (fun X => iteratedFDeriv ℝ q (fun w => a • f X w) z) =ᶠ[𝓝 Y]
      (fun X => a • iteratedFDeriv ℝ q (f X) z) := by
    filter_upwards [hfast] with X hX
    exact iteratedFDeriv_const_smul_apply' hX
  rw [(he.iteratedFDeriv ℝ r).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' hslow, norm_smul, Real.norm_eq_abs]

/-- A single selected word is controlled by the full positive context-size budget. -/
theorem selected_word_budget {n : ℕ} (θ : DerivativeWord2 n → Fin 2 → ℝ)
    (hθ : ∀ I c, 0 ≤ θ I c) {e R S : ℝ} (he : 0 < e) (hR : 0 < R) (l : ℕ)
    (hbudget : (e / R) ^ l * ∑ I, ∑ c, θ I c ≤ S) (I : DerivativeWord2 n) :
    (∑ c, θ I c) ≤ S * (R / e) ^ l := by
  have hp : 0 < (e / R) ^ l := pow_pos (div_pos he hR) _
  have hall : (∑ I, ∑ c, θ I c) ≤ S / (e / R) ^ l :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hbudget)
  exact (Finset.single_le_sum (fun I _ => Finset.sum_nonneg (fun c _ => hθ I c))
    (Finset.mem_univ I)).trans (by
      rw [div_eq_mul_inv, ← inv_pow, inv_div] at hall
      exact hall)

/-- Uniform, genuine mixed derivatives on the actual inner stage carrier. The level floor
is zero: the only level requirement is the positive level already in the input. -/
theorem context_carrier_scaled_jets : ContextCarrierScaledJetStatement := by
  intro p
  let Δ : ℝ := p.certReserve - p.innerReserve
  let N : ℕ := max p.Kan (p.Ks + p.Jm)
  let Q : ℕ := max p.Lan p.Ks
  have hΔ : 0 < Δ := sub_pos.mpr p.gap
  obtain ⟨B, hB, hbound⟩ := stage_exists_scalar_mixed_jet_bounds p.bw Δ p.bw_pos hΔ N
  let cost : ℕ → ℕ → ℝ := fun r q => B r * ((q.factorial : ℝ) *
    (2 * Real.pi / (3 * Real.pi * p.bw)) ^ q)
  have hcost (r q : ℕ) : 0 ≤ cost r q := by
    dsimp only [cost]
    exact mul_nonneg (hB r) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by positivity)
      (mul_nonneg (by positivity) p.bw_pos.le)) _))
  let A : ℝ := ∑ r ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (Q + 1), cost r q
  have hA : 0 ≤ A := Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun q _ => hcost r q
  have hcostA (r q : ℕ) (hr : r ≤ N) (hq : q ≤ Q) : cost r q ≤ A := by
    exact (Finset.single_le_sum (fun q _ => hcost r q)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))).trans
      (Finset.single_le_sum (fun r _ => Finset.sum_nonneg (fun q _ => hcost r q))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hr)))
  refine ⟨A, 0, hA, ?_⟩
  intro hr _ _ D Dm j₀ b G k mres ρ hinput _ W
  have hb_eq := hinput.bw_eq
  subst b
  obtain ⟨CH, Υ, _, env⟩ := context_carrier_environment hinput
  have hm2 : mres ≤ 2 := hinput.inner_le.trans (p.gap.le.trans p.cert_le_two)
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos env.hΛ1
  have he : 0 < D.eps G.level := Construction.Stream.ocEpsilon_pos env.hΛ1
  have hgap (v : CompIn G.comps) : mres + Δ ≤ compReserve k v.1 := by
    have hh := hinput.inner_le
    have hc := hinput.reserve_le v
    dsimp only [Δ]
    linarith only [hh, hc]
  have hN : max k.Kan (k.Ks + k.Jm) ≤ N :=
    max_le_max hinput.slow_order (Nat.add_le_add hinput.slot_order hinput.molecular_order)
  have hQ : max k.Lan k.Ks ≤ Q := max_le_max hinput.fast_order hinput.slot_order
  have htime (p : OddSlot) {t : ℝ} (ht : t ∈ (G.fam.piece p).output) :
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 := by
    obtain ⟨M, hM⟩ := hinput.natural
    rwa [← (hM.1 p).2.1]
  have hcert (v u : CompIn G.comps) (γ : G.fam.Γ v u) d (I : DerivativeWord2 (d - 1)) :
      ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
        (∀ d I c, 0 ≤ θ d I c) ∧
        (∀ d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
          (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
            ∑ I, ∑ c, θ d I c ≤ (G.fam.identity v u γ).record.size) ∧
        (∀ c, Nonempty (StageScalarCertificate G k v u γ d I c (θ d I c))) := by
    obtain ⟨θ, hθ, hbudget, hforms⟩ := hinput.certified v u γ
    refine ⟨θ, hθ, hbudget, ?_⟩
    intro c
    obtain ⟨f, F, hF, hmodes⟩ := hforms d I c
    refine ⟨{ f := f
              F := F
              hol := fun p => (hF p).2.1
              realize := fun p => (hF p).2.2
              nonneg := hθ d I c
              modes := hmodes }⟩
  refine ⟨?_, ?_⟩
  · intro p ctx v u γ d I tY hdom z
    obtain ⟨θ, _, _, hc⟩ := hcert v u γ d I
    apply contDiffAt_pi.mpr
    intro c
    exact (stage_scalar_smooth (Classical.choice (hc c)) env hm2
      (htime p hdom.1.1) hdom.2).of_le (by simp)
  · intro v u γ d hd hdu I r q hrq hqq a
    have hrN : r ≤ N := hrq.trans hN
    have hqQ : q ≤ Q := hqq.trans hQ
    obtain ⟨θ, hθ, hbudget, hc⟩ := hcert v u γ d I
    let s (c : Fin 2) := Classical.choice (hc c)
    have hθsum : (∑ c, θ d I c) ≤ (G.fam.identity v u γ).record.size *
        ((G.fam.identity v u γ).record.length / D.eps G.level) ^ (d - 2) :=
      selected_word_budget (θ d) (hθ d) he (G.fam.identity v u γ).record.length_pos
        (d - 2) (hbudget d hd hdu) I
    unfold pointwiseJetSupFam pointwiseJetSupOn
    refine iSup_le fun x => iSup_le fun t => iSup_le fun Y => iSup_le fun hdom => iSup_le fun z => ?_
    have ht := htime x.1 hdom.1.1
    let f : Vec 2 → Vec 2 → Vec 2 := G.fam.slowFlux (D.eps (G.level - 1)) x.1 x.2 v u γ d I t
    have hjoint : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w : Vec 2 × Vec 2 => f w.1 w.2) (Y, z) := by
      have hs : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun w : Vec 2 × Vec 2 => G.fam.flux x.1 x.2 v u γ d I t w.1 w.2)
          ((D.eps (G.level - 1))⁻¹ • Y, z) :=
        contDiffAt_pi.mpr (fun c => stage_scalar_smooth (s c) env hm2 ht hdom.2)
      exact hs.comp (Y, z) ((contDiffAt_fst.const_smul _).prodMk contDiffAt_snd)
    have hfast : ∀ᶠ X : Vec 2 in 𝓝 Y, ContDiffAt ℝ (q : ℕ) (f X) z :=
      eventually_fast_regular q (hjoint.of_le (by simp))
    have hs (c : Fin 2) := hbound hr D Dm j₀ G k v u γ d I c (θ d I c) CH Υ mres
      (s c) env hinput.inner_nonneg
      (hgap v) (hinput.reserve_upper v) x.1 x.2 t Y z ht hdom.2 q
    have hslow : ContDiffAt ℝ (r : ℕ) (fun X => iteratedFDeriv ℝ q (f X) z) Y := by
      apply vector_fast_jet_slow_regular r q f Y z
      · filter_upwards [hfast] with X hX c
        exact (contDiffAt_pi.mp hX) c
      · intro c
        exact (hs c).1.of_le (by exact_mod_cast hrN)
    have hscalar (c : Fin 2) :
        ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (fun w => f X w c) z) Y‖ ≤
          cost r q * θ d I c / (D.eps (G.level - 1)) ^ r := by
      have hh := (hs c).2 r hrN
      simpa only [cost, mul_assoc] using hh
    have hv : ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (f X) z) Y‖ ≤
        A * (G.fam.identity v u γ).record.size *
          ((G.fam.identity v u γ).record.length / D.eps G.level) ^ (d - 2) /
            (D.eps (G.level - 1)) ^ r := by
      calc
        _ ≤ ∑ c, cost r q * θ d I c / (D.eps (G.level - 1)) ^ r :=
          vector_mixed_jet_norm_le_sum r q f Y z hfast hslow _
            (fun c => div_nonneg (mul_nonneg (hcost r q) (hθ d I c)) (pow_nonneg hE.le _)) hscalar
        _ = cost r q * (∑ c, θ d I c) / (D.eps (G.level - 1)) ^ r := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
        _ ≤ cost r q * ((G.fam.identity v u γ).record.size *
            ((G.fam.identity v u γ).record.length / D.eps G.level) ^ (d - 2)) /
            (D.eps (G.level - 1)) ^ r :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hθsum (hcost r q)) (pow_nonneg hE.le _)
        _ ≤ _ := by
          rw [mul_assoc A]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcostA r q hrN hqQ)
              (mul_nonneg (G.fam.identity v u γ).record.size_nonneg
                (pow_nonneg (div_nonneg (G.fam.identity v u γ).record.length_pos.le he.le) _)))
            (pow_nonneg hE.le _)
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    change ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (fun w => a • f X w) z) Y‖ ≤ _
    rw [norm_mixed_jet_const_smul r q f Y z a hfast hslow]
    exact (mul_le_mul_of_nonneg_left hv (abs_nonneg a)).trans_eq (by ring)

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! Shared constituent Cauchy assembly: the analytic carrier estimate and the scalar radius
summation are separate leaves, with one common pre-data choice of constants. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

/-- Exact shared constituent producer from its one remaining analytic ingredient.
The radius normalization, both time conventions and finite menus are discharged here. -/
theorem context_certified_constituent_cauchy_of_ingredients
    (hcarrier : ContextCarrierScaledJetStatement) :
    ContextCertifiedConstituentCauchyStatement := by
  intro p
  obtain ⟨A, mStar, hA, hjet⟩ := hcarrier p
  refine ⟨analyticCost p A, fun _ => molecularCost p A, mStar,
    mul_nonneg (Nat.cast_nonneg _) hA, fun _ => mul_nonneg (Nat.cast_nonneg _) hA, ?_⟩
  intro hr _ _ D Dm j₀ b G k mres ρ hinput hlevel hCa hCm W w hw
  exact molecular_radius_summation p A hA hr D Dm j₀ b G k mres ρ hinput hCa hCm W
    (hjet hr D Dm j₀ b G k mres ρ hinput hlevel W) w hw

/-- The shared constituent producer, with the all-history Cauchy ingredient discharged. -/
theorem context_certified_constituent_cauchy : ContextCertifiedConstituentCauchyStatement :=
  context_certified_constituent_cauchy_of_ingredients context_carrier_scaled_jets

/-- One stage-generic producer supplies the successor, weak entry and terminal entry.
The same constants give molecular and analytic envelopes in both time conventions. -/
theorem context_stage_envelopes : ContextStageEnvelopesStatement :=
  context_stage_envelopes_of_cauchy context_certified_constituent_cauchy

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end
end
