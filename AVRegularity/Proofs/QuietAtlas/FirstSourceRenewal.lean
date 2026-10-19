-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.QuietAtlas.PiolaGeom
public import AVRegularity.Proofs.QuietAtlas.QuietPulse
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.CycleComparison.Reconstruction.InvPiola
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.QuietAtlas

/-! **The source phase algebra on a history-quiet set** (`quietSourcePhase`, the first hard leaf
of the quiet matching). At a history-quiet time `t`:

* **transfer.** For an active finer slot `k`, the whole Jacobian germ
  `h ↦ childTransition(k, t, ch^{[h]}, z + h/ε)⁻¹` does not read the phase: the appended child
  has center `0` and the parent flow between `t` and its anchor (`appendChild_famJac_phase`).
  The finer coefficients at `0` are those of QC1. Inactive slots contribute zero.
* **first source.** The label shear vanishes at `t`, so the context strain is the strain of the
  family (`contextStrain_of_labelShear_zero`). In the assembled diagonal mean flux, the
  admissibility and the push maps of the appended children do not read the phase, and the finer
  germs of QC1 pass through the continuous inverse chart, which fixes `0`
  (`diagTerm_germ`, `diagMeanFluxCtx_germ`). The covariance polynomials are local operators, so
  germs suffice (`covPolyQ_eq_of_eventuallyEq`). -/

section
/-! ### Local operators -/

section Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covOperator_eventuallyEq (Hc : Matrix (Fin 2) (Fin 2) ℝ) {φ ψ : Vec 2 → E} {x : Vec 2}
    (h : φ =ᶠ[𝓝 x] ψ) : covOperator Hc φ =ᶠ[𝓝 x] covOperator Hc ψ := by
  have h2 : ∀ j : Fin 2, (fun y => fderiv ℝ φ y (basisVec j)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ ψ y (basisVec j)) :=
    fun j => (h.fderiv (𝕜 := ℝ)).mono fun y hy => by simp only []; rw [hy]
  have h3 : ∀ j : Fin 2, fderiv ℝ (fun y => fderiv ℝ φ y (basisVec j)) =ᶠ[𝓝 x]
      fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec j)) := fun j => (h2 j).fderiv
  filter_upwards [h3 0, h3 1] with y hy0 hy1
  simp only [covOperator, Fin.sum_univ_two, hy0, hy1]

theorem covOperator_iterate_eventuallyEq (Hc : Matrix (Fin 2) (Fin 2) ℝ) {φ ψ : Vec 2 → E}
    {x : Vec 2} (h : φ =ᶠ[𝓝 x] ψ) (l : ℕ) :
    (covOperator Hc)^[l] φ =ᶠ[𝓝 x] (covOperator Hc)^[l] ψ := by
  induction l with
  | zero => exact h
  | succ l ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact covOperator_eventuallyEq Hc ih

theorem covPolyQ_eq_of_eventuallyEq (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {φ ψ : Vec 2 → E}
    {x : Vec 2} (h : φ =ᶠ[𝓝 x] ψ) : covPolyQ Hc p φ x = covPolyQ Hc p ψ x := by
  unfold covPolyQ
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun l _ => by
    rw [(covOperator_iterate_eventuallyEq Hc h l).eq_of_nhds]

end Germ

variable (D : OCData)

/-! ### Geometric facts -/

theorem recenter_wellSlotted {ch : RealChain} (hl : ch.WellSlotted) (h : Vec 2) :
    (ch.recenter D h).WellSlotted := by
  obtain ⟨-, hs, hc⟩ := EntryWeakProofs.weak_recenter_metadata D ch h
  change (ch.recenter D h).slots.length = (ch.recenter D h).children.length + 1
  rw [hs, hc]
  exact hl

theorem recenter_ctxLevel (ch : RealChain) (h : Vec 2) :
    (ch.recenter D h).ctxLevel = ch.ctxLevel := by
  obtain ⟨hb, -, hc⟩ := EntryWeakProofs.weak_recenter_metadata D ch h
  simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hc]

theorem recenter_slot (ch : RealChain) (h : Vec 2) : (ch.recenter D h).slot = ch.slot := by
  obtain ⟨-, hs, -⟩ := EntryWeakProofs.weak_recenter_metadata D ch h
  simp only [RealChain.slot, hs]

/-- Without label shear, the context strain is the strain of the family. -/
theorem contextStrain_of_labelShear_zero {i : ℕ} {pc : ℤ} {t : ℝ}
    (h : labelShear D i pc t = 0) (ch : RealChain) (ζ : Vec 2) :
    contextStrain D i pc t ch ζ = ch.famStrain D t := by
  unfold contextStrain
  rw [h]
  have h1 : (Matrix.of fun a c => fderiv ℝ (fun h : Vec 2 => (ch.recenter D h).famJac D t a c) 0
      ((0 : Vec 2 → Vec 2) ζ)) = 0 := by
    ext a c
    simp
  have h2 : jacMatrix (0 : Vec 2 → Vec 2) ζ = 0 := by
    ext a c
    simp [jacMatrix, fderiv_zero]
  rw [h1, h2, smul_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul, add_zero]

/-! ### The diagonal mean flux -/

open scoped Classical in
/-- **One finer slot of the assembled diagonal mean flux** does not read the phase, as a germ. -/
theorem diagTerm_germ (hζ : IsFastProfile D.ζ) {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} {t : ℝ} {ch : RealChain}
    (hl : ch.WellSlotted) {k : ℤ} {n : ℕ} {z z' : Vec 2}
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0)
    (h0' : ∀ θ, D.relDisp ch.ctxLevel ch.slot t (D.slotAnchor (ch.ctxLevel + 1) k) θ = 0)
    (hL : ∀ f, diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t z) n t f =ᶠ[𝓝 0]
      diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t z') n t f) (g : Vec 2 → ℝ) :
    (fun x => if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t z) then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t z).famMap D t)
          ((ch.appendChild D k t z).famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t z) n t) g x
      else 0) =ᶠ[𝓝 0]
    (fun x => if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t z') then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t z').famMap D t)
          ((ch.appendChild D k t z').famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t z') n t) g x
      else 0) := by
  have hadm := isAdmissibleChain_appendChild_phase D (b := b) (j₀ := j₀) (i := m) (p := k)
    ch k t z z' h0
  have hΨ := appendChild_famMap_phase D ch hl k t z z' h0 h0'
  have hΨi := appendChild_famMapInv_phase D ch hl k t z z' h0 h0' h0
  have hcont : Tendsto ((ch.appendChild D k t z).famMapInv D t) (𝓝 0) (𝓝 0) := by
    have := (GenSem.contDiff_famMapInv (D := D) (ch.appendChild D k t z) t).continuous.tendsto 0
    rwa [GenSem.famMapInv_zero hζ] at this
  have hL' := (hL (g ∘ (ch.appendChild D k t z).famMap D t)).comp_tendsto hcont
  filter_upwards [hL'] with x hx
  simp only [← hΨ, ← hΨi, ← hadm, pushFlux]
  split_ifs
  · simp only [Function.comp_apply] at hx
    rw [hx]
  · rfl

open scoped Classical in
/-- **The assembled diagonal mean flux** does not read the phase, as a germ, when each active
finer slot does not. -/
theorem diagMeanFluxCtx_germ (hΛ : 1 ≤ D.Λ) {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} {t : ℝ} {ch : RealChain}
    {n : ℕ} {z z' : Vec 2} (g : Vec 2 → ℝ)
    (hterm : ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      (fun x => if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t z) then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t z).famMap D t)
          ((ch.appendChild D k t z).famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t z) n t) g x
      else 0) =ᶠ[𝓝 0]
      (fun x => if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t z') then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t z').famMap D t)
          ((ch.appendChild D k t z').famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t z') n t) g x
      else 0)) :
    (fun x => diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch z n g x) =ᶠ[𝓝 0]
      (fun x => diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch z' n g x) := by
  have hF := CycleReference.ocCutoff_support_finite (α := D.α) (q := D.q) (Λ := D.Λ) (m := m)
    hΛ (t := t)
  have hev := (Filter.eventually_all_finite hF).2 fun k hk => hterm k.1 k.2 hk
  filter_upwards [hev] with x hx
  unfold diagMeanFluxCtx
  refine finsum_congr fun k => finsum_congr fun hk => ?_
  by_cases hkt : ocCutoff D.α D.q D.Λ m k t = 0
  · simp only [hkt, zero_smul, ite_self]
  · exact hx ⟨k, hk.1⟩ hkt

/-- **The first-source flux at the center** does not read the phase when the context strain does
not and the diagonal flux does not as a germ. -/
theorem firstSourceFlux_phase {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ} {N p : ℕ} {s₀ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} {t : ℝ} {ch : RealChain}
    {ζ ζ' : Vec 2}
    (hS : ∀ ch' w, contextStrain D (m - 1) ch.slot t ch' w = ch'.famStrain D t)
    (hdiag : ∀ g, (fun x => diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ g x) =ᶠ[𝓝 0]
      (fun x => diagFluxCtx D b j₀ Dm m ρ N Cc0 t ch ζ' g x)) (f : Vec 2 → ℝ) :
    firstSourceFlux D b j₀ Dm m ρ N p s₀ Cc0 t ch ζ f 0 =
      firstSourceFlux D b j₀ Dm m ρ N p s₀ Cc0 t ch ζ' f 0 := by
  simp only [firstSourceFlux, pullFlux, hS, GenSem.famMap_zero]
  congr 1
  refine covPolyQ_eq_of_eventuallyEq _ p ?_
  filter_upwards [hdiag (covPolyP (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) p
    (f ∘ ch.famMapInv D t))] with x hx
  rw [hx]

/-! ### The source phase statement -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The source phase algebra (`QuietSourcePhaseStatement`).** -/
theorem quietSourcePhase :
    QuietSourcePhaseStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀) := by
  intro G P Mtop U hΛ hζ hU hQC p ch t ht htp v u γ d I _ z z'
  have hq := hQC v u γ p ch t ht htp
  obtain ⟨h1, -, h3, h4, -, -, -⟩ := ch.2
  have hl : ch.1.WellSlotted := h3
  have hctx : ch.1.ctxLevel = G.level := h1
  have hslot : ch.1.slot = p.1 := h4
  -- no displacement on the history of an active child
  have hz : ∀ k, ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 → ∀ u r,
      u ∈ availInterval D Mtop (G.level + 1) k → r ∈ availInterval D Mtop (G.level + 1) k →
      ∀ θ, D.relDisp G.level p.1 u r θ = 0 :=
    fun k hkt u r hu hr θ => relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt p.2 hu hr θ
  have hsk : ∀ k, D.slotAnchor (G.level + 1) k ∈ availInterval D Mtop (G.level + 1) k :=
    fun k => slotAnchor_mem_availInterval D Mtop (G.level + 1) k
  have htk : ∀ k, ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 →
      t ∈ availInterval D Mtop (G.level + 1) k :=
    fun k hkt => mem_availInterval_of_ocCutoff D hΛ hkt
  -- the same, for every recentered chain
  have hzc : ∀ (h : Vec 2) k, ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 →
      (∀ θ, D.relDisp (ch.1.recenter D h).ctxLevel (ch.1.recenter D h).slot
        (D.slotAnchor ((ch.1.recenter D h).ctxLevel + 1) k) t θ = 0) ∧
      (∀ θ, D.relDisp (ch.1.recenter D h).ctxLevel (ch.1.recenter D h).slot t
        (D.slotAnchor ((ch.1.recenter D h).ctxLevel + 1) k) θ = 0) := by
    intro h k hkt
    rw [recenter_ctxLevel, recenter_slot, hctx, hslot]
    exact ⟨hz k hkt _ _ (hsk k) (htk k hkt), hz k hkt _ _ (htk k hkt) (hsk k)⟩
  generalize P.source v u γ = src at hq ⊢
  cases src with
  | transfer lam order fop =>
    simp only [QuietSource.finer, QuietSource.degrees] at hq
    simp only [QuietSource.array]
    unfold transferAt
    refine congrArg (HSMul.hSMul _) ?_
    refine finsum_congr fun k => finsum_congr fun hk => ?_
    by_cases hkt : ocCutoff D.α D.q D.Λ (G.level + 1) k t = 0
    · rw [hkt, zero_smul, zero_smul]
    have hK : (fun h => (childTransition D k t (ch.1.recenter D h)
          (z + (D.eps (G.level + 1 - 1))⁻¹ • h))⁻¹) =
        (fun h => (childTransition D k t (ch.1.recenter D h)
          (z' + (D.eps (G.level + 1 - 1))⁻¹ • h))⁻¹) := by
      funext h
      obtain ⟨h0h, huh⟩ := hzc h k hkt
      unfold childTransition
      rw [appendChild_famJac_phase D (ch.1.recenter D h) (recenter_wellSlotted D hl h) k t _ _
        h0h huh]
    have hB : (fun d I => fluxCoeff (fop k t (ch.1.appendChild D k t z)) d I 0) =
        (fun d I => fluxCoeff (fop k t (ch.1.appendChild D k t z')) d I 0) := by
      funext d' I'
      unfold fluxCoeff
      rw [(hq k hk.1 hkt 0 rfl z z' _).eq_of_nhds]
    rw [hK, hB]
  | first lam ρ s₀ N pc Cc0 =>
    simp only [QuietSource.finer, QuietSource.degrees] at hq
    simp only [QuietSource.array]
    refine congrArg (HSMul.hSMul _) ?_
    unfold fluxCoeff
    refine congrArg (HSMul.hSMul _) ?_
    have hshear : labelShear D (G.level + 1 - 1) ch.1.slot t = 0 := by
      rw [Nat.add_sub_cancel, hslot]
      exact labelShear_eq_zero_of_quiet D hΛ hζ p.2 (hU.1 ht)
    have h0 : ∀ k, ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 →
        (∀ θ, D.relDisp ch.1.ctxLevel ch.1.slot (D.slotAnchor (ch.1.ctxLevel + 1) k) t θ = 0) ∧
        (∀ θ, D.relDisp ch.1.ctxLevel ch.1.slot t (D.slotAnchor (ch.1.ctxLevel + 1) k) θ = 0) := by
      intro k hkt
      rw [hctx, hslot]
      exact ⟨hz k hkt _ _ (hsk k) (htk k hkt), hz k hkt _ _ (htk k hkt) (hsk k)⟩
    have hmean : ∀ n ∈ insert 2 (Set.Icc 3 (N + 1)), ∀ g : Vec 2 → ℝ,
        (fun x => diagMeanFluxCtx D b j₀ Dm (G.level + 1) ρ Cc0 t ch.1 z n g x) =ᶠ[𝓝 0]
          (fun x => diagMeanFluxCtx D b j₀ Dm (G.level + 1) ρ Cc0 t ch.1 z' n g x) := by
      intro n hn g
      refine diagMeanFluxCtx_germ D hΛ g fun k hk hkt => ?_
      exact diagTerm_germ D hζ hl (h0 k hkt).1 (h0 k hkt).2
        (fun f => hq k hk hkt n hn z z' f) g
    refine firstSourceFlux_phase D (contextStrain_of_labelShear_zero D hshear) (fun g => ?_) _
    have h2 := hmean 2 (Set.mem_insert _ _) g
    have hrest : ∀ᶠ x in 𝓝 (0 : Vec 2), ∀ n ∈ Finset.Icc 3 (N + 1),
        diagMeanFluxCtx D b j₀ Dm (G.level + 1) ρ Cc0 t ch.1 z n g x =
          diagMeanFluxCtx D b j₀ Dm (G.level + 1) ρ Cc0 t ch.1 z' n g x :=
      (Finset.eventually_all _).2 fun n hn =>
        hmean n (Set.mem_insert_of_mem _ (by simpa using hn)) g
    filter_upwards [h2, hrest] with x hx2 hxn
    unfold diagFluxCtx
    rw [hx2, Finset.sum_congr rfl hxn]
end

/-! **The Piola leaf for transfer presentations** (quiet matching). For a stage whose identities
are all transfers of finer outputs (the weak passages), the exact quiet transition
holds on a history-quiet overlap, at every lowered order
(`quietReanchorTransfer_of_allTransfer`). On the quiet history, the transfer Jacobians of the two
native descriptions are inverse Jacobians of the label changes to the finer anchor, which differ
by the renewal transition (`childTransition_inv_native`). The finer coefficients agree by QC2,
and the transported arrays compose exactly (`transportedCoeff_comp`). The active finer slots are
the same in both descriptions, and the arrays are linear in the finer coefficients.

The first source of the cascade successor is not covered: its arrays are symmetric extractions,
and the exact rule fails for them at lowered orders. -/

section
/-! ### Linear algebra of the transported arrays -/

theorem transportedCoeff_finset_sum {ι : Type*} (s : Finset ι)
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ) (c : ι → ℝ)
    (B : ι → ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (A : DerivativeWord2 r)
    (y : Vec 2) :
    transportedCoeff K Dγ (fun d I => ∑ k ∈ s, c k • B k d I) r A y =
      ∑ k ∈ s, c k • transportedCoeff K Dγ (B k) r A y := by
  funext a₀
  have hB : ∀ d (I : DerivativeWord2 (d - 1)) (i₀ : Fin 2),
      (∑ k ∈ s, c k • B k d I) i₀ = ∑ k ∈ s, c k * B k d I i₀ := fun d I i₀ => by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hR : (∑ k ∈ s, c k • transportedCoeff K Dγ (B k) r A y) a₀ =
      ∑ k ∈ s, c k * transportedCoeff K Dγ (B k) r A y a₀ := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hR]
  simp only [transportedCoeff, hB, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem transportedCoeff_smul (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ) (c : ℝ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (A : DerivativeWord2 r)
    (y : Vec 2) :
    transportedCoeff K Dγ (fun d I => c • B d I) r A y = c • transportedCoeff K Dγ B r A y := by
  funext a₀
  simp only [transportedCoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun I _ =>
    Finset.sum_congr rfl fun i₀ _ => ?_
  ring

/-- The transported array reads only the orders `r + 1 ≤ d ≤ Dγ`. -/
theorem transportedCoeff_congr (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    {B B' : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2} {r : ℕ}
    (h : ∀ d, r + 1 ≤ d → d ≤ Dγ → ∀ I, B d I = B' d I) (A : DerivativeWord2 r) (y : Vec 2) :
    transportedCoeff K Dγ B r A y = transportedCoeff K Dγ B' r A y := by
  funext a₀
  unfold transportedCoeff
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  simp only [h d hd.1 hd.2]

/-- Raising the maximal order over vanishing orders. -/
theorem transportedCoeff_order_le (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) {Dγ Dγ' : ℕ}
    (hle : Dγ ≤ Dγ') {B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2} {r : ℕ}
    (h0 : ∀ d, r + 1 ≤ d → Dγ < d → d ≤ Dγ' → ∀ I, B d I = 0) (A : DerivativeWord2 r)
    (y : Vec 2) :
    transportedCoeff K Dγ B r A y = transportedCoeff K Dγ' B r A y := by
  funext a₀
  unfold transportedCoeff
  by_cases hr : r + 1 ≤ Dγ
  · rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
      ← Finset.sum_Ico_consecutive _ (by omega : r + 1 ≤ Dγ + 1) (by omega : Dγ + 1 ≤ Dγ' + 1)]
    refine (add_eq_left.mpr (Finset.sum_eq_zero fun d hd => ?_)).symm
    rw [Finset.mem_Ico] at hd
    refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun i₀ _ => ?_
    rw [h0 d (by omega) (by omega) (by omega) I, Pi.zero_apply, mul_zero, zero_mul]
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    refine (Finset.sum_eq_zero fun d hd => ?_).symm
    rw [Finset.mem_Icc] at hd
    refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun i₀ _ => ?_
    rw [h0 d hd.1 (by omega) hd.2 I, Pi.zero_apply, mul_zero, zero_mul]

/-! ### The active finer slots -/

variable (D : OCData)

/-- The active odd finer slots at the time `t`. -/
def activeSlots (hΛ : 1 ≤ D.Λ) (m : ℕ) (t : ℝ) : Finset {k : ℤ // Odd k} :=
  (CycleReference.ocCutoff_support_finite (α := D.α) (q := D.q) (Λ := D.Λ) (m := m + 1) hΛ
    (t := t)).toFinset

/-- **The scheduled slot sum is the sum over the active slots**, for every slot whose window
contains `t`. -/
theorem finsum_sched_eq_sum (hΛ : 1 ≤ D.Λ) {m : ℕ} {c : ℤ} {t : ℝ}
    (htc : t ∈ ocPulseWindow D.α D.q D.Λ m c) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (X : ℤ → E) :
    ∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D m k c), ocCutoff D.α D.q D.Λ (m + 1) k t • X k =
      ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t • X k.1 := by
  classical
  have hP : ∀ k : {k : ℤ // Odd k}, k ∈ activeSlots D hΛ m t →
      Odd k.1 ∧ IsScheduledIn D m k.1 c := fun k hk => by
    refine ⟨k.2, t, ?_, htc⟩
    simpa [activeSlots] using hk
  simp only [finsum_eq_if]
  rw [finsum_eq_sum_of_support_subset _ (s := (activeSlots D hΛ m t).map
    (Function.Embedding.subtype _)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Function.Embedding.coe_subtype, hP k hk, and_self, ↓reduceIte]
  · intro k hk
    rw [Function.mem_support] at hk
    split_ifs at hk with h
    · have hc : ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0 := fun h0 => hk (by rw [h0, zero_smul])
      simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
        Finset.mem_coe]
      exact ⟨⟨k, h.1⟩, by simpa [activeSlots] using hc, rfl⟩
    · exact absurd rfl hk

/-! ### The transfer arrays at native labels -/

/-- The dimensional transfer array is `lam` times the sum over the active finer slots. -/
theorem dim_transferAt (hΛ : 1 ≤ D.Λ) {m : ℕ} (hκ : D.kap m ≠ 0) {c : ℤ} {t : ℝ}
    (htc : t ∈ ocPulseWindow D.α D.q D.Λ m c) (lam : ℝ) (order : ℕ) (fop : FamFluxOp)
    (ch : RealChain) (z : Vec 2) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    (D.kap m * D.eps m ^ (d - 2)) • transferAt D (m + 1) c lam order fop t ch z d I =
      lam • ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
        transportedCoeff
          (fun h => (childTransition D k.1 t (ch.recenter D h) (z + (D.eps m)⁻¹ • h))⁻¹) order
          (fun d I => fluxCoeff (fop k.1 t (ch.appendChild D k.1 t z)) d I 0) (d - 1) I 0 := by
  have hε : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  unfold transferAt
  simp only [Nat.add_sub_cancel]
  rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hκ (pow_ne_zero _ hε)), one_mul,
    finsum_sched_eq_sum D hΛ htc]

/-- **One active finer slot**: on a quiet history, the transported finer coefficients in the
renewal description `q` are the Piola transport of those in the description `p`. -/
theorem slot_piola {m : ℕ} (hm : 1 ≤ m) (p q : OddSlot) {k : ℤ} {t : ℝ} (Y z : Vec 2)
    (hp0 : ∀ θ, D.relDisp m p.1 (D.slotAnchor (m + 1) k) t θ = 0)
    (hp1 : ∀ θ, D.relDisp m p.1 t (D.slotAnchor (m + 1) k) θ = 0)
    (hq0 : ∀ θ, D.relDisp m q.1 (D.slotAnchor (m + 1) k) t θ = 0)
    (hq1 : ∀ θ, D.relDisp m q.1 t (D.slotAnchor (m + 1) k) θ = 0) (order : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (A : DerivativeWord2 r) :
    transportedCoeff (fun h => (childTransition D k t
        (((nativeChain m q.1).recenter D Y).recenter D h) (z + (D.eps m)⁻¹ • h))⁻¹) order B r A 0 =
      transportedCoeff (chartInvJacobian (renewalTransition D m p q)) order
        (fun e J => transportedCoeff (fun h => (childTransition D k t
          (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).recenter D h)
            (z + (D.eps m)⁻¹ • h))⁻¹) order B (e - 1) J 0) r A Y := by
  set sk := D.slotAnchor (m + 1) k
  set sp := D.slotAnchor m p.1
  set sq := D.slotAnchor m q.1
  set Υ := renewalTransition D m p q with hΥ
  have hΥf : Υ = fun y => D.flowOf (m - 1) sp y sq := rfl
  set Υi : Vec 2 → Vec 2 := fun y => D.flowOf (m - 1) sq y sp
  set φp : Vec 2 → Vec 2 := fun y => D.flowOf (m - 1) sk y sp
  set φq : Vec 2 → Vec 2 := fun y => D.flowOf (m - 1) sk y sq
  set ψ : Vec 2 → Vec 2 := fun h => Υ (Y + h) - Υ Y with hψdef
  set χ : Vec 2 → Vec 2 := fun h => Υi (Υ Y + h) - Y with hχdef
  have hself : ∀ (s : ℝ) (x : Vec 2), D.flowOf (m - 1) s x s = x := fun s x => by
    have hX := AVenhance.flow_isFlow _ (D.hΦ (m - 1)).vel_continuous (D.hΦ (m - 1)).vel_lipschitz
    change streamFlow (D.Φ (m - 1)) (D.hΦ (m - 1)) s x s = x
    unfold streamFlow
    exact hX.1 x s
  have hΥΥi : ∀ w, Υ (Υi w) = w := fun w => by
    simp only [hΥf, Υi]
    rw [flowOf_group, hself]
  have hΥiΥ : ∀ w, Υi (Υ w) = w := fun w => by
    simp only [hΥf, Υi]
    rw [flowOf_group, hself]
  have hψχ : ∀ h, ψ (χ h) = h := fun h => by
    simp only [hψdef, hχdef, add_sub_cancel, hΥΥi, add_sub_cancel_left]
  have hχψ : ∀ h, χ (ψ h) = h := fun h => by
    simp only [hψdef, hχdef, add_sub_cancel, hΥiΥ, add_sub_cancel_left]
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    ((flowOf_contDiff D _ _ _).comp (contDiff_const.add contDiff_id)).sub contDiff_const
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ :=
    ((flowOf_contDiff D _ _ _).comp (contDiff_const.add contDiff_id)).sub contDiff_const
  have hφpi : ∀ w, φp (D.flowOf (m - 1) sp w sk) = w := fun w => by
    simp only [φp]
    rw [flowOf_group, hself]
  have hφpi' : ∀ w, D.flowOf (m - 1) sp (φp w) sk = w := fun w => by
    simp only [φp]
    rw [flowOf_group, hself]
  -- the two transfer Jacobians
  have hKq : (fun h => (childTransition D k t
      (((nativeChain m q.1).recenter D Y).recenter D h) (z + (D.eps m)⁻¹ • h))⁻¹) =
      fun h => chartInvJacobian φq (0 + Y + h) :=
    funext fun h => childTransition_inv_native D hm (0 + Y + h) _ hq0 hq1
  have hKp : (fun h => (childTransition D k t
      (((nativeChain m p.1).recenter D (Υ Y)).recenter D h) (z + (D.eps m)⁻¹ • h))⁻¹) =
      fun h => chartInvJacobian φp (0 + Υ Y + h) :=
    funext fun h => childTransition_inv_native D hm (0 + Υ Y + h) _ hp0 hp1
  have hcomp : (fun h => chartInvJacobian φq (0 + Y + h)) =
      fun h => chartInvJacobian ψ h * (fun h' => chartInvJacobian φp (0 + Υ Y + h')) (ψ h) := by
    funext h
    have hφ : φq = φp ∘ Υ := funext fun y => (flowOf_group D (m - 1) y sq sp sk).symm
    simp only [hψdef, chartInvJacobian_translate, zero_add, add_sub_cancel, hφ]
    exact chartInvJacobian_comp (Y + h) ((flowOf_contDiff D _ _ _).differentiable (by simp) _)
      ((flowOf_contDiff D _ _ _).differentiable (by simp) _)
  rw [hKq, hKp, hcomp]
  have hK₁ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x => chartInvJacobian ψ x a i :=
    CycleComparison.Reconstruction.chartInvJacobian_entry_contDiff hχs hψs hψχ hχψ
  have hK₂ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x => chartInvJacobian φp (0 + Υ Y + x) a i :=
    fun a i => (CycleComparison.Reconstruction.chartInvJacobian_entry_contDiff
      (flowOf_contDiff D _ _ _) (flowOf_contDiff D _ _ _) hφpi hφpi' a i).comp
        (contDiff_const.add contDiff_id)
  rw [transportedCoeff_comp hK₁ hK₂ hψs
    (hder_of_inverse (hχs.differentiable (by simp)) (hψs.differentiable (by simp)) hψχ hχψ)]
  have hψ0 : ψ 0 = 0 := by simp only [hψdef, add_zero, sub_self]
  rw [hψ0, show chartInvJacobian ψ = fun h => chartInvJacobian Υ (Y + h) from
    funext fun h => chartInvJacobian_translate Υ Y (Υ Y) h, transportedCoeff_translate, add_zero]

/-! ### The Piola leaf -/

variable {D}
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A presentation whose sources are all transfers (the weak passages). -/
def QuietPresentation.AllTransfer {G : GenStage D hr Dm b j₀} (P : QuietPresentation G) : Prop :=
  ∀ v u (γ : G.fam.Γ v u), ∃ (lam : ℝ) (order : ℕ) (fop : FamFluxOp),
    P.source v u γ = .transfer lam order fop

/-- The flux at a native label is the transfer array of its source. -/
theorem flux_native_transfer (hΛ : 1 ≤ D.Λ) {G : GenStage D hr Dm b j₀} (P : QuietPresentation G)
    {Mtop : ℕ} (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hnat : G.IsNatural Mtop)
    {v u : CompIn G.comps} {γ : G.fam.Γ v u} {lam : ℝ} {order : ℕ} {fop : FamFluxOp}
    (hsrc : P.source v u γ = .transfer lam order fop) (c : OddSlot) (X : Vec 2) (t : ℝ)
    (z : Vec 2) (d : ℕ) (I : DerivativeWord2 (d - 1)) (hd : 2 ≤ d) :
    G.fam.flux c (G.actual c) v u γ d I t ((D.eps (G.level - 1))⁻¹ • X) z =
      transferAt D (G.level + 1) c.1 lam order fop t ((nativeChain G.level c.1).recenter D X)
        z d I := by
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [P.represents c (G.actual c) v u γ d I t _ z hd, hsrc, hnat.2.2.1 c, smul_smul,
    mul_inv_cancel₀ hε, one_smul]
  split_ifs with h
  · rfl
  · exact absurd (isAdmissibleChain_nativeChain_recenter hi hj c X) h

/-- **The exact Piola rule for one transfer edge** on a quiet overlap. -/
theorem quietReanchor_transfer_edge (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (U : Set ℝ)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hnat : G.IsNatural Mtop)
    (hU : IsHistoryQuiet D Mtop G.level U) (hQC2 : QuietReanchors G P U)
    {v u : CompIn G.comps} {γ : G.fam.Γ v u} {lam : ℝ} {order : ℕ} {fop : FamFluxOp}
    (hsrc : P.source v u γ = .transfer lam order fop)
    (p q : OddSlot) (hpq : p ≠ q) (t : ℝ) (ht : t ∈ U)
    (htp : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (htq : t ∈ ocPulseWindow D.α D.q D.Λ G.level q.1) (Y z : Vec 2) (r : ℕ)
    (A : DerivativeWord2 r) :
    (D.kap G.level * D.eps G.level ^ (r - 1)) •
        G.fam.flux q (G.actual q) v u γ (r + 1) A t ((D.eps (G.level - 1))⁻¹ • Y) z =
      transportedCoeff (chartInvJacobian (renewalTransition D G.level p q))
        (G.fam.identity v u γ).maxOrder
        (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
          p (G.actual p) v u γ d I t (renewalTransition D G.level p q Y) z) r A Y := by
  have hdim0 : ∀ d (I : DerivativeWord2 (d - 1)),
      ¬ (2 ≤ d ∧ d ≤ (G.fam.identity v u γ).maxOrder) →
      G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) p (G.actual p) v u γ
        d I t (renewalTransition D G.level p q Y) z = 0 := by
    intro d I hd
    simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux,
      G.fam.flux_zero p (G.actual p) v u γ d I hd, smul_zero]
  -- the order one
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [G.fam.flux_zero q (G.actual q) v u γ (0 + 1) A (by omega), smul_zero]
    funext a₀
    exact (CycleComparison.Reconstruction.transportedCoeff_low_eq_zero _ _ _ rfl A Y a₀
      fun I => hdim0 1 I (by omega)).symm
  -- a vanishing diffusivity
  by_cases hκ : D.kap G.level = 0
  · rw [hκ, zero_mul, zero_smul]
    simp only [ChartedFamily.dimFlux, zero_mul, zero_smul]
    funext a₀
    simp [transportedCoeff]
  -- the native transfer arrays
  set m := G.level with hmdef
  set Ty := activeSlots D hΛ m t
  set Υ := renewalTransition D m p q
  set Kc : OddSlot → Vec 2 → ℤ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun c X k h =>
    (childTransition D k t (((nativeChain m c.1).recenter D X).recenter D h)
      (z + (D.eps m)⁻¹ • h))⁻¹
  set Bf : OddSlot → Vec 2 → ℤ → ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 := fun c X k d I =>
    fluxCoeff (fop k t (((nativeChain m c.1).recenter D X).appendChild D k t z)) d I 0
  set Sp : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 := fun d I =>
    ∑ k ∈ Ty, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
      transportedCoeff (Kc p (Υ Y) k.1) order (Bf p (Υ Y) k.1) (d - 1) I 0
  -- the dimensional arrays of the description `p`
  have hBp : ∀ d, 2 ≤ d → ∀ I : DerivativeWord2 (d - 1),
      G.fam.dimFlux (D.kap m) (D.eps m) (D.eps (m - 1)) p (G.actual p) v u γ d I t (Υ Y) z =
        lam • Sp d I := by
    intro d hd I
    simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux]
    rw [flux_native_transfer hΛ P hi hj hnat hsrc p (Υ Y) t z d I hd]
    exact dim_transferAt D hΛ hκ htp lam order fop _ z d I
  have hSp_top : ∀ d, 2 ≤ d → (G.fam.identity v u γ).maxOrder < d →
      ∀ I : DerivativeWord2 (d - 1), lam • Sp d I = 0 := by
    intro d hd hdm I
    rw [← hBp d hd I]
    exact hdim0 d I (by omega)
  have hSp_order : ∀ d, order < d → ∀ I : DerivativeWord2 (d - 1), Sp d I = 0 := by
    intro d hd I
    refine Finset.sum_eq_zero fun k _ => ?_
    have : transportedCoeff (Kc p (Υ Y) k.1) order (Bf p (Υ Y) k.1) (d - 1) I 0 = 0 := by
      funext a₀
      exact CycleComparison.Reconstruction.transportedCoeff_eq_zero_of_lt _ _ _ I 0 a₀ (by omega)
    rw [this, smul_zero]
  -- the left side
  have hL : (D.kap m * D.eps m ^ (r - 1)) •
      G.fam.flux q (G.actual q) v u γ (r + 1) A t ((D.eps (m - 1))⁻¹ • Y) z =
      lam • ∑ k ∈ Ty, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
        transportedCoeff (Kc q Y k.1) order (Bf q Y k.1) r A 0 := by
    rw [flux_native_transfer hΛ P hi hj hnat hsrc q Y t z (r + 1) A (by omega),
      show r - 1 = r + 1 - 2 by omega]
    exact dim_transferAt D hΛ hκ htq lam order fop _ z (r + 1) A
  rw [hL]
  -- the right side
  have hR1 := transportedCoeff_congr (chartInvJacobian Υ) (G.fam.identity v u γ).maxOrder
    (B := fun d I => G.fam.dimFlux (D.kap m) (D.eps m) (D.eps (m - 1)) p (G.actual p) v u γ d I t
      (Υ Y) z) (B' := fun d I => lam • Sp d I)
    (fun d hd _ I => hBp d (by omega) I) A Y
  rw [hR1, transportedCoeff_order_le _ (le_max_left _ order)
      (fun d hd hd1 _ I => hSp_top d (by omega) hd1 I) A Y,
    ← transportedCoeff_order_le _ (le_max_right (G.fam.identity v u γ).maxOrder order)
      (fun d _ hd1 _ I => by rw [hSp_order d hd1 I, smul_zero]) A Y,
    transportedCoeff_smul]
  congr 1
  rw [transportedCoeff_finset_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  -- one active slot
  have hkt : ocCutoff D.α D.q D.Λ (m + 1) k.1 t ≠ 0 := by simpa [Ty, activeSlots] using hk
  have hsk : D.slotAnchor (m + 1) k.1 ∈ availInterval D Mtop (m + 1) k.1 :=
    slotAnchor_mem_availInterval D Mtop (m + 1) k.1
  have htk : t ∈ availInterval D Mtop (m + 1) k.1 := mem_availInterval_of_ocCutoff D hΛ hkt
  have hz : ∀ c : OddSlot, (∀ θ, D.relDisp m c.1 (D.slotAnchor (m + 1) k.1) t θ = 0) ∧
      (∀ θ, D.relDisp m c.1 t (D.slotAnchor (m + 1) k.1) θ = 0) := fun c =>
    ⟨relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt c.2 hsk htk,
      relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt c.2 htk hsk⟩
  have hB : Bf p (Υ Y) k.1 = Bf q Y k.1 := by
    funext d I
    have h2 := hQC2 v u γ p q hpq t ht htp htq k.1 k.2 hkt 0 (by rw [hsrc]; rfl) Y z
      (fun Y' => ∏ j, (Y' - 0) (I j))
    rw [hsrc] at h2
    simp only [QuietSource.finer] at h2
    simp only [Bf, fluxCoeff]
    rw [h2.eq_of_nhds]
  rw [← hB]
  exact slot_piola D hi p q Y z (hz p).1 (hz p).2 (hz q).1 (hz q).2 order (Bf p (Υ Y) k.1) r A

/-- **The Piola leaf for transfer presentations**: the transported identity of the renewal
transitions for a presentation whose sources are all transfers (the clause `QuietPhaseBlind` is
not needed). -/
theorem quietReanchorTransfer_of_allTransfer (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (U : Set ℝ)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hnat : G.IsNatural Mtop)
    (hU : IsHistoryQuiet D Mtop G.level U) (hQC2 : QuietReanchors G P U)
    (hall : P.AllTransfer) :
    ∀ (p q : OddSlot), p ≠ q → ∀ t, t ∈ U →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level q.1 →
      ∀ Y z : Vec 2, ∀ v u (γ : G.fam.Γ v u) r (A : DerivativeWord2 r),
        (D.kap G.level * D.eps G.level ^ (r - 1)) •
            G.fam.flux q (G.actual q) v u γ (r + 1) A t ((D.eps (G.level - 1))⁻¹ • Y) z =
          transportedCoeff (chartInvJacobian (renewalTransition D G.level p q))
            (G.fam.identity v u γ).maxOrder
            (fun d I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
              p (G.actual p) v u γ d I t (renewalTransition D G.level p q Y) z) r A Y := by
  intro p q hpq t ht htp htq Y z v u γ r A
  obtain ⟨lam, order, fop, hsrc⟩ := hall v u γ
  exact quietReanchor_transfer_edge hΛ hζ G P Mtop U hi hj hnat hU hQC2 hsrc p q hpq t ht htp htq
    Y z r A
end

end AVRegularity.Providers.QuietAtlas
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.QuietAtlas

/-! **The two renewal descriptions of a native family** (for the first source on a quiet
overlap). With `Υ = X_{m-1}(s_p, ·, s_q)` and `ψ h = Υ(Y + h) - ΥY`:
* the centered maps satisfy `Φ_q = Φ_p ∘ ψ` and `Φ_q⁻¹ = ψ⁻¹ ∘ Φ_p⁻¹`
  (`famMap_native_renewal`, `famMapInv_native_renewal`);
* the strains agree, being the velocity gradient at the common physical point
  (`famStrain_native_renewal`, from `famStrain_eq`). -/

variable (D : OCData)

/-- The geometry of a native chain at a base label. -/
theorem geom_nativeChain_recenter {m : ℕ} (hm : 1 ≤ m) (c : ℤ) (X : Vec 2) :
    ((nativeChain m c).recenter D X).geom D = (D.flowOf (m - 1), 0 + X, D.slotAnchor m c) := by
  show (D.flowOf (m - 1), 0 + X, D.slotAnchor (m - 1 + 1) c) = _
  rw [Nat.sub_add_cancel hm]

theorem flowOf_self (k : ℕ) (s : ℝ) (x : Vec 2) : D.flowOf k s x s = x := by
  have hX := AVenhance.flow_isFlow _ (D.hΦ k).vel_continuous (D.hΦ k).vel_lipschitz
  change streamFlow (D.Φ k) (D.hΦ k) s x s = x
  unfold streamFlow
  exact hX.1 x s

/-- **The centered maps of the two renewal descriptions.** -/
theorem famMap_native_renewal {m : ℕ} (hm : 1 ≤ m) (p q : OddSlot) (Y : Vec 2) (t : ℝ) :
    ((nativeChain m q.1).recenter D Y).famMap D t =
      ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).famMap D t ∘
        fun h => renewalTransition D m p q (Y + h) - renewalTransition D m p q Y := by
  funext h
  simp only [RealChain.famMap, geom_nativeChain_recenter D hm, zero_add, Function.comp_apply,
    add_sub_cancel, renewalTransition]
  rw [flowOf_group, flowOf_group]

theorem famMapInv_native_renewal {m : ℕ} (hm : 1 ≤ m) (p q : OddSlot) (Y : Vec 2) (t : ℝ) :
    ((nativeChain m q.1).recenter D Y).famMapInv D t =
      (fun h => D.flowOf (m - 1) (D.slotAnchor m q.1)
          (renewalTransition D m p q Y + h) (D.slotAnchor m p.1) - Y) ∘
        ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).famMapInv D t := by
  funext w
  simp only [RealChain.famMapInv, geom_nativeChain_recenter D hm, zero_add, Function.comp_apply,
    add_sub_cancel, renewalTransition]
  rw [flowOf_group, flowOf_group]

/-- **The strains of the two renewal descriptions agree.** -/
theorem famStrain_native_renewal {m : ℕ} (hm : 1 ≤ m) (p q : OddSlot) (Y : Vec 2) (t : ℝ) :
    ((nativeChain m q.1).recenter D Y).famStrain D t =
      ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).famStrain D t := by
  simp only [RealChain.famStrain, RealChain.famJac, geom_nativeChain_recenter D hm, zero_add]
  rw [show D.flowOf (m - 1) = streamFlow (D.Φ (m - 1)) (D.hΦ (m - 1)) from rfl,
    StrainPhysical.famStrain_eq (D.hΦ (m - 1)), StrainPhysical.famStrain_eq (D.hΦ (m - 1))]
  congr 1
  show D.flowOf (m - 1) t Y (D.slotAnchor m q.1) =
    D.flowOf (m - 1) t (D.flowOf (m - 1) (D.slotAnchor m p.1) Y (D.slotAnchor m q.1))
      (D.slotAnchor m p.1)
  rw [flowOf_group]

/-- Recentering a recentered native chain adds the offsets. -/
theorem nativeChain_recenter_recenter (m : ℕ) (c : ℤ) (Y h : Vec 2) :
    ((nativeChain m c).recenter D Y).recenter D h = (nativeChain m c).recenter D (Y + h) := by
  show (⟨m - 1, [c], 0 + Y + h, []⟩ : RealChain) = ⟨m - 1, [c], 0 + (Y + h), []⟩
  rw [add_assoc]

/-- The renewal transition carries the recentered point of the description `q` to that of the
description `p`. -/
theorem renewal_famMapInv_point {m : ℕ} (hm : 1 ≤ m) (p q : OddSlot) (Y : Vec 2) (t : ℝ)
    (x : Vec 2) :
    renewalTransition D m p q (Y + ((nativeChain m q.1).recenter D Y).famMapInv D t x) =
      renewalTransition D m p q Y +
        ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).famMapInv D t x := by
  rw [famMapInv_native_renewal D hm p q Y t]
  simp only [Function.comp_apply, add_sub_cancel]
  unfold renewalTransition
  rw [flowOf_group, flowOf_self]

/-- **The strains at the recentered points of the two descriptions agree.** -/
theorem famStrain_native_renewal_point {m : ℕ} (hm : 1 ≤ m) (p q : OddSlot) (Y : Vec 2) (t : ℝ)
    (x : Vec 2) :
    (((nativeChain m q.1).recenter D Y).recenter D
        (((nativeChain m q.1).recenter D Y).famMapInv D t x)).famStrain D t =
      (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).recenter D
        (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).famMapInv D t x)).famStrain
          D t := by
  rw [nativeChain_recenter_recenter, nativeChain_recenter_recenter,
    famStrain_native_renewal D hm p q _ t, renewal_famMapInv_point D hm p q Y t x]

/-- The geometry of the child appended to a recentered native chain, without displacement. -/
theorem appendChild_native_geom {m : ℕ} (hm : 1 ≤ m) (c : ℤ) (Y : Vec 2) (k : ℤ) (t : ℝ)
    (z : Vec 2) (h0 : ∀ θ, D.relDisp m c (D.slotAnchor (m + 1) k) t θ = 0) :
    (((nativeChain m c).recenter D Y).appendChild D k t z).geom D =
      D.childGeom m c (D.slotAnchor (m + 1) k) ⟨0, z⟩ (D.flowOf (m - 1), 0 + Y, D.slotAnchor m c) := by
  have e : ((nativeChain m c).recenter D Y).appendChild D k t z =
      ⟨m - 1, [c, k], 0 + Y, [⟨0, z⟩]⟩ := by
    rw [appendChild_eq_quiet D _ k t z (by
      change ∀ θ, D.relDisp (m - 1 + 0 + 1) c (D.slotAnchor (m - 1 + 0 + 1 + 1) k) t θ = 0
      rw [Nat.add_zero, Nat.sub_add_cancel hm]
      exact h0)]
    rfl
  rw [e]
  show D.childGeom (m - 1 + 1) c (D.slotAnchor (m - 1 + 1 + 1) k) ⟨0, z⟩
      (D.flowOf (m - 1), 0 + Y, D.slotAnchor (m - 1 + 1) c) = _
  rw [Nat.sub_add_cancel hm]

/-- **The children appended in the two descriptions have the same centered maps**, without
displacement between the time and the finer anchor. -/
theorem appendChild_native_renewal_famMap {m : ℕ} (hm : 1 ≤ m) (p q : OddSlot) (Y : Vec 2)
    (k : ℤ) (t : ℝ) (z : Vec 2)
    (hp0 : ∀ θ, D.relDisp m p.1 (D.slotAnchor (m + 1) k) t θ = 0)
    (hp1 : ∀ θ, D.relDisp m p.1 t (D.slotAnchor (m + 1) k) θ = 0)
    (hq0 : ∀ θ, D.relDisp m q.1 (D.slotAnchor (m + 1) k) t θ = 0)
    (hq1 : ∀ θ, D.relDisp m q.1 t (D.slotAnchor (m + 1) k) θ = 0) :
    (((nativeChain m q.1).recenter D Y).appendChild D k t z).famMap D t =
        (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t z).famMap
          D t ∧
      (((nativeChain m q.1).recenter D Y).appendChild D k t z).famMapInv D t =
        (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t z).famMapInv
          D t := by
  have gq := appendChild_native_geom D hm q.1 Y k t z hq0
  have gp := appendChild_native_geom D hm p.1 (renewalTransition D m p q Y) k t z hp0
  have h2 : ((((nativeChain m q.1).recenter D Y).appendChild D k t z).geom D).2 =
      ((((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t
        z).geom D).2 := by
    rw [gq, gp]
    simp only [OCData.childGeom, zero_add, add_zero, renewalTransition]
    rw [flowOf_group]
  have h1 : ∀ y, ((((nativeChain m q.1).recenter D Y).appendChild D k t z).geom D).1 t y
        ((((nativeChain m q.1).recenter D Y).appendChild D k t z).geom D).2.2 =
      ((((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t
        z).geom D).1 t y
        ((((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t
          z).geom D).2.2 := by
    intro y
    rw [gq, gp]
    simp only [OCData.childGeom, hq1, hp1, smul_zero, add_zero]
    rw [flowOf_group, flowOf_group]
  have h1' : ∀ y, ((((nativeChain m q.1).recenter D Y).appendChild D k t z).geom D).1
        ((((nativeChain m q.1).recenter D Y).appendChild D k t z).geom D).2.2 y t =
      ((((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t
        z).geom D).1
        ((((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t
          z).geom D).2.2 y t := by
    intro y
    rw [gq, gp]
    simp only [OCData.childGeom, hq0, hp0, smul_zero, add_zero]
    rw [flowOf_group, flowOf_group]
  exact ⟨famMap_congr D h2 h1, famMapInv_congr D h2 h1 h1'⟩

end AVRegularity.Providers.QuietAtlas
end

section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.QuietAtlas

/-! **The first source in the two renewal descriptions** (operator form). On a quiet
overlap the inner physical operator of the first source is the same in the two descriptions: the
context strains are the physical strain (no label shear), equal at the common physical point, and
the diagonal mean fluxes agree as germs. The Piola pullbacks by `Φ_q = Φ_p ∘ ψ_Y` then give
`D_q f (0) = (Dψ_Y(0))⁻¹ D_p (f ∘ ψ_Y⁻¹) (0)` (`firstSourceFlux_native_renewal`). -/

/-- **The Piola pullback under a change of chart at the centre.** -/
theorem pullFlux_renewal {Φq Φp ψ Φqinv Φpinv ψinv : Vec 2 → Vec 2}
    {F G : (Vec 2 → ℝ) → Vec 2 → Vec 2} (hΦ : Φq = Φp ∘ ψ) (hinv : Φqinv = ψinv ∘ Φpinv)
    (hψ0 : ψ 0 = 0) (hΦp0 : Φp 0 = 0) (hdp : DifferentiableAt ℝ Φp 0)
    (hdψ : DifferentiableAt ℝ ψ 0) (hFG : ∀ g, F g 0 = G g 0) (f : Vec 2 → ℝ) :
    pullFlux Φq Φqinv F f 0 = ((jacMatrix ψ 0)⁻¹).mulVec (pullFlux Φp Φpinv G (f ∘ ψinv) 0) := by
  subst hΦ hinv
  unfold pullFlux
  have hdp' : DifferentiableAt ℝ Φp (ψ 0) := by rw [hψ0]; exact hdp
  rw [GenSem.jacMatrix_comp hdp' hdψ, hψ0, Function.comp_apply, hψ0, hΦp0, hFG,
    Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  rfl

variable (D : OCData)

theorem nativeChain_famMap_eq {m : ℕ} (hm : 1 ≤ m) (c : ℤ) (X : Vec 2) (t : ℝ) :
    ((nativeChain m c).recenter D X).famMap D t =
      fun h => D.flowOf (m - 1) t (X + h) (D.slotAnchor m c) -
        D.flowOf (m - 1) t X (D.slotAnchor m c) := by
  funext h
  simp only [RealChain.famMap, geom_nativeChain_recenter D hm, zero_add]

theorem nativeChain_famMap_differentiableAt {m : ℕ} (hm : 1 ≤ m) (c : ℤ) (X : Vec 2) (t : ℝ) :
    DifferentiableAt ℝ (((nativeChain m c).recenter D X).famMap D t) 0 := by
  rw [nativeChain_famMap_eq D hm]
  have hd : Differentiable ℝ (fun y => D.flowOf (m - 1) t y (D.slotAnchor m c)) :=
    (flowOf_contDiff D (m - 1) t _).differentiable (by simp)
  exact ((hd.comp ((differentiable_const X).add differentiable_id)).sub
    (differentiable_const _)).differentiableAt

theorem renewal_centered_differentiableAt (m : ℕ) (p q : OddSlot) (Y : Vec 2) :
    DifferentiableAt ℝ (fun h => renewalTransition D m p q (Y + h) - renewalTransition D m p q Y)
      0 := by
  unfold renewalTransition
  have hd : Differentiable ℝ (fun y => D.flowOf (m - 1) (D.slotAnchor m p.1) y (D.slotAnchor m q.1)) :=
    (flowOf_contDiff D (m - 1) _ _).differentiable (by simp)
  exact ((hd.comp ((differentiable_const Y).add differentiable_id)).sub
    (differentiable_const _)).differentiableAt

/-- **The first source in the two renewal descriptions**, at the centre: on a quiet overlap
(no label shear for either slot, and diagonal mean fluxes agreeing as germs),
`D_q f (0) = (Dψ_Y(0))⁻¹ D_p (f ∘ ψ_Y⁻¹) (0)`. -/
theorem firstSourceFlux_native_renewal {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ} {N pc : ℕ} {s₀ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} (hm : 1 ≤ m)
    (p q : OddSlot) (Y z : Vec 2) (t : ℝ)
    (hSq : ∀ ch' w, contextStrain D m q.1 t ch' w = ch'.famStrain D t)
    (hSp : ∀ ch' w, contextStrain D m p.1 t ch' w = ch'.famStrain D t)
    (hdiag : ∀ g, (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t
        ((nativeChain m q.1).recenter D Y) z g x) =ᶠ[𝓝 0]
      (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t
        ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z g x))
    (f : Vec 2 → ℝ) :
    firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t ((nativeChain m q.1).recenter D Y) z f 0 =
      ((jacMatrix (fun h => renewalTransition D m p q (Y + h) - renewalTransition D m p q Y)
          0)⁻¹).mulVec
        (firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t
          ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z
          (f ∘ fun w => D.flowOf (m - 1) (D.slotAnchor m q.1) (renewalTransition D m p q Y + w)
            (D.slotAnchor m p.1) - Y) 0) := by
  have hslq : ((nativeChain m q.1).recenter D Y).slot = q.1 := rfl
  have hslp : ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).slot = p.1 := rfl
  unfold firstSourceFlux
  simp only [Nat.add_sub_cancel, hslq, hslp, hSq, hSp, famStrain_native_renewal_point D hm p q Y t]
  refine pullFlux_renewal (famMap_native_renewal D hm p q Y t) (famMapInv_native_renewal D hm p q Y t)
    (by simp) (GenSem.famMap_zero _ t) (nativeChain_famMap_differentiableAt D hm _ _ t)
    (renewal_centered_differentiableAt D m p q Y) (fun g => ?_) f
  apply covPolyQ_eq_of_eventuallyEq
  exact EventuallyEq.add (EventuallyEq.refl _ _) (hdiag _)

/-! ### The diagonal mean fluxes of the two descriptions -/

open scoped Classical in
/-- The scheduled sum of a cut-off term with a carrier condition is the sum over the active
slots, for every slot whose window contains `t`. -/
theorem finsum_sched_ite_eq_sum (hΛ : 1 ≤ D.Λ) {m : ℕ} {c : ℤ} {t : ℝ}
    (htc : t ∈ ocPulseWindow D.α D.q D.Λ m c) (P : ℤ → Prop) (X : ℤ → Vec 2) :
    ∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D m k c),
        (if P k then ocCutoff D.α D.q D.Λ (m + 1) k t • X k else 0) =
      ∑ k ∈ activeSlots D hΛ m t,
        ocCutoff D.α D.q D.Λ (m + 1) k.1 t • (if P k.1 then X k.1 else 0) := by
  have e : ∀ k, (if P k then ocCutoff D.α D.q D.Λ (m + 1) k t • X k else 0) =
      ocCutoff D.α D.q D.Λ (m + 1) k t • (if P k then X k else 0) := fun k => by
    split_ifs <;> simp
  simp only [e]
  exact finsum_sched_eq_sum D hΛ htc _

open scoped Classical in
/-- **The diagonal mean fluxes of the two descriptions agree as germs**, degree by degree, when
the finer label fluxes of the appended children do (QC2) and no displacement enters. -/
theorem diagMeanFluxCtx_native_renewal (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {b : ℝ}
    (hb : 0 < b) {j₀ Dm m : ℕ} {ρ : ℝ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} (hm : 1 ≤ m) (hj : j₀ ≤ m)
    (p q : OddSlot) (Y z : Vec 2) (t : ℝ)
    (htp : t ∈ ocPulseWindow D.α D.q D.Λ m p.1) (htq : t ∈ ocPulseWindow D.α D.q D.Λ m q.1)
    (hrel : ∀ k : ℤ, ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0 →
      (∀ θ, D.relDisp m p.1 (D.slotAnchor (m + 1) k) t θ = 0) ∧
      (∀ θ, D.relDisp m p.1 t (D.slotAnchor (m + 1) k) θ = 0) ∧
      (∀ θ, D.relDisp m q.1 (D.slotAnchor (m + 1) k) t θ = 0) ∧
      (∀ θ, D.relDisp m q.1 t (D.slotAnchor (m + 1) k) θ = 0))
    (n : ℕ)
    (hL : ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0 → ∀ f,
      diagLabelFlux D Dm (m + 1) ρ Cc0 k
          (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t z) n t f
        =ᶠ[𝓝 0]
      diagLabelFlux D Dm (m + 1) ρ Cc0 k
          (((nativeChain m q.1).recenter D Y).appendChild D k t z) n t f)
    (g : Vec 2 → ℝ) :
    (fun x => diagMeanFluxCtx D b j₀ Dm (m + 1) ρ Cc0 t ((nativeChain m q.1).recenter D Y) z n g x)
      =ᶠ[𝓝 0]
    (fun x => diagMeanFluxCtx D b j₀ Dm (m + 1) ρ Cc0 t
      ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z n g x) := by
  have hslq : ((nativeChain m q.1).recenter D Y).slot = q.1 := rfl
  have hslp : ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).slot = p.1 := rfl
  unfold diagMeanFluxCtx
  simp only [Nat.add_sub_cancel, hslq, hslp, finsum_sched_ite_eq_sum D hΛ htq,
    finsum_sched_ite_eq_sum D hΛ htp]
  have hadm : ∀ (c : OddSlot) (X : Vec 2) (k : {k : ℤ // Odd k}),
      ocCutoff D.α D.q D.Λ (m + 1) k.1 t ≠ 0 → t ∈ ocPulseWindow D.α D.q D.Λ m c.1 →
      (∀ θ, D.relDisp m c.1 (D.slotAnchor (m + 1) k.1) t θ = 0) →
      IsAdmissibleChain D b j₀ (m + 1) k.1 (((nativeChain m c.1).recenter D X).appendChild D k.1 t z) :=
    fun c X k hkt htc h0 => isAdmissibleChain_appendChild hb hΛ
      (isAdmissibleChain_nativeChain_recenter hm hj c X) k.2 hkt htc z (by
        change ∀ θ, D.relDisp (m - 1 + 0 + 1) c.1 (D.slotAnchor (m - 1 + 0 + 1 + 1) k.1) t θ = 0
        rw [Nat.add_zero, Nat.sub_add_cancel hm]
        exact h0)
  have hterm : ∀ k ∈ activeSlots D hΛ m t,
      (fun x => if IsAdmissibleChain D b j₀ (m + 1) k.1
          (((nativeChain m q.1).recenter D Y).appendChild D k.1 t z) then
          pushFlux ((((nativeChain m q.1).recenter D Y).appendChild D k.1 t z).famMap D t)
            ((((nativeChain m q.1).recenter D Y).appendChild D k.1 t z).famMapInv D t)
            (diagLabelFlux D Dm (m + 1) ρ Cc0 k.1
              (((nativeChain m q.1).recenter D Y).appendChild D k.1 t z) n t) g x else 0)
        =ᶠ[𝓝 0]
      (fun x => if IsAdmissibleChain D b j₀ (m + 1) k.1
          (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k.1 t z) then
          pushFlux ((((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k.1
              t z).famMap D t)
            ((((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k.1 t
              z).famMapInv D t)
            (diagLabelFlux D Dm (m + 1) ρ Cc0 k.1
              (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k.1 t z)
              n t) g x else 0) := by
    intro k hk
    have hkt : ocCutoff D.α D.q D.Λ (m + 1) k.1 t ≠ 0 := by simpa [activeSlots] using hk
    obtain ⟨hp0, hp1, hq0, hq1⟩ := hrel k.1 hkt
    simp only [ite_eq_left (hadm q Y k hkt htq hq0),
      ite_eq_left (hadm p (renewalTransition D m p q Y) k hkt htp hp0)]
    obtain ⟨hmap, hinv⟩ := appendChild_native_renewal_famMap D hm p q Y k.1 t z hp0 hp1 hq0 hq1
    rw [hmap, hinv]
    unfold pushFlux
    set Ψ := (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k.1 t
      z).famMap D t
    set Ψi := (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k.1 t
      z).famMapInv D t with hΨi
    have htend : Tendsto Ψi (𝓝 0) (𝓝 0) := by
      have h0 : Ψi 0 = 0 := GenSem.famMapInv_zero hζ _ t
      have hc := (GenSem.contDiff_famMapInv (D := D) (((nativeChain m p.1).recenter D
        (renewalTransition D m p q Y)).appendChild D k.1 t z) t).continuous.tendsto 0
      rwa [← hΨi, h0] at hc
    have hg := ((hL k.1 k.2 hkt (g ∘ Ψ)).symm).comp_tendsto htend
    filter_upwards [hg] with x hx
    simp only [Function.comp_apply] at hx
    rw [hx]
  filter_upwards [(Filter.eventually_all_finset _).2 hterm] with x hx
  exact Finset.sum_congr rfl fun k hk => by rw [hx k hk]

open scoped Classical in
/-- **The diagonal fluxes of the two descriptions agree as germs.** -/
theorem diagFluxCtx_native_renewal (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {b : ℝ}
    (hb : 0 < b) {j₀ Dm m : ℕ} {ρ : ℝ} {N : ℕ}
    {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} (hm : 1 ≤ m) (hj : j₀ ≤ m)
    (p q : OddSlot) (Y z : Vec 2) (t : ℝ)
    (htp : t ∈ ocPulseWindow D.α D.q D.Λ m p.1) (htq : t ∈ ocPulseWindow D.α D.q D.Λ m q.1)
    (hrel : ∀ k : ℤ, ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0 →
      (∀ θ, D.relDisp m p.1 (D.slotAnchor (m + 1) k) t θ = 0) ∧
      (∀ θ, D.relDisp m p.1 t (D.slotAnchor (m + 1) k) θ = 0) ∧
      (∀ θ, D.relDisp m q.1 (D.slotAnchor (m + 1) k) t θ = 0) ∧
      (∀ θ, D.relDisp m q.1 t (D.slotAnchor (m + 1) k) θ = 0))
    (hL : ∀ n ∈ insert 2 (Set.Icc 3 (N + 1)), ∀ k : ℤ, Odd k →
      ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0 → ∀ f,
      diagLabelFlux D Dm (m + 1) ρ Cc0 k
          (((nativeChain m p.1).recenter D (renewalTransition D m p q Y)).appendChild D k t z) n t f
        =ᶠ[𝓝 0]
      diagLabelFlux D Dm (m + 1) ρ Cc0 k
          (((nativeChain m q.1).recenter D Y).appendChild D k t z) n t f)
    (g : Vec 2 → ℝ) :
    (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t ((nativeChain m q.1).recenter D Y) z g x)
      =ᶠ[𝓝 0]
    (fun x => diagFluxCtx D b j₀ Dm (m + 1) ρ N Cc0 t
      ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z g x) := by
  have hn : ∀ n ∈ insert 2 (Set.Icc 3 (N + 1)), _ := fun n hn =>
    diagMeanFluxCtx_native_renewal D hΛ hζ hb (ρ := ρ) (Cc0 := Cc0) (Dm := Dm) hm hj p q Y z t
      htp htq hrel n (hL n hn) g
  have h2 := hn 2 (Set.mem_insert _ _)
  have hs : ∀ᶠ x in 𝓝 0, ∀ n ∈ Finset.Icc 3 (N + 1),
      diagMeanFluxCtx D b j₀ Dm (m + 1) ρ Cc0 t ((nativeChain m q.1).recenter D Y) z n g x =
        diagMeanFluxCtx D b j₀ Dm (m + 1) ρ Cc0 t
          ((nativeChain m p.1).recenter D (renewalTransition D m p q Y)) z n g x :=
    (Filter.eventually_all_finset _).2 fun n hnI =>
      hn n (Set.mem_insert_of_mem _ (by simpa using hnI))
  filter_upwards [h2, hs] with x hx2 hxs
  unfold diagFluxCtx
  rw [hx2, Finset.sum_congr rfl hxs]

end AVRegularity.Providers.QuietAtlas
end
