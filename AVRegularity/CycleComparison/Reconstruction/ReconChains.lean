-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableBlocks
import AVRegularity.CycleComparison.Reconstruction.ObsEdgesTested
import AVRegularity.CycleComparison.Reconstruction.FiniteRankIdentity
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Residual.TailJets
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Continuity of the pieces of the approximant identity**. The continuity in
space of the pieces of the weak identity of the glued lift of a Galerkin approximant
(`approx_weak_identity`):
* the classical defect field of a smooth coarse field is of class `C^N` when the coefficients of
  the coarse equation are of class `C^{N+1}` and the drift of class `C^N`
  (`classicalDefectField_contDiff_of_smooth`), hence so is the commutator remainder
  (`defectRemainder_contDiff`);
* the physical cleanup flux and force of a lift with cleanup chains of the data `(g, 0)` are
  continuous at a time whose cell time is in the window of the chains (`liftPhys_continuous`);
* the physical edge flux of the glued lift of a finite-rank coarse field is continuous at every
  time of the observation window (`glued_edges_continuous`): it is the weighted sum of the edge
  fluxes of the weighted pulses (`physEdgeFluxVec_weighted_sum`), each continuous
  (`pulse_edge_tested_instance`). -/

section Defect

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- The classical defect field of a smooth coarse field is of class `C^N`. -/
theorem classicalDefectField_contDiff_of_smooth {b : ℝ → Vec 2 → Vec 2} {D H N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {s : ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a s))
    (hAD : ∀ d, ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (CE r v u d s))
    (hb : ContDiff ℝ (N : ℕ∞) (b s)) :
    ContDiff ℝ (N : ℕ∞) (fun x => fun v => classicalDefectField b D H AD CE Jm a s v x) := by
  have hav : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => a s y v) := fun v => contDiff_pi.1 ha v
  -- the ordered derivatives of the components are of class `C^{N+1}`
  have hw : ∀ v {q : ℕ} (α : DerivativeWord2 q),
      ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (orderedDerivative α (fun y => a s y v)) := fun v q α =>
    AVRegularity.ChartTransport.contDiff_orderedDerivative (p := N + 1) α
      ((hav v).of_le (by exact_mod_cast le_top))
  have hd : ∀ v (l : Fin 2),
      ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (fun x => fderiv ℝ (fun y => a s y v) x (basisVec l)) :=
    fun v l => by
      have h1 := hw v (fun _ : Fin 1 => l)
      rw [orderedDerivative_one_eq_fderiv] at h1
      exact h1
  -- the grade fluxes and the total flux are of class `C^{N+1}`
  have hG : ∀ v (j : Fin 2), ∀ r ∈ Finset.range (H + 1),
      ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (fun x => classicalGradeFlux D r AD CE Jm a v s x j) := by
    intro v j r hr
    by_cases hr0 : r = 0
    · subst hr0
      simp only [classicalGradeFlux_zero]
      refine ContDiff.add (ContDiff.sum fun l _ => (hd v l).const_smul (Jm s j l))
        (ContDiff.sum fun d _ => ContDiff.sum fun α _ => ?_)
      have h1 : ContDiff ℝ ((N + 1 : ℕ) : ℕ∞)
          (fun x => AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ)))) :=
        (hAD d).clm_apply contDiff_const
      exact ((contDiff_piLp 2).1 h1 j).fun_smul (hw v α)
    · have hrI : r ∈ Finset.Icc 1 H :=
        Finset.mem_Icc.2 ⟨by omega, by have := Finset.mem_range.1 hr; omega⟩
      simp only [classicalGradeFlux_ne_zero hr0]
      refine ContDiff.sum fun u _ => ContDiff.sum fun d _ => ?_
      have hwu : ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (fun x => (WithLp.toLp 2
          (fun α : DerivativeWord2 (d.1 - 1) => orderedDerivative α (fun y => a s y u) x) :
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u))) :=
        (contDiff_piLp 2).2 fun α => hw u α
      exact (contDiff_piLp 2).1 ((hCE r hrI v u d).clm_apply hwu) j
  have hT : ∀ v (j : Fin 2),
      ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (fun x => classicalTotalFlux D H AD CE Jm a s v x j) :=
    fun v j => ContDiff.sum fun r hr => hG v j r hr
  have hTd : ∀ v (j : Fin 2), ContDiff ℝ (N : ℕ∞)
      (fun x => fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a s v y j) x (basisVec j)) :=
    fun v j => by
      have h1 := AVRegularity.ChartTransport.contDiff_orderedDerivative (p := N)
        (fun _ : Fin 1 => j) (hT v j)
      rw [orderedDerivative_one_eq_fderiv] at h1
      exact h1
  have hbj : ∀ j : Fin 2, ContDiff ℝ (N : ℕ∞) (fun x => b s x j) := fun j => contDiff_pi.1 hb j
  refine contDiff_pi.2 fun v => ?_
  show ContDiff ℝ (N : ℕ∞) (fun x =>
    -(∑ j : Fin 2, b s x j • fderiv ℝ (fun y => a s y v) x (basisVec j)) +
      ∑ j : Fin 2, fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm a s v y j) x (basisVec j))
  exact (ContDiff.sum fun j _ => (hbj j).smul
    ((hd v j).of_le (by exact_mod_cast Nat.le_succ N))).neg.add (ContDiff.sum fun j _ => hTd v j)

variable [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The Galerkin projection of a family of fields is smooth. -/
theorem coarseProjField_contDiff (n : ℕ) (g : ∀ v, Vec 2 → h v) :
    ContDiff ℝ (⊤ : ℕ∞) (coarseProjField n g) :=
  ContDiff.sum fun r _ => (coarseMode_contDiff n r).const_smul _

/-- **The commutator remainder of a Galerkin approximant is of class `C^N`.** -/
theorem defectRemainder_contDiff (n : ℕ) {b : ℝ → Vec 2 → Vec 2} {D H N K : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (W : ∀ v, ℝ → TorusHk K (h v))
    (aRep : ℝ → Vec 2 → ∀ i, h i) {s : ℝ}
    (hAD : ∀ d, ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ ((N + 1 : ℕ) : ℕ∞) (CE r v u d s))
    (hb : ContDiff ℝ (N : ℕ∞) (b s)) :
    ContDiff ℝ (N : ℕ∞) (defectRemainder n b D H AD CE Jm W aRep s) :=
  ((coarseProjField_contDiff n _).of_le (by exact_mod_cast le_top)).sub
    (classicalDefectField_contDiff_of_smooth (coarseTraj_contDiff n W s) hAD hCE hb)

end Defect

section LiftPhys

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- **The physical cleanup flux and force of a lift are continuous** at a time whose cell time is
in the window of the cleanup chains of the data `(g, 0)`. -/
theorem liftPhys_continuous {sXc sZc Acl : ℕ} (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    {H N : ℕ} (ε : ℝ) {c ρs es a b : ℝ} (A : ℝ → Vec 2 → ∀ i, h i)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ n, n < N → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (liftApply (n + 1) (Cc hh (n + 1)) A τ) (fun _ _ _ => 0) (fun j => Vn hh n j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (v : ι) :
    (∀ a₀ : Fin 2, Continuous (fun x => liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ v)) ∧
      Continuous (fun x => liftForcePhys ψ H N Acl ε c ρs es Vn t x v) := by
  have hbox : ∀ n, n < N → ∀ hh, hh ≤ H → ∀ j, j < Acl →
      IsBoxSmooth sXc sZc (Vn hh n j (c⁻¹ * t)) := fun n hn hh hhh =>
    cleanupChain_zeroFlux_box (hV hh hhh n hn _ ht)
  have hF : ∀ n, n < N → ∀ a₀, ContDiff ℝ 1
      (fun x => tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x a₀) := fun n hn =>
    contDiff_tailFluxPhys hχ hψ hψχ hχψ H n Acl ε c ρs es (fun hh => Vn hh n) t
      (contDiff_tailFluxLabel hXc hZc H n Acl ε c ρs es (fun hh => Vn hh n) t (hbox n hn))
  have hGc : ∀ a₀ : Fin 2, ContDiff ℝ 1 (fun x => liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀) :=
    fun a₀ => ContDiff.sum fun n hn => (hF n (Finset.mem_range.1 hn) a₀).const_smul c
  refine ⟨fun a₀ => (contDiff_pi.1 (hGc a₀) v).continuous, ?_⟩
  exact (continuous_apply v).comp (continuous_finsetSum _ fun n hn =>
    (continuous_tailForcePhys hψ.continuous H n Acl ε c ρs es (fun hh => Vn hh n) t
      fun hh hhh => continuous_cleanupRemainder_sample hAcl hXc c⁻¹ ρs es t
        (hbox n (Finset.mem_range.1 hn) hh hhh)).const_smul c)

end LiftPhys

section Edges

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- A `PiLp` valued map with continuous components is continuous. -/
theorem continuous_piLp_of_components {E : Type*} [NormedAddCommGroup E] {X : Type*}
    [TopologicalSpace X] {f : X → PiLp 2 (fun _ : Fin 2 => E)}
    (hf : ∀ a₀ : Fin 2, Continuous (fun x => f x a₀)) : Continuous f :=
  ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => E)).comp (continuous_pi hf)).congr fun _ => rfl

/-- **The physical edge flux of the glued lift of a finite-rank coarse field is continuous**
at every time of the observation window. -/
theorem glued_edges_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hφs : IsAdmissibleStream φs) {ν B : ℝ} (hν : 0 < ν)
    (hB : 0 < B) {ρ E : ℝ} (hρ : 0 < ρ) {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*}
    (F : ChartedFamily ι h D Pc Ctx) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (hdesc : F.IsDescending K) (htorus : IsTorusCompatible F actual E) (T : F.Atlas)
    {tA tZ : ℝ} (hTcons : T.IsConsecutiveClosed (Icc tA tZ))
    (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Icc tA tZ))
    (hTq : T.IsQuiet ν (ocEpsilon q Λ m) E)
    (hTact : ∀ p q' (hpq : T.adjacent p q'),
      ((F.piece p).output ∩ (F.piece q').output ∩ Icc tA tZ).Nonempty →
        T.sameCtx p q' hpq (actual p) (actual q'))
    (pp : ℤ → Pc)
    (hpp : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
      (∀ t, ⇑((F.piece (pp k)).material t) =
        ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) ∧
      ocPulseWindow α q Λ m k ∩ Icc tA tZ ⊆ (F.piece (pp k)).output)
    (hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tA tZ)) {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) quiet (Icc tA tZ) (ocTau α q Λ m) Cpart)
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) k
          (F.fiber (pp k) (actual (pp k)))) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) k
          (F.fiber (pp k) (actual (pp k)))) sX sZ
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j))
    {t : ℝ} (ht : t ∈ Icc tA tZ) (v : ι) :
    Continuous (fun x => physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
      (fun y => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t •
        obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hcov : ∀ t ∈ Icc tA tZ, ∃ p, t ∈ (F.piece p).output := fun t ht =>
    exists_output_of_partition F pp hpart ht
  -- the edge flux of every weighted pulse is continuous, and its lift of class `C^D`
  have hpulse : ∀ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t ≠ 0 →
      (∀ a₀ : Fin 2, Continuous (fun x => physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
        (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x a₀)) ∧
      ContDiff ℝ (D : ℕ∞) (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) := by
    intro k hk hw
    have hs := weighted_cellTime_mem_liftWindow hℓ hpart hk ht hw
    obtain ⟨-, hcont⟩ := pulse_edge_tested_instance hΛ hφs hν hB hρ F actual K htorus (pp k)
      (hpp k hk).2.1 (P k hk) sX sZ hsZ (Cc k) (hseq k hk) cf φ hφ hφp
      (pulse_edge_slow_invariant α q Λ m ζ hφs ν B hρ.ne' k htorus (pp k)) hs v
      (fun {U} hU x a₀ => obs_family_flux hΛ hζ F ν (ocEpsilon q Λ m) E actual K hdesc T hTcons
        hTcov hTq hTact pp (fun k' hk' => (hpp k' hk').1) (fun k' hk' => (hpp k' hk').2.2)
        hppinj hpart hcov hk ht hw hU (Nat.le_succ D) v x a₀)
      (φt := fun _ => (0 : h v)) contDiff_const (fun _ _ => rfl)
    refine ⟨hcont, ?_⟩
    have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
    have hψs : ContDiff ℝ (⊤ : ℕ∞)
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t) :=
      (Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    exact (setting_labelLift_contDiff (P k hk) hsZ (hseq k hk) _ _ ρ (ocEpsilon q Λ m)
      (chartField_contDiff cf φ hφ _ hχj _ ρ _) hs).comp (hψs.of_le (by exact_mod_cast le_top))
  have hfun : (fun x => physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
      (fun y => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t •
        obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x) = fun x =>
      ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) t • physEdgeFluxVec F ν (ocEpsilon q Λ m)
        E actual K t (fun y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y) v x :=
    funext fun x => physEdgeFluxVec_weighted_sum F ν (ocEpsilon q Λ m) E actual K t _
      (fun k => F.weight (pp k) t)
      (fun k y => obsLift α q Λ m φs hφs ν B ρ Cc N H cf φ k t y)
      (fun k hk hw => (hpulse k hk hw).2) v x
  rw [hfun]
  refine continuous_finsetSum _ fun k hk => ?_
  by_cases hw : F.weight (pp k) t = 0
  · simp only [hw, zero_smul]
    exact continuous_const
  · exact (continuous_piLp_of_components (hpulse k hk hw).1).const_smul (F.weight (pp k) t)

end Edges

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVenhance
open AVRegularity.CycleComparison.Lift
open AVRegularity.CycleComparison.Coarse AVRegularity.CycleComparison.Coarse.JointOps
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time measurability of the residual of the glued lift of a Galerkin approximant**.
For the residual presentation `(approxFlux, approxForce)` of `approx_weak_identity`, the
tested residuals `s ↦ ∫_{cell} ⟪R_n(s), ψ⟫` and `s ↦ ∫_{cell} ⟪q_n(s), ψ⟫` are measurable in the
clamped time `s ↦ Set.projIcc tA tZ s`, for every continuous `ψ`
(`approxFlux_tested_measurable`, `approxForce_tested_measurable`).

The lift coefficients and the cleanup chains are not assumed measurable: on every observed pulse
they are measurable in clamped cell time (`setting_tail_chain_measurable`,
`setting_lift_chain_measurable`, `setting_liftApply_joint_measurable`), the clamp being invisible
where the partition weight of the pulse, or its derivative, does not vanish
(`glued_tail_joint_measurable`, `glued_lift_joint_measurable`,
`glued_pulseLift_joint_measurable`). The inputs are assumed measurable: the Galerkin coefficients
of the coarse field and of the coarse flux, and the classical representative, the drift, the
matrix `𝖩` and the coefficients `A_d`, `C^{[r]}` of the coarse defect equation (the forms of
`IsCoarseSetting`). The chain orders satisfy the inequalities of the existence of the chains
(`exists_tail_cleanupChain`, `setting_exists_lift_cleanupChain`). -/

/-! ### Windows -/

/-- A time of a clipped lift window is, in physical time, a time of the observation window. -/
theorem physTime_mem_obs {c a' b' tA tZ τ : ℝ} (hc : 0 < c)
    (hτ : τ ∈ Set.Icc (max a' tA / c) (min b' tZ / c)) : c * τ ∈ Set.Icc tA tZ := by
  have h' : c⁻¹ * (c * τ) ∈ Set.Icc (max a' tA / c) (min b' tZ / c) := by
    rwa [inv_mul_cancel_left₀ hc.ne']
  exact (AVRegularity.CycleComparison.Assembly.mem_window_of_cellTime hc h').2

/-- The derivative of a function vanishing off a closed set vanishes off the set. -/
theorem mem_of_deriv_ne_zero {w : ℝ → ℝ} {S : Set ℝ} (hS : IsClosed S)
    (hw : ∀ t, w t ≠ 0 → t ∈ S) {t : ℝ} (ht : deriv w t ≠ 0) : t ∈ S := by
  by_contra hts
  apply ht
  have hev : w =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [hS.isOpen_compl.mem_nhds hts] with s hs
    by_contra hne
    exact absurd (hw s hne) hs
  rw [hev.deriv_eq, deriv_const]

/-! ### Glued pieces over the observed pulses -/

/-- **The glued physical tail flux and force of the cleanup chains of the pulses are jointly
measurable** in the clamped physical time and the position. -/
theorem glued_tail_joint_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (kset : Finset ℤ) (lo hi : ℤ → ℝ) {c tA tZ : ℝ} (htAZ : tA ≤ tZ)
    {χs ψs : ℤ → ℝ → Vec 2 → Vec 2}
    (hχ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => χs k p.1 p.2)
    (hψ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => ψs k p.1 p.2)
    (hψχ : ∀ k t y, ψs k t (χs k t y) = y) (hχψ : ∀ k t x, χs k t (ψs k t x) = x)
    (wk : ℤ → ℝ → ℝ) (hwm : ∀ k ∈ kset, Measurable (wk k))
    (hwin : ∀ k ∈ kset, ∀ t ∈ Set.Icc tA tZ, wk k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (lo k) (hi k))
    {D H N K₀ k₀ L qs qf : ℕ} (Qk : ℤ → LiftOperatorData ι h D) {π : ι → ℝ}
    {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ kset, IsLiftSetting (Qk k) π (lo k) (hi k) e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀
      (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ kset, IsLiftSequence (Qk k) (K₀ + D + 2) (max (k₀ + 1) (L + 2)) (lo k)
      (hi k) N H (Cc k))
    {sXc sZc Acl : ℕ} (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc) (hXA : sXc + Acl ≤ K₀ + D + 2)
    (hZ1 : sZc + 1 ≤ max (k₀ + 1) (L + 2)) (εd : ℝ) (Ak : ℤ → ℝ → Vec 2 → ∀ i, h i)
    (hAk : ∀ k ∈ kset, ∀ τ ∈ Set.Icc (lo k) (hi k), ContDiff ℝ (⊤ : ℕ∞) (Ak k τ))
    (hAkm : ∀ k (hk : k ∈ kset), ∀ X,
      Measurable fun τ => Ak k (Set.projIcc (lo k) (hi k) (P k hk).window τ) X)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ kset, ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc (lo k) (hi k),
      IsCleanupChain sXc sZc Acl (tailScalarField (fun _ => 0) N D εd (Ak k) τ)
        (tailFluxField (fun n' => tailFluxCoefficient (par k) (Qk k) (Cc k) N hh n') N D εd
          (Ak k) τ) (fun j => Vc k hh j τ))
    (ε ρs es : ℝ) :
    (∀ a₀ : Fin 2, Measurable fun p : ℝ × Vec 2 => gluedTailFlux kset wk ψs H N Acl ε c ρs es Vc
        (Set.projIcc tA tZ htAZ p.1) p.2 a₀) ∧
      (1 ≤ Acl → Measurable fun p : ℝ × Vec 2 => gluedTailForce kset wk ψs H N Acl ε c ρs es Vc
        (Set.projIcc tA tZ htAZ p.1) p.2) := by
  have hθ : Measurable fun p : ℝ × Vec 2 => (Set.projIcc tA tZ htAZ p.1 : ℝ) :=
    (continuous_subtype_val.comp (continuous_projIcc (h := htAZ))).measurable.comp
      measurable_fst
  have hΨ : ∀ k, Measurable fun p : ℝ × Vec 2 => ψs k p.1 p.2 := fun k =>
    (hψ k).continuous.measurable
  have hK : ∀ k, ∀ a₀ i₀ : Fin 2,
      Measurable fun p : ℝ × Vec 2 => chartInvJacobian (ψs k p.1) p.2 a₀ i₀ := fun k a₀ i₀ =>
    (continuous_chartInvJacobian_joint (hχ k) (hψ k) (hψχ k) (hχψ k) a₀ i₀).measurable
  have hchain : ∀ k (hk : k ∈ kset), ∀ hh, hh ≤ H →
      (∀ j, j < Acl → Measurable fun q : ℝ × Vec 2 × Vec 2 =>
        Vc k hh j (Set.projIcc (lo k) (hi k) (P k hk).window q.1) q.2.1 q.2.2) ∧
      (1 ≤ Acl → Measurable fun q : ℝ × Vec 2 × Vec 2 =>
        cleanupSource (fun j => Vc k hh j (Set.projIcc (lo k) (hi k) (P k hk).window q.1)) Acl
          q.2.1 q.2.2) := by
    intro k hk hh hhh
    obtain ⟨hm1, hm2⟩ := setting_tail_chain_measurable (P k hk) (K₀ + D + 2)
      (max (k₀ + 1) (L + 2)) (by omega) (by omega) (Cc k) (hseq k hk) hXc hZc hXA hZ1 εd (Ak k)
      (hAk k hk) (hAkm k hk) hh hhh (Vc k hh) (hV k hk hh hhh)
    have hFbox : ∀ τ ∈ Set.Icc (lo k) (hi k), IsBoxSmooth sXc sZc
        (tailFluxField (fun n' => tailFluxCoefficient (par k) (Qk k) (Cc k) N hh n') N D εd
          (Ak k) τ) := fun τ hτ =>
      (isBoxSmooth_tailFluxField_of_presentation (f := fun _ => 0)
        (F := fun n' => tailFluxCoefficient (par k) (Qk k) (Cc k) N hh n')
        (fun n' hn1 hn2 => setting_tail_presentation (P k hk) (K₀ + D + 2)
          (max (k₀ + 1) (L + 2)) (by omega) (by omega) (Cc k) (hseq k hk) hh hhh n' (by omega)
          hn2) εd (Ak k) hτ (hAk k hk τ hτ)).mono (by omega) (by omega)
    refine ⟨fun j hj => cleanupChain_joint_measurable (P k hk).window (Vc k hh) hFbox
      (hV k hk hh hhh) j hj fun X z => measurable_pi_iff.mpr fun kk =>
        measurable_pi_iff.mpr fun i => hm1 j hj X z kk i, fun hA1 => ?_⟩
    exact cleanupSource_joint_measurable hXc hA1 (P k hk).window (Vc k hh) hFbox
      (hV k hk hh hhh) fun X z => measurable_pi_iff.mpr fun i => hm2 hA1 X z i
  refine ⟨fun a₀ => ?_, fun hA1 => ?_⟩
  · show Measurable fun p : ℝ × Vec 2 => ∑ k ∈ kset, wk k (Set.projIcc tA tZ htAZ p.1) •
      tailFluxPhys (ψs k (Set.projIcc tA tZ htAZ p.1)) H N Acl ε c ρs es (Vc k)
        (Set.projIcc tA tZ htAZ p.1) p.2 a₀
    refine Finset.measurable_sum _ fun k hk => measurable_weight_smul_of_ne ((hwm k hk).comp hθ)
      (measurable_tailFluxPhys_joint hθ (hΨ k) (hK k) H N Acl ε c ρs es
        (fun hh j τ => Vc k hh j (Set.projIcc (lo k) (hi k) (P k hk).window τ))
        (fun hh hhh j hj => (hchain k hk hh hhh).1 j hj) a₀) fun p hp => ?_
    exact (tailFluxPhys_clamp_eq _ H N Acl ε c ρs es (P k hk).window (Vc k)
      (hwin k hk _ (Set.projIcc tA tZ htAZ p.1).2 hp) p.2 a₀).symm
  · show Measurable fun p : ℝ × Vec 2 => ∑ k ∈ kset, wk k (Set.projIcc tA tZ htAZ p.1) •
      tailForcePhys (ψs k (Set.projIcc tA tZ htAZ p.1)) H N Acl ε c ρs es (Vc k)
        (Set.projIcc tA tZ htAZ p.1) p.2
    refine Finset.measurable_sum _ fun k hk => measurable_weight_smul_of_ne ((hwm k hk).comp hθ)
      (measurable_tailForcePhys_joint hθ (hΨ k) H N Acl ε c ρs es
        (fun hh j τ => Vc k hh j (Set.projIcc (lo k) (hi k) (P k hk).window τ))
        (fun hh hhh => (hchain k hk hh hhh).2 hA1)) fun p hp => ?_
    exact (tailForcePhys_clamp_eq _ H N Acl ε c ρs es (P k hk).window (Vc k)
      (hwin k hk _ (Set.projIcc tA tZ htAZ p.1).2 hp) p.2).symm

/-- **The glued physical lifted coarse flux and force of the cleanup chains of the pulses are
jointly measurable** in the clamped physical time and the position. -/
theorem glued_lift_joint_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (kset : Finset ℤ) (lo hi : ℤ → ℝ) {c tA tZ : ℝ} (htAZ : tA ≤ tZ)
    {χs ψs : ℤ → ℝ → Vec 2 → Vec 2}
    (hχ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => χs k p.1 p.2)
    (hψ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => ψs k p.1 p.2)
    (hψχ : ∀ k t y, ψs k t (χs k t y) = y) (hχψ : ∀ k t x, χs k t (ψs k t x) = x)
    (wk : ℤ → ℝ → ℝ) (hwm : ∀ k ∈ kset, Measurable (wk k))
    (hwin : ∀ k ∈ kset, ∀ t ∈ Set.Icc tA tZ, wk k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (lo k) (hi k))
    {D H N K₀ k₀ L qs qf : ℕ} (Qk : ℤ → LiftOperatorData ι h D) {π : ι → ℝ}
    {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ kset, IsLiftSetting (Qk k) π (lo k) (hi k) e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀
      (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ kset, IsLiftSequence (Qk k) (K₀ + D + 2) (max (k₀ + 1) (L + 2)) (lo k)
      (hi k) N H (Cc k))
    {sXl sZl Acl : ℕ} (hXl : 1 ≤ sXl) (hZl : 1 ≤ sZl) (hXlA : sXl + Acl ≤ K₀ + N + 2 * D + 2)
    (hZlA : sZl + 1 ≤ max k₀ (L + 2) + 2 * D) (Gk : ℤ → ℝ → Vec 2 → ∀ i, h i)
    (hGk : ∀ k ∈ kset, ∀ τ ∈ Set.Icc (lo k) (hi k), ContDiff ℝ (⊤ : ℕ∞) (Gk k τ))
    (hGkm : ∀ k (hk : k ∈ kset), ∀ X,
      Measurable fun τ => Gk k (Set.projIcc (lo k) (hi k) (P k hk).window τ) X)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ kset, ∀ hh, hh ≤ H → ∀ n', n' < N → ∀ τ ∈ Set.Icc (lo k) (hi k),
      IsCleanupChain sXl sZl Acl (liftApply (n' + 1) (Cc k hh (n' + 1)) (Gk k) τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    (ε ρs es : ℝ) :
    (∀ a₀ : Fin 2, Measurable fun p : ℝ × Vec 2 => gluedLiftFlux kset wk ψs H N Acl ε c ρs es Vn
        (Set.projIcc tA tZ htAZ p.1) p.2 a₀) ∧
      (1 ≤ Acl → Measurable fun p : ℝ × Vec 2 => gluedLiftForce kset wk ψs H N Acl ε c ρs es Vn
        (Set.projIcc tA tZ htAZ p.1) p.2) := by
  have hθ : Measurable fun p : ℝ × Vec 2 => (Set.projIcc tA tZ htAZ p.1 : ℝ) :=
    (continuous_subtype_val.comp (continuous_projIcc (h := htAZ))).measurable.comp
      measurable_fst
  have hΨ : ∀ k, Measurable fun p : ℝ × Vec 2 => ψs k p.1 p.2 := fun k =>
    (hψ k).continuous.measurable
  have hK : ∀ k, ∀ a₀ i₀ : Fin 2,
      Measurable fun p : ℝ × Vec 2 => chartInvJacobian (ψs k p.1) p.2 a₀ i₀ := fun k a₀ i₀ =>
    (continuous_chartInvJacobian_joint (hχ k) (hψ k) (hψχ k) (hχψ k) a₀ i₀).measurable
  have hchain : ∀ k (hk : k ∈ kset), ∀ hh, hh ≤ H → ∀ n', n' < N →
      (∀ j, j < Acl → Measurable fun q : ℝ × Vec 2 × Vec 2 =>
        Vn k hh n' j (Set.projIcc (lo k) (hi k) (P k hk).window q.1) q.2.1 q.2.2) ∧
      (1 ≤ Acl → Measurable fun q : ℝ × Vec 2 × Vec 2 =>
        cleanupSource (fun j => Vn k hh n' j (Set.projIcc (lo k) (hi k) (P k hk).window q.1))
          Acl q.2.1 q.2.2) := by
    intro k hk hh hhh n' hn'
    obtain ⟨hm1, hm2⟩ := setting_lift_chain_measurable (P k hk) (K₀ + D + 2)
      (max (k₀ + 1) (L + 2)) (by omega) (Cc k) (hseq k hk) hXl hZl hXlA hZlA (Gk k) (hGk k hk)
      (hGkm k hk) hh hhh n' hn' (Vn k hh n') (hVn k hk hh hhh n' hn')
    have hFbox : ∀ τ ∈ Set.Icc (lo k) (hi k), IsBoxSmooth sXl sZl
        ((fun (_ : ℝ) (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) τ) := fun _ _ =>
      isBoxSmooth_zero _ _
    refine ⟨fun j hj => cleanupChain_joint_measurable
      (F₀ := fun (_ : ℝ) (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) (P k hk).window
      (Vn k hh n') hFbox (hVn k hk hh hhh n' hn') j hj fun X z => measurable_pi_iff.mpr fun kk =>
        measurable_pi_iff.mpr fun i => hm1 j hj X z kk i, fun hA1 => ?_⟩
    exact cleanupSource_joint_measurable
      (F₀ := fun (_ : ℝ) (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) hXl hA1 (P k hk).window
      (Vn k hh n') hFbox (hVn k hk hh hhh n' hn') fun X z => measurable_pi_iff.mpr fun i =>
        hm2 hA1 X z i
  refine ⟨fun a₀ => ?_, fun hA1 => ?_⟩
  · show Measurable fun p : ℝ × Vec 2 => ∑ k ∈ kset, wk k (Set.projIcc tA tZ htAZ p.1) •
      liftFluxPhys (ψs k (Set.projIcc tA tZ htAZ p.1)) H N Acl ε c ρs es (Vn k)
        (Set.projIcc tA tZ htAZ p.1) p.2 a₀
    refine Finset.measurable_sum _ fun k hk => measurable_weight_smul_of_ne ((hwm k hk).comp hθ)
      (measurable_liftFluxPhys_joint hθ (hΨ k) (hK k) H N Acl ε c ρs es
        (fun hh n' j τ => Vn k hh n' j (Set.projIcc (lo k) (hi k) (P k hk).window τ))
        (fun hh hhh n' hn' j hj => (hchain k hk hh hhh n' hn').1 j hj) a₀) fun p hp => ?_
    exact (liftFluxPhys_clamp_eq _ H N Acl ε c ρs es (P k hk).window (Vn k)
      (hwin k hk _ (Set.projIcc tA tZ htAZ p.1).2 hp) p.2 a₀).symm
  · show Measurable fun p : ℝ × Vec 2 => ∑ k ∈ kset, wk k (Set.projIcc tA tZ htAZ p.1) •
      liftForcePhys (ψs k (Set.projIcc tA tZ htAZ p.1)) H N Acl ε c ρs es (Vn k)
        (Set.projIcc tA tZ htAZ p.1) p.2
    refine Finset.measurable_sum _ fun k hk => measurable_weight_smul_of_ne ((hwm k hk).comp hθ)
      (measurable_liftForcePhys_joint hθ (hΨ k) H N Acl ε c ρs es
        (fun hh n' j τ => Vn k hh n' j (Set.projIcc (lo k) (hi k) (P k hk).window τ))
        (fun hh hhh n' hn' => (hchain k hk hh hhh n' hn').2 hA1)) fun p hp => ?_
    exact (liftForcePhys_clamp_eq _ H N Acl ε c ρs es (P k hk).window (Vn k)
      (hwin k hk _ (Set.projIcc tA tZ htAZ p.1).2 hp) p.2).symm

/-- **The glued physical lift of a jointly measurable coarse field, with weights vanishing off
the lift windows, is jointly measurable** in the clamped physical time and the position. -/
theorem glued_pulseLift_joint_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (kset : Finset ℤ) (lo hi : ℤ → ℝ) {c tA tZ : ℝ} (htAZ : tA ≤ tZ)
    (hphys : ∀ k ∈ kset, ∀ τ ∈ Set.Icc (lo k) (hi k), c * τ ∈ Set.Icc tA tZ)
    {χs ψs : ℤ → ℝ → Vec 2 → Vec 2}
    (hχ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => χs k p.1 p.2)
    (hψ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => ψs k p.1 p.2)
    (wk : ℤ → ℝ → ℝ) (hwm : ∀ k ∈ kset, Measurable (wk k))
    (hwin : ∀ k ∈ kset, ∀ t ∈ Set.Icc tA tZ, wk k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (lo k) (hi k))
    {D H N K₀ k₀ L qs qf : ℕ} (Qk : ℤ → LiftOperatorData ι h D) {π : ι → ℝ}
    {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ kset, IsLiftSetting (Qk k) π (lo k) (hi k) e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀
      (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ kset, IsLiftSequence (Qk k) (K₀ + D + 2) (max (k₀ + 1) (L + 2)) (lo k)
      (hi k) N H (Cc k))
    (a : ℝ → Vec 2 → ∀ i, h i) (ha : JointlyMeas tA tZ a)
    (haN : ∀ s ∈ Set.Icc tA tZ, ContDiff ℝ (N : ℕ∞) (a s)) (ρ e εc : ℝ) :
    Measurable fun p : ℝ × Vec 2 => ∑ k ∈ kset, wk k (Set.projIcc tA tZ htAZ p.1) •
      pulsePhysicalLift c ρ e εc N H (Cc k) (χs k) (ψs k) a (Set.projIcc tA tZ htAZ p.1) p.2 := by
  have hθ : Measurable fun p : ℝ × Vec 2 => (Set.projIcc tA tZ htAZ p.1 : ℝ) :=
    (continuous_subtype_val.comp (continuous_projIcc (h := htAZ))).measurable.comp
      measurable_fst
  have hΨ : ∀ k, Measurable fun p : ℝ × Vec 2 => ψs k p.1 p.2 := fun k =>
    (hψ k).continuous.measurable
  have hχt : ∀ k t, ContDiff ℝ (⊤ : ℕ∞) (χs k t) := fun k t =>
    (hχ k).comp (contDiff_const.prodMk contDiff_id)
  refine Finset.measurable_sum _ fun k hk => measurable_weight_smul_of_ne ((hwm k hk).comp hθ)
    (measurable_pulseLift_clamped (P k hk).window hθ (hΨ k) c ρ e εc N H (Cc k)
      (fun s' X' => a (c * s') (χs k (c * s') (ρ • X')))
      (fun hh hhh n' hn' v => setting_liftApply_joint_measurable (P k hk) (K₀ + D + 2)
        (max (k₀ + 1) (L + 2)) (by omega) (Cc k) (hseq k hk) hh hhh n' _
        (fun τ hτ => ((haN (c * τ) (hphys k hk τ hτ)).comp
          (((hχt k (c * τ)).of_le (order_natCast_le_top _)).comp
            (contDiff_const_smul ρ))).of_le (by exact_mod_cast hn'))
        (fun X => chartFrame_clamped_measurable (c := c) (ρ := ρ) (P k hk).window (hphys k hk)
          ha (hχ k).continuous X) v)) fun p hp => ?_
  rw [pulsePhysicalLift_eq_sum,
    projIcc_val_of_mem (P k hk).window (hwin k hk _ (Set.projIcc tA tZ htAZ p.1).2 hp)]

/-! ### The residual of the glued lift of a Galerkin approximant -/

/-- **The tested flux residual of the glued lift of a Galerkin approximant is measurable in
time** (clamped to the window `[tA, tZ]`), for every continuous test `ψ`. -/
theorem approxFlux_tested_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {α q : ℝ} {Λ m : ℕ} {φs : ℝ → Vec 2 → ℝ} (hφs : IsAdmissibleStream φs) (hΛ : 1 ≤ Λ)
    {ν B ρ : ℝ} (hν : 0 < ν) {D : ℕ} {tA tZ : ℝ} (htAZ : tA ≤ tZ) (ϖ : ℤ → ℝ → ℝ)
    {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Set.Icc tA tZ) (ocTau α q Λ m) Cpart)
    (Qk : ℤ → LiftOperatorData ι h D) {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ}
    {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ} {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ}
    {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (Qk k) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (Qk k) (K₀ + D + 2) (max (k₀ + 1) (L + 2))
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {sXc sZc Acl : ℕ} (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hXA : sXc + Acl ≤ K₀ + D + 2) (hZ1 : sZc + 1 ≤ max (k₀ + 1) (L + 2))
    {sXl sZl : ℕ} (hXl : 1 ≤ sXl) (hZl : 1 ≤ sZl)
    (hXlA : sXl + Acl ≤ K₀ + N + 2 * D + 2) (hZlA : sZl + 1 ≤ max k₀ (L + 2) + 2 * D)
    (n : ℕ) {K kc : ℕ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
    (hcm : ∀ r, Measurable fun s => coarseCoeff n W r (Set.projIcc tA tZ htAZ s))
    (hFm : ∀ r, Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tA tZ htAZ s)) r)
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) N D (ocDStar q Λ m ν B / ρ) (chartField (coarseCoeff n W)
          (coarseMode n) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocEll q Λ m ν ^ 2) ρ) τ)
        (tailFluxField (fun n' => tailFluxCoefficient (par k) (Qk k) (Cc k) N hh n') N D
          (ocDStar q Λ m ν B / ρ) (chartField (coarseCoeff n W) (coarseMode n)
            (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) τ)
        (fun j => Vc k hh j τ))
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H → ∀ n', n' < N →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s X => fluxApproxDiv n Fc
          (ocEll q Λ m ν ^ 2 * s)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
            (ρ • X))) τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    (v : ι) (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (hψ : Continuous ψ) :
    Measurable fun s => ∫ x in AVenhance.unitCube, inner ℝ
      (approxFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc Vn n Fc v
        (Set.projIcc tA tZ htAZ s) x) (ψ x) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hℓ).symm
  have hcm' : ∀ r, Measurable fun s : Set.Icc tA tZ => coarseCoeff n W r s := fun r => by
    have h1 := (hcm r).comp (measurable_subtype_coe (p := fun s => s ∈ Set.Icc tA tZ))
    simpa only [Function.comp_def, Set.projIcc_val] using h1
  have hFm' : ∀ r, Measurable fun s : Set.Icc tA tZ =>
      coarseModeCoeff n (fun v => Fc v s) r := fun r => by
    have h1 := (hFm r).comp (measurable_subtype_coe (p := fun s => s ∈ Set.Icc tA tZ))
    simpa only [Function.comp_def, Set.projIcc_val] using h1
  have hχ : ∀ k : ℤ, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 =>
      ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) p.1 p.2 := fun k =>
    Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
  have hψc : ∀ k : ℤ, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 =>
      ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) p.1 p.2 := fun k =>
    Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
  have hphys : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ τ ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      ocEll q Λ m ν ^ 2 * τ ∈ Set.Icc tA tZ := fun _ _ _ hτ => physTime_mem_obs hc0 hτ
  have hwin : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ t ∈ Set.Icc tA tZ, ϖ k t ≠ 0 →
      (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
    fun k hk t ht hw => cellTime_mem_pulseLiftWindow hc0 (hpart.2.2.2.1 k hk t hw) ht
  have hwm : ∀ k ∈ ocObsPulses α q Λ m tA tZ, Measurable (ϖ k) := fun k hk =>
    (hpart.2.1 k hk).continuous.measurable
  have hTraj : JointlyMeas tA tZ (coarseTraj n W) := jointlyMeas_coarseTraj n W hcm'
  have hDiv : JointlyMeas tA tZ (fluxApproxDiv n Fc) := jointlyMeas_fluxApproxDiv n Fc hFm'
  obtain ⟨hT, -⟩ := glued_tail_joint_measurable (ocObsPulses α q Λ m tA tZ)
    (fun k : ℤ => max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
    (fun k : ℤ => min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) htAZ
    (χs := fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (ψs := fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) hχ hψc
    (fun k t y => Charts.ocChartInv_ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t y)
    (fun k t x => Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x)
    ϖ hwm hwin Qk P Cc hseq hXc hZc hXA hZ1 (ocDStar q Λ m ν B / ρ)
    (fun k => chartField (coarseCoeff n W) (coarseMode n)
      (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ)
    (fun k _ τ _ => chartField_contDiff (coarseCoeff n W) (coarseMode n) (coarseMode_contDiff n)
      (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (hχ k) (ocEll q Λ m ν ^ 2) ρ τ)
    (fun k hk X => chartFrame_clamped_measurable (c := ocEll q Λ m ν ^ 2) (ρ := ρ)
      (P k hk).window (hphys k hk) hTraj (hχ k).continuous X)
    Vc hV (ocDStar q Λ m ν B / ρ) ρ (ocEpsilon q Λ m)
  obtain ⟨hL, -⟩ := glued_lift_joint_measurable (ocObsPulses α q Λ m tA tZ)
    (fun k : ℤ => max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
    (fun k : ℤ => min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) htAZ
    (χs := fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (ψs := fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) hχ hψc
    (fun k t y => Charts.ocChartInv_ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t y)
    (fun k t x => Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x)
    ϖ hwm hwin Qk P Cc hseq hXl hZl hXlA hZlA
    (fun k s X => fluxApproxDiv n Fc (ocEll q Λ m ν ^ 2 * s)
      (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s) (ρ • X)))
    (fun k _ τ _ => (fluxApproxDiv_contDiff n Fc (ocEll q Λ m ν ^ 2 * τ)).comp
      (((hχ k).comp ((contDiff_const (c := ocEll q Λ m ν ^ 2 * τ)).prodMk contDiff_id)).comp
        (contDiff_const_smul ρ)))
    (fun k hk X => chartFrame_clamped_measurable (c := ocEll q Λ m ν ^ 2) (ρ := ρ)
      (P k hk).window (hphys k hk) hDiv (hχ k).continuous X)
    Vn hVn (ocDStar q Λ m ν B / ρ) ρ (ocEpsilon q Λ m)
  have hA : ∀ a₀ : Fin 2, Measurable fun p : ℝ × Vec 2 =>
      fluxApprox n (fun v => Fc v (Set.projIcc tA tZ htAZ p.1)) p.2 a₀ v := fun a₀ =>
    jointlyMeas_comp_projIcc htAZ (jointlyMeas_fluxApprox n Fc hFm' a₀ v)
  have hjoint : Measurable fun p : ℝ × Vec 2 => inner ℝ
      (approxFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc Vn n Fc v
        (Set.projIcc tA tZ htAZ p.1) p.2) (ψ p.2) := by
    have e : (fun p : ℝ × Vec 2 => inner ℝ
        (approxFlux α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Vc Vn n Fc v
          (Set.projIcc tA tZ htAZ p.1) p.2) (ψ p.2)) = fun p => ∑ a₀ : Fin 2, inner ℝ
        (gluedTailFlux (ocObsPulses α q Λ m tA tZ) ϖ
            (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
            (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc
            (Set.projIcc tA tZ htAZ p.1) p.2 a₀ v
          + fluxApprox n (fun v => Fc v (Set.projIcc tA tZ htAZ p.1)) p.2 a₀ v
          + gluedLiftFlux (ocObsPulses α q Λ m tA tZ) ϖ
            (fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) H N Acl
            (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn
            (Set.projIcc tA tZ htAZ p.1) p.2 a₀ v) (ψ p.2 a₀) :=
      funext fun p => PiLp.inner_apply _ _
    rw [e]
    exact Finset.measurable_sum _ fun a₀ _ => Measurable.inner
      ((((measurable_pi_apply v).comp (hT a₀)).fun_add (hA a₀)).fun_add
        ((measurable_pi_apply v).comp (hL a₀)))
      (((PiLp.continuous_apply 2 _ a₀).comp hψ).measurable.comp measurable_snd)
  exact (hjoint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict AVenhance.unitCube)).measurable

/-- **The tested forcing residual of the glued lift of a Galerkin approximant is measurable in
time** (clamped to the window `[tA, tZ]`), for every continuous test `ψ`. -/
theorem approxForce_tested_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {α q : ℝ} {Λ m : ℕ} {φs : ℝ → Vec 2 → ℝ} (hφs : IsAdmissibleStream φs) (hΛ : 1 ≤ Λ)
    {ν B ρ : ℝ} (hν : 0 < ν) {D : ℕ} {tA tZ : ℝ} (htAZ : tA ≤ tZ) (ϖ : ℤ → ℝ → ℝ)
    {quiet : Set ℝ} {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) ϖ (ocPulseWindow α q Λ m) quiet
      (Set.Icc tA tZ) (ocTau α q Λ m) Cpart)
    (Qk : ℤ → LiftOperatorData ι h D) {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ}
    {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ} {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ}
    {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (Qk k) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (Qk k) (K₀ + D + 2) (max (k₀ + 1) (L + 2))
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    {sXc sZc Acl : ℕ} (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hXA : sXc + Acl ≤ K₀ + D + 2) (hZ1 : sZc + 1 ≤ max (k₀ + 1) (L + 2))
    {sXl sZl : ℕ} (hXl : 1 ≤ sXl) (hZl : 1 ≤ sZl)
    (hXlA : sXl + Acl ≤ K₀ + N + 2 * D + 2) (hZlA : sZl + 1 ≤ max k₀ (L + 2) + 2 * D)
    -- the coarse defect data
    {b : ℝ → Vec 2 → Vec 2} {Dl : ℕ}
    {AD : ∀ d : Finset.Icc 2 Dl, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 Dl), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (n : ℕ) {K kc r₀ : ℕ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))} (aRep : ℝ → Vec 2 → ∀ i, h i)
    (hrep : ∀ s ∈ Set.Icc tA tZ, ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hDl : 2 ≤ Dl) (hDr : Dl ≤ r₀)
    (hAD : ∀ s ∈ Set.Icc tA tZ, ∀ d, ContDiff ℝ 1 (AD d s))
    (hCE : ∀ s ∈ Set.Icc tA tZ, ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hbc : ∀ s, Continuous (b s))
    (hEN : ∀ s ∈ Set.Icc tA tZ, ContDiff ℝ (N : ℕ∞)
      (defectRemainder n b Dl H AD CE Jm W aRep s))
    -- the measurability of the inputs
    (hcm : ∀ r, Measurable fun s => coarseCoeff n W r (Set.projIcc tA tZ htAZ s))
    (hFm : ∀ r, Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tA tZ htAZ s)) r)
    (hbm : Measurable fun q : Set.Icc tA tZ × Vec 2 => b q.1 q.2)
    (hJm : ∀ i j, Measurable fun t => Jm t i j)
    (hADm : ∀ d, Measurable fun q : Set.Icc tA tZ × Vec 2 => AD d q.1 q.2)
    (hCEm : ∀ r ∈ Finset.Icc 1 H, ∀ v u d,
      Measurable fun q : Set.Icc tA tZ × Vec 2 => CE r v u d q.1 q.2)
    (haRm : Measurable fun q : Set.Icc tA tZ × Vec 2 => aRep q.1 q.2)
    -- the cleanup chains
    (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) N D (ocDStar q Λ m ν B / ρ) (chartField (coarseCoeff n W)
          (coarseMode n) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
          (ocEll q Λ m ν ^ 2) ρ) τ)
        (tailFluxField (fun n' => tailFluxCoefficient (par k) (Qk k) (Cc k) N hh n') N D
          (ocDStar q Λ m ν B / ρ) (chartField (coarseCoeff n W) (coarseMode n)
            (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ) τ)
        (fun j => Vc k hh j τ))
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H → ∀ n', n' < N →
      ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s X => fluxApproxDiv n Fc
          (ocEll q Λ m ν ^ 2 * s)
          (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
            (ρ • X))) τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    (v : ι) (ψ : Vec 2 → h v) (hψ : Continuous ψ) :
    Measurable fun s => ∫ x in AVenhance.unitCube, inner ℝ
      (approxForce α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Cc Vc Vn n b Dl AD CE Jm W aRep v
        (Set.projIcc tA tZ htAZ s) x) (ψ x) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hℓ).symm
  have hcm' : ∀ r, Measurable fun s : Set.Icc tA tZ => coarseCoeff n W r s := fun r => by
    have h1 := (hcm r).comp (measurable_subtype_coe (p := fun s => s ∈ Set.Icc tA tZ))
    simpa only [Function.comp_def, Set.projIcc_val] using h1
  have hFm' : ∀ r, Measurable fun s : Set.Icc tA tZ =>
      coarseModeCoeff n (fun v => Fc v s) r := fun r => by
    have h1 := (hFm r).comp (measurable_subtype_coe (p := fun s => s ∈ Set.Icc tA tZ))
    simpa only [Function.comp_def, Set.projIcc_val] using h1
  have hχ : ∀ k : ℤ, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 =>
      ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) p.1 p.2 := fun k =>
    Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
  have hψc : ∀ k : ℤ, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 =>
      ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) p.1 p.2 := fun k =>
    Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)
  have hphys : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ τ ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      ocEll q Λ m ν ^ 2 * τ ∈ Set.Icc tA tZ := fun _ _ _ hτ => physTime_mem_obs hc0 hτ
  have hwin : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ t ∈ Set.Icc tA tZ, ϖ k t ≠ 0 →
      (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
    fun k hk t ht hw => cellTime_mem_pulseLiftWindow hc0 (hpart.2.2.2.1 k hk t hw) ht
  have hwin' : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ t ∈ Set.Icc tA tZ, deriv (ϖ k) t ≠ 0 →
      (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) :=
    fun k hk t ht hw => cellTime_mem_pulseLiftWindow hc0
      (mem_of_deriv_ne_zero (S := ocPulseWindow α q Λ m k) isClosed_Icc
        (hpart.2.2.2.1 k hk) hw) ht
  have hwm : ∀ k ∈ ocObsPulses α q Λ m tA tZ, Measurable (ϖ k) := fun k hk =>
    (hpart.2.1 k hk).continuous.measurable
  have hTraj : JointlyMeas tA tZ (coarseTraj n W) := jointlyMeas_coarseTraj n W hcm'
  have hDiv : JointlyMeas tA tZ (fluxApproxDiv n Fc) := jointlyMeas_fluxApproxDiv n Fc hFm'
  have hRem : JointlyMeas tA tZ (defectRemainder n b Dl H AD CE Jm W aRep) :=
    jointlyMeas_defectRemainder n W aRep hDl hDr hbm hbc hJm hADm hAD hCEm hCE hcm' haRm hrep
  obtain ⟨-, hT⟩ := glued_tail_joint_measurable (ocObsPulses α q Λ m tA tZ)
    (fun k : ℤ => max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
    (fun k : ℤ => min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) htAZ
    (χs := fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (ψs := fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) hχ hψc
    (fun k t y => Charts.ocChartInv_ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t y)
    (fun k t x => Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x)
    ϖ hwm hwin Qk P Cc hseq hXc hZc hXA hZ1 (ocDStar q Λ m ν B / ρ)
    (fun k => chartField (coarseCoeff n W) (coarseMode n)
      (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ)
    (fun k _ τ _ => chartField_contDiff (coarseCoeff n W) (coarseMode n) (coarseMode_contDiff n)
      (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) (hχ k) (ocEll q Λ m ν ^ 2) ρ τ)
    (fun k hk X => chartFrame_clamped_measurable (c := ocEll q Λ m ν ^ 2) (ρ := ρ)
      (P k hk).window (hphys k hk) hTraj (hχ k).continuous X)
    Vc hV (ocDStar q Λ m ν B / ρ) ρ (ocEpsilon q Λ m)
  obtain ⟨-, hL⟩ := glued_lift_joint_measurable (ocObsPulses α q Λ m tA tZ)
    (fun k : ℤ => max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
    (fun k : ℤ => min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) htAZ
    (χs := fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (ψs := fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) hχ hψc
    (fun k t y => Charts.ocChartInv_ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t y)
    (fun k t x => Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) t x)
    ϖ hwm hwin Qk P Cc hseq hXl hZl hXlA hZlA
    (fun k s X => fluxApproxDiv n Fc (ocEll q Λ m ν ^ 2 * s)
      (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s) (ρ • X)))
    (fun k _ τ _ => (fluxApproxDiv_contDiff n Fc (ocEll q Λ m ν ^ 2 * τ)).comp
      (((hχ k).comp ((contDiff_const (c := ocEll q Λ m ν ^ 2 * τ)).prodMk contDiff_id)).comp
        (contDiff_const_smul ρ)))
    (fun k hk X => chartFrame_clamped_measurable (c := ocEll q Λ m ν ^ 2) (ρ := ρ)
      (P k hk).window (hphys k hk) hDiv (hχ k).continuous X)
    Vn hVn (ocDStar q Λ m ν B / ρ) ρ (ocEpsilon q Λ m)
  have hO := glued_pulseLift_joint_measurable (ocObsPulses α q Λ m tA tZ)
    (fun k : ℤ => max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
    (fun k : ℤ => min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) htAZ hphys
    (χs := fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (ψs := fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) hχ hψc
    ϖ hwm hwin Qk P Cc hseq (defectRemainder n b Dl H AD CE Jm W aRep) hRem hEN ρ
    (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ)
  have hD := glued_pulseLift_joint_measurable (ocObsPulses α q Λ m tA tZ)
    (fun k : ℤ => max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
    (fun k : ℤ => min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) htAZ hphys
    (χs := fun k => ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m k))
    (ψs := fun k => ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m k)) hχ hψc
    (fun k => deriv (ϖ k)) (fun k _ => measurable_deriv (ϖ k)) hwin' Qk P Cc hseq
    (coarseTraj n W) hTraj (fun s _ => (coarseTraj_contDiff n W s).of_le
      (order_natCast_le_top _)) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ)
  have hjoint : Measurable fun p : ℝ × Vec 2 => inner ℝ
      (approxForce α q Λ m φs hφs ν B ρ tA tZ ϖ H N Acl Cc Vc Vn n b Dl AD CE Jm W aRep v
        (Set.projIcc tA tZ htAZ p.1) p.2) (ψ p.2) :=
    Measurable.inner (((((measurable_pi_apply v).comp (hT hAcl)).fun_add
      ((measurable_pi_apply v).comp (hL hAcl))).fun_add ((measurable_pi_apply v).comp hO)).fun_add
        ((measurable_pi_apply v).comp hD)) (hψ.measurable.comp measurable_snd)
  exact (hjoint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict AVenhance.unitCube)).measurable

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Cleanup chains of the Galerkin approximants**. For every Galerkin level `n`,
cleanup chains of the tails of the lifts of the approximant `a_n` (`exists_tail_chains`) and of
the positive degrees of the lifts of the divergence of the flux approximant
(`exists_lift_chains`) exist on every observed pulse, at chain orders `(sXc, sZc)` below the
orders of the lift sequences. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **Cleanup chains of the tails of the lifts of an approximant.** -/
theorem ReconWindowAt.exists_tail_chains
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀) (n :
          ℕ)
    (sXc sZc Acl : ℕ) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc) (hX : sXc + Acl ≤ Klift + D + 2)
    (hZ : sZc + 1 ≤ Llift + 2) :
    ∃ Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
      ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
        ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
        IsCleanupChain sXc sZc Acl
          (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
            (chartField (coarseCoeff n W) (coarseMode n) (ocChart α q Λ m (Φ (m - 1)) hφ
                (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2)
              ρ) τ)
          (tailFluxField (fun n' => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
              hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k (F.fiber (pp k) (actual (pp
                k)))) (Cc k) Nc hh n') Nc D
            (ocDStar q Λ m ν B / ρ)
            (chartField (coarseCoeff n W) (coarseMode n) (ocChart α q Λ m (Φ (m - 1)) hφ
                (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2)
              ρ) τ)
          (fun j => Vc k hh j τ) := by
  have hex : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H →
      ∃ V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i, ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) *
          ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
        IsCleanupChain sXc sZc Acl
          (tailScalarField (fun _ => 0) Nc D (ocDStar q Λ m ν B / ρ)
            (chartField (coarseCoeff n W) (coarseMode n) (ocChart α q Λ m (Φ (m - 1)) hφ
                (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2)
              ρ) τ)
          (tailFluxField (fun n' => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
              hφ ν B ρ
            (ρ / ocEpsilon q Λ (m - 1)) k (F.fiber (pp k) (actual (pp
                k)))) (Cc k) Nc hh n') Nc D
            (ocDStar q Λ m ν B / ρ)
            (chartField (coarseCoeff n W) (coarseMode n) (ocChart α q Λ m (Φ (m - 1)) hφ
                (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2)
              ρ) τ)
          (fun j => V j τ) := by
    intro k hk hh hhh
    have hχ : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m (Φ (m - 1)) hφ
        (ocPulseChartIndex α q Λ m k) τ) := fun τ => contDiff_ocChart hφ α q Λ m _ τ
    have hA : ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
        ContDiff ℝ (⊤ : ℕ∞) (chartField (coarseCoeff n W) (coarseMode n)
          (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2)
          ρ τ) :=
      fun τ _ => ContDiff.sum fun r _ => ((coarseMode_contDiff n r).comp
        ((hχ _).comp (contDiff_const_smul _))).const_smul _
    exact exists_tail_cleanupChain sXc sZc Acl hXc hZc (sX := Klift + D + 2)
      (sZ := max (Llift + 1) (Llift + 2)) hX (by omega)
      (fun n' hn1 hn2 => setting_tail_presentation (w.hsetting k hk) (Klift + D + 2)
        (max (Llift + 1) (Llift + 2)) (by omega) (by omega) (Cc k) (w.hseq k hk) hh hhh n'
        (by omega) hn2) _ _ hA
  choose! Vc hVc using hex
  exact ⟨Vc, hVc⟩

/-- **Cleanup chains of the positive degrees of the lifts of the divergence of the flux
approximant.** -/
theorem ReconWindowAt.exists_lift_chains
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀) (n :
          ℕ)
    (sXc sZc Acl : ℕ) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc + Acl ≤ Klift + Nc + 2 * D + 2) (hZ : sZc + 1 ≤ Llift + 2 + 2 * D) :
    ∃ Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
      ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n', n' < Nc →
        ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
        IsCleanupChain sXc sZc Acl
          (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s X => fluxApproxDiv n Fc
            (ocEll q Λ m ν ^ 2 * s) ((ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (ocEll q Λ m ν ^ 2 * s) (ρ • X))) τ)
          (fun _ _ _ => 0) (fun j => Vn k hh n' j τ) := by
  have hex : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∃ V : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 →
      ∀ i, h i,
      ∀ hh, hh ≤ H → ∀ n', n' < Nc → ∀ τ ∈ Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
          ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
        IsCleanupChain sXc sZc Acl
          (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s X => fluxApproxDiv n Fc
            (ocEll q Λ m ν ^ 2 * s) ((ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (ocEll q Λ m ν ^ 2 * s) (ρ • X))) τ)
          (fun _ _ _ => 0) (fun j => V hh n' j τ) := by
    intro k hk
    have hχ : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m (Φ (m - 1)) hφ
        (ocPulseChartIndex α q Λ m k) τ) := fun τ => contDiff_ocChart hφ α q Λ m _ τ
    exact setting_exists_lift_cleanupChain (w.hsetting k hk) (Klift + D + 2)
      (max (Llift + 1) (Llift + 2)) (by omega) (Cc k) (w.hseq k hk) sXc sZc Acl hXc hZc hX
      (by omega) _ fun τ _ => (fluxApproxDiv_contDiff n Fc _).comp
        ((hχ _).comp (contDiff_const_smul _))
  choose! Vn hVn using hex
  exact ⟨Vn, hVn⟩

end AVRegularity.CycleComparison.Reconstruction
end
