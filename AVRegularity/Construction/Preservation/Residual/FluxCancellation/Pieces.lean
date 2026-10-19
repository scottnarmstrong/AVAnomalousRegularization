-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.Core
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Construction.Preservation.Residual.Assembly.RetainedReadoutOfIngredients
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

section
section
/-! Spatial continuity of the readout fluxes `R`, `RO`, `RD`, `Pl` on a frame (first part of
`RetainedReadoutFluxContinuityStatement`). Frame-level lemmas: each takes the continuity of the
physical coefficients of the relevant stage and the classical-representative data of the frame.

* `R`: `kernel_readout_flux_continuous` for the retained family;
* `RO`, `RD`, `Pl`: the same argument for the rows of the extended successor `G'`
  (`fluxCont_RO`, `fluxCont_rootFluxOn`, `fluxCont_RD`, `fluxCont_Pl`), through the continuity of
  `readoutFlux`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- Casting a continuous `PiLp`-valued map along an equality of root indices. -/
theorem fluxCont_cast {X : Type*} [TopologicalSpace X] {r r' : ℕ} (e : r = r')
    (f : X → PiLp 2 (fun _ : Fin 2 => hr r)) (hf : Continuous f) :
    Continuous (fun x => cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (f x)) := by
  subst e
  simpa using hf

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The readout of fluxes continuous in space is continuous in space. -/
theorem fluxCont_readoutFlux {S S' : Finset Comp} (m : ℕ) (E η : ℝ) (sel : Comp → Prop)
    (Q : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (v : CompIn S) (t : ℝ) (hQ : ∀ v', Continuous (Q v' t)) :
    Continuous (readoutFlux m E η sel Q v t) := by
  classical
  unfold readoutFlux
  refine continuous_finsetSum _ fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1 ∧ sel v'.1
  · simp only [h, and_self, ↓reduceDIte]
    exact (fluxCont_cast (hr := hr) (X := Vec 2)
      ((compParent_root m v'.1).symm.trans (congrArg Comp.root h.1)) _ (hQ v')).const_smul
      (E ^ (η * ((compWord m v'.1).length : ℝ)))
  · simp only [h, ↓reduceDIte]
    exact continuous_const

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- One term of a coefficient flux is continuous. -/
theorem fluxCont_term {G : GenStage D hr Dm b j₀} {v u : CompIn G.comps} (γ : G.fam.Γ v u)
    {k : ℕ} (d : Finset.Icc 2 Dm) (hDm : Dm ≤ k) (t : ℝ)
    (hA : Continuous (G.physCoeff v u γ d.1 t)) (f : Vec 2 → hr u.1.root)
    (hf : ContDiff ℝ (k : ℕ) f) :
    Continuous (fun x => G.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word f x)) := by
  have hd : d.1 - 1 ≤ k := (Nat.sub_le _ _).trans ((Finset.mem_Icc.mp d.2).2.trans hDm)
  apply hA.clm_apply
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun word =>
    ChartTransport.continuous_orderedDerivative word (hf.of_le (by exact_mod_cast hd)))

section Frame
variable (F : Frame D hr Dm b j₀)

/-- The retained kernel fluxes `R` is continuous in space at every time of the window. -/
theorem fluxCont_R (hφ₀ : Integrable F.φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφc : HasCompactSupport F.φ₀) (hDm : Dm ≤ F.Naux)
    (hA : ∀ v u (γ : F.Gr.fam.Γ v u) d, ∀ t ∈ Set.Icc F.tp F.tf,
      Continuous (F.Gr.physCoeff v u γ d t)) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, Continuous (fluxR F v t) := by
  intro v t ht
  unfold fluxR
  refine fluxCont_readoutFlux (hr := hr) _ _ _ _ _ v t fun v' => ?_
  exact kernel_readout_flux_continuous F.Gr F.P F.seedK F.freshK hφ₀ hφs hφc F.aY F.Y hDm t
    (fun w => F.retained w t ht) (fun v u γ d => hA v u γ d t ht) v'

/-- The omitted rows: `RO` is continuous in space at every time of the window. -/
theorem fluxCont_RO (hφ₀ : Integrable F.φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφc : HasCompactSupport F.φ₀) (hDm : Dm ≤ F.Naux)
    (hA : ∀ v u (γ : F.G'.fam.Γ v u) d, ∀ t ∈ Set.Icc F.tp F.tf,
      Continuous (F.G'.physCoeff v u γ d t)) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, Continuous (fluxRO F v t) := by
  classical
  intro v t ht
  unfold fluxRO
  refine fluxCont_readoutFlux (hr := hr) _ _ _ _ _ v t fun v' => ?_
  unfold omittedFluxClassical
  refine continuous_finsetSum _ fun u _ => ?_
  by_cases hu : u.1 ∈ F.Gr.comps
  · simp only [hu, ↓reduceDIte]
    refine continuous_finsetSum _ fun γ _ => continuous_finsetSum _ fun d _ => ?_
    have hrep := kernel_readout_kernel_classical_rep hφ₀ hφs hφc
      (F.G'.kernelOf F.P F.seedK F.freshK v' u γ) t (F.Y ⟨u.1, hu⟩ t)
      (fun x => F.aY t x ⟨u.1, hu⟩) (F.retained ⟨u.1, hu⟩ t ht)
    exact fluxCont_term γ d hDm t (hA v' u γ d.1 t ht) _ hrep.2.1
  · simp only [hu, ↓reduceDIte]
    exact continuous_const

/-- The fluxes out of the roots, in any mode, are continuous in space on the extended
successor. -/
theorem fluxCont_rootFluxOn (hφ₀ : Integrable F.φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφc : HasCompactSupport F.φ₀) (hDm : Dm ≤ F.Naux)
    (hA : ∀ v u (γ : F.G'.fam.Γ v u) d, ∀ t ∈ Set.Icc F.tp F.tf,
      Continuous (F.G'.physCoeff v u γ d t))
    (mode : KerMode) (v' : CompIn F.G'.comps) (t : ℝ) (ht : t ∈ Set.Icc F.tp F.tf) :
    Continuous (rootFluxOn F.P F.seedK F.freshK F.φ₀ F.G F.G' mode F.aZ v' t) := by
  classical
  unfold rootFluxOn
  refine continuous_finsetSum _ fun u' _ => ?_
  by_cases hu : u'.1 ∈ F.G.comps
  · simp only [hu, ↓reduceDIte]
    refine continuous_finsetSum _ fun γ _ => continuous_finsetSum _ fun d _ => ?_
    have hZ : ContDiff ℝ (F.Naux : ℕ) (fun x => F.aZ t x ⟨u'.1, hu⟩) :=
      (F.readout ⟨u'.1, hu⟩ t ht).2.1
    have hrep := kernel_readout_kernel_classical_rep hφ₀ hφs hφc
      (F.G'.kernelOf F.P F.seedK F.freshK v' u' γ) t
      (succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun w => F.Y w t) ⟨u'.1, hu⟩)
      (fun x => F.aZ t x ⟨u'.1, hu⟩) (F.readout ⟨u'.1, hu⟩ t ht)
    have hK := hrep.2.1
    have hA' := hA v' u' γ d.1 t ht
    cases mode
    · exact fluxCont_term γ d hDm t hA' _ hZ
    · exact fluxCont_term γ d hDm t hA' _ hK
    · exact fluxCont_term γ d hDm t hA' _ (hZ.sub hK)
  · simp only [hu, ↓reduceDIte]
    exact continuous_const

/-- `RD` and `Pl` (and `K`) are continuous in space at every time of the window. -/
theorem fluxCont_rootReadout (hφ₀ : Integrable F.φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφc : HasCompactSupport F.φ₀) (hDm : Dm ≤ F.Naux)
    (hA : ∀ v u (γ : F.G'.fam.Γ v u) d, ∀ t ∈ Set.Icc F.tp F.tf,
      Continuous (F.G'.physCoeff v u γ d t))
    (mode : KerMode) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, Continuous (rootReadout F.P F.seedK F.freshK F.φ₀ F.G F.G' mode
      F.m (D.eps (F.m - 1)) F.η₀ F.aZ v t) := by
  intro v t ht
  exact fluxCont_readoutFlux (hr := hr) _ _ _ _ _ v t fun v' =>
    fluxCont_rootFluxOn F hφ₀ hφs hφc hDm hA mode v' t ht

/-- `RD` is continuous in space at every time of the window. -/
theorem fluxCont_RD (hφ₀ : Integrable F.φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφc : HasCompactSupport F.φ₀) (hDm : Dm ≤ F.Naux)
    (hA : ∀ v u (γ : F.G'.fam.Γ v u) d, ∀ t ∈ Set.Icc F.tp F.tf,
      Continuous (F.G'.physCoeff v u γ d t)) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, Continuous (fluxRD F v t) :=
  fluxCont_rootReadout F hφ₀ hφs hφc hDm hA .defect

/-- `Pl` is continuous in space at every time of the window. -/
theorem fluxCont_Pl (hφ₀ : Integrable F.φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφc : HasCompactSupport F.φ₀) (hDm : Dm ≤ F.Naux)
    (hA : ∀ v u (γ : F.G'.fam.Γ v u) d, ∀ t ∈ Set.Icc F.tp F.tf,
      Continuous (F.G'.physCoeff v u γ d t)) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, Continuous (fluxPl F v t) :=
  fluxCont_rootReadout F hφ₀ hφs hφc hDm hA .plain

end Frame

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Proof of `RetainedReadoutKernelSplitStatement`: the kernel flux of the successor out of
the roots is the plain flux minus the root defect, pointwise.

Termwise, `orderedDerivative` of `g - K g` is the difference of the ordered derivatives of the
two `C^{Naux}` fields, the coefficient is linear, and the readout is linear in the flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- One term of the three modes: the kernel term is the plain term minus the defect term. -/
theorem kernelSplit_term {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] {n : ℕ}
    (c : (PiLp 2 (fun _ : DerivativeWord2 n => E)) →L[ℝ] E') (f Kf : Vec 2 → E)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hK : ContDiff ℝ (n : ℕ∞) Kf) (x : Vec 2) :
    c (WithLp.toLp 2 fun word : DerivativeWord2 n => orderedDerivative word Kf x) =
      c (WithLp.toLp 2 fun word : DerivativeWord2 n => orderedDerivative word f x) -
      c (WithLp.toLp 2 fun word : DerivativeWord2 n =>
        orderedDerivative word (fun y => f y - Kf y) x) := by
  rw [← map_sub]
  congr 1
  ext word
  simp [orderedDerivative_sub word hf hK]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- The kernel flux of the successor out of the roots is the plain flux minus the defect flux,
at one time, when the field and its kernel averages are `C^{Naux}` and `Dm ≤ Naux`. -/
theorem rootFluxOn_kernel_eq_sub (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (G G' : GenStage D hr Dm b j₀)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) {Naux : ℕ} (hDm : Dm ≤ Naux)
    (hg : ∀ w, ContDiff ℝ (Naux : ℕ∞) (fun y => g t y w))
    (hK : ∀ (v' u' : CompIn G'.comps) (hu : u'.1 ∈ G.comps) (γ : G'.fam.Γ v' u'),
      ContDiff ℝ (Naux : ℕ∞) ((G'.kernelOf P seedK freshK v' u' γ).applyClassical φ₀ t
        (fun y' => g t y' ⟨u'.1, hu⟩)))
    (v' : CompIn G'.comps) (x : Vec 2) :
    rootFluxOn P seedK freshK φ₀ G G' .kernel g v' t x =
      rootFluxOn P seedK freshK φ₀ G G' .plain g v' t x -
        rootFluxOn P seedK freshK φ₀ G G' .defect g v' t x := by
  unfold rootFluxOn
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u' _ => ?_
  by_cases hu : u'.1 ∈ G.comps
  · simp only [hu, ↓reduceDIte]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hd := Finset.mem_Icc.1 d.2
    have hle : (((d.1 - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((Naux : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : d.1 - 1 ≤ Naux)
    exact kernelSplit_term _ _ _ ((hg _).of_le hle) ((hK v' u' hu γ).of_le hle) x
  · simp [hu]

omit [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- Casts along an equality of roots are additive. -/
theorem kernelSplit_cast_sub {r r' : ℕ} (e : r = r') (x y : PiLp 2 (fun _ : Fin 2 => hr r)) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (x - y) =
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) x -
        cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) y := by
  subst e
  rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The readout is additive in the flux (pointwise in `v, t, x`). -/
theorem kernelSplit_readoutFlux_sub {S S' : Finset Comp} (m : ℕ) (E η : ℝ) (sel : Comp → Prop)
    (F₁ F₂ F₃ : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (v : CompIn S) (t : ℝ) (x : Vec 2) (h : ∀ v', F₁ v' t x = F₂ v' t x - F₃ v' t x) :
    readoutFlux m E η sel F₁ v t x =
      readoutFlux m E η sel F₂ v t x - readoutFlux m E η sel F₃ v t x := by
  unfold readoutFlux
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases hc : compParent m v'.1 = v.1 ∧ sel v'.1
  · simp only [hc, and_self, ↓reduceDIte]
    rw [h v', kernelSplit_cast_sub ((compParent_root m v'.1).symm.trans (congrArg Comp.root hc.1)),
      smul_sub]
  · simp [hc]

/-- On a frame whose kernel has a smooth, integrable, compactly supported profile and whose
auxiliary regularity reaches the maximal order `Dm`, `K = Pl - RD` pointwise on the window. -/
theorem kernelSplitOn_of_profile (F : Frame D hr Dm b j₀) (hφi : Integrable F.φ₀)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀) (hφc : HasCompactSupport F.φ₀) (hDm : Dm ≤ F.Naux) :
    KernelSplitOn F := by
  intro v t ht x
  refine kernelSplit_readoutFlux_sub F.m (D.eps (F.m - 1)) F.η₀ (fun _ => True) _ _ _ v t x ?_
  intro v'
  refine rootFluxOn_kernel_eq_sub F.P F.seedK F.freshK F.φ₀ F.G F.G' F.aZ t hDm
    (fun w => (F.readout w t ht).2.1) ?_ v' x
  intro v'' u' hu γ
  exact (kernel_readout_kernel_classical_rep hφi hφs hφc _ t _ _ (F.readout ⟨u'.1, hu⟩ t ht)).2.1

end AVRegularity.Construction.Preservation.Residual.FluxCancellation

namespace AVRegularity.Construction.Preservation.Residual
open FluxCancellation CovarianceTransport

/-- (c) The kernel split `K = Pl - RD`, pointwise, under the quantifier prefix. -/
theorem retainedReadoutKernelSplit (α s q : ℝ) (ζ : ℝ → ℝ) :
    RetainedReadoutKernelSplitStatement α s q ζ := by
  refine ⟨128, le_rfl, fun Λ _ => ⟨1, one_pos, ?_⟩⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨kS, 1, 1, le_rfl, one_pos, fun kI _ => ⟨0, 0, fun CI Cw j₀ _ _ CQ Cpr => ⟨0, ?_⟩⟩⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  have haux := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hDm : succSchedD D₀ N p (H + 1) ≤ Naux := by omega
  exact kernelSplitOn_of_profile _ hφ₀ hφsmooth
    (Providers.hasCompactSupport_of_unitBall hφsupport) hDm

end AVRegularity.Construction.Preservation.Residual
end
end
end

section
section
/-! Finite bookkeeping for the provenance reindexing of the retained readout flux:
sums over a subfamily of components, the split of a readout into retained and omitted rows,
the identification of the kernel flux of the retained family with the omitted-flux expression of
the extended family, and `constituentPhysical` as a function of the data of one identity, with
its transport along equalities of root indices. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]

theorem reindex_sum_filter {S : Finset Comp} (ret : Comp → Prop) [DecidablePred ret]
    {M : Type*} [AddCommMonoid M] (T : CompIn S → M) :
    ∑ v' : CompIn S, (if ret v'.1 then T v' else 0) =
      ∑ v'' : CompIn (S.filter ret), T ⟨v''.1, (Finset.mem_filter.1 v''.2).1⟩ := by
  classical
  let g : Comp → M := fun c => if hc : c ∈ S then T ⟨c, hc⟩ else 0
  have hg : ∀ v' : CompIn S, g v'.1 = T v' := fun v' => by simp [g, v'.2]
  have h1 : ∑ v' : CompIn S, (if ret v'.1 then T v' else 0) =
      ∑ c ∈ S, if ret c then g c else 0 := by
    rw [← Finset.sum_coe_sort S (fun c => if ret c then g c else 0)]
    refine Finset.sum_congr rfl fun v' _ => ?_
    simp only [hg]
  have h2 : ∑ v'' : CompIn (S.filter ret), T ⟨v''.1, (Finset.mem_filter.1 v''.2).1⟩ =
      ∑ c ∈ S.filter ret, g c := by
    rw [← Finset.sum_coe_sort (S.filter ret) g]
    refine Finset.sum_congr rfl fun v'' _ => ?_
    exact (hg ⟨v''.1, (Finset.mem_filter.1 v''.2).1⟩).symm
  rw [h1, h2, Finset.sum_filter]


open scoped Classical in
/-- The readout of the retained rows plus the readout of the non-retained rows is the readout of all
rows. -/
theorem reindex_readout_split {S S' : Finset Comp} (m : ℕ) (E η : ℝ) (ret : Comp → Prop)
    [DecidablePred ret]
    (F : ∀ v' : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (F1 : ∀ v' : CompIn (S'.filter ret), ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v'.1.root))
    (hF : ∀ v' t x, F1 v' t x = F ⟨v'.1, (Finset.mem_filter.1 v'.2).1⟩ t x)
    (v : CompIn S) (t : ℝ) (x : Vec 2) :
    readoutFlux m E η (fun _ => True) F1 v t x + readoutFlux m E η (fun c => ¬ ret c) F v t x =
      readoutFlux m E η (fun _ => True) F v t x := by
  let T : CompIn S' → PiLp 2 (fun _ : Fin 2 => hr v.1.root) := fun v' =>
    if h : compParent m v'.1 = v.1 then
      (E ^ (η * ((compWord m v'.1).length : ℝ))) •
        cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
          ((compParent_root m v'.1).symm.trans (congrArg Comp.root h))) (F v' t x)
    else 0
  have e1 : readoutFlux m E η (fun _ => True) F v t x = ∑ v' : CompIn S', T v' := by
    unfold readoutFlux
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h : compParent m v'.1 = v.1 <;> simp [T, h]
  have e2 : readoutFlux m E η (fun _ => True) F1 v t x =
      ∑ v' : CompIn S', if ret v'.1 then T v' else 0 := by
    rw [reindex_sum_filter ret T]
    unfold readoutFlux
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h : compParent m v'.1 = v.1
    · simp [T, h, hF]
    · simp [T, h]
  have e3 : readoutFlux m E η (fun c => ¬ ret c) F v t x =
      ∑ v' : CompIn S', if ret v'.1 then 0 else T v' := by
    unfold readoutFlux
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h : compParent m v'.1 = v.1 <;> by_cases hr' : ret v'.1 <;> simp [T, h, hr']
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases hr' : ret v'.1 <;> simp [hr']


theorem reindex_sum_dite {S S₂ : Finset Comp} (h : S₂ ⊆ S) {M : Type*} [AddCommMonoid M]
    (T : CompIn S₂ → M) :
    ∑ u : CompIn S, (if hu : u.1 ∈ S₂ then T ⟨u.1, hu⟩ else 0) = ∑ u : CompIn S₂, T u := by
  classical
  let g : Comp → M := fun c => if hc : c ∈ S₂ then T ⟨c, hc⟩ else 0
  have h1 : ∑ u : CompIn S, (if hu : u.1 ∈ S₂ then T ⟨u.1, hu⟩ else 0) = ∑ c ∈ S, g c := by
    rw [← Finset.sum_coe_sort S g]
  have h2 : ∑ u : CompIn S₂, T u = ∑ c ∈ S₂, g c := by
    rw [← Finset.sum_coe_sort S₂ g]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [g, u.2]
  rw [h1, h2]
  exact (Finset.sum_subset h (fun c _ hc => by simp [g, hc])).symm

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The kernel flux of the retained family into a retained row is the omitted-flux expression of
the extended family with all columns. -/
theorem reindex_coeffFlux_eq_omitted (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (G' : GenStage D hr Dm b j₀) (m H J : ℕ)
    (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, hr v.1.root)
    (v' : CompIn (G'.retained m H J).comps) (t : ℝ) (x : Vec 2) :
    coeffFluxOn P seedK freshK φ₀ (G'.retained m H J) .kernel aY v' t x =
      omittedFluxClassical P seedK freshK φ₀ G' (G'.retained m H J) aY
        ⟨v'.1, (Finset.mem_filter.1 v'.2).1⟩ t x := by
  classical
  unfold coeffFluxOn omittedFluxClassical
  rw [reindex_sum_dite (S := G'.comps) (S₂ := (G'.retained m H J).comps) (Finset.filter_subset _ _)
    (fun u => ∑ γ : G'.fam.Γ ⟨v'.1, (Finset.mem_filter.1 v'.2).1⟩ ⟨u.1, (Finset.filter_subset _ _ u.2)⟩, ∑ d : Finset.Icc 2 Dm,
      G'.physCoeff ⟨v'.1, (Finset.mem_filter.1 v'.2).1⟩ ⟨u.1, (Finset.filter_subset _ _ u.2)⟩ γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word ((G'.kernelOf P seedK freshK ⟨v'.1, (Finset.mem_filter.1 v'.2).1⟩ ⟨u.1, (Finset.filter_subset _ _ u.2)⟩ γ).applyClassical φ₀ t
          (fun y => aY t y u)) x))]
  rfl


/-- `constituentPhysical` with the fibre spaces and the data of the identity as parameters. -/
def reindexPhi {Hu Hv : Type*} [NormedAddCommGroup Hu] [NormedSpace ℝ Hu]
    [NormedAddCommGroup Hv] [NormedSpace ℝ Hv] {P : Type*} (weight : P → ℝ → ℝ)
    (piece : P → ChartPiece) (e : ℝ) (maxO : ℕ)
    (fl : P → ∀ d' : ℕ, DerivativeWord2 (d' - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (C : Hu →L[ℝ] Hv) (d : ℕ) (t : ℝ) (x : Vec 2) :
    (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => Hu)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => Hv)) :=
  ∑ᶠ p : P, weight p t •
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => Hv)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k : Fin 2 =>
        ∑ A : DerivativeWord2 (d - 1),
          (transportedCoeff (chartInvJacobian ⇑((piece p).material t).symm)
              maxO
              (fun d' I => fl p d' I t
                (((piece p).material t).symm x) (e⁻¹ • ((piece p).material t).symm x))
              (d - 1) A x k) •
            C.comp (PiLp.proj 2 (fun _ : DerivativeWord2 (d - 1) => Hu) A)))

theorem reindex_physCoeff_eq (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) (d : ℕ) (t : ℝ) (x : Vec 2) :
    G.physCoeff v u γ d t x = reindexPhi G.fam.weight G.fam.piece (D.eps G.level)
      (G.fam.identity v u γ).maxOrder
      (fun p d' I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) p
        (G.actual p) v u γ d' I) (G.fam.identity v u γ).map d t x := rfl


theorem reindexPhi_cast {ru ru' rv rv' : ℕ} (hu : ru = ru') (hv : rv = rv') {P : Type*}
    (weight : P → ℝ → ℝ) (piece : P → ChartPiece) (e : ℝ) {maxO maxO' : ℕ}
    {fl fl' : P → ∀ d' : ℕ, DerivativeWord2 (d' - 1) → ℝ → Vec 2 → Vec 2 → Vec 2}
    (hmax : maxO = maxO') (hfl : fl = fl')
    (C : hr ru →L[ℝ] hr rv) (C' : hr ru' →L[ℝ] hr rv')
    (hC : ∀ z, cast (congrArg hr hv) (C z) = C' (cast (congrArg hr hu) z))
    (d : ℕ) (t : ℝ) (x : Vec 2)
    (w : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr ru))
    (w' : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr ru'))
    (hw : ∀ word, w' word = cast (congrArg hr hu) (w word)) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hv)
        (reindexPhi weight piece e maxO fl C d t x w) =
      reindexPhi weight piece e maxO' fl' C' d t x w' := by
  subst hu hv hmax hfl
  have hC' : C = C' := ContinuousLinearMap.ext fun z => by simpa using hC z
  subst hC'
  have hw' : w' = w := by
    ext word
    simpa using hw word
  subst hw'
  rfl

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Assembly of the `RetainedReadoutFluxCancellationStatement` from

* `RetainedReadoutReindexStatement` (`R = K - RO`),
* `RetainedReadoutKernelSplitStatement` (`K = Pl - RD`),
* `SuccessorSplitCoreStatement` (the split on an arbitrary classical field, generic over the stage
  and the menu) together with `CascadeSplitInputStatement` (the cascade supplies its hypotheses),
* `RetainedReadoutFluxContinuityStatement`.

The quantifier prefix is the `CovarianceTransportProductionStatement`: the uniform choices of
the four prefixed statements are joined by `frame_production_join` (the threshold join of
`retained_readout_weak_equation_of_ingredients`, on frame predicates), and the quantifier prefix is
unfolded once, in the last theorem. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Preservation.Residual
open FluxCancellation CovarianceTransport

/-- Data for the conjunction of two frame predicates, at the larger threshold. -/
theorem FluxCancellation.frame_data_join {Q₁ Q₂ : FramePredicate} {α s q : ℝ} {ζ : ℝ → ℝ}
    {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {bw Ce τe : ℝ} {kS : InvConsts}
    {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ} {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ}
    {CQ Cpr Q T₀ : ℝ} {ma mb : ℕ}
    (ha : CovarianceTransportDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ ma Q₁)
    (hb : CovarianceTransportDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mb Q₂) :
    CovarianceTransportDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ (max ma mb) (fun F => Q₁ F ∧ Q₂ F) := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  exact ⟨ha D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA s₀ htA hs₀ htf hT₀ G G'
      hcascade hlevel hG hactual tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û
      hlift aZ aY hZ hY,
    hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA s₀ htA hs₀ htf hT₀ G G'
      hcascade hlevel hG hactual tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û
      hlift aZ aY hZ hY⟩

/-- Joining two prefixed frame statements: the uniform choices are the joins of the two. -/
theorem FluxCancellation.frame_production_join {Q₁ Q₂ : FramePredicate} {α s q : ℝ}
    {ζ : ℝ → ℝ} (hread : CovarianceTransportProductionStatement α s q ζ Q₁)
    (hcov : CovarianceTransportProductionStatement α s q ζ Q₂) :
    CovarianceTransportProductionStatement α s q ζ (fun F => Q₁ F ∧ Q₂ F) := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := hread
  obtain ⟨Λb, hΛb, hb⟩ := hcov
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min ca cb, lt_min hca hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  obtain ⟨ta, CHa, Υa, hCHa, hΥa, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  refine ⟨certificateThresholdJoin ta tb, max CHa CHb, max Υa Υb,
    hCHa.trans (le_max_left _ _), hΥa.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIa, Cwa, ha⟩ := ha kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIb, Cwb, hb⟩ := hb kI (invariant_admissible_threshold_right hkI)
  refine ⟨max CIa CIb, max Cwa Cwb, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLa : IsLedgerAdmissible Ce CI Cw CIa Cwa :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  intro CQ Cpr
  obtain ⟨ma, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart) CQ Cpr
  obtain ⟨mb, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart) CQ Cpr
  exact ⟨max ma mb, FluxCancellation.frame_data_join ha hb⟩

/-- **The retained readout flux cancellation from its ingredients**: the literal
statement from the reindexing, the kernel split, the generic core with its cascade input, and
the continuity of the fluxes. -/
theorem retained_readout_flux_cancellation_of_ingredients {α s q : ℝ} {ζ : ℝ → ℝ}
    (hreindex : RetainedReadoutReindexStatement α s q ζ)
    (hsplit : RetainedReadoutKernelSplitStatement α s q ζ)
    (hcore : SuccessorSplitCoreStatement)
    (hinput : CascadeSplitInputStatement α s q ζ)
    (hcont : RetainedReadoutFluxContinuityStatement α s q ζ) :
    RetainedReadoutFluxCancellationStatement α s q ζ := by
  have hall := FluxCancellation.frame_production_join
    (FluxCancellation.frame_production_join hreindex hsplit)
    (FluxCancellation.frame_production_join hcont hinput)
  obtain ⟨Λ₀, hΛ₀, h⟩ := hall
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  obtain ⟨c, hc, h⟩ := h Λ hΛ
  refine ⟨c, hc, ?_⟩
  intro φ₀ hφ₀ h1 h2 h3 h4 bw hbw hbw' Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe a1 a2 a3 a4 a5 a6
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hfX hfZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ h1 h2 h3 h4 bw hbw hbw' Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe a1 a2 a3 a4 a5 a6 H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀
    a σ hsched hNaux hNout halloc hfX hfZ
  refine ⟨thr, CH, Υ, hCH, hΥ, fun kI hkI => ?_⟩
  obtain ⟨CIt, Cwt, h⟩ := h kI hkI
  refine ⟨CIt, Cwt, fun CI Cw j₀ hl hs => ?_⟩
  intro CQ Cpr
  obtain ⟨mStar, h⟩ := h CI Cw j₀ hl hs CQ Cpr
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', Gr := G'.retained m H J,
      Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s),
      P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p,
      seedK := seedK, freshK := freshK, φ₀ := φ₀, m := m, H := H, J := J, N := N,
      p := p, depth := succSchedR r₀ J H, Naux := Naux, sX := sX, sZ := sZ,
      η₀ := succEta0 α q s, tp := tp, tf := tf, Y := Y, CcT := CcT, PZ := PZ,
      aRep := aRep, aZ := aZ, aY := aY, û := û,
      lift := (isMenuLiftedField_cascade (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s))
        rfl rfl G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) tp tf
        Y CcT PZ aRep û).2 hlift,
      readout := hZ, retained := hY }
  have hF : (ReindexOn F ∧ KernelSplitOn F) ∧ (FluxContinuityOn F ∧ SplitInputOn F) :=
    h D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hs₀ htf hT₀ G G'
      hcascade hlevel hG hactual tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û
      hlift aZ aY hZ hY
  have hC : CancellationOn F :=
    cancellationOn_of_steps F hF.1.1 hF.1.2 (reconstructOn_of_core hcore F hF.2.2) hF.2.1
  -- the frame's right-hand flux at the cascade menu (anchor `0`, factor `1`) is the one
  have hread := frame_readFlux_cascade F rfl rfl
  intro v t ht φ hφ hper
  have h' := hC v t ht φ hφ hper
  rw [hread] at h'
  exact h'

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! The eight pieces of the split `(𝖮 + ∑ 𝖥_𝔩) g = -Q_p(𝒟 - 𝐄^flux P_p) g` and the assembly of
`SuccessorSplitCoreStatement` from them. Every piece is generic over the stage and the menu
(no `IsCascadeStage`, no `succMenu`): the stage enters through `StageSuccessor.Input` and
`SplitInput`, the menu through its anchor and slow-length factor.

Route (pointwise in `(t, x)`, for a field of class `C^K`):
`Pl = (Pl - Dg) + Dg`, where `Dg` is the readout of the first-source identities alone
(`diagReadout`); the first-source-flux step gives `Dg = -Q_p 𝒟 g`; the source-mean step gives `Pl - Dg = Q_p 𝐄^flux P_p g` from the
Eulerian form of every transferred identity (the transfer step, from the Piola-transport and finer-output steps) and the path expansion
of the lift of the Hilbert fibre (the path-sum step); the root-bookkeeping step is the bookkeeping of the identities out of
the roots; the flux-regularity step is the regularity that makes `Q_p` additive on the two parts and the pairings
integrable.

A piece whose proof consumes other pieces is stated as the implication from them, so that the
assembly `successor_split_core_of_pieces` uses all eight and no intermediate object is assumed.

The `C^k` caveat: the lemmas of this kind (`transportedCoeff_flux`,
`arrOp_eq_sum_fluxCoeff`, `firstSourceFlux_applyArr`) are stated for `ContDiff ℝ ⊤` fields; the
readout representative is only `C^{Naux}`. The Piola-transport, finer-output and
first-source-flux steps are therefore stated at the finite order they use. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### Vocabulary -/

open scoped Classical in
/-- The witnesses of `IsActualSuccessor` (the body of its existential: the source bijection, the
lifts of the scalar path families, the grade-zero lifts, and the formulas of the coefficients). -/
structure SplitWitness (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) where
  /-- The identities of `G'` are the valid sources. -/
  e : ∀ v' u', G'.fam.Γ v' u' ≃ {s : SuccSource G //
    s.Valid Mn.A Mn.J ∧ s.srcComp G.level = u'.1 ∧ s.tgtComp G.level = v'.1}
  /-- The lifts of the scalar path family of every source. -/
  Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)
  /-- The grade-zero lifts. -/
  Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)
  lifts : ∀ s : SuccSource G, s.IsLiftFamily Mn (Cc s)
  diag : IsDiagLifts D Dm b j₀ Mn G.level Cc0
  spec : ∀ v' u' (γ' : G'.fam.Γ v' u'),
    G'.prov v' u' γ' = (e v' u' γ').1.prov G.level ∧
    (G'.fam.identity v' u' γ').map = rootPathMap hr u'.1.root (e v' u' γ').1.maps v'.1.root ∧
    ((¬ (e v' u' γ').1.IsDiag →
      ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1))
        (t : ℝ) (X z : Vec 2), 2 ≤ d →
        G'.fam.flux p c v' u' γ' d I t X z =
          if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
          then transferAt D G.level p.1 ((e v' u' γ').1.lam G.level Mn.η0)
            (((e v' u' γ').1.prov G.level).tags P).order
            ((e v' u' γ').1.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
              (Cc (e v' u' γ').1)) t
            (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
          else 0) ∧
     ((e v' u' γ').1.IsDiag →
      ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1))
        (t : ℝ) (X z : Vec 2), 2 ≤ d →
        G'.fam.flux p c v' u' γ' d I t X z =
          if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
          then ((e v' u' γ').1.lam G.level Mn.η0 *
              (D.κ G'.level * D.eps G'.level ^ (d - 2))⁻¹) •
            fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
              Mn.N Mn.p Mn.anchor Cc0 t
              (c.1.recenter D (D.eps (G'.level - 1) • X)) z) d I 0
          else 0))

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- An actual successor has witnesses. -/
theorem splitWitness_nonempty {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (h : IsActualSuccessor D P Mn G G') : Nonempty (SplitWitness P Mn G G') := by
  obtain ⟨-, -, -, -, -, -, e, Cc, Cc0, hLF, hDL, hall⟩ := h
  exact ⟨⟨e, Cc, Cc0, hLF, hDL, hall⟩⟩

/-- The differential operator whose coefficients of the orders `2 ≤ d ≤ K` are those of the scalar
flux operator `L` at the point (`fluxCoeff`, symmetric in the word), applied to a vector field
through the constant map `C`. For a scalar differential flux operator of order below `K` without
zeroth-order term and `C = id` this is `L` itself. -/
def fluxOpApply {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (K : ℕ) (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (C : E →L[ℝ] E')
    (f : Vec 2 → E) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => E') :=
  WithLp.toLp 2 fun k => ∑ d ∈ Finset.Icc 2 K, ∑ I : DerivativeWord2 (d - 1),
    fluxCoeff L d I x k • C (orderedDerivative I f x)

/-- The Eulerian glue of label flux operators `fop k` of the pulses of level `m` active at `t`:
`∑_k ϖ_{m,k}(t) (Ψ_{k,t})_* fop k`, with the natural chart `Ψ_{k,t} = X_{m-1}(t, ·, s_k)` of the
pulse and its inverse (the convention of `pulseMeanFluxEuler`). -/
def gluedFluxOp (D : OCData) (m : ℕ) (fop : ℤ → (Vec 2 → ℝ) → Vec 2 → Vec 2) (t : ℝ) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  fun f x => ∑ k ∈ ocObsPulses D.α D.q D.Λ m t t,
    ocCutoff D.α D.q D.Λ m k t •
      pushFlux (fun y => D.flowOf (m - 1) t y (D.slotAnchor m k))
        (fun x' => D.flowOf (m - 1) (D.slotAnchor m k) x' t) (fop k) f x

/-- The Eulerian flux operator of a source: the glue of its finer outputs on the native family of
every active pulse, at the slow length `ρ` and the covariance anchor `s₀`. -/
def sourceEulerOp {G : GenStage D hr Dm b j₀} (ρ s₀ : ℝ) (s : SuccSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) (t : ℝ) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  gluedFluxOp D G.level (fun k => s.fluxOp ρ s₀ Cc k t (nativeChain G.level k)) t

open scoped Classical in
/-- The plain flux out of the roots of the first-source identities alone (those of provenance
`.letter m .diag []`). -/
def rootDiagFlux (G G' : GenStage D hr Dm b j₀)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v' : CompIn G'.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v'.1.root) :=
  ∑ u' : CompIn G'.comps, if hu : u'.1 ∈ G.comps then
    ∑ γ : G'.fam.Γ v' u',
      if G'.prov v' u' γ = Prov.letter G.level WordLetter.diag [] then
        ∑ d : Finset.Icc 2 Dm,
          G'.physCoeff v' u' γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => g t y ⟨u'.1, hu⟩) x)
      else 0
    else 0

/-- `Dg`: the readout of the first-source part of the plain flux out of the roots. -/
def diagReadout (G G' : GenStage D hr Dm b j₀) (m : ℕ) (E η : ℝ)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    ∀ v : CompIn G.comps, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  readoutFlux m E η (fun _ => True) (fun v' s y => rootDiagFlux G G' g v' s y)

/-- `Q_p 𝒟 g` as a `PiLp` field. -/
def covTemporalAt (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  toFluxL (covPolyQ (menuCovPrimitive D Mn m t) p
    (fun y => menuTemporalFlux Mn G m N p CcT a t v y) x)

/-- `Q_p 𝐄^flux P_p g` as a `PiLp` field. -/
def covMeanAt (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  toFluxL (covPolyQ (menuCovPrimitive D Mn m t) p
    (fun y => menuMeanFluxE Mn G m N depth CcT (menuCovPRep Mn D m p a) t y v) x)

/-- The reserves of the lifts used by the finite-order clause of the finer-output step: `Dm + 2`, and
`2a + Dm + 2` for a covariance letter `𝖵_{n,h,a,a'}` (the outer `𝒞^a` differentiates the
coefficients of the path mean `2a` times). -/
def CenteredReserve (Mn : SuccMenu) {G : GenStage D hr Dm b j₀} (s : SuccSource G) : Prop :=
  Dm + 2 ≤ Mn.sX ∧ Dm + 2 ≤ Mn.sZ ∧
    match s with
    | .letterCov _ _ _ a _ _ => 2 * a + Dm + 2 ≤ Mn.sX ∧ 2 * a + Dm + 2 ≤ Mn.sZ
    | _ => True

/-- What the transfer to the coarser chart (the transfer step) uses of the incoming stage beyond
`StageSuccessor.Input`: the stream sequence is the constructed one
(`sourceEulerOp` uses the flow of level `m - 1`, `transferAt` the flow of level `m - 2` and the
pulses of level `m - 1`); the carried history invariant (the appended child and the recentred
finer native family are different chains with the same history geometry); the carrier start
(admissible appended children, a single coarser pulse on the availability interval of an active
finer slot); the reserves of the lifts of the finer-output step. `SplitInput` supplies it
(`SplitInput.transferInput`). -/
structure TransferInput (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) : Prop where
  stream : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ
  history : ∃ Mtop : ℕ, StageHistoryInvariant G Mtop
  start : IsCarrierStart D.α D.q D.Λ b 1 1 j₀
  reserve : ∀ s : SuccSource G, s.Valid Mn.A Mn.J → CenteredReserve Mn s

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The reserves of the finer-output step from the floors of the lifts, for a valid source of a successor
alphabet `succAlphabet nMax hMax p npad` (the covariance letters have `a ≤ p`). -/
theorem centeredReserve_of_alphabet {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    {nMax hMax npad : ℕ} (hA : Mn.A = succAlphabet nMax hMax Mn.p npad)
    (hsX : 2 * Mn.p + Dm + 2 ≤ Mn.sX) (hsZ : 2 * Mn.p + Dm + 2 ≤ Mn.sZ) (s : SuccSource G)
    (hv : s.Valid Mn.A Mn.J) : CenteredReserve Mn s := by
  refine ⟨by omega, by omega, ?_⟩
  cases s with
  | letterCov t n h a a' π =>
    have hmem := (hv.2.1 _ rfl).2
    rw [hA] at hmem
    simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range,
      reduceCtorEq, false_or, or_false, and_false, exists_false, WordLetter.covariance.injEq,
      Prod.exists] at hmem
    obtain ⟨n', h', a₁, a₂, ⟨⟨⟨⟨hn2, hnM⟩, -⟩, ha₁, -⟩, -⟩, hnn, -, haa, -⟩ := hmem
    subst haa
    exact ⟨by omega, by omega⟩
  | copyDir t v u γ => trivial
  | copyQuad t h π => trivial
  | letterDiag t u => trivial
  | letterMean t n h π => trivial

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The split input supplies the facts used by the transfer to the coarser chart. -/
theorem SplitInput.transferInput {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    {depth : ℕ} {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hin : SplitInput P Mn G G' depth CcT) : TransferInput Mn G := by
  obtain ⟨Dord, nMax, hMax, npad, hA, -, -, -, -, hsX, hsZ⟩ := hin.range
  have h2 := le_max_right (Mn.N + Dord) (2 * Mn.p)
  exact ⟨hin.stream, hin.history, hin.start,
    centeredReserve_of_alphabet hA (by omega) (by omega)⟩

/-! ### The pieces -/

/-- **The root-bookkeeping step (bookkeeping of the identities out of the roots).** For a certified stage
and an actual successor with witnesses:
(i) an incoming component is a component of `G'`, is its own parent and has the empty word;
(ii) an identity of `G'` out of a root has a source with the empty word and old source the root;
its row is the child `(oldTgt, newWord)` of an incoming component, the readout weight of the row
cancels the normalization of the source (`E^{η₀·0}·1 = 1` on a copy, `E^{η₀}·E^{-η₀} = 1` on a
letter), and the source is the first source exactly when the provenance is `.letter m .diag []`;
(iii) every valid source with the empty word is the source of an identity out of a root.
An incoming component without incoming identity has exactly the first-source identity
into `(v, 𝖣)`. The proof uses `old_births` of
`StageSuccessor.Input`, `InitialValue.compParent_eq_self`,
`Preservation.FullLift.parent_word_succComp`, `Uniqueness.succComp_inj`,
`Providers.CascadeInvariants.stagePath_src_mem`, `stagePath_tgt_mem`, `Real.rpow_add`. The same
facts for all words are what the reindexing step needs. -/
def RootSourceBookkeepingStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → IsActualSuccessor D P Mn G G' →
    ∀ W : SplitWitness P Mn G G',
    (∀ c ∈ G.comps, c ∈ G'.comps ∧ compParent G.level c = c ∧ compWord G.level c = []) ∧
    (∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'), u'.1 ∈ G.comps →
      (W.e v' u' γ').1.word = [] ∧ (W.e v' u' γ').1.oldSrc = u'.1 ∧
      (W.e v' u' γ').1.oldTgt ∈ G.comps ∧
      compParent G.level v'.1 = (W.e v' u' γ').1.oldTgt ∧
      compWord G.level v'.1 = (W.e v' u' γ').1.newWord ∧
      D.eps (G.level - 1) ^ (Mn.η0 * ((compWord G.level v'.1).length : ℝ)) *
        (W.e v' u' γ').1.lam G.level Mn.η0 = 1 ∧
      ((W.e v' u' γ').1.IsDiag ↔
        G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag [])) ∧
    (∀ s : SuccSource G, s.Valid Mn.A Mn.J → s.word = [] →
      ∃ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
        (W.e v' u' γ').1 = s ∧ u'.1 ∈ G.comps)

/-- **The Piola-transport step (the Piola transport of one chart piece, at finite order).**
The statement of `CycleComparison.Reconstruction.transportedCoeff_flux`, indexed by the orders
`d ∈ [1, Dγ]`, for a field of class `C^{Dγ-1}` instead of `ContDiff ℝ ⊤`: the
transported array contracted with the physical jets of `V ∘ ψ` is the label flux read
through `K = chartInvJacobian ψ`. It is what `constituentPhysical` computes for one piece with
`χ` the chart and `ψ` its inverse. Pointwise, for each flux index: the word symmetrization
plays no role. The proof is that of `transportedCoeff_flux`
with `ContDiff.of_le` at the orders actually differentiated (the recursion `transitionT` uses
derivatives of `V` of order below `Dγ` only). For `Dγ = 0, 1` the sums are empty or of
zeroth order, and for `χ = ψ = id` the transport is the identity. -/
def PiecePiolaFiniteOrderStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {χ ψ : Vec 2 → Vec 2},
    ContDiff ℝ (⊤ : ℕ∞) χ → ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y, ψ (χ y) = y) → (∀ x, χ (ψ x) = x) →
    ∀ (Dγ : ℕ) {V : Vec 2 → E}, ContDiff ℝ (Dγ - 1 : ℕ) V →
    ∀ (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (x : Vec 2) (a₀ : Fin 2),
    ∑ d ∈ Finset.Icc 1 Dγ, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ψ) Dγ B (d - 1) A x a₀ •
          orderedDerivative A (V ∘ ψ) x =
      ∑ d ∈ Finset.Icc 1 Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
        (chartInvJacobian ψ x a₀ i₀ * B d I i₀) • orderedDerivative I V (ψ x)

/-- **The finer-output step (the finer output from its centred coefficients).**
Clause (ii) cannot be stated for a field of class `C^{order}` and
without reserves of the lifts: the `ε`-coefficients of `dEpsWord` take more slow derivatives than
the order and `fderiv` of a non-differentiable function is `0`, and without reserves the output
is not linear in the field). For a valid source other than the first source, a pulse `k`, a time
of its window and an admissible family `A` whose recentering at the label `y` is admissible:
(i) recentering covariance, for every field: the output of the recentred family at its centre, on
the shifted field, is the output of `A` at `y` (the lift data at `X` of `A^{[y]}` are those of `A`
at `X + y/ρ`, and the lifts agree there by uniqueness on the ladder; for the direct transport it
is the context formula of `IsContextCertified`);
(ii) finite order, for smooth fields and under the reserves `CenteredReserve`: the output is the
differential operator of its `fluxCoeff` at the point, of the orders `2 ≤ d ≤` the recorded order
of the source, with no zeroth-order term.
Together they give `fluxCoeff (fop (A^{[y]})) d I 0 = fluxCoeff (fop A) d I y` (apply (i) to the
monomials), which is how `transferAt` reads the coefficients. A quadratic conversion
(`n = 2`) is a first-order flux, and a padding letter has no source.
Clause (i), and clause (ii) with the zeroth-order term kept, are proved
(`centeredCoefficient_expansion`); the statement follows from
`CenteredConstantsStatement` (`centeredCoefficientFiniteOrder_of_constants`). -/
def CenteredCoefficientFiniteOrderStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → IsActualSuccessor D P Mn G G' →
    ∀ (W : SplitWitness P Mn G G') (s : SuccSource G), s.Valid Mn.A Mn.J → ¬ s.IsDiag →
    ∀ (k : ℤ), Odd k → ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level k,
    ∀ (A : RealChain), IsAdmissibleChain D b j₀ G.level k A →
    ∀ (y : Vec 2), IsAdmissibleChain D b j₀ G.level k (A.recenter D y) →
      (∀ f : Vec 2 → ℝ,
        s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (W.Cc s) k t (A.recenter D y)
            (fun h => f (y + h)) 0 =
          s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (W.Cc s) k t A f y) ∧
      (CenteredReserve Mn s → ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
        s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (W.Cc s) k t A f y =
          ∑ d ∈ Finset.Icc 2 ((s.prov G.level).tags P).order, ∑ I : DerivativeWord2 (d - 1),
            orderedDerivative I f y •
              fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (W.Cc s) k t A)
                d I y)

/-- The conclusion of the transfer step: **the Eulerian form of a transferred identity**. For an identity
of `G'` other than a first source, at every time and point and for a field of class `C^{Dm-1}`
on its source component, the physical flux of the identity is the normalization `lam` times the
Eulerian operator of its source (`sourceEulerOp`: the glue over the active finer pulses of the
finer outputs on the native families), through the constant map of the identity.
The hypothesis `TransferInput Mn G` is needed: the
statement from `StageSuccessor.Input` and `IsActualSuccessor` alone is false for a general
`OCData`, whose stream sequence is arbitrary. -/
def TransferredIdentityEulerianOnStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → IsActualSuccessor D P Mn G G' → TransferInput Mn G →
    ∀ (W : SplitWitness P Mn G G') (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
    ¬ (W.e v' u' γ').1.IsDiag →
    ∀ (t : ℝ) (f : Vec 2 → hr u'.1.root), ContDiff ℝ (Dm - 1 : ℕ) f → ∀ x : Vec 2,
      ∑ d : Finset.Icc 2 Dm,
          G'.physCoeff v' u' γ' d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word f x) =
        (W.e v' u' γ').1.lam G.level Mn.η0 •
          fluxOpApply Dm
            (sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (W.e v' u' γ').1
              (W.Cc (W.e v' u' γ').1) t)
            (G'.fam.identity v' u' γ').map f x

/-- **The transfer step (transfer to the coarser chart collapses to the finer natural chart).**
From the Piola-transport and finer-output steps: the flux arrays of a transferred identity are `transferAt` of its finer
output (`IsActualSuccessor`); `constituentPhysical` transports
them by the inverse of the natural chart of each coarser piece (the Piola-transport step with the dimensional
samples; the factors `κ_{m-1} ε_{m-1}^{d-2}` of `dimFlux` and `transferAt` cancel, `D.kap = D.κ`
at the levels `m - 1 ≤ m ≤ D.term`); the child appended to the recentred actual coarser context is
the native family of the finer slot recentred at the finer label of the point, so that the
transition `childTransition` followed by the coarser chart is the finer natural chart
(`transitionT` composes exactly for transfers), and
the finer-output step turns the centred coefficients into the finer output at the label; finally the sum over
the coarser pieces collapses by `weight_sum` (`ocCutoff_finsum_one`).
The scheduling condition holds by definition: a finer slot with `ϖ_{m,k}(t) ≠ 0` at
a time `t` of the output window of a coarser piece is `IsScheduledIn` it (the support of the
finer cutoff meets the coarser window), so the sum of `transferAt` over the
scheduled slots is the sum over `ocObsPulses m t t`. Two coarser pieces overlapping at `t`
give the same Eulerian operator and the weights add to one; a copy and a letter differ only by
`lam`. The appended child of the coarser native context is not the
recentred finer native family as a chain, but has its history geometry on the availability
interval of the finer slot, at every time of nonzero weight (`tc_appendChild_histEq`: the
single-pulse flow identity `flowOf_single_pulse` under `IsOCStreamSeq` and the carrier start); the
old fluxes then agree by the carried history invariant. These are the fields of `TransferInput`. -/
def TransferChartCollapseStatement : Prop :=
  PiecePiolaFiniteOrderStatement → CenteredCoefficientFiniteOrderStatement →
    TransferredIdentityEulerianOnStatement

open scoped Classical in
/-- **The path-sum step (the lift of the Hilbert fibre is the sum over the paths).** On the native family of a pulse `k`, at a cell time of its lift interval
and a slow offset of the ladder, for a smooth coarse field `a` and every functional `ℓ` on the
space of the target component:
* grade `h ≥ 1`: the mean flux of the lift `CcT` of the Hilbert fibre is the sum over the paths
  `π` of `h` edges with target `v` of the mean flux of the lift of the scalar path family of `π`
  (in the form `IsLiftSequenceOn` in which `IsActualSuccessor` supplies it) applied to the scalar
  field `ℓ ∘ C_π ∘ a_{src π}`, `C_π` the ordered product of the maps of `π`;
* grade `0`: it is the mean flux of the scalar lift with no edge applied to `ℓ ∘ a_v`.
A component without incoming identity has no path, so all grades `h ≥ 1` vanish; one edge with two
identities gives two paths. The proof uses uniqueness of lift sequences (`lift_sequence_unique` and
its localized form), linearity of `liftFluxX` in the edges, `G.actual = nativeChain`
(`IsNatural`). The index conventions of `liftFluxX` against `pathEdges` are those of
`pathMeanFlux` and `pulseMeanFluxEuler`. `C^k` caveat: stated for smooth coarse fields, as
`IsLiftSequence` is; the consumers apply it to monomials (coefficient extraction) or pass to finite
order through the coefficients. The hypothesis gives the lifts `Cπ h' π` of the paths of every
length `1 ≤ h' ≤ h`, not only of `h` edges (as `lift_path_decomposition` assumes). The core supplies
them: `SplitInput.successor` gives `IsLiftFamily` of every source, in particular of `copyQuad [] h' π`,
and `(Cc (copyQuad [] h' π)) k (nativeChain ..)` is the lift of `π`. The floors `N + Dm + 2 ≤ sX, sZ`. The path sum moves the non-injective linear maps
(`ℓ`, `rootPathMap`) through the bare `fderiv`s of `slowPartial`, `fastPartial`, `orderedDerivative`,
`dEpsWord`, which needs differentiability of the coefficient arrays, available only up to the box
orders `sX`, `sZ`; the core has them from `SplitInput.range`.
Hypothesis `ActualFluxJointSmooth G`: the right side splits
`fieldCellMean` over the finite sum of paths and each path integrand must be continuous; the
consumers have it from `SplitInput.edge` (`CovFluxReg.actualFluxJointSmooth`). -/
def HilbertLiftPathSumStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → CovFluxReg.ActualFluxJointSmooth G →
    Mn.N + Dm + 2 ≤ Mn.sX → Mn.N + Dm + 2 ≤ Mn.sZ →
    ∀ (ρ : ℝ), ρ = Mn.lenFactor * liftLength D G.level →
    ∀ (depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (k : ℤ) (hk : Odd k) (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)),
    IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N depth
      (CcT k) →
    ∀ τ ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
    ∀ (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root), (∀ s, ContDiff ℝ (⊤ : ℕ∞) (a s)) →
    ∀ (n : ℕ) (X : Vec 2), X ∈ ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ →
    ∀ (j : Fin 2) (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ),
    (∀ (h : ℕ), 1 ≤ h → h ≤ depth →
      ∀ (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)),
      (∀ h' : ℕ, 1 ≤ h' → h' ≤ h → ∀ π : StagePath G h',
        IsLiftSequenceOn (ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ)
          (familyLiftData D G.level k (nativeChain G.level k) ρ
            (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
          Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          Mn.N h' (Cπ h' π)) →
      ℓ (fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a h n τ X z j) v) =
        ∑ᶠ π : StagePath G h, if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
          fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
              (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)) (Cπ h π)
            (fun s' X' => Pi.single (0 : Fin (h + 1))
              (ℓ (rootPathMap hr π.src.root π.mapList v.1.root (a s' X' ⟨π.src, hπ.2⟩))))
            h n τ X z j) (Fin.last h)
        else 0) ∧
    (∀ (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
      IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k
          (nativeChain G.level k) ρ (fun _ _ _ => []))
        Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N 0 C0 →
      ℓ (fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a 0 n τ X z j) v) =
        fieldCellMean (fun z => liftFluxX (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ)
            D G.level k (nativeChain G.level k) ρ (fun _ _ _ => [])) C0
          (fun s' X' => fun _ : Fin 1 => ℓ (a s' X' v)) 0 n τ X z j) 0)

/-- The conclusion of the source-mean step: **the non-diagonal part of the plain flux is `Q_p 𝐄^flux P_p g`**,
pointwise on the window, for a field of class `C^K`, `K ≥ N + Dm + 4p`. -/
def SourceMeanIdentityStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ (ta tb : ℝ) (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc ta tb,
        ContDiff ℝ (K : ℕ) (fun x => g t x v) ∧ IsZ2Periodic (fun x => g t x v)) →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2,
      rootReadout P seedK freshK φ₀ G G' .plain G.level (D.eps (G.level - 1)) Mn.η0 g v t x -
          diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 g v t x =
        covMeanAt Mn G G.level Mn.N Mn.p depth CcT g v t x

/-- **The source-mean step (the letters sum to the source mean).** From the root-bookkeeping, transfer and path-sum steps: by the root-bookkeeping step
the identities out of the roots into the children of `v` other than the first source are the
valid sources `copyDir`, `copyQuad`, `letterMean`, `letterCov` with the empty word and old target
`v`, with unit total weight; by the transfer step each is its Eulerian operator; by the path-sum step the grade-`h`
degree-`n` mean of the Hilbert fibre is the sum over the paths. Then:
* degree `2`: the quadratic conversions (`copyQuad`); degree `n ≥ 3`: `letterMean` plus, for a
  one-edge path, the all-slow direct part, which is `copyDir`;
* covariance: `Q_p 𝐄 P_p = ∑_{a,a' ≤ p} (-1)^a 𝒞^a 𝐄 𝒞^{a'}/(a! a'!)`, the term `a = a' = 0` being
  the two items above and the others the letters `letterCov` (`pullFlux ∘ pushFlux = id`, and
  `𝒞` has constant coefficients, so the centring of the chart is immaterial);
* the two range conditions, from `SplitInput.range`: the means of degree `n > N + Dord` vanish
  (`C_n = 0` for `n > N`, and the `ε^j` coefficient of `sourceFlux` vanishes above the order of
  the edges), so the degrees up to `N + Dm` of `meanFluxE` are covered by the letters `n ≤ nMax`;
  no path is longer than `min hMax depth`, so the grades `1..depth` are covered and no copy of a
  longer path exists. Letters of the alphabet above the range have zero output.
With no incoming identity
both sides vanish; `p = 0` is excluded by the schedule but the identity then reads
`Pl - Dg = 𝐄^flux g`. Note that `Q_p` is moved through the
glue (the cutoffs do not depend on `x`; the charts do, and the letters are defined with the
Eulerian `𝒞`), using the degree-by-degree vanishing above `N + Dord`. -/
def SourceMeanLetterSumStatement : Prop :=
  RootSourceBookkeepingStatement → TransferredIdentityEulerianOnStatement →
    HilbertLiftPathSumStatement → SourceMeanIdentityStatement

/-- The conclusion of the first-source-flux step: **the first-source part of the plain flux is `-Q_p 𝒟 g`**,
pointwise on the window, for a field of class `C^K`, `K ≥ N + Dm + 4p`. -/
def FirstSourceIdentityStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ (ta tb : ℝ) (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc ta tb,
        ContDiff ℝ (K : ℕ) (fun x => g t x v) ∧ IsZ2Periodic (fun x => g t x v)) →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2,
      diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 g v t x =
        -covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x

/-- **The first-source-flux step (the physical flux of the first source).** From the root-bookkeeping, Piola-transport and path-sum steps (grade
`0`): the only first-source identity out of a root into a child of `v` is `letterDiag [] v`, into
`(v, 𝖣)`, with the identity map and unit total weight; its arrays are the symmetric coefficients
of `firstSourceFlux` at the centre of the recentred context, of
order `N + 1 + 4p`; they reconstruct the operator (`arrOp_eq_sum_fluxCoeff`;
`firstSourceFlux_applyArr`) and the Piola-transport step transports it; the context strain at the
actual context is `D𝐛_{m-1}` and the assembled diagonal flux `diagFluxCtx` is `diagFluxPhys` (the
grade-zero lift of the Hilbert fibre is the scalar one on each component, the path-sum step; the
appended children as in the transfer step), so that the Eulerian operator of every coarser piece is
`-Q_p 𝒟` and the weights add to one. The symmetrization of `fluxCoeff` is over the word alone, the
flux index is untouched, so the contraction with ordered derivatives of a `C^{d-1}` field is
unchanged pointwise, whatever the space dependence of the coefficients; only the operator-level
agreement of chart pieces is used (`firstSourceFlux_coeff_renewal_sym`, or directly each piece
against the physical operator), never the word-by-word quiet clause. At a time where the
covariance primitive vanishes `𝒟 = -𝓕_A`; a stage without identities still has this term.
The two identifications (context strain, `diagFluxCtx`) hold at
every time of nonzero weight, and the recorded order `N + 1 + 4p` is at least the order of
`firstSourceFlux` plus one. `C^k` caveat: the lemmas are for `ContDiff ℝ ⊤`. -/
def FirstSourcePhysicalFluxStatement : Prop :=
  RootSourceBookkeepingStatement → PiecePiolaFiniteOrderStatement →
    HilbertLiftPathSumStatement → FirstSourceIdentityStatement

/-- **The flux-regularity step (regularity of the covariance flux).** For a field of class `C^K`,
`K ≥ N + Dm + 4p`, at every time of the window: `𝒟 g` and `𝐄^flux P_p g` are `C^{2p}` in space,
hence `Q_p G = Q_p 𝒟 g - Q_p 𝐄^flux P_p g` (third clause: additivity of `covPolyQ` on `C^{2p}`
fields, recorded so that the assembly does not redo it); `Q_p G` is continuous in space
(continuity of `Pl` is `fluxCont_Pl`). Inputs: `IsBoxSmooth sX sZ` of the lift coefficients
(`IsLiftSequence`) with the floors of `SplitInput.range`, smoothness of the flow charts and of
`D𝐛_{m-1}`, differentiation under the cell mean. The floors of `SplitInput.range` are the cascade's;
the terminal floors are existential. It overlaps `readoutFluxRegularity` of
`CovarianceTransport.Regularity` (the same flux at `g = aZ`, with time bounds). -/
def CovarianceFluxRegularityStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (_seedK _freshK : ℕ → KernelSpec) (_φ₀ : Vec 2 → ℝ) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ (ta tb : ℝ) (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc ta tb,
        ContDiff ℝ (K : ℕ) (fun x => g t x v) ∧ IsZ2Periodic (fun x => g t x v)) →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb,
      ContDiff ℝ (2 * Mn.p : ℕ) (fun y => menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y) ∧
      ContDiff ℝ (2 * Mn.p : ℕ) (fun y => menuMeanFluxE Mn G G.level Mn.N depth CcT
        (menuCovPRep Mn D G.level Mn.p g) t y v) ∧
      (∀ x : Vec 2, menuCovFlux Mn G G.level Mn.N Mn.p depth CcT g v t x =
        covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x -
          covMeanAt Mn G G.level Mn.N Mn.p depth CcT g v t x) ∧
      Continuous (menuCovFlux Mn G G.level Mn.N Mn.p depth CcT g v t)

/-! ### The assembly of the core -/

/-- **The split on a classical field from its eight pieces.** -/
theorem successor_split_core_of_pieces
    (h1 : RootSourceBookkeepingStatement) (h2 : PiecePiolaFiniteOrderStatement)
    (h3 : CenteredCoefficientFiniteOrderStatement) (h4 : TransferChartCollapseStatement)
    (h5 : HilbertLiftPathSumStatement) (h6 : SourceMeanLetterSumStatement)
    (h7 : FirstSourcePhysicalFluxStatement) (h8 : CovarianceFluxRegularityStatement) :
    SuccessorSplitCoreStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P seedK freshK φ₀ Mn G G' depth CcT hin K hK ta tb g hg
    v t ht φ hφ _
  have hsrc := h6 h1 (h4 h2 h3) h5 P seedK freshK φ₀ Mn G G' depth CcT hin K hK ta tb g hg
  have hdiag := h7 h1 h2 h5 P Mn G G' depth CcT hin K hK ta tb g hg
  have hreg := h8 P seedK freshK φ₀ Mn G G' depth CcT hin K hK ta tb g hg
  have hsub : ∀ s ∈ Set.Ioc ta t, s ∈ Set.Icc ta tb :=
    fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  refine testedFlux_of_pointwise ?_ ?_
  · intro s hs x
    have e1 := hsrc v s (hsub s hs) x
    have e2 := hdiag v s (hsub s hs) x
    have e3 := (hreg v s (hsub s hs)).2.2.1 x
    show rootReadout P seedK freshK φ₀ G G' KerMode.plain G.level (D.eps (G.level - 1)) Mn.η0
      g v s x = -menuCovFlux Mn G G.level Mn.N Mn.p depth CcT g v s x
    rw [← sub_add_cancel (rootReadout P seedK freshK φ₀ G G' KerMode.plain G.level
      (D.eps (G.level - 1)) Mn.η0 g v s x)
      (diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 g v s x), e1, e2, e3]
    abel
  · intro s hs
    exact fluxPairing_integrable (hreg v s (hsub s hs)).2.2.2.neg hφ

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
