-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.FluxAe
import AVRegularity.CycleJoint.PlaneWeakCurveCongruenceOn
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleComparison.Reconstruction.ApproxJets
import AVRegularity.CycleComparison.Error.Main
public import AVRegularity.EntryTerminal.Ingredients.PrepCore.PrepCore
import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
import AVenhance.Infra.Construction.StreamAdmissible

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Analysis.Convolution AVRegularity.EntryTerminal.Ingredients
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The plain flux is the kernel flux plus the fine flux**.

`plain_flux_eq_kernel_add_fine`: at a time `s`, if the lifts `wK j s` are classical representatives
of `uh s ·`, the kernel inputs `Y` have the classical derivatives of `S uh` as jets (up to the
orders `n ≤ K j + 1`, `n + 1 ≤ D_m`), and `ff` realizes the fine flux, then almost everywhere in
`x` the plain flux of the lifts equals the kernel flux of `Y` plus `ff`. The sum over `[2, D_m]`
is cut to the admissible orders by `physCoeff_zero_of_not_admissible`
(`kernel_orders_sum_eq`).

For `S = I` the fine flux is `0`, and with no edges all three fluxes are `0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The value of the splitting at one order of one identity (for `x` in the good set). -/
theorem order_term_eq (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (k : ℕ) (K : CompIn G.comps → ℕ) (hdesc : G.fam.IsDescending K)
    (v j : CompIn G.comps) (α : G.fam.Γ v j) (s : ℝ) (uhj : Vec 2 → hr j.1.root)
    (hc : ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) uhj) (hp : IsZ2Periodic uhj)
    (Yj : TorusHk (k + Dm - 1) (hr j.1.root)) (x : Vec 2)
    (hY : ∀ (n : ℕ) (hn : n ≤ K j + 1 ∧ n + 1 ≤ Dm) (word : DerivativeWord2 n),
      Yj.toFunction.jet ⟨⟨n, by omega⟩, word⟩ x =
        orderedDerivative word
          ((G.kernelOf P seedK freshK v j α).applyClassical φ₀ s uhj) x)
    (d : ↥(Finset.Icc 2 Dm)) (pf₁ : d.1 - 1 < k + Dm - 1 + 1) :
    G.physCoeff v j α d.1 s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word uhj x) =
      G.physCoeff v j α d.1 s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        Yj.toFunction.jet ⟨⟨d.1 - 1, pf₁⟩, word⟩ x) +
      G.physCoeff v j α d.1 s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => uhj y -
          (G.kernelOf P seedK freshK v j α).applyClassical φ₀ s uhj y) x) := by
  by_cases hd : d.1 ∈ admissibleOrders K Dm v j
  · have hd' := Finset.mem_filter.1 hd
    have hd2 := Finset.mem_Icc.1 hd'.1
    rw [← map_add]
    congr 1
    refine PiLp.ext fun word => ?_
    simp only [PiLp.add_apply]
    rw [hY (d.1 - 1) ⟨by omega, by omega⟩ word]
    exact classical_split_word G P seedK freshK φ₀ hφs hφsupp v j α s uhj hc hp (by omega) word x
  · rw [physCoeff_zero_of_not_admissible G K hdesc v j α d.1 d.2 hd]
    simp


/-- **The plain flux is the kernel flux plus the fine flux**, almost everywhere in `x`. -/
theorem plain_flux_eq_kernel_add_fine (G : GenStage D hr Dm b j₀) (hD : 2 ≤ Dm) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (k : ℕ) (K : CompIn G.comps → ℕ) (hdesc : G.fam.IsDescending K)
    (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (v : CompIn G.comps) (s : ℝ) (ff : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (hsm : ∀ j, ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) (fun x => uh s x j) ∧ IsZ2Periodic (fun x => uh s x j))
    (hv : ∀ j, (wK j s).toFunction.jet (valueIndex2 (K j + 1)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => uh s x j)
    (hy : ∀ j (α : G.fam.Γ v j), ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ∀ (n : ℕ) (hn : n ≤ K j + 1 ∧ n + 1 ≤ Dm) (word : DerivativeWord2 n),
      (Y v j α s).toFunction.jet ⟨⟨n, by omega⟩, word⟩ x =
        orderedDerivative word
          ((G.kernelOf P seedK freshK v j α).applyClassical φ₀ s (fun y => uh s y j)) x)
    (hf : ff.toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      fineFluxF P seedK freshK φ₀ G uh v s) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      plainFlux G K wK v s x = kernelFlux G k Y v s x + ff.toFunction.jet (valueIndex2 k) x := by
  classical
  have hW : ∀ j, ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (n : ℕ) (hn : n ≤ K j + 1 ∧ n + 1 ≤ Dm)
      (word : DerivativeWord2 n), (wK j s).toFunction.jet ⟨⟨n, by omega⟩, word⟩ x =
        orderedDerivative word (fun y => uh s y j) x := fun j => by
      have hrK : min (K j + 1) (Dm - 1) ≤ K j + 1 := min_le_left _ _
      have hrep := lowRep hrK (wK j s) _ ((hsm j).1.of_le (by exact_mod_cast min_le_right _ _))
        (hsm j).2 (hv j)
      filter_upwards [classicalRepJetsAeAll _ _ hrep] with x hx n hn word using
        hx n (by omega) word
  have hY : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j (α : G.fam.Γ v j),
      ∀ (n : ℕ) (hn : n ≤ K j + 1 ∧ n + 1 ≤ Dm) (word : DerivativeWord2 n),
      (Y v j α s).toFunction.jet ⟨⟨n, by omega⟩, word⟩ x =
        orderedDerivative word
          ((G.kernelOf P seedK freshK v j α).applyClassical φ₀ s (fun y => uh s y j)) x :=
    ae_all_iff.2 fun j => ae_all_iff.2 (hy j)
  filter_upwards [ae_all_iff.2 hW, hY, hf] with x hxW hxY hxF
  rw [hxF]
  simp only [plainFlux, kernelFlux, fineFluxF, coeffFluxOn]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  simp only [edge_apply_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  have key := Providers.WeakGen.Comparison.kernel_orders_sum_eq K (le_refl Dm) v j (L₁ := Dm - 1) (L₂ := K j + 1) le_rfl
    (fun n => G.physCoeff v j α n s x)
    (fun n hn hna => physCoeff_zero_of_not_admissible G K hdesc v j α n hn hna s x)
    (fun a => orderedDerivative a.2 (fun y => uh s y j) x)
    (fun a => (wK j s).toFunction.jet a x)
    (fun n h₁ h₂ word => (hxW j n ⟨by omega, by omega⟩ word).symm)
    (fun d => by have := Finset.mem_Icc.1 d.2; omega)
    (fun d => by
      have h := Finset.mem_filter.1 d.2
      have := Finset.mem_Icc.1 h.1
      omega)
  refine key.symm.trans (Finset.sum_congr rfl fun d _ => ?_)
  exact order_term_eq G P seedK freshK φ₀ hφs hφsupp k K hdesc v j α s (fun y => uh s y j)
    (hsm j).1 (hsm j).2 (Y v j α s) x (hxY j α) d _

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Ingredients AVRegularity.Analysis.Convolution
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The weak identity of the kernel system from the plain one**.

`weak_clause`: at a time `t` of the window, the weak identity of the kernel system with the
inputs `Y` and the forcing `(trunc RK + Ff, trunc qK)` follows from the plain weak identity of the
reconstruction. At the times `s` where `Y s = 0` (the carrier replaced by `0` on the null set
`N`) the right-hand side is integrable by `cwiRhs_integrable_of_memLp`; elsewhere it equals the plain
one almost everywhere in space (`plain_flux_eq_kernel_add_fine`).

For `Ff = 0` and `S = I` the correction terms vanish. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The right-hand side of the kernel identity at a good time equals the plain one a.e. in `x`. -/
theorem good_rhs_ae (G : GenStage D hr Dm b j₀) (hD : 2 ≤ Dm) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (k : ℕ) (K : CompIn G.comps → ℕ) (hK : ∀ v, k ≤ K v) (hdesc : G.fam.IsDescending K)
    (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (v : CompIn G.comps) (s : ℝ)
    (hsm : ∀ j, ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) (fun x => uh s x j) ∧
      IsZ2Periodic (fun x => uh s x j))
    (hv : ∀ j, (wK j s).toFunction.jet (valueIndex2 (K j + 1)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => uh s x j)
    (hy : ∀ j (α : G.fam.Γ v j), ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ∀ (n : ℕ) (hn : n ≤ K j + 1 ∧ n + 1 ≤ Dm) (word : DerivativeWord2 n),
      (Y v j α s).toFunction.jet ⟨⟨n, by omega⟩, word⟩ x =
        orderedDerivative word
          ((G.kernelOf P seedK freshK v j α).applyClassical φ₀ s (fun y => uh s y j)) x)
    (hf : (Ff v s).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      fineFluxF P seedK freshK φ₀ G uh v s) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      kernelFlux G k Y v s x +
          (truncateTorusHk (hK v) (RK v s) + Ff v s).toFunction.jet (valueIndex2 k) x =
        plainFlux G K wK v s x + (RK v s).toFunction.jet (valueIndex2 (K v)) x := by
  have h1 := plain_flux_eq_kernel_add_fine G hD P seedK freshK φ₀ hφs hφsupp k K hdesc uh wK Y v s
    (Ff v s) hsm hv hy hf
  have h2 := CycleComparison.Coarse.jet_add_ae (truncateTorusHk (hK v) (RK v s)) (Ff v s)
  have h3 := KernelEnergy.truncateTorusHk_toFunction_jet_ae (hK v) (RK v s) (valueIndex2 k)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx2, hx1, hx3]
  change _ + ((RK v s).toFunction.jet (valueIndex2 (K v)) x + _) = _
  abel


/-- The drift of an admissible stream is measurable and bounded in each component at a time of a
compact window. -/
theorem streamVel_data {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (T : Set ℝ)
    (hT : IsCompact T) (s : ℝ) (hs : s ∈ T) (μ : Measure (Vec 2)) :
    (∀ k, AEStronglyMeasurable (fun x => streamVel φ s x k) μ) ∧
      ∃ C : ℝ, ∀ x k, ‖streamVel φ s x k‖ ≤ C := by
  refine ⟨fun k => ?_, ?_⟩
  · have hc : Continuous (streamVel φ s) :=
      (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous.comp
        (continuous_const.prodMk continuous_id)
    exact ((continuous_apply k).comp hc).aestronglyMeasurable
  · obtain ⟨C, -, hC⟩ := CycleJointProofs.streamVel_bounded_on_compact_time hφ T hT
    exact ⟨C, fun x k => (norm_le_pi_norm (streamVel φ s x) k).trans (hC s hs x)⟩


section Clause

variable (G : GenStage D hr Dm b j₀) (hD : 2 ≤ Dm) (P : ProvParams)
  (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
  (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
  (m k : ℕ) (π : CompIn G.comps → ℝ) (tp tf rs Xr : ℝ)
  (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (K : CompIn G.comps → ℕ)
  (hK : ∀ v, k ≤ K v)
  (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
  (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
  (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
  (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
  (hsm : ∀ v, ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) (fun x => uh t x v) ∧
    IsZ2Periodic (fun x => uh t x v))
  (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK)
  (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
  (hFf : IsFluxRealization (ι := CompIn G.comps) (h := fun v => hr v.1.root) k (Set.Icc tp tf)
    (fineFluxF P seedK freshK φ₀ G uh) Ff)
  (hΦ : IsAdmissibleStream (D.Φ m))
  (N : Set ℝ)
  (hgoodN : ∀ s ∉ N, ∀ i, truncateTorusHk (Nat.le_succ (K i)) (wK i s) = uK i s)
  (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
  (hY0 : ∀ s ∈ N, ∀ v u (γ : G.fam.Γ v u), Y v u γ s = 0)
  (hYval : ∀ s ∈ Set.Icc tp tf, s ∉ N → ∀ v u (γ : G.fam.Γ v u),
    (Y v u γ s).val (valueIndex2 (k + Dm - 1)) =
      G.sysS P seedK freshK φ₀ hφ₀ v u γ s ((wK u s).val (valueIndex2 (K u + 1))))

/-- The right-hand side of the kernel identity. -/
def kerRhs (i : CompIn G.comps) (φ : TorusHk 1 (hr i.1.root)) : ℝ → Vec 2 → ℝ :=
  EntryTerminal.Ingredients.cwiRhs (D.κ m) (streamVel (D.Φ m))
    (φ.toFunction.jet (valueIndex2 1))
    (fun m' => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m'⟩)
    (fun s m' => (truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i s)).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m'⟩)
    (kernelFlux G k Y i)
    (fun s => (truncateTorusHk (hK i) (RK i s) + Ff i s).toFunction.jet (valueIndex2 k))
    (fun s => (truncateTorusHk (hK i) (qK i s)).toFunction.jet (valueIndex2 k))

/-- The right-hand side of the plain identity. -/
def plainRhs (i : CompIn G.comps) (φ : TorusHk 1 (hr i.1.root)) : ℝ → Vec 2 → ℝ :=
  EntryTerminal.Ingredients.cwiRhs (D.κ m) (streamVel (D.Φ m))
    (φ.toFunction.jet (valueIndex2 1))
    (fun m' => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m'⟩)
    (fun s m' => (wK i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => m'⟩)
    (plainFlux G K wK i) (fun s => (RK i s).toFunction.jet (valueIndex2 (K i)))
    (fun s => (qK i s).toFunction.jet (valueIndex2 (K i)))

variable {G} {P} {seedK freshK} {φ₀} {hφ₀} {m k} {π} {tp tf rs Xr} {uh} {K} {hK} {uK wK RK qK} {Ff} {N} {Y}

include hD hφs hφsupp hsm hrec hFf hgoodN hYval in
/-- At a good time of the window the two right-hand sides agree a.e. in space. -/
theorem good_cwi (i : CompIn G.comps) (φ : TorusHk 1 (hr i.1.root)) (s : ℝ)
    (hs : s ∈ Set.Icc tp tf) (hsN : s ∉ N) :
    kerRhs G m k K hK wK RK qK Ff Y i φ s =ᵐ[volume.restrict AVenhance.unitCube]
      plainRhs G m K wK RK qK i φ s := by
  have hdu : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ m' : Fin 2,
      (truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i s)).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m'⟩ x =
      (wK i s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => m'⟩ x :=
    ae_all_iff.2 fun m' => KernelEnergy.truncateTorusHk_toFunction_jet_ae
      (Nat.succ_le_succ (hK i)) (wK i s) ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m'⟩
  have hv : ∀ j, (wK j s).toFunction.jet (valueIndex2 (K j + 1))
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => uh s x j := fun j => by
    have h := hrec.value s hs j
    rw [← hgoodN s hsN j] at h
    exact h
  have hy : ∀ j (α : G.fam.Γ i j), ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ∀ (n : ℕ) (hn : n ≤ K j + 1 ∧ n + 1 ≤ Dm) (word : DerivativeWord2 n),
      (Y i j α s).toFunction.jet ⟨⟨n, by omega⟩, word⟩ x =
        orderedDerivative word
          ((G.kernelOf P seedK freshK i j α).applyClassical φ₀ s (fun y => uh s y j)) x :=
    fun j α => flux_jets_ae G P seedK freshK φ₀ hφ₀ hφs hφsupp k i j α s (fun y => uh s y j)
      (wK j s) (hsm j s hs).1 (hsm j s hs).2 (hv j) (Y i j α s) (hYval s hs hsN i j α)
  have hq := KernelEnergy.truncateTorusHk_toFunction_jet_ae (hK i) (qK i s) (valueIndex2 k)
  refine cwiRhs_congr_ae_at s ?_
  filter_upwards [hdu, good_rhs_ae G hD P seedK freshK φ₀ hφs hφsupp k K hK hrec.desc uh wK RK
    Ff Y i s (fun j => hsm j s hs) hv hy (hFf i s hs), hq] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩

include hΦ hY0 in
/-- At a time of the null set the kernel right-hand side is integrable. -/
theorem bad_cwi (i : CompIn G.comps) (φ : TorusHk 1 (hr i.1.root)) (s : ℝ)
    (hs : s ∈ Set.Icc tp tf) (hsN : s ∈ N) :
    Integrable (kerRhs G m k K hK wK RK qK Ff Y i φ s)
      (volume.restrict AVenhance.unitCube) := by
  have hY0' := hY0 s hsN
  have hvd := streamVel_data hΦ (Set.Icc tp tf) isCompact_Icc s hs
    (volume.restrict AVenhance.unitCube)
  have hz : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (j : CompIn G.comps)
      (α : G.fam.Γ i j) (a : JetIndex2 (k + Dm - 1)),
      (0 : TorusHk (k + Dm - 1) (hr j.1.root)).toFunction.jet a x = 0 :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun α => ae_all_iff.2 fun a => torusHk_zero_jet_ae a
  have hflux : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), kernelFlux G k Y i s x = 0 := by
    filter_upwards [hz] with x hx
    unfold kernelFlux
    simp only [hY0']
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun α _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (0 : TorusHk (k + Dm - 1) (hr j.1.root)).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) = 0 :=
      PiLp.ext fun word => hx j α _
    rw [h0, map_zero]
  unfold kerRhs
  refine cwiRhs_integrable_of_memLp s hvd.1 hvd.2
    (CycleComparison.Coarse.memLp_jet φ _) (fun m' => CycleComparison.Coarse.memLp_jet φ _)
    (fun m' => CycleComparison.Coarse.memLp_jet _ _) ?_ (CycleComparison.Coarse.memLp_jet _ _)
  refine (CycleComparison.Coarse.memLp_jet (truncateTorusHk (hK i) (RK i s) + Ff i s)
    (valueIndex2 k)).ae_eq ?_
  filter_upwards [hflux] with x hx
  change _ = kernelFlux G k Y i s x + _
  rw [hx, zero_add]

include hD hφs hφsupp hsm hrec hFf hΦ hgoodN hY0 hYval in
/-- **The weak identity of the kernel system** at one component and one time. -/
theorem weak_clause (hNae : ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)), s ∉ N)
    (i : CompIn G.comps) (t : ℝ) (ht : t ∈ Set.Icc tp tf) (φ : TorusHk 1 (hr i.1.root)) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ m) tp t (streamVel (D.Φ m))
      ((truncateTorusHk (hK i) (uK i t)).toFunction.jet (valueIndex2 k))
      ((truncateTorusHk (hK i) (uK i tp)).toFunction.jet (valueIndex2 k))
      (φ.toFunction.jet (valueIndex2 1))
      (fun m' => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m'⟩)
      (fun s m' => (truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i s)).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m'⟩)
      (kernelFlux G k Y i)
      (fun s => (truncateTorusHk (hK i) (RK i s) + Ff i s).toFunction.jet (valueIndex2 k))
      (fun s => (truncateTorusHk (hK i) (qK i s)).toFunction.jet (valueIndex2 k)) := by
  obtain ⟨-, -, -, -, hident⟩ := hrec.plain
  have hsub : Set.Ioc tp t ⊆ Set.Icc tp tf := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hI : CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ m) tp t
      (streamVel (D.Φ m)) ((uK i t).toFunction.jet (valueIndex2 (K i)))
      ((uK i tp).toFunction.jet (valueIndex2 (K i))) (φ.toFunction.jet (valueIndex2 1))
      (fun m' => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m'⟩)
      (fun s m' => (wK i s).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => m'⟩)
      (plainFlux G K wK i) (fun s => (RK i s).toFunction.jet (valueIndex2 (K i)))
      (fun s => (qK i s).toFunction.jet (valueIndex2 (K i))) := hident i t ht φ
  refine coupledWeakIdentity_transfer hI
    (KernelEnergy.truncateTorusHk_toFunction_jet_ae (hK i) (uK i t) (valueIndex2 k)).symm
    (KernelEnergy.truncateTorusHk_toFunction_jet_ae (hK i) (uK i tp) (valueIndex2 k)).symm
    ?_ ?_
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hNae,
      ae_restrict_mem measurableSet_Ioc] with s hsN hsI
    exact good_cwi hD hφs hφsupp hsm hrec hFf hgoodN hYval i φ s (hsub hsI) hsN
  · intro s hsI
    have hs := hsub hsI
    by_cases hsN : s ∈ N
    · exact bad_cwi hΦ hY0 i φ s hs hsN
    · exact ((coupledWeakIdentity_iff.mp hI).2.2.1 s hsI).congr
        (good_cwi hD hφs hφsupp hsm hrec hFf hgoodN hYval i φ s hs hsN).symm

end Clause

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The bounds of the residual at a cascade passage: the second instance of the forms**.

The statements are at one frame `F` of the covariance transport
(`CovarianceTransport.Frame`: the stage, its successor, the retained family, the menu, the lift
coefficients, the classical representatives and the lifted field at the order `0`), with the
masses of a law, the trace bound `A_in` and the parameters of `succBill`. They are the forms of
the residual presentation (`CovTruncBound`, …) at the frame, at the common order `0`, with the
prices of the groups of `succBill`:

| Statement | Form | Radius | Price |
|---|---|---|---|
| `FrameCovTruncAt` | `CovTruncBound` | `ρ = c_r√(κ_{m-1}τ_m'')` | `ω^p + ω^{p+1}` |
| `FrameFrontierAt` | `FrontierBound` | `ρ` | `E^{ιΣ_H} + E^{θ₁+Jθ₂}` |
| `FrameFilterAt` | `FilterBound` | `ρ` | `ε_o^{L_c}` |
| `FrameFineTailAt` | `FineTailBound` | `ρ_⋆` | `ε_f^{L_f}` |
| `FrameReconAt` | `ReconBound` | `ρ_⋆` | `succBill` without `ε_f^{L_f}` |

In the bill the flux prices carry the factor `E^{-qγ}` of the reconstruction (it bounds
`√(B/ν) + ε_c²(1 + Z_cl)`); the flux statements are without it.

`frameResidualBound_of_parts` is the assembly at a frame: the residual clause at the order `0`
for the pair `(-RK - Ff, -qK)` with the bill `3·C·A_in·succBill`. The consumer
`ComparisonClauses` asks the residual norm of
the value jets of the positive pair `(RK + Ff, qK)`, the forcing of `û`: it is the same number
(the word of order `0` is the value jet, the residual norm does not see the sign). That
conversion, the quantifier prefix of `SuccessorBillResidualDataStatement` and the instance of
the frame at the cascade menu are not written here.

By `succBill_eq_recon_add_fine` the prices are the groups of `succBill`. For a stage without
identities the suprema of the widths are those of an empty family (`0` for reals),
`ε_f^{L_f} = 0` for `L_f ≥ 1`, and the fine tail is `0`. For `J = 0` the length frontier is
`E^{θ₁}`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The groups of `succBill` -/

/-- The price of the covariance truncation: `ω^p + ω^{p+1}`, `ω = ‖𝖧‖_∞/ρ²`. -/
def succCovPrice (D : OCData) (m : ℕ) (cr : ℝ) (p : ℕ) (tp tf : ℝ) : ℝ :=
  ((⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive D m t a a'|) /
      rhoEnh D cr m ^ 2) ^ p +
    ((⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive D m t a a'|) /
      rhoEnh D cr m ^ 2) ^ (p + 1)

/-- The price of the coarse filter tails: `ε_o^{L_c}`, `ε_o = max{E^{σ₀}, max_γ r_γ/ρ}`. -/
def succFilterPrice (D : OCData) (G : GenStage D hr Dm b j₀) (m : ℕ) (cr σ₀ : ℝ) (Lc : ℕ) : ℝ :=
  (max (D.eps (m - 1) ^ σ₀) (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
    (G.fam.identity v u γ).record.width / rhoEnh D cr m)) ^ Lc

/-- The price of the response boundary: `E^{ιΣ_H} + E^{θ₁+Jθ₂}` (`ι = η₀/8`). -/
def succFrontPrice (D : OCData) (m : ℕ) (η₀ : ℝ) (J H : ℕ) (θ₁ θ₂ : ℝ) : ℝ :=
  D.eps (m - 1) ^ (η₀ / 8 * succSigmaH D.q H) + D.eps (m - 1) ^ (θ₁ + (J : ℝ) * θ₂)

/-- The price of the fine matrix tail: `ε_f^{L_f}`, `ε_f = max_γ r_γ/ρ_⋆`. -/
def succFineBill (D : OCData) (G : GenStage D hr Dm b j₀) (m : ℕ) (c₀ : ℝ) (Lf : ℕ) : ℝ :=
  (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
    (G.fam.identity v u γ).record.width / rhoStar D c₀ m) ^ Lf

/-- The bill of the reconstruction at a cascade passage: `succBill` without the fine tail. -/
def succReconBill (D : OCData) (G : GenStage D hr Dm b j₀) (m : ℕ) (cr c σ₀ η₀ : ℝ)
    (p N Lc Acl J H : ℕ) (tp tf θ₁ θ₂ : ℝ) : ℝ :=
  D.eps (m - 1) ^ (-(D.q * ocGamma D.α D.q)) *
      (succCovPrice D m cr p tp tf + succFilterPrice D G m cr σ₀ Lc +
        succFrontPrice D m η₀ J H θ₁ θ₂) +
    (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / rhoEnh D cr m) ^ N *
      (1 + Real.sqrt (tf - tp) / Real.sqrt (D.cellScaleSq m) * (D.eps m / rhoEnh D cr m) ^ Acl) +
    Real.sqrt (D.cellScaleSq m) *
      Real.sqrt ((1 + (tf - tp) / ocTau D.α D.q D.Λ m) / ocTau D.α D.q D.Λ m) *
      Real.exp (-(c * ocTau D.α D.q D.Λ m / Real.sqrt (D.cellScaleSq m) ^ 2))

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The groups of the successor bill**: `succBill` is the bill of the reconstruction plus the
price of the fine matrix tail. -/
theorem succBill_eq_recon_add_fine (D : OCData) (G : GenStage D hr Dm b j₀) (m : ℕ)
    (c₀ cr c σ₀ η₀ : ℝ) (p N Lc Lf Acl J H : ℕ) (tp tf θ₁ θ₂ : ℝ) :
    succBill D G m c₀ cr c σ₀ η₀ p N Lc Lf Acl J H tp tf θ₁ θ₂ =
      succReconBill D G m cr c σ₀ η₀ p N Lc Acl J H tp tf θ₁ θ₂ + succFineBill D G m c₀ Lf := by
  simp only [succBill, succReconBill, succFineBill, succCovPrice, succFilterPrice, succFrontPrice]
  ring

/-! ### The statements at a frame -/

section Statements

variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- **The covariance truncation at a frame**: a realization of order `k_c` with
`B^{-1/2}‖·‖_{L²(I;H_{ρ,k_c;π})} ≤ C(ω^p + ω^{p+1})A_in`. -/
def FrameCovTruncAt (kc : ℕ) (cr Ain C : ℝ) : Prop :=
  CovTruncBound F.Mn F.G F.m F.N F.p F.depth kc F.CcT F.aZ (F.G.mass law) F.tp F.tf
    (rhoEnh D cr F.m) (C * succCovPrice D F.m cr F.p F.tp F.tf * Ain)

/-- **The response boundary at a frame**: `P_p` of the readout of the omitted flux on the
omitted rows, with `B^{-1/2}‖·‖ ≤ C(E^{ιΣ_H} + E^{θ₁+Jθ₂})A_in` (`successor_frontier_bounds`,
here after `P_p` and on a classical representative). -/
def FrameFrontierAt (kc : ℕ) (cr θ₁ θ₂ Ain C : ℝ) : Prop :=
  FrontierBound F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.p F.H F.J kc
    (D.eps (F.m - 1)) F.η₀ F.aY (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m)
    (C * succFrontPrice D F.m F.η₀ F.J F.H θ₁ θ₂ * Ain)

/-- **The coarse filter tails at a frame**: `B^{-1/2}‖·‖ ≤ Cε_o^{L_c}A_in`.
-/
def FrameFilterAt (kc : ℕ) (cr σ₀ : ℝ) (Lc : ℕ) (Ain C : ℝ) : Prop :=
  FilterBound F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.m F.p kc (D.eps (F.m - 1)) F.η₀ F.aZ
    (F.G.mass law) F.tp F.tf (rhoEnh D cr F.m) (C * succFilterPrice D F.G F.m cr σ₀ Lc * Ain)

/-- **The fine matrix tail at a frame**: `ν^{-1/2}‖·‖_{L²(I;L²_π)} ≤ Cε_f^{L_f}A_in` on the
lifted field. -/
def FrameFineTailAt (c₀ : ℝ) (Lf : ℕ) (Ain C : ℝ) : Prop :=
  FineTailBound F.P F.seedK F.freshK F.φ₀ F.Mn F.G F.m F.N F.depth 0 F.CcT F.aRep
    (F.G.mass law) F.tp F.tf (rhoStar D c₀ F.m) (C * succFineBill D F.G F.m c₀ Lf * Ain)

/-- **The reconstruction bound at a frame (groups 1, 5, 6)**: from the three flux bounds with the
constant `C_fl`, a reconstruction of the lifted field at the order `0` with the bound
`C·𝔅_rec·A_in`. -/
def FrameReconAt (kc : ℕ) (c₀ cr c σ₀ : ℝ) (Lc Acl : ℕ) (θ₁ θ₂ Ain Cfl C : ℝ) : Prop :=
  FrameCovTruncAt F law kc cr Ain Cfl → FrameFrontierAt F law kc cr θ₁ θ₂ Ain Cfl →
    FrameFilterAt F law kc cr σ₀ Lc Ain Cfl →
    ReconBound F.Mn F.G F.m F.N F.depth 0 F.CcT F.aRep (F.G.mass law) F.tp F.tf
      (rhoStar D c₀ F.m)
      (C * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ * Ain)

/-- **The bounds of the residual at a frame**: a reconstruction of the lifted field, a
realization of the fine tail, square integrable in time (the plain-to-kernel step asks it), and
the residual clause at the order `0` with the bill `C·𝔅·A_in`, `𝔅 = succBill`. -/
def FrameResidualBoundAt (c₀ cr c σ₀ : ℝ) (Lc Lf Acl : ℕ) (θ₁ θ₂ Ain C : ℝ) : Prop :=
  ∃ (K : CompIn F.G.comps → ℕ) (hK : ∀ v, 0 ≤ K v)
    (uK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (wK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn F.G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (Ff : ∀ v : CompIn F.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Xr : ℝ),
    IsStageRecon F.G F.m 0 (F.G.mass law) F.tp F.tf (rhoStar D c₀ F.m)
      (menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep) Xr K hK uK wK RK qK ∧
    IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) 0
      (Set.Icc F.tp F.tf)
      (fineFluxF F.P F.seedK F.freshK F.φ₀ F.G
        (menuLiftedRep F.Mn F.G F.m F.N F.depth F.CcT F.aRep)) Ff ∧
    (∀ v, MemLp (Ff v) 2 (volume.restrict (Set.Icc F.tp F.tf))) ∧
    ErrorResidualClause F.G F.m 0 (F.G.mass law) F.tp F.tf (rhoStar D c₀ F.m)
      (C * succBill D F.G F.m c₀ cr c σ₀ F.η₀ F.p F.N Lc Lf Acl F.J F.H F.tp F.tf θ₁ θ₂ * Ain)
      K hK RK qK Ff

/-- **Assembly at a frame.** The three flux bounds with a common constant, the reconstruction and
the fine matrix tail with a common constant `C`, and the word conversion give the bounds of the
residual with the constant `3·0!·C`. -/
theorem frameResidualBound_of_parts (hW : ResidualWordsOfMassStatement)
    (hπ : ∀ v, 0 < F.G.mass law v) {kc : ℕ} {c₀ cr c σ₀ : ℝ} {Lc Lf Acl : ℕ}
    {θ₁ θ₂ Ain Cfl C : ℝ}
    (h2a : FrameCovTruncAt F law kc cr Ain Cfl) (h2b : FrameFrontierAt F law kc cr θ₁ θ₂ Ain Cfl)
    (h3 : FrameFilterAt F law kc cr σ₀ Lc Ain Cfl)
    (hrec : FrameReconAt F law kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain Cfl C)
    (hfine : FrameFineTailAt F law c₀ Lf Ain C) :
    FrameResidualBoundAt F law c₀ cr c σ₀ Lc Lf Acl θ₁ θ₂ Ain
      (3 * ((0 : ℕ).factorial : ℝ) * C) := by
  obtain ⟨K, hK, uK, wK, RK, qK, hrecon⟩ := hrec h2a h2b h3
  obtain ⟨Ff, hFf, hFm⟩ := hfine
  refine ⟨K, hK, uK, wK, RK, qK, Ff, _, hrecon, hFf, hFm.1, ?_⟩
  refine (errorResidualClause_of_recon_fine hW F.G F.m 0 (F.G.mass law) hπ F.tp F.tf
    (rhoStar D c₀ F.m) _ _ _ K hK uK wK RK qK hrecon Ff hFm).congr ?_
  rw [succBill_eq_recon_add_fine]
  ring

end Statements

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Error
namespace AVRegularity.Construction.Residual.Presentation

/-! # The word clause from the mass form (proof of `residualWordsOfMass`)

One word `∂^β` of order `j ≤ K` of a torus Sobolev element is one summand of the factorial norm:
`ρ^{2j} ‖∂^β U‖² ≤ (j!)² |U|²_{ρ,K}`. Summed over the components, integrated in time with
`residual_split_le`, and combined with the subadditivity of the mass norm (crude constant
`(a+b)² ≤ 2a² + 2b²`), this gives the constant `3·k!`. -/

section Word

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

theorem wordsMass_norm_sq_eq_lintegral {K : ℕ} (U : TorusHk K E) (a : JetIndex2 K) :
    ENNReal.ofReal (‖U.val a‖ ^ 2) =
      ∫⁻ x in AVenhance.unitCube, ‖U.toFunction.jet a x‖ₑ ^ 2 := by
  have hae := AVRegularity.KernelEnergy.torusHk_toFunction_jet_ae U a
  have hm : MemLp (U.toFunction.jet a) 2 (volume.restrict AVenhance.unitCube) :=
    (Lp.memLp (U.val a)).ae_eq hae.symm
  have hn : ‖U.val a‖ =
      (eLpNorm (U.toFunction.jet a) 2 (volume.restrict AVenhance.unitCube)).toReal := by
    rw [eLpNorm_congr_ae hae, ← Lp.norm_def]
  rw [hn]
  exact ofReal_eLpNorm_sq_cell hm

/-- One word of order `j ≤ K` is one summand of the factorial norm. -/
theorem wordsMass_word_le {K : ℕ} (ρ : ℝ) (U : TorusHk K E) {j : ℕ} (hj : j ≤ K)
    (β : DerivativeWord2 j) :
    ∫⁻ x in AVenhance.unitCube, ‖ρ ^ j • AVRegularity.torusJetOrder U j β x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((j.factorial : ℝ) ^ 2 * factorialNormSq ρ U.val) := by
  set a : JetIndex2 K := ⟨⟨j, Nat.lt_succ_of_le hj⟩, β⟩ with ha
  have hT : ∀ x, AVRegularity.torusJetOrder U j β x = U.toFunction.jet a x := fun x => by
    simp only [AVRegularity.torusJetOrder, hj, ↓reduceDIte, ha]
  have hpt : ∀ x, ‖ρ ^ j • AVRegularity.torusJetOrder U j β x‖ₑ ^ 2 =
      ENNReal.ofReal ((ρ ^ j) ^ 2) * ‖U.toFunction.jet a x‖ₑ ^ 2 := by
    intro x
    rw [hT, enorm_smul, mul_pow, enorm_sq_eq_ofReal_sq (ρ ^ j), Real.norm_eq_abs, sq_abs]
  have h1 : ∫⁻ x in AVenhance.unitCube, ‖ρ ^ j • AVRegularity.torusJetOrder U j β x‖ₑ ^ 2 =
      ENNReal.ofReal ((ρ ^ j) ^ 2 * ‖U.val a‖ ^ 2) := by
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← wordsMass_norm_sq_eq_lintegral, ← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  set i0 : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj⟩ with hi0
  have hd : ‖U.val a‖ ^ 2 ≤ derivativeNormSq U.val i0 := by
    unfold derivativeNormSq
    exact Finset.single_le_sum (f := fun w : DerivativeWord2 i0.val => ‖U.val ⟨i0, w⟩‖ ^ 2)
      (fun w _ => sq_nonneg _) (Finset.mem_univ β)
  have hs : factorialWeight ρ j * derivativeNormSq U.val i0 ≤ factorialNormSq ρ U.val := by
    unfold factorialNormSq
    exact Finset.single_le_sum (f := fun i : Fin (K + 1) =>
      factorialWeight ρ i.val * derivativeNormSq U.val i)
      (fun i _ => mul_nonneg (factorialWeight_nonneg ρ _) (derivativeNormSq_nonneg _ _))
      (Finset.mem_univ i0)
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hpow : (ρ ^ j) ^ 2 = ρ ^ (2 * j) := by rw [← pow_mul, mul_comm]
  calc (ρ ^ j) ^ 2 * ‖U.val a‖ ^ 2 ≤ (ρ ^ j) ^ 2 * derivativeNormSq U.val i0 :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    _ = (j.factorial : ℝ) ^ 2 * (factorialWeight ρ j * derivativeNormSq U.val i0) := by
        unfold factorialWeight
        rw [hpow]
        field_simp
    _ ≤ (j.factorial : ℝ) ^ 2 * factorialNormSq ρ U.val :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)

end Word

section Family

variable {ι : Type*} [Fintype ι]

theorem wordsMass_family_le {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, CompleteSpace (E i)] {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (U : ∀ v, TorusHk (K v) (E v)) {j : ℕ} (hj : ∀ v, j ≤ K v) (β : DerivativeWord2 j) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j • AVRegularity.torusJetOrder (U v) j β x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((j.factorial : ℝ) ^ 2 * massNormSq (E := E) (K := K) ρ π
        (fun v => (U v).val)) := by
  have hmass : massNormSq (E := E) (K := K) ρ π (fun v => (U v).val) =
      ∑ v, (π v)⁻¹ * factorialNormSq ρ (U v).val := rfl
  rw [hmass, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun v _ =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.2 (hπ v).le)
      (factorialNormSq_nonneg ρ (U v).val))]
  refine Finset.sum_le_sum fun v _ => ?_
  calc ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j • AVRegularity.torusJetOrder (U v) j β x‖ₑ ^ 2
      ≤ ENNReal.ofReal (π v)⁻¹ *
          ENNReal.ofReal ((j.factorial : ℝ) ^ 2 * factorialNormSq ρ (U v).val) := by
        gcongr
        exact wordsMass_word_le ρ (U v) (hj v) β
    _ = ENNReal.ofReal ((j.factorial : ℝ) ^ 2 * ((π v)⁻¹ * factorialNormSq ρ (U v).val)) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
        congr 1
        ring

theorem wordsMass_flux_family_le {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (U : ∀ v, TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v))) {j : ℕ} (hj : ∀ v, j ≤ K v)
    (β : DerivativeWord2 j) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖ρ ^ j • (AVRegularity.torusJetOrder (U v) j β x) k‖ₑ ^ 2 ≤
      ENNReal.ofReal ((j.factorial : ℝ) ^ 2 *
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) ρ π
          (fun v => (U v).val)) := by
  refine le_trans (le_of_eq ?_) (wordsMass_family_le (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
    ρ π hπ U hj β)
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  refine lintegral_congr fun x => ?_
  have := sum_enorm_sq_pair (ρ ^ j • AVRegularity.torusJetOrder (U v) j β x)
  simpa [PiLp.smul_apply] using this

theorem wordsMass_massNormSq_neg_sub_le {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, CompleteSpace (E i)] {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (A B : ∀ v, TorusHk (K v) (E v)) :
    massNormSq (E := E) (K := K) ρ π (fun v => (-(A v) - B v).val) ≤
      2 * (massNormSq (E := E) (K := K) ρ π (fun v => (A v).val) +
        massNormSq (E := E) (K := K) ρ π (fun v => (B v).val)) := by
  have e : massNormSq (E := E) (K := K) ρ π (fun v => (-(A v) - B v).val) =
      massNormSq (E := E) (K := K) ρ π (fun v => ((0 - A v) + (0 - B v)).val) := by
    congr 1
    funext v
    rw [zero_sub, zero_sub, sub_eq_add_neg]
  have h := sqrt_massNormSq_add_le K ρ π hπ (fun v => 0 - A v) (fun v => 0 - B v)
  rw [massNormSq_zero_sub, massNormSq_zero_sub] at h
  have hA := CoupledEnergy.Variational.massNormSq_nonneg (K := K) ρ π hπ (fun v => (A v).val)
  have hB := CoupledEnergy.Variational.massNormSq_nonneg (K := K) ρ π hπ (fun v => (B v).val)
  have hsq := (Real.sqrt_le_iff.1 h).2
  rw [e]
  have h2 : (Real.sqrt (massNormSq (E := E) (K := K) ρ π (fun v => (A v).val)) +
      Real.sqrt (massNormSq (E := E) (K := K) ρ π (fun v => (B v).val))) ^ 2 ≤
      2 * (massNormSq (E := E) (K := K) ρ π (fun v => (A v).val) +
        massNormSq (E := E) (K := K) ρ π (fun v => (B v).val)) := by
    nlinarith [sq_nonneg (Real.sqrt (massNormSq (E := E) (K := K) ρ π (fun v => (A v).val)) -
      Real.sqrt (massNormSq (E := E) (K := K) ρ π (fun v => (B v).val))),
      Real.sq_sqrt hA, Real.sq_sqrt hB]
  exact hsq.trans h2

end Family

theorem wordsMass_real_bound {c₁ c₂ X₁ X₂ f : ℝ} (h₁ : Real.sqrt c₁ ≤ X₁)
    (h₂ : Real.sqrt c₂ ≤ X₂) :
    Real.sqrt (2 * f ^ 2 * (c₁ + c₂)) ≤ 2 * |f| * (X₁ + X₂) := by
  obtain ⟨hX₁, hc₁⟩ := Real.sqrt_le_iff.1 h₁
  obtain ⟨hX₂, hc₂⟩ := Real.sqrt_le_iff.1 h₂
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hf : f ^ 2 = |f| ^ 2 := (sq_abs f).symm
  rw [hf]
  have hcc : c₁ + c₂ ≤ (X₁ + X₂) ^ 2 := by nlinarith [mul_nonneg hX₁ hX₂]
  have := mul_le_mul_of_nonneg_left hcc (by positivity : (0 : ℝ) ≤ 2 * |f| ^ 2)
  nlinarith [sq_nonneg (|f| * (X₁ + X₂))]

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Error
namespace AVRegularity.Construction.Residual.Presentation

/-! # The word clause from the mass form: assembly (`residualWordsOfMass`) -/

theorem wordsMass_final_arith {f F S Q X₁ X₂ : ℝ} (hf0 : 0 ≤ f) (hfF : f ≤ F) (hX₁ : 0 ≤ X₁)
    (hX₂ : 0 ≤ X₂) (hS : S ≤ 2 * f * (X₁ + X₂)) (hQ : Q ≤ X₁) :
    S + f * Q ≤ 3 * F * (X₁ + X₂) := by
  have h1 : f * Q ≤ f * X₁ := mul_le_mul_of_nonneg_left hQ hf0
  have h2 : f * X₁ ≤ f * (X₁ + X₂) := mul_le_mul_of_nonneg_left (by linarith) hf0
  have h3 : f * (X₁ + X₂) ≤ F * (X₁ + X₂) := mul_le_mul_of_nonneg_right hfF (by linarith)
  linarith

/-- The residual norm bound for one word. -/
theorem wordsMass_word_bound {ι : Type} [Fintype ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (k : ℕ) (ν r : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (tp tf : ℝ)
    (R₁ R₂ : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (q : ∀ v, ℝ → TorusHk k (h v)) (X₁ X₂ : ℝ)
    (hF₁ : FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν r π (Set.Icc tp tf) R₁ X₁)
    (hF₂ : FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν r π (Set.Icc tp tf) R₂ X₂)
    (hq : ScalarMassLe (ι := ι) (h := h) (K := fun _ => k) r π (Set.Icc tp tf) q X₁)
    (j : ℕ) (hjk : j ≤ k) (β : DerivativeWord2 j) :
    residualNorm (ι := ι) (h := h) ν π (Set.Icc tp tf)
        (fun t x i v => r ^ j • (AVRegularity.torusJetOrder (-(R₁ v t) - R₂ v t) j β x) i)
        (fun t x v => r ^ j • AVRegularity.torusJetOrder (-(q v t)) j β x) ≤
      ENNReal.ofReal (3 * (k.factorial : ℝ) * (X₁ + X₂)) := by
  obtain ⟨hm₁, hb₁⟩ := hF₁
  obtain ⟨hm₂, hb₂⟩ := hF₂
  obtain ⟨hqi, hbq⟩ := hq
  set I : Set ℝ := Set.Icc tp tf with hI
  set f : ℝ := (j.factorial : ℝ) with hf
  have hf0 : 0 ≤ f := by positivity
  have hX₁ : 0 ≤ X₁ := (Real.sqrt_nonneg _).trans hb₁
  have hX₂ : 0 ≤ X₂ := (Real.sqrt_nonneg _).trans hb₂
  have hfk : f ≤ (k.factorial : ℝ) := by rw [hf]; exact_mod_cast Nat.factorial_le hjk
  let m₁ : ℝ → ℝ := fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
    (K := fun _ => k) r π (fun v => (R₁ v s).val)
  let m₂ : ℝ → ℝ := fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
    (K := fun _ => k) r π (fun v => (R₂ v s).val)
  let mq : ℝ → ℝ := fun s => massNormSq (E := h) (K := fun _ => k) r π (fun v => (q v s).val)
  have i₁ : Integrable m₁ (volume.restrict I) :=
    integrable_massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) r π R₁ hm₁
  have i₂ : Integrable m₂ (volume.restrict I) :=
    integrable_massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) r π R₂ hm₂
  have iq : Integrable (fun s => Real.sqrt (mq s)) (volume.restrict I) :=
    integrable_sqrt_massNormSq r π hπ q hqi
  have hm0 : ∀ s, 0 ≤ m₁ s := fun s => CoupledEnergy.Variational.massNormSq_nonneg
    (K := fun _ => k) r π hπ _
  have hm0' : ∀ s, 0 ≤ m₂ s := fun s => CoupledEnergy.Variational.massNormSq_nonneg
    (K := fun _ => k) r π hπ _
  have hmq0 : ∀ s, 0 ≤ mq s := fun s => CoupledEnergy.Variational.massNormSq_nonneg
    (K := fun _ => k) r π hπ _
  have hsq : ∀ s, Real.sqrt (f ^ 2 * mq s) = f * Real.sqrt (mq s) := fun s => by
    rw [Real.sqrt_mul (sq_nonneg f), Real.sqrt_sq hf0]
  unfold residualNorm
  refine le_trans (residual_split_le (MR := fun s => 2 * f ^ 2 * (m₁ s + m₂ s))
    (Mq := fun s => f ^ 2 * mq s) ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · intro t
    refine (wordsMass_flux_family_le r π hπ (fun v => -(R₁ v t) - R₂ v t)
      (fun _ => hjk) β).trans (ENNReal.ofReal_le_ofReal ?_)
    have := wordsMass_massNormSq_neg_sub_le (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => k) r π hπ (fun v => R₁ v t) (fun v => R₂ v t)
    show f ^ 2 * _ ≤ 2 * f ^ 2 * (m₁ t + m₂ t)
    nlinarith [sq_nonneg f]
  · intro t
    refine (wordsMass_family_le r π hπ (fun v => -(q v t)) (fun _ => hjk) β).trans
      (le_of_eq ?_)
    show _ = ENNReal.ofReal (f ^ 2 * mq t)
    congr 2
    have : ∀ v, -(q v t) = 0 - q v t := fun v => (zero_sub _).symm
    simp only [this]
    exact massNormSq_zero_sub (K := fun _ => k) r π (fun v => q v t)
  · intro t
    show 0 ≤ 2 * f ^ 2 * (m₁ t + m₂ t)
    exact mul_nonneg (mul_nonneg two_pos.le (sq_nonneg f)) (add_nonneg (hm0 t) (hm0' t))
  · intro t
    show 0 ≤ f ^ 2 * mq t
    exact mul_nonneg (sq_nonneg f) (hmq0 t)
  · exact (i₁.add i₂).const_mul _
  · refine (iq.const_mul f).congr (Filter.Eventually.of_forall fun t => ?_)
    exact (hsq t).symm
  · have e₁ : ∫ s in I, 2 * f ^ 2 * (m₁ s + m₂ s) =
        2 * f ^ 2 * ((∫ s in I, m₁ s) + ∫ s in I, m₂ s) := by
      rw [integral_const_mul, integral_add i₁ i₂]
    have e₂ : ∫ s in I, Real.sqrt (f ^ 2 * mq s) = f * ∫ s in I, Real.sqrt (mq s) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hsq)
    have hnn : 0 ≤ ∫ s in I, Real.sqrt (f ^ 2 * mq s) := integral_nonneg fun _ => Real.sqrt_nonneg _
    rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr₁ : Real.sqrt (ν⁻¹ * ∫ s in I, m₁ s) ≤ X₁ := hb₁
    have hr₂ : Real.sqrt (ν⁻¹ * ∫ s in I, m₂ s) ≤ X₂ := hb₂
    have key := wordsMass_real_bound (f := f) hr₁ hr₂
    rw [abs_of_nonneg hf0] at key
    have hk : ν⁻¹ * (∫ s in I, 2 * f ^ 2 * (m₁ s + m₂ s)) =
        2 * f ^ 2 * (ν⁻¹ * (∫ s in I, m₁ s) + ν⁻¹ * ∫ s in I, m₂ s) := by
      rw [e₁]; ring
    rw [hk, e₂]
    exact wordsMass_final_arith hf0 hfk hX₁ hX₂ key hbq

/-- **From the mass form to the word clause.** -/
theorem residualWordsOfMass : ResidualWordsOfMassStatement := by
  intro ι _ h _ _ _ _ _ _ k ν r π hπ tp tf R₁ R₂ q X₁ X₂ hF₁ hF₂ hq
  refine ⟨fun v => torusHk_aestronglyMeasurable_neg_sub (hF₁.1 v).aestronglyMeasurable
    (hF₂.1 v).aestronglyMeasurable, fun v => torusHk_aestronglyMeasurable_neg
    (hq.1 v).aestronglyMeasurable, ?_⟩
  intro j hjk β
  exact wordsMass_word_bound k ν r π hπ tp tf R₁ R₂ q X₁ X₂ hF₁ hF₂ hq j hjk β

end AVRegularity.Construction.Residual.Presentation
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The plain-to-kernel statement**.

`PlainToKernelStatementR` passes from the plain coupled system of the reconstruction to the kernel
system of the stage. Besides the reconstruction, it has three hypotheses, each used in the
proof:

* `2 ≤ Dm`: the lift of the kernel input at the order `k + Dm - 1` uses the regularizer clause of
  the invariant, which needs `2 ≤ Dm`;
* `φ₀` is smooth with support in the closed unit ball (the template of every kernel of the
  construction): the classical kernel average `applyClassical` of the fine flux is the operator
  `KernelSpec.op` and preserves `C^n`;
* `uh t ·` is `C^{D_m - 1}` and periodic on the window: the classical derivatives in `fineFluxF`
  have order at most `D_m - 1`, and are the weak jets of the lift (uniform in the slots `K`).

Width `0` kernels give `Ff = 0`. -/

/-- **From the plain coupled system of the reconstruction to the kernel system of the
stage.** -/
def PlainToKernelStatementR : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}, 2 ≤ Dm →
    ∀ (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ →
    Function.support φ₀ ⊆ closedEuclideanUnitBall →
    ∀ (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ)
    (G : GenStage D hr Dm b j₀) (m k : ℕ),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat kI tA tB S θK G → G.level = m →
    D.kap G.level = D.κ m → k ≤ kI.Ks →
    ∀ (π : CompIn G.comps → ℝ) (tp tf rs Xr : ℝ), tA ≤ tp → tf ≤ tB →
    ∀ (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (K : CompIn G.comps → ℕ)
      (hK : ∀ v, k ≤ K v)
      (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
      (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
      (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
      (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)),
      (∀ v, ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) (fun x => uh t x v) ∧
        IsZ2Periodic (fun x => uh t x v)) →
      IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK →
    ∀ (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))),
      IsFluxRealization (ι := CompIn G.comps) (h := fun v => hr v.1.root) k (Set.Icc tp tf)
        (fineFluxF P seedK freshK φ₀ G uh) Ff →
      (∀ v, MemLp (Ff v) 2 (volume.restrict (Set.Icc tp tf))) →
    ∃ ŷ : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) k tp tf
        (fun v => truncateTorusHk (hK v) (uK v tp))
        (fun v t => truncateTorusHk (hK v) (RK v t) + Ff v t)
        (fun v t => truncateTorusHk (hK v) (qK v t))
        (fun v t => truncateTorusHk (hK v) (uK v t))
        (fun v t => truncateTorusHk (Nat.succ_le_succ (hK v)) (wK v t)) ŷ

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Analysis.Convolution AVRegularity.EntryTerminal.Ingredients
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **From the plain coupled system of the reconstruction to the kernel system of the stage**:
the proof of `PlainToKernelStatementR`.

The kernel inputs are the regularizer lifts (`kerInput`) of the truncation of `wK` to the order
`k + 1`, with the carrier replaced by `0` on a measurable null set `N` of times where the lift
`wK` is not the lift of `uK`. The clauses of `IsKernelWeakSolutionTorus` are then: continuity,
square integrability, truncation and initial value (from the plain system), square integrability
and value of the inputs (`kerInput_memLp`, `kerInput_value`), and the weak identity
(`weak_clause`).

For `tp > tf` the window is empty and `ŷ = 0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Every function is square integrable on the empty set. -/
theorem memLp_restrict_empty {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    MemLp f 2 (volume.restrict (∅ : Set ℝ)) := by
  rw [Measure.restrict_empty]
  simp [MemLp]

/-- A kernel weak solution on an empty window is determined by the initial value. -/
theorem kernelWeak_of_empty {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    (ν t₀ t₁ : ℝ) (htf : ¬ t₀ ≤ t₁) (v : ℝ → Vec 2 → Vec 2) (k D : ℕ)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (f : ∀ i, TorusHk k (h i)) (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i)) (u : ∀ i, ℝ → TorusHk k (h i))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)) (hinit : ∀ i, u i t₀ = f i) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y := by
  have hI : Set.Icc t₀ t₁ = ∅ := Set.Icc_eq_empty htf
  have hae : ∀ p : ℝ → Prop, ∀ᵐ s ∂(volume.restrict (∅ : Set ℝ)), p s := fun p => by
    rw [Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  unfold IsKernelWeakSolutionTorus
  rw [hI]
  exact ⟨fun i => continuousOn_empty _, fun i => memLp_restrict_empty _, fun i => hae _, hinit,
    fun i j α => memLp_restrict_empty _, fun i j α => hae _, fun i t ht => absurd ht (Set.notMem_empty t)⟩


/-- A finite family of a.e. properties holds off one measurable null set. -/
theorem exists_bad_set {ι : Type*} [Finite ι] {μ : Measure ℝ} {p : ι → ℝ → Prop}
    (h : ∀ i, ∀ᵐ s ∂μ, p i s) :
    ∃ N : Set ℝ, MeasurableSet N ∧ (∀ᵐ s ∂μ, s ∉ N) ∧ ∀ s ∉ N, ∀ i, p i s := by
  have hg : ∀ᵐ s ∂μ, ∀ i, p i s := ae_all_iff.2 h
  obtain ⟨N, hNs, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hg)
  refine ⟨N, hNm, ae_iff.2 (by simpa using hN0), fun s hs i => ?_⟩
  by_contra hc
  exact hs (hNs (fun hall => hc (hall i)))

section Carrier

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The truncated carrier, replaced by `0` on `N`. -/
def kerCarrier {k : ℕ} {K : ι → ℕ} (hK : ∀ v, k ≤ K v)
    (wK : ∀ v : ι, ℝ → TorusHk (K v + 1) (h v)) (N : Set ℝ)
    [DecidablePred (· ∈ N)] (u : ι) (s : ℝ) : TorusHk (k + 1) (h u) :=
  if s ∈ N then 0 else truncateTorusHk (Nat.succ_le_succ (hK u)) (wK u s)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem kerCarrier_of_notMem {k : ℕ} {K : ι → ℕ} (hK : ∀ v, k ≤ K v)
    (wK : ∀ v : ι, ℝ → TorusHk (K v + 1) (h v))
    (N : Set ℝ) [DecidablePred (· ∈ N)] (u : ι) {s : ℝ} (hs : s ∉ N) :
    kerCarrier hK wK N u s = truncateTorusHk (Nat.succ_le_succ (hK u)) (wK u s) := by
  simp [kerCarrier, hs]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem kerCarrier_of_mem {k : ℕ} {K : ι → ℕ} (hK : ∀ v, k ≤ K v)
    (wK : ∀ v : ι, ℝ → TorusHk (K v + 1) (h v))
    (N : Set ℝ) [DecidablePred (· ∈ N)] (u : ι) {s : ℝ} (hs : s ∈ N) :
    kerCarrier hK wK N u s = 0 := by
  simp [kerCarrier, hs]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The modified carrier is square integrable. -/
theorem kerCarrier_memLp {k : ℕ} {K : ι → ℕ} (hK : ∀ v, k ≤ K v)
    (wK : ∀ v : ι, ℝ → TorusHk (K v + 1) (h v))
    (N : Set ℝ) [DecidablePred (· ∈ N)] (I : Set ℝ)
    (hNae : ∀ᵐ s ∂(volume.restrict I), s ∉ N)
    (hmem : ∀ u, MemLp (wK u) 2 (volume.restrict I)) (u : ι) :
    MemLp (kerCarrier hK wK N u) 2 (volume.restrict I) := by
  have h1 : MemLp (fun s => truncateTorusHk (Nat.succ_le_succ (hK u)) (wK u s)) 2
      (volume.restrict I) := (truncateTorusHk (Nat.succ_le_succ (hK u))).comp_memLp' (hmem u)
  refine h1.ae_eq ?_
  filter_upwards [hNae] with s hs
  exact (kerCarrier_of_notMem hK wK N u hs).symm

end Carrier

section PlainClauses

variable {G : GenStage D hr Dm b j₀} {m k : ℕ} {π : CompIn G.comps → ℝ}
  {tp tf rs Xr : ℝ} {uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root}
  {K : CompIn G.comps → ℕ} {hK : ∀ v, k ≤ K v}
  {uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)}
  {wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)}
  {RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
  {qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)}

theorem plain_cont (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK) :
    ∀ i, ContinuousOn (uK i) (Set.Icc tp tf) := fun i => hrec.plain.1 i

theorem plain_memLp (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK) :
    ∀ i, MemLp (wK i) 2 (volume.restrict (Set.Icc tp tf)) := fun i => hrec.plain.2.1 i

theorem plain_compat (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK) :
    ∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
      truncateTorusHk (Nat.le_succ (K i)) (wK i s) = uK i s := fun i => hrec.plain.2.2.1 i

theorem clause_cont (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK) :
    ∀ i, ContinuousOn (fun t => truncateTorusHk (hK i) (uK i t)) (Set.Icc tp tf) := fun i =>
  (truncateTorusHk (hK i)).continuous.comp_continuousOn (plain_cont hrec i)

theorem clause_memLp (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK) :
    ∀ i, MemLp (fun t => truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i t)) 2
      (volume.restrict (Set.Icc tp tf)) := fun i =>
  Providers.WeakGen.Reduction.truncate_memLp (Nat.succ_le_succ (hK i)) (plain_memLp hrec i)

theorem clause_trunc (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK) :
    ∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
      truncateTorusHk (Nat.le_succ k) (truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i s)) =
        truncateTorusHk (hK i) (uK i s) := fun i => by
  filter_upwards [plain_compat hrec i] with s hs
  rw [← hs]
  rfl

end PlainClauses

/-- The seven clauses give the regularized solution (all in reduced form). -/
theorem regSolution_of_clauses (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (m k : ℕ)
    (tp tf : ℝ) (K : CompIn G.comps → ℕ) (hK : ∀ v, k ≤ K v)
    (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (c1 : ∀ i, ContinuousOn (fun t => truncateTorusHk (hK i) (uK i t)) (Set.Icc tp tf))
    (c2 : ∀ i, MemLp (fun t => truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i t)) 2
      (volume.restrict (Set.Icc tp tf)))
    (c3 : ∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
      truncateTorusHk (Nat.le_succ k) (truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i s)) =
        truncateTorusHk (hK i) (uK i s))
    (c5 : ∀ v u (γ : G.fam.Γ v u), MemLp (Y v u γ) 2 (volume.restrict (Set.Icc tp tf)))
    (c6 : ∀ i j (α : G.fam.Γ i j), ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
      (Y i j α s).val (valueIndex2 (k + Dm - 1)) =
        G.sysS P seedK freshK φ₀ hφ₀ i j α s
          ((ContinuousLinearMap.id ℝ (hr j.1.root)).compLp
            ((truncateTorusHk (Nat.succ_le_succ (hK j)) (wK j s)).val (valueIndex2 (k + 1)))))
    (c7 : ∀ i, ∀ t ∈ Set.Icc tp tf, ∀ φ : TorusHk 1 (hr i.1.root),
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ m) tp t (streamVel (D.Φ m))
      ((truncateTorusHk (hK i) (uK i t)).toFunction.jet (valueIndex2 k))
      ((truncateTorusHk (hK i) (uK i tp)).toFunction.jet (valueIndex2 k))
      (φ.toFunction.jet (valueIndex2 1))
      (fun m' => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m'⟩)
      (fun s m' => (truncateTorusHk (Nat.succ_le_succ (hK i)) (wK i s)).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m'⟩)
      (kernelFlux G k Y i)
      (fun s => (truncateTorusHk (hK i) (RK i s) + Ff i s).toFunction.jet (valueIndex2 k))
      (fun s => (truncateTorusHk (hK i) (qK i s)).toFunction.jet (valueIndex2 k))) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) k tp tf
        (fun v => truncateTorusHk (hK v) (uK v tp))
        (fun v t => truncateTorusHk (hK v) (RK v t) + Ff v t)
        (fun v t => truncateTorusHk (hK v) (qK v t))
        (fun v t => truncateTorusHk (hK v) (uK v t))
        (fun v t => truncateTorusHk (Nat.succ_le_succ (hK v)) (wK v t)) Y :=
  ⟨c1, c2, c3, fun _ => rfl, c5, c6, c7⟩

/-- **The main case** `t_p ≤ t_f`. -/
theorem plain_to_kernel_main (G : GenStage D hr Dm b j₀) (hD : 2 ≤ Dm) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (m k : ℕ) (π : CompIn G.comps → ℝ) (tp tf rs Xr : ℝ) (htf : tp ≤ tf) (c : ℕ → ℝ)
    (hreg : ∀ v u (γ : G.fam.Γ v u), IsSpatialRegularizerTorus 1 k Dm tp tf c
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (K : CompIn G.comps → ℕ)
    (hK : ∀ v, k ≤ K v)
    (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (hsm : ∀ v, ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) (fun x => uh t x v) ∧
      IsZ2Periodic (fun x => uh t x v))
    (hrec : IsStageRecon G m k π tp tf rs uh Xr K hK uK wK RK qK)
    (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (hFf : IsFluxRealization (ι := CompIn G.comps) (h := fun v => hr v.1.root) k (Set.Icc tp tf)
      (fineFluxF P seedK freshK φ₀ G uh) Ff) :
    ∃ ŷ : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) k tp tf
        (fun v => truncateTorusHk (hK v) (uK v tp))
        (fun v t => truncateTorusHk (hK v) (RK v t) + Ff v t)
        (fun v t => truncateTorusHk (hK v) (qK v t))
        (fun v t => truncateTorusHk (hK v) (uK v t))
        (fun v t => truncateTorusHk (Nat.succ_le_succ (hK v)) (wK v t)) ŷ := by
  classical
  have hcont := plain_cont hrec
  have hmem := plain_memLp hrec
  have hcompat := plain_compat hrec
  obtain ⟨N, hNm, hNae, hgoodN⟩ := exists_bad_set hcompat
  let W' := kerCarrier hK wK N
  have hW'eq : ∀ u, ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
      W' u s = truncateTorusHk (Nat.succ_le_succ (hK u)) (wK u s) := fun u => by
    filter_upwards [hNae] with s hs
    exact kerCarrier_of_notMem hK wK N u hs
  have hW'mem := kerCarrier_memLp (ι := CompIn G.comps) (h := fun v => hr v.1.root) hK wK N
    (Set.Icc tp tf) hNae hmem
  have hY0 : ∀ s ∈ N, ∀ v u (γ : G.fam.Γ v u),
      kerInput G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hreg W' v u γ s = 0 := fun s hs v u γ => by
    exact kerInput_zero G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hreg W' v u γ s
      (kerCarrier_of_mem hK wK N u hs)
  have hYval : ∀ s ∈ Set.Icc tp tf, s ∉ N → ∀ v u (γ : G.fam.Γ v u),
      (kerInput G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hreg W' v u γ s).val
          (valueIndex2 (k + Dm - 1)) =
        G.sysS P seedK freshK φ₀ hφ₀ v u γ s ((wK u s).val (valueIndex2 (K u + 1))) :=
    fun s hs hsN v u γ => by
      rw [kerInput_value G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hreg W' v u γ s hs]
      rw [show W' u s = _ from kerCarrier_of_notMem hK wK N u hsN]
      rfl
  refine ⟨kerInput G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hreg W', ?_⟩
  refine regSolution_of_clauses G P seedK freshK φ₀ hφ₀ m k tp tf K hK uK wK RK qK Ff _
    (clause_cont hrec) (clause_memLp hrec) (clause_trunc hrec)
    (fun v u γ => kerInput_memLp G P seedK freshK φ₀ hφ₀ k hD tp tf htf c hreg W' hW'mem v u γ)
    (fun i j α => ?_) (fun i t ht φ => ?_)
  · filter_upwards [ae_restrict_mem measurableSet_Icc, hNae] with s hs hsN
    rw [hYval s hs hsN i j α]
    exact congrArg _ (Providers.WeakGen.Comparison.id_compLp_eq _).symm
  · exact weak_clause (hD := hD) hφs hφsupp hsm hrec hFf (D.hΦ m) hgoodN hY0 hYval hNae i t ht φ


/-- The case of an empty window: `ŷ = 0`. -/
theorem plain_to_kernel_empty (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (m k : ℕ)
    (tp tf : ℝ) (htf : ¬ tp ≤ tf) (K : CompIn G.comps → ℕ) (hK : ∀ v, k ≤ K v)
    (uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root))
    (Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    ∃ ŷ : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) k tp tf
        (fun v => truncateTorusHk (hK v) (uK v tp))
        (fun v t => truncateTorusHk (hK v) (RK v t) + Ff v t)
        (fun v t => truncateTorusHk (hK v) (qK v t))
        (fun v t => truncateTorusHk (hK v) (uK v t))
        (fun v t => truncateTorusHk (Nat.succ_le_succ (hK v)) (wK v t)) ŷ :=
  ⟨fun _ _ _ _ => 0, kernelWeak_of_empty _ tp tf htf _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => rfl)⟩

/-- **The plain-to-kernel statement.** -/
theorem plainToKernelStatementR : PlainToKernelStatementR := by
  intro hr _ _ _ _ _ _ D Dm b j₀ hDm law P seedK freshK φ₀ hφ₀ hφs hφsupp Mnat kI tA tB S θK G m k
    hinv hlev hkap hk π tp tf rs Xr htpA htfB uh K hK uK wK RK qK hsm hrec Ff hFf hFm
  by_cases htf : tp ≤ tf
  · obtain ⟨-, -, -, -, -, -, -, -, hker, -⟩ := hinv
    exact plain_to_kernel_main G hDm P seedK freshK φ₀ hφ₀ hφs hφsupp m k π tp tf rs Xr htf kI.cker
      (fun v u γ => isSpatialRegularizerTorus_mono_window
        ((hker v u γ).2.2.2.2 1 one_pos k hk) htpA htfB) uh K hK uK wK RK qK hsm hrec Ff hFf
  · exact plain_to_kernel_empty G P seedK freshK φ₀ hφ₀ m k tp tf htf K hK uK wK RK qK Ff

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
