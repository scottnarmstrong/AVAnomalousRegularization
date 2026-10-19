-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ChainLinear
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
public import AVRegularity.EntryWeak.SourceParameterPeriodicity
public import AVRegularity.CycleComparison.Coarse.Meas.Pairing
public import AVRegularity.CycleReference.MeanEnhancementScale
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
import AVRegularity.CycleJoint.TransitionAffineSampling
public import AVRegularity.CycleComparison.Reconstruction.GlueWeight
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseDefect
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Statements.Intermediate.Families.IsSampledEnvelope
import AVRegularity.CycleReference.CoreFlux
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Two-scale sampling of the source operator**, the edge analogue of
`sample_cell_operators` (`TwoScale.lean`).

With the scale law `√η ε = e/ρ`, the sampled covariant derivative is `e` times the label
derivative of the sample: `∂_{y_i}[Ψ(ρ⁻¹y, e⁻¹y)] = ρ⁻¹ ∂_{X_i}Ψ + e⁻¹ ∂_{z_i}Ψ
= e⁻¹ (∂_{z_i}Ψ + (e/ρ) ∂_{X_i}Ψ)`, so

* `sample_dEps`: `(D_{ε,i}Ψ)(ρ⁻¹y, e⁻¹y) = e ∂_{y_i}(SΨ)(y)`;
* `sample_dEpsWord`: `(D_ε^αΨ)(ρ⁻¹y, e⁻¹y) = e^{|α|} ∂^α_y(SΨ)(y)` (both fold the first letter
  innermost);
* `sample_sourceFlux`: the sampled source flux is the flux of the sampled field, with the label
  jets `e^{d-1} ∂^α_y(SΦ)`;
* `sample_sourceOp`, `sample_sourceOp_label`: the sampled source is `e` times the label divergence
  of the sampled flux.

Here `SΨ = twoScaleSample ρ e Ψ`, `y ↦ Ψ(ρ⁻¹y, e⁻¹y)`. Box smoothness is propagated through `dEps`
(`isBoxSmooth_dEps`, `isBoxSmooth_dEpsWord`) and through the source flux
(`isBoxSmooth_sourceFlux`). -/

section Words

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `D_{ε,i}` lowers the box orders by one. -/
theorem isBoxSmooth_dEps {Ψ : Vec 2 → Vec 2 → E} {sX sZ : ℕ}
    (hΨ : IsBoxSmooth (sX + 1) (sZ + 1) Ψ) (η ε : ℝ) (i : Fin 2) :
    IsBoxSmooth sX sZ (dEps η ε i Ψ) :=
  ((hΨ.fastPartial i).mono (Nat.le_succ sX) le_rfl).add
    (((hΨ.slowPartial i).mono le_rfl (Nat.le_succ sZ)).const_smul (Real.sqrt η * ε))

/-- A fold of `D_ε` along a list of length `n` lowers the box orders by `n`. -/
theorem isBoxSmooth_foldl_dEps (η ε : ℝ) (s : ℕ) (l : List (Fin 2)) {Ψ : Vec 2 → Vec 2 → E}
    (hΨ : IsBoxSmooth (s + l.length) (s + l.length) Ψ) :
    IsBoxSmooth s s (l.foldl (fun Ψ' i => dEps η ε i Ψ') Ψ) := by
  induction l generalizing Ψ with
  | nil => exact hΨ
  | cons i l ih =>
    rw [List.length_cons, ← Nat.add_assoc] at hΨ
    exact ih (isBoxSmooth_dEps hΨ η ε i)

/-- `D_ε^α` lowers the box orders by `|α|`. -/
theorem isBoxSmooth_dEpsWord (η ε : ℝ) {m : ℕ} (α : DerivativeWord2 m)
    {Ψ : Vec 2 → Vec 2 → E} {s : ℕ} (hΨ : IsBoxSmooth (s + m) (s + m) Ψ) :
    IsBoxSmooth s s (dEpsWord η ε α Ψ) := by
  have hΨ' : IsBoxSmooth (s + (List.ofFn α).length) (s + (List.ofFn α).length) Ψ := by
    rw [List.length_ofFn]
    exact hΨ
  exact isBoxSmooth_foldl_dEps η ε s (List.ofFn α) hΨ'

/-- The last letter of a word is the outermost `D_ε`. -/
theorem dEpsWord_snoc (η ε : ℝ) {m : ℕ} (β : DerivativeWord2 m) (i : Fin 2)
    (Ψ : Vec 2 → Vec 2 → E) :
    dEpsWord η ε (Fin.snoc β i : DerivativeWord2 (m + 1)) Ψ = dEps η ε i (dEpsWord η ε β Ψ) := by
  simp only [dEpsWord, List.ofFn_succ', List.concat_eq_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- **Sampled covariant derivative.** If `√η ε = e ρ⁻¹` and `e ≠ 0`, then
`(D_{ε,i}Ψ)(ρ⁻¹y, e⁻¹y) = e ∂_{y_i}(SΨ)(y)`. -/
theorem sample_dEps {Ψ : Vec 2 → Vec 2 → E} {sX sZ : ℕ} (hΨ : IsBoxSmooth sX sZ Ψ)
    (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) {η ε ρ e : ℝ} (he : e ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (i : Fin 2) (y : Vec 2) :
    dEps η ε i Ψ (ρ⁻¹ • y) (e⁻¹ • y) = e • fderiv ℝ (twoScaleSample ρ e Ψ) y (basisVec i) := by
  simp only [dEps]
  rw [sample_fderiv hΨ hX hZ ρ e y i, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ he,
    one_smul, ← hscale]
  exact add_comm _ _

/-- **Sampled covariant words.** If `√η ε = e ρ⁻¹`, `e ≠ 0` and `Ψ` is box smooth of order
`(m, m)`, then for every word `α` of length `m`,
`(D_ε^αΨ)(ρ⁻¹y, e⁻¹y) = e^m ∂^α_y(SΨ)(y)`. -/
theorem sample_dEpsWord {η ε ρ e : ℝ} (he : e ≠ 0) (hscale : Real.sqrt η * ε = e * ρ⁻¹) :
    ∀ {m : ℕ} (α : DerivativeWord2 m) {Ψ : Vec 2 → Vec 2 → E}, IsBoxSmooth m m Ψ →
      ∀ y : Vec 2, dEpsWord η ε α Ψ (ρ⁻¹ • y) (e⁻¹ • y) =
        e ^ m • orderedDerivative α (twoScaleSample ρ e Ψ) y := by
  intro m
  induction m with
  | zero =>
    intro α Ψ _ y
    simp only [dEpsWord, orderedDerivative, twoScaleSample, List.ofFn_zero, List.foldl_nil,
      pow_zero, one_smul]
  | succ n ih =>
    intro α Ψ hΨ y
    obtain ⟨β, i, rfl⟩ : ∃ (β : DerivativeWord2 n) (i : Fin 2),
        α = (Fin.snoc β i : DerivativeWord2 (n + 1)) :=
      ⟨Fin.init α, α (Fin.last n), (Fin.snoc_init_self α).symm⟩
    have hΨn : IsBoxSmooth n n Ψ := hΨ.mono (by omega) (by omega)
    have hB : IsBoxSmooth 1 1 (dEpsWord η ε β Ψ) :=
      isBoxSmooth_dEpsWord η ε β (s := 1) (hΨ.mono (by omega) (by omega))
    have hfun : twoScaleSample ρ e (dEpsWord η ε β Ψ) =
        (e ^ n) • orderedDerivative β (twoScaleSample ρ e Ψ) :=
      funext fun y' => ih β hΨn y'
    have hinv : Invertible (e ^ n) := invertibleOfNonzero (pow_ne_zero n he)
    rw [dEpsWord_snoc, sample_dEps hB le_rfl le_rfl he hscale i y, hfun,
      fderiv_const_smul_of_invertible (e ^ n), AVRegularity.Sampling.orderedDerivative_snoc]
    simp only [_root_.smul_apply, smul_smul, pow_succ']

end Words

section Source

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- **Box smoothness of the source flux.** If every edge coefficient is box smooth of order
`(s, s)` and `Φ` of order `(N, N)` with `s + D ≤ N + 1` (so `s + |α| ≤ N` for all words of the
orders `d ≤ D`), the source flux is box smooth of order `(s, s)`. -/
theorem isBoxSmooth_sourceFlux (edge : ConstituentEdges D h) (η ε t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) {s N : ℕ}
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth s s (fun X z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth N N Φ) (hN : s + D ≤ N + 1) :
    IsBoxSmooth s s (sourceFlux edge η ε t Φ k) := by
  have he : sourceFlux edge η ε t Φ k = fun X z v => ∑ u : ι, ∑ d : Finset.Icc 2 D,
      ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
        γ.coeff α t X z k • γ.map (dEpsWord η ε α Φ X z u)).sum := rfl
  rw [he]
  apply AVRegularity.CycleComparison.Lift.isBoxSmooth_pi
  intro v
  apply IsBoxSmooth.sum
  intro u _
  apply IsBoxSmooth.sum
  intro d _
  apply AVRegularity.CycleComparison.Lift.isBoxSmooth_list_sum
  intro γ hγ
  apply IsBoxSmooth.sum
  intro α _
  have hd := Finset.mem_Icc.mp d.2
  have hw : IsBoxSmooth s s (dEpsWord η ε α Φ) :=
    isBoxSmooth_dEpsWord η ε α (hΦ.mono (by omega) (by omega))
  have hscalar := (hΓ v u d γ hγ α).clm_comp (ContinuousLinearMap.proj k)
  have hvector := hw.clm_comp (γ.map.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using!
    AVRegularity.CycleComparison.Lift.isBoxSmooth_bilinear hscalar hvector
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)

/-- **Sampled source flux.** If `√η ε = e ρ⁻¹`, `e ≠ 0` and `Φ` is box smooth of order `(D, D)`,
the sampled source flux is the source flux of the sample, the covariant words becoming the label
jets `e^{d-1} ∂^α_y(SΦ)`. -/
theorem sample_sourceFlux (edge : ConstituentEdges D h) {η ε ρ e : ℝ} (he : e ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (t : ℝ) {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : IsBoxSmooth D D Φ) (k : Fin 2) (y : Vec 2) (v : ι) :
    sourceFlux edge η ε t Φ k (ρ⁻¹ • y) (e⁻¹ • y) v =
      ∑ u : ι, ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
        ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α t (ρ⁻¹ • y) (e⁻¹ • y) k) •
          γ.map (e ^ (d.1 - 1) • orderedDerivative α (twoScaleSample ρ e Φ) y u)).sum := by
  have hW : ∀ (d : Finset.Icc 2 D) (α : DerivativeWord2 (d.1 - 1)) (u : ι),
      dEpsWord η ε α Φ (ρ⁻¹ • y) (e⁻¹ • y) u =
        e ^ (d.1 - 1) • orderedDerivative α (twoScaleSample ρ e Φ) y u := by
    intro d α u
    have hd := (Finset.mem_Icc.mp d.2).2
    rw [sample_dEpsWord he hscale α (hΦ.mono (by omega) (by omega)) y, Pi.smul_apply]
  simp only [sourceFlux, hW]

/-- **Sampled source operator.** If `√η ε = e ρ⁻¹`, `e ≠ 0`, the edge coefficients are box smooth
of order `(1, 1)` and `Φ` of order `(D, D)`, the sampled source is `e` times the label divergence
of the sampled flux: `(𝒮_ε Φ)(ρ⁻¹y, e⁻¹y) = e ∑_k ∂_{y_k}(S flux_k)(y)`. -/
theorem sample_sourceOp (edge : ConstituentEdges D h) {η ε ρ e : ℝ} (he : e ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (t : ℝ) {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth 1 1 (fun X z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth D D Φ) (y : Vec 2) :
    sourceOp edge η ε t Φ (ρ⁻¹ • y) (e⁻¹ • y) =
      e • ∑ k : Fin 2, fderiv ℝ (twoScaleSample ρ e (sourceFlux edge η ε t Φ k)) y
        (basisVec k) := by
  show ∑ k : Fin 2, dEps η ε k (sourceFlux edge η ε t Φ k) (ρ⁻¹ • y) (e⁻¹ • y) = _
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => sample_dEps
    (isBoxSmooth_sourceFlux edge η ε t Φ k hΓ hΦ (by omega)) le_rfl le_rfl he hscale k y

/-- **The sampled source is `e` times the label divergence of the label flux**
`y ↦ ∑_{u,d,γ,α} γ.coeff α t (ρ⁻¹y) (e⁻¹y) k • γ.map (e^{d-1} ∂^α_y(SΦ)(y)_u)`. -/
theorem sample_sourceOp_label (edge : ConstituentEdges D h) {η ε ρ e : ℝ} (he : e ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (t : ℝ) {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth 1 1 (fun X z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth D D Φ) (y : Vec 2) :
    sourceOp edge η ε t Φ (ρ⁻¹ • y) (e⁻¹ • y) =
      e • ∑ k : Fin 2, fderiv ℝ (fun (y' : Vec 2) (v : ι) => ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α t (ρ⁻¹ • y') (e⁻¹ • y') k) •
            γ.map (e ^ (d.1 - 1) • orderedDerivative α (twoScaleSample ρ e Φ) y' u)).sum) y
        (basisVec k) := by
  have hfun : ∀ k : Fin 2, twoScaleSample ρ e (sourceFlux edge η ε t Φ k) =
      fun (y' : Vec 2) (v : ι) => ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α t (ρ⁻¹ • y') (e⁻¹ • y') k) •
            γ.map (e ^ (d.1 - 1) • orderedDerivative α (twoScaleSample ρ e Φ) y' u)).sum :=
    fun k => funext fun y' => funext fun v => sample_sourceFlux edge he hscale t hΦ k y' v
  rw [sample_sourceOp edge he hscale t hΓ hΦ y]
  simp only [hfun]

end Source

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Torus Sobolev carriers of finitely smooth periodic fields.** A `ℤ²`-periodic field of class
`C^K` has a torus Sobolev element of order `K` whose jets are its ordered classical derivatives
(the finite-order version of `EntryWeakProofs.smoothPeriodicHk`). This packages the physical
lift `û(t) = 𝒯a(t)`, which is only finitely smooth, as a torus Sobolev trajectory.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem rawJet_hasWeakJet_of_contDiff (K : ℕ) {f : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f) :
    HasOrderedWeakJetOn Set.univ (EntryWeakProofs.smoothPeriodicRawJet K f) := by
  intro j w i e
  have hs : ContDiff ℝ 1 (orderedDerivative w f) :=
    ChartTransport.contDiff_orderedDerivative (p := 1) w
      (hf.of_le (by exact_mod_cast (show 1 + j.val ≤ K by have := j.isLt; omega)))
  have he := EntryWeakProofs.smooth_vector_weak_coordinate hs i e
  have hn : orderedDerivative (Fin.snoc w i) f =
      fun x => (fderiv ℝ (orderedDerivative w f) x) (basisVec i) := by
    rw [orderedDerivative_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (orderedDerivative w f x))
    (fun x => inner ℝ e (orderedDerivative (Fin.snoc w i) f x))
  rw [hn]
  exact he

variable [MeasurableSpace E] [BorelSpace E]

/-- The torus Sobolev element of a `C^K` periodic field. -/
def periodicHk (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) : TorusHk K E :=
  (show TorusHkFunction K E from ⟨EntryWeakProofs.smoothPeriodicRawJet K f,
    (fun a => ChartTransport.isZ2Periodic_orderedDerivative a.2 hp),
    (fun a => Coarse.memLp_two_cell_of_continuous
      (ChartTransport.contDiff_orderedDerivative (p := 0) a.2
        (hf.of_le (by exact_mod_cast (show 0 + a.1.val ≤ K by have := a.1.isLt; omega)))).continuous),
    rawJet_hasWeakJet_of_contDiff K hf⟩).toHk

theorem periodicHk_jet_ae (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) (a : JetIndex2 K) :
    (periodicHk K f hf hp).val a =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative a.2 f :=
  torusJetToL2_ae _ _ a

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleComparison.Reconstruction

/-! Time derivatives of the renewal charts and the chart stream increment off the renewal block.

* The chart `χ(t,y) = X_{m-1}(t, y, lτ'')` (`ocChart`) is the flow of `b_{m-1} = ∇^⊥φ` from the
  time `lτ''`, so `∂_t χ(t,y) = b(t, χ(t,y))`.
* The label `ψ(t,x) = X_{m-1}(lτ'', x, t)` (`ocChartInv`) is the flow read at the start time,
  so `∂_t ψ(t,x) = -Dψ(t,x) b(t,x)` (the transport equation of the labels,
  `AVenhance.Infra.Flow.flow_initialTime_hasDerivAt`). The time derivative is jointly smooth.
* The stream increment of the chart `l` is the reference pulse stream at every time at which every
  active pulse carries the label `l`. This generalizes `chartStreamIncrement_eq_ocPulseStream` from
  the renewal block `[(l-½)τ'', (l+½)τ'']` to that hypothesis. In particular it holds when the only
  possibly active pulse is `k` and `ocLabel k = l` (and `ocLabel = ocPulseChartIndex`,
  `ocLabel_eq_ocPulseChartIndex`). -/

section Derivatives

variable (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ)

/-- `∂_t χ(t,y) = b(t, χ(t,y))`. -/
theorem ocChart_hasDerivAt_time (t : ℝ) (y : Vec 2) :
    HasDerivAt (fun t' => ocChart α q Λ m φ hφ l t' y)
      (streamVel φ t (ocChart α q Λ m φ hφ l t y)) t :=
  (flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz).2 y
    ((l : ℝ) * ocTauPP α q Λ m) t

/-- The time derivative `b(t, χ(t,y))` of the chart is jointly smooth in `(t,y)`. -/
theorem ocChart_timeDeriv_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      streamVel φ p.1 (ocChart α q Λ m φ hφ l p.1 p.2)) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocChart α q Λ m φ hφ l p.1 p.2) :=
    (CycleReference.streamFlow_joint_smooth hφ).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  exact hv.comp (contDiff_fst.prodMk hc)

end Derivatives

section Increment

/-- The chart form of the next stream at a time at which every active pulse carries the label
`l` (the renewal block condition of `CycleReference.ocNextStream_in_chart` is one sufficient
condition, by `CycleReference.pulse_label_on_block`). -/
theorem ocNextStream_in_chart_of_labels {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ) (t : ℝ)
    (hlab : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t ≠ 0 → ocLabel α q Λ m k = l) (y : Vec 2) :
    ocNextStream α q Λ ζ m φ hφ t (ocChart α q Λ m φ hφ l t y) =
      φ t (ocChart α q Λ m φ hφ l t y) + ocPulseStream α q Λ ζ m t y := by
  classical
  let f : ℤ → ℝ := fun k => ocPulse α q Λ ζ m k t * ocShear α q Λ m k
    (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t
      (ocChart α q Λ m φ hφ l t y) ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m))
  have hs : Function.support f ⊆ {k : ℤ | Odd k} := by
    intro k hk
    by_contra h
    apply hk
    dsimp [f]
    rw [CycleReference.ocShear_zero_of_not_odd α q Λ m h, mul_zero]
  change φ t (ocChart α q Λ m φ hφ l t y) + (∑' k : ℤ, f k) = _
  congr 1
  rw [← tsum_subtype_eq_of_support_subset hs]
  unfold ocPulseStream
  apply tsum_congr
  intro k
  by_cases hp : ocPulse α q Λ ζ m k.1 t = 0
  · simp [f, hp]
  · have hl := hlab k.1 k.2 hp
    have hgroup :=
      (CycleReference.streamFlowHomeomorph hφ t ((l : ℝ) * ocTauPP α q Λ m)).left_inv y
    change AVRegularity.streamFlow φ hφ ((l : ℝ) * ocTauPP α q Λ m)
      (ocChart α q Λ m φ hφ l t y) t = y at hgroup
    dsimp [f]
    rw [hl]
    change ocPulse α q Λ ζ m k.1 t * ocShear α q Λ m k.1
      (AVRegularity.streamFlow φ hφ ((l : ℝ) * ocTauPP α q Λ m)
        (ocChart α q Λ m φ hφ l t y) t) = _
    rw [hgroup]

/-- **Chart stream increment off the renewal block.** At a time at which every active pulse
carries the label `l`, the stream increment of the chart `l` is the reference pulse stream. -/
theorem chartStreamIncrement_eq_ocPulseStream_of_labels {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1))) (l : ℤ) (t : ℝ)
    (hlab : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t ≠ 0 → ocLabel α q Λ m k = l) (y : Vec 2) :
    CycleReference.chartStreamIncrement hφ ((l : ℝ) * ocTauPP α q Λ m) (Φ m) t y =
      ocPulseStream α q Λ ζ m t y := by
  obtain ⟨hprev, hrec⟩ := hseq.2 m hm
  have hh : hprev = hφ := Subsingleton.elim _ _
  rw [hh] at hrec
  unfold CycleReference.chartStreamIncrement
  rw [hrec]
  change ocNextStream α q Λ ζ m (Φ (m - 1)) hφ t (ocChart α q Λ m (Φ (m - 1)) hφ l t y) -
    Φ (m - 1) t (ocChart α q Λ m (Φ (m - 1)) hφ l t y) = _
  rw [ocNextStream_in_chart_of_labels hφ l t hlab]
  ring

/-- If no odd pulse other than `k` is active at `t`, every active odd pulse carries the label of
`k`. -/
theorem labels_of_isolated {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {k : ℤ} {t : ℝ}
    (hiso : ∀ k' : ℤ, Odd k' → k' ≠ k → ocPulse α q Λ ζ m k' t = 0) :
    ∀ k' : ℤ, Odd k' → ocPulse α q Λ ζ m k' t ≠ 0 → ocLabel α q Λ m k' = ocLabel α q Λ m k := by
  intro k' hodd hk'
  by_cases hkk : k' = k
  · rw [hkk]
  · exact absurd (hiso k' hodd hkk) hk'

/-- **Isolated pulse.** If no pulse other than `k` is active at `t` and `l` is the label of `k`,
the stream increment of the chart `l` is the reference pulse stream at `t`. -/
theorem chartStreamIncrement_eq_ocPulseStream_of_isolated {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1))) (k l : ℤ)
    (hkl : ocLabel α q Λ m k = l) (t : ℝ)
    (hiso : ∀ k' : ℤ, Odd k' → k' ≠ k → ocPulse α q Λ ζ m k' t = 0) (y : Vec 2) :
    CycleReference.chartStreamIncrement hφ ((l : ℝ) * ocTauPP α q Λ m) (Φ m) t y =
      ocPulseStream α q Λ ζ m t y :=
  chartStreamIncrement_eq_ocPulseStream_of_labels hseq hm hφ l t
    (fun k' hodd hk' => (labels_of_isolated hiso k' hodd hk').trans hkl) y

end Increment

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The edge coefficients from a sampled envelope**. Under a sampled envelope the
edge coefficients are continuous in space at every time of the window
(`edgeCoefficient_continuous_of_sampled`) and bounded uniformly on the window
(`edgeCoefficient_bound_of_sampled`). -/

/-- An abstract division bound. -/
theorem le_of_mul_div_mul_le {a c f x y : ℝ} (ha : 0 < a) (hc : 0 < c) (hf : 0 < f)
    (hxy : a * (x / c * f) ≤ y) : x ≤ y * c / (a * f) := by
  rw [le_div_iff₀ (mul_pos ha hf)]
  have e : x * (a * f) = a * (x / c * f) * c := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right hxy hc.le

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **The edge coefficients are continuous in space** at the times of the window of a sampled
envelope. -/
theorem edgeCoefficient_continuous_of_sampled (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (K : ι → ℕ) (actual : ∀ p, Ctx p) {t₀ t₁ ν e E ρ C : ℝ} {b : ι → ι → ℝ}
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b) (v u : ι)
    (d : admissibleOrders K D v u) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    Continuous (edgeCoefficient F ν e E actual K v u d t) := by
  change Continuous (fun x => ∑ γ : F.Γ v u, constituentPhysical F ν e E actual v u γ d.1 t x)
  exact continuous_finsetSum _ fun γ _ => (hfwd.1 v u γ d.1 t ht).continuous

/-- **The edge coefficients are bounded on the window of a sampled envelope.** -/
theorem edgeCoefficient_bound_of_sampled (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (actual : ∀ p, Ctx p) {t₀ t₁ ν e E ρ C : ℝ}
    {b : ι → ι → ℝ} (hν : 0 < ν) (hρ : 0 < ρ)
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b) (hCb : ∀ v u, 0 ≤ C * b v u) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ t ∈ Set.Icc t₀ t₁, ∀ v u (d : admissibleOrders K D v u) x,
      ‖edgeCoefficient F ν e E actual K v u d t x‖ ≤ CA := by
  obtain ⟨T, hT⟩ : ∃ T : ι → ι → ℕ → ℝ, ∀ v u d, T v u d = C * b v u * (ν * ρ ^ (d - 2)) /
      (Real.sqrt (π u / π v) * (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hT0 : ∀ v u d, 0 ≤ T v u d := fun v u d => by
    rw [hT]
    have := hCb v u
    positivity
  refine ⟨∑ v, ∑ u, ∑ d ∈ admissibleOrders K D v u, T v u d,
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ =>
      hT0 v u d, fun t ht v u d x => ?_⟩
  have hd : d.1 ∈ Finset.Icc 2 D := (Finset.mem_filter.1 d.2).1
  have hb := CycleJointProofs.sampledEnvelope_physicalCoefficient_normalized_bound (P := P) F π K
    actual t₀ t₁ ν e E ρ C b hν hρ hfwd v u (hCb v u) d.1 hd t ht x
  have hpos1 : 0 < Real.sqrt (π u / π v) := Real.sqrt_pos.2 (div_pos (hπ u) (hπ v))
  have hpos2 : 0 < ν * ρ ^ (d.1 - 2) := mul_pos hν (pow_pos hρ _)
  have hpos3 : 0 < ((K v + d.1 - 2).factorial : ℝ) / ((K v).factorial : ℝ) := by positivity
  have h1 := le_of_mul_div_mul_le hpos1 hpos2 hpos3 hb
  have h2 : ‖edgeCoefficient F ν e E actual K v u d t x‖ ≤ T v u d.1 := by
    rw [hT]
    exact h1
  refine h2.trans ?_
  refine (Finset.single_le_sum (f := fun d => T v u d) (fun d _ => hT0 v u d) d.2).trans ?_
  refine (Finset.single_le_sum (f := fun u => ∑ d ∈ admissibleOrders K D v u, T v u d)
    (fun u _ => Finset.sum_nonneg fun d _ => hT0 v u d) (Finset.mem_univ u)).trans ?_
  exact Finset.single_le_sum (f := fun v => ∑ u, ∑ d ∈ admissibleOrders K D v u, T v u d)
    (fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ => hT0 v u d)
    (Finset.mem_univ v)

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The chain rule behind the physical edge coefficient**.

Exact Piola transports flux by `(DΦR)∘Φ⁻¹` and scalars by composition; the divergence pairing
and the scalar norm are preserved, and chart jets pay the chain rule.

Let `χ` be a smooth chart (label `y` ↦ physical `x`) with smooth inverse `ψ` (the label map), and
let `K = chartInvJacobian ψ`, so that `K(x) = (Dψ(x))⁻¹ = Dχ(ψ x)`
(`chartInvJacobian_eq_of_inverse`). The label derivative `∂_{y_i}` acts on functions of `x` as
`∑_a K_{ai}(x) ∂_{x_a}`, and the order-lowering recursion `transitionT` records the
coefficients of the label derivative `∂^I_y` in the physical derivatives `∂^A_x`: for `u = V ∘ ψ`,
`(∂^I V)(ψ x) = ∑_{|A| ≤ |I|} T_{I,A}(x) (∂^A u)(x)` (`transitionT_chain`).

In `transitionT` the first letter of each word is the *outermost* derivative, while
`orderedDerivative` applies the first letter *innermost*. The chain rule is first proved for the
outer-first derivative `outerListDeriv` (`outerListDeriv_chain`, no symmetry needed), and the two
orders are then identified by the symmetry of smooth derivatives (`outerListDeriv_ofFn`). The
coefficients `T_{I,A}` vanish for `|A| > |I|`
(`CycleJointProofs.transitionT_zero_above_native_order`), so the sum stops at `|I|`. -/

section Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous linear map on the plane in the standard basis: `L v = ∑_k v_k L e_k`. -/
theorem transition_clm_apply_eq_sum (L : Vec 2 →L[ℝ] E) (v : Vec 2) :
    L v = ∑ k : Fin 2, v k • L (basisVec k) := by
  calc L v = L (∑ k : Fin 2, v k • basisVec k) := by
        rw [← AVRegularity.ChartTransport.vec2_eq_sum_basisVec v]
    _ = ∑ k : Fin 2, v k • L (basisVec k) := by
        rw [map_sum]
        simp only [map_smul]

end Basis

section Jacobian

/-- The entries of `chartJacobian`: `J_{ia}(y) = ∂_a Υ_i(y)`. -/
theorem chartJacobian_apply (Υ : Vec 2 → Vec 2) (y : Vec 2) (i a : Fin 2) :
    chartJacobian Υ y i a = fderiv ℝ Υ y (basisVec a) i := rfl

/-- For mutually inverse differentiable planar maps (chart `χ`, label map `ψ`), the inverse
Jacobian of the label map at `x` is the Jacobian of the chart at the label `ψ x`:
`(Dψ(x))⁻¹ = Dχ(ψ x)`. -/
theorem chartInvJacobian_eq_of_inverse {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (x : Vec 2) :
    chartInvJacobian ψ x = chartJacobian χ (ψ x) := by
  have hfun : ψ ∘ χ = id := funext hψχ
  have h1 : HasFDerivAt (ψ ∘ χ) ((fderiv ℝ ψ (χ (ψ x))).comp (fderiv ℝ χ (ψ x))) (ψ x) :=
    (hψ (χ (ψ x))).hasFDerivAt.comp (ψ x) (hχ (ψ x)).hasFDerivAt
  rw [hfun] at h1
  have h2 := h1.unique (hasFDerivAt_id (ψ x))
  rw [hχψ x] at h2
  have h3 : ∀ j : Fin 2, fderiv ℝ ψ x (fderiv ℝ χ (ψ x) (basisVec j)) = basisVec j := by
    intro j
    have h4 := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (basisVec j)) h2
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h4
  unfold chartInvJacobian
  apply Matrix.inv_eq_right_inv
  ext i j
  have h5 := congrFun (h3 j) i
  rw [transition_clm_apply_eq_sum (fderiv ℝ ψ x), Finset.sum_apply] at h5
  have h6 : (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = basisVec j i := by
    rw [Matrix.one_apply, basisVec_apply]
  rw [Matrix.mul_apply, h6, ← h5]
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp only [chartJacobian, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Entrywise form of `chartInvJacobian_eq_of_inverse`: `K_{ai}(x) = ∂_i χ_a(ψ x)`. -/
theorem chartInvJacobian_apply_of_inverse {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (x : Vec 2) (a i : Fin 2) :
    chartInvJacobian ψ x a i = fderiv ℝ χ (ψ x) (basisVec i) a := by
  rw [chartInvJacobian_eq_of_inverse hχ hψ hψχ hχψ x, chartJacobian_apply]

/-- The entries of the inverse Jacobian of a smooth label map with smooth inverse are smooth. -/
theorem chartInvJacobian_entry_contDiff {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (a i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => chartInvJacobian ψ x a i) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ χ y) :=
    hχ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ χ y (basisVec i)) :=
    h1.clm_apply contDiff_const
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ χ y (basisVec i) a) := contDiff_pi.1 h2 a
  simp only [chartInvJacobian_apply_of_inverse (hχ.differentiable (by simp))
    (hψ.differentiable (by simp)) hψχ hχψ]
  exact h3.comp hψ

end Jacobian

/-! ### Outer-first derivatives along lists -/

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative along a list of letters with the **first letter outermost**,
`∂^{[i₁,…,iₘ]} g = ∂_{i₁}(⋯(∂_{iₘ} g))`: the convention of the recursion `transitionT`. -/
def outerListDeriv (l : List (Fin 2)) (g : Vec 2 → E) : Vec 2 → E :=
  l.foldr (fun i g' => fun x => fderiv ℝ g' x (basisVec i)) g

theorem outerListDeriv_cons_apply (i : Fin 2) (l : List (Fin 2)) (g : Vec 2 → E) (x : Vec 2) :
    outerListDeriv (i :: l) g x = fderiv ℝ (outerListDeriv l g) x (basisVec i) := rfl

/-- The outer-first derivative along `l` is the inner-first derivative along the reversed list. -/
theorem outerListDeriv_eq_reverse (l : List (Fin 2)) (g : Vec 2 → E) :
    outerListDeriv l g = AVRegularity.CycleComparison.Lift.orderedListDerivative l.reverse g :=
  (List.foldl_reverse (l := l) (f := fun (g' : Vec 2 → E) (k : Fin 2) =>
    AVRegularity.CycleComparison.Lift.coordinateDerivative k g') (b := g)).symm

theorem outerListDeriv_contDiff (l : List (Fin 2)) {g : Vec 2 → E}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (outerListDeriv l g) := by
  rw [outerListDeriv_eq_reverse]
  exact AVRegularity.CycleComparison.Lift.orderedListDerivative_contDiff _ g hg

/-- For smooth `g`, the outer-first derivative along a word is its `orderedDerivative`
(symmetry of smooth derivatives). -/
theorem outerListDeriv_ofFn {g : Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {m : ℕ}
    (A : DerivativeWord2 m) : outerListDeriv (List.ofFn A) g = orderedDerivative A g := by
  have h := AVRegularity.CycleComparison.Lift.orderedListDerivative_perm
    (List.reverse_perm (List.ofFn A)) g hg
  rw [outerListDeriv_eq_reverse]
  exact h

/-! ### Auxiliary sum manipulations -/

/-- Summing over words of length `s + 1` is summing over first letters and remaining words. -/
theorem transition_sum_word_succ {M : Type*} [AddCommMonoid M] {s : ℕ}
    (F : DerivativeWord2 (s + 1) → M) :
    ∑ A : DerivativeWord2 (s + 1), F A =
      ∑ a : Fin 2, ∑ A₀ : DerivativeWord2 s, F (Fin.cons a A₀ : Fin (s + 1) → Fin 2) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => Fin 2)) F, Fintype.sum_prod_type]
  rfl

/-- The derivative of a finite word-indexed sum of scalar multiples (Leibniz rule). -/
theorem transition_fderiv_wordSum_apply (s : Finset ℕ)
    (c : ∀ r, DerivativeWord2 r → Vec 2 → ℝ) (f : ∀ r, DerivativeWord2 r → Vec 2 → E)
    (hc : ∀ r A, Differentiable ℝ (c r A)) (hf : ∀ r A, Differentiable ℝ (f r A))
    (x v : Vec 2) :
    fderiv ℝ (fun y => ∑ r ∈ s, ∑ A : DerivativeWord2 r, c r A y • f r A y) x v =
      ∑ r ∈ s, ∑ A : DerivativeWord2 r,
        (c r A x • fderiv ℝ (f r A) x v + fderiv ℝ (c r A) x v • f r A x) := by
  have hA : ∀ (r : ℕ) (A : DerivativeWord2 r),
      DifferentiableAt ℝ (fun y => c r A y • f r A y) x :=
    fun r A => ((hc r A) x).fun_smul ((hf r A) x)
  have hr : ∀ r : ℕ,
      DifferentiableAt ℝ (fun y => ∑ A : DerivativeWord2 r, c r A y • f r A y) x :=
    fun r => DifferentiableAt.fun_sum fun A _ => hA r A
  rw [fderiv_fun_sum fun r _ => hr r, _root_.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [fderiv_fun_sum fun A _ => hA r A, _root_.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [fderiv_fun_smul ((hc r A) x) ((hf r A) x)]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply]

/-- Regrouping the one-step chain rule: the derivative falls either on the coefficient or on the
physical jet. -/
theorem transition_sum_regroup {m : ℕ} (k : Fin 2 → ℝ) (t : ∀ r, DerivativeWord2 r → ℝ)
    (dt : Fin 2 → ∀ r, DerivativeWord2 r → ℝ) (w : ∀ r, DerivativeWord2 r → E)
    (wb : Fin 2 → ∀ r, DerivativeWord2 r → E) :
    ∑ b : Fin 2, k b • ∑ r ∈ Finset.range m, ∑ A : DerivativeWord2 r,
        (t r A • wb b r A + dt b r A • w r A) =
      (∑ r ∈ Finset.range m, ∑ b : Fin 2, ∑ A : DerivativeWord2 r, (k b * t r A) • wb b r A) +
        ∑ r ∈ Finset.range m, ∑ A : DerivativeWord2 r,
          (∑ b : Fin 2, k b * dt b r A) • w r A := by
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib, smul_smul, Finset.sum_smul]
  congr 1
  · exact Finset.sum_comm
  · exact Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

/-- Peeling the order-raising sum: split each coefficient as `p + (tc - p)`, drop the top order
of the `p`-part and the bottom order of the `(tc - p)`-part. -/
theorem transition_sum_peel {m : ℕ} (tc p : ∀ r, DerivativeWord2 r → ℝ)
    (w : ∀ r, DerivativeWord2 r → E) (j : ℕ → E) (hp : ∀ A : DerivativeWord2 m, p m A = 0)
    (h0 : ∀ A : DerivativeWord2 0, tc 0 A = p 0 A)
    (hj : ∀ s, ∑ A : DerivativeWord2 (s + 1), (tc (s + 1) A - p (s + 1) A) • w (s + 1) A =
      j s) :
    ∑ r ∈ Finset.range (m + 1), ∑ A : DerivativeWord2 r, tc r A • w r A =
      ∑ r ∈ Finset.range m, j r +
        ∑ r ∈ Finset.range m, ∑ A : DerivativeWord2 r, p r A • w r A := by
  have hsplit : ∀ r, ∑ A : DerivativeWord2 r, tc r A • w r A =
      ∑ A : DerivativeWord2 r, p r A • w r A +
        ∑ A : DerivativeWord2 r, (tc r A - p r A) • w r A := by
    intro r
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← add_smul]
    congr 1
    ring
  have hP : ∑ A : DerivativeWord2 m, p m A • w m A = 0 :=
    Finset.sum_eq_zero fun A _ => by rw [hp A, zero_smul]
  have hZ : ∑ A : DerivativeWord2 0, (tc 0 A - p 0 A) • w 0 A = 0 :=
    Finset.sum_eq_zero fun A _ => by rw [h0 A, sub_self, zero_smul]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun r => ∑ A : DerivativeWord2 r, p r A • w r A) m,
    Finset.sum_range_succ' (fun r => ∑ A : DerivativeWord2 r, (tc r A - p r A) • w r A) m]
  simp only [hP, hZ, add_zero, hj]
  exact add_comm _ _

/-! ### The recursion `transitionT` -/

theorem transitionT_cons_nil_apply (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2)
    (I : List (Fin 2)) (x : Vec 2) :
    transitionT K (i :: I) [] x =
      ∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I []) x (basisVec b) := by
  simp only [transitionT, add_zero]

theorem transitionT_cons_cons_apply (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i a : Fin 2)
    (I A : List (Fin 2)) (x : Vec 2) :
    transitionT K (i :: I) (a :: A) x =
      (∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I (a :: A)) x (basisVec b)) +
        K x a i * transitionT K I A x := by
  simp only [transitionT]

/-- The right side of the chain rule, `∑_{|A| ≤ |I|} T_{I,A}(x) ∂^A u(x)`, with the physical
derivatives taken first letter outermost. -/
def transitionSum (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (I : List (Fin 2)) (u : Vec 2 → E) :
    Vec 2 → E := fun x =>
  ∑ r ∈ Finset.range (I.length + 1), ∑ A : DerivativeWord2 r,
    transitionT K I (List.ofFn A) x • outerListDeriv (List.ofFn A) u x

theorem transitionSum_contDiff {K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hK : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x a i)) (I : List (Fin 2)) {u : Vec 2 → E}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) : ContDiff ℝ (⊤ : ℕ∞) (transitionSum K I u) := by
  unfold transitionSum
  exact ContDiff.sum fun _ _ => ContDiff.sum fun A _ =>
    (AVRegularity.CycleJointProofs.transitionT_spatial_smooth K hK I (List.ofFn A)).fun_smul
      (outerListDeriv_contDiff (List.ofFn A) hu)

/-! ### The chain rule -/

/-- **Chain rule, outer-first form.** If `χ` and `ψ` are smooth and mutually inverse and
`K(x) = Dχ(ψ x)` (entrywise, `K_{ai}(x) = ∂_i χ_a(ψ x)`), then for every smooth `V` and every
list `I`, `(∂^I V)(ψ x) = ∑_{|A| ≤ |I|} T_{I,A}(x) (∂^A (V ∘ ψ))(x)`, all derivatives first letter
outermost. -/
theorem outerListDeriv_chain {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hK : ∀ x a i, K x a i = fderiv ℝ χ (ψ x) (basisVec i) a)
    (hKs : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x a i))
    {V : Vec 2 → E} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (I : List (Fin 2)) :
    (fun x => outerListDeriv I V (ψ x)) = transitionSum K I (V ∘ ψ) := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (V ∘ ψ) := hV.comp hψ
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  induction I with
  | nil =>
    funext x
    show V (ψ x) = ∑ r ∈ Finset.range 1, ∑ A : DerivativeWord2 r,
      transitionT K [] (List.ofFn A) x • outerListDeriv (List.ofFn A) (V ∘ ψ) x
    rw [Finset.sum_range_one]
    simp only [Fintype.sum_unique, List.ofFn_zero]
    exact (one_smul ℝ (V (ψ x))).symm
  | cons i I ih =>
    have hSd : Differentiable ℝ (transitionSum K I (V ∘ ψ)) :=
      (transitionSum_contDiff hKs I hu).differentiable (by simp)
    -- the label derivative `∂^I V` read through the chart
    have h1 : outerListDeriv I V = transitionSum K I (V ∘ ψ) ∘ χ := by
      funext y
      have hy : outerListDeriv I V (ψ (χ y)) = transitionSum K I (V ∘ ψ) (χ y) :=
        congrFun ih (χ y)
      rw [hψχ y] at hy
      exact hy
    funext x
    have hdT : ∀ (r : ℕ) (A : DerivativeWord2 r),
        Differentiable ℝ (transitionT K I (List.ofFn A)) := fun _ A =>
      (AVRegularity.CycleJointProofs.transitionT_spatial_smooth K hKs I
        (List.ofFn A)).differentiable (by simp)
    have hdD : ∀ (r : ℕ) (A : DerivativeWord2 r),
        Differentiable ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) := fun _ A =>
      (outerListDeriv_contDiff (List.ofFn A) hu).differentiable (by simp)
    have hderiv : ∀ b : Fin 2, fderiv ℝ (transitionSum K I (V ∘ ψ)) x (basisVec b) =
        ∑ r ∈ Finset.range (I.length + 1), ∑ A : DerivativeWord2 r,
          (transitionT K I (List.ofFn A) x •
              fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b) +
            fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) •
              outerListDeriv (List.ofFn A) (V ∘ ψ) x) := fun b =>
      transition_fderiv_wordSum_apply (Finset.range (I.length + 1))
        (fun _ A => transitionT K I (List.ofFn A))
        (fun _ A => outerListDeriv (List.ofFn A) (V ∘ ψ)) hdT hdD x (basisVec b)
    -- one label derivative: `∂_{y_i} = ∑_b K_{bi} ∂_{x_b}`
    have hchain : outerListDeriv (i :: I) V (ψ x) =
        ∑ b : Fin 2, K x b i • ∑ r ∈ Finset.range (I.length + 1), ∑ A : DerivativeWord2 r,
          (transitionT K I (List.ofFn A) x •
              fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b) +
            fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) •
              outerListDeriv (List.ofFn A) (V ∘ ψ) x) := by
      rw [outerListDeriv_cons_apply, h1, fderiv_comp (ψ x) (hSd (χ (ψ x))) (hχd (ψ x)),
        ContinuousLinearMap.comp_apply, hχψ x,
        transition_clm_apply_eq_sum (fderiv ℝ (transitionSum K I (V ∘ ψ)) x)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hK x b i, hderiv b]
    -- the top order of the derivative part vanishes
    have hp : ∀ A : DerivativeWord2 (I.length + 1),
        ∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) = 0 := by
      intro A
      rw [AVRegularity.CycleJointProofs.transitionT_zero_above_native_order K I (List.ofFn A)
        (by rw [List.length_ofFn]; omega)]
      simp
    -- the empty output word has no order-lowering part
    have h0 : ∀ A : DerivativeWord2 0, transitionT K (i :: I) (List.ofFn A) x =
        ∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) := by
      intro A
      rw [List.ofFn_zero, transitionT_cons_nil_apply]
    -- the order-lowering part of `T_{(i,I),(a,A₀)}` is `K_{ai} T_{I,A₀}`
    have hj : ∀ s : ℕ, ∑ A : DerivativeWord2 (s + 1),
        (transitionT K (i :: I) (List.ofFn A) x -
            ∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b)) •
          outerListDeriv (List.ofFn A) (V ∘ ψ) x =
        ∑ b : Fin 2, ∑ A : DerivativeWord2 s, (K x b i * transitionT K I (List.ofFn A) x) •
          fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b) := by
      intro s
      rw [transition_sum_word_succ]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      simp only [List.ofFn_cons]
      rw [transitionT_cons_cons_apply, outerListDeriv_cons_apply]
      congr 1
      ring
    exact hchain.trans ((transition_sum_regroup (m := I.length + 1) (fun b => K x b i)
      (fun _ A => transitionT K I (List.ofFn A) x)
      (fun b _ A => fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b))
      (fun _ A => outerListDeriv (List.ofFn A) (V ∘ ψ) x)
      (fun b _ A => fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b))).trans
      (transition_sum_peel (m := I.length + 1)
        (fun _ A => transitionT K (i :: I) (List.ofFn A) x)
        (fun _ A => ∑ b : Fin 2, K x b i *
          fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b))
        (fun _ A => outerListDeriv (List.ofFn A) (V ∘ ψ) x)
        (fun s => ∑ b : Fin 2, ∑ A : DerivativeWord2 s,
          (K x b i * transitionT K I (List.ofFn A) x) •
            fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b))
        hp h0 hj).symm)

/-- **The chain rule behind the physical edge coefficient** (`transitionT_chain`). Let `χ`
(chart) and `ψ` (label map) be smooth and mutually inverse, `K = chartInvJacobian ψ`, `V` smooth
and `u = V ∘ ψ`. For every word `I` of length `m` and every `x`,
`(∂^I V)(ψ x) = ∑_{r ≤ m} ∑_{|A| = r} T_{I,A}(x) (∂^A u)(x)`. -/
theorem transitionT_chain {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {V : Vec 2 → E} (hV : ContDiff ℝ (⊤ : ℕ∞) V) {m : ℕ} (I : DerivativeWord2 m) (x : Vec 2) :
    orderedDerivative I V (ψ x) =
      ∑ r ∈ Finset.range (m + 1), ∑ A : DerivativeWord2 r,
        transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x •
          orderedDerivative A (V ∘ ψ) x := by
  have hmain : outerListDeriv (List.ofFn I) V (ψ x) =
      transitionSum (chartInvJacobian ψ) (List.ofFn I) (V ∘ ψ) x :=
    congrFun (outerListDeriv_chain hχ hψ hψχ hχψ
      (chartInvJacobian_apply_of_inverse (hχ.differentiable (by simp))
        (hψ.differentiable (by simp)) hψχ hχψ)
      (chartInvJacobian_entry_contDiff hχ hψ hψχ hχψ) hV (List.ofFn I)) x
  rw [outerListDeriv_ofFn hV I] at hmain
  rw [hmain]
  simp only [transitionSum, List.length_ofFn, outerListDeriv_ofFn (hV.comp hψ)]

end ChainRule

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Tested time identities of the retained coarse field.** The exact defect identity
`(M I - E) W = div F_coarse`, `W(t₀) = f` (`IsCoarseDefect`) is an integrated `L²`-duality identity
(`CoupledWeakIdentity`) at every time `t ∈ [t₀, t₁]` and for every `H¹` test. Tested against a `C¹`
`ℤ²`-periodic field `ψ` (through its torus carrier `periodicHk 1 ψ`, whose jets are a.e. `ψ` and
`∂_k ψ`), the pairing `t ↦ ∫_{cell} ⟪W_v(t), ψ⟫` is of integral type on `[t₀, t₁]` (`IsPrimOn`),
with density the right side of the weak identity written with `ψ` and `∂_k ψ` (`coarseTestedRhs`);
at `t = t₀` the pairing is `∫_{cell} ⟪f_v, ψ⟫`. These are the time coefficients of the finite-rank
approximants of the coarse field (`coarseApprox`), which the time-dependent lift identity consumes.
-/

/-! ### Integrated weak identities are of integral type -/

/-- **Integrated weak identities are of integral type.** If the integrated identity holds at every
`t ∈ [t₀, t₁]` (with the time-dependent value `u t`), then `t ↦ ∫ ⟪u(t), φ⟫` is of integral type on
`[t₀, t₁]` with the tested right side as density. -/
theorem isPrimOn_of_coupledWeakIdentity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : Measure (Vec 2)) (ν : ℝ) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (b : ℝ → Vec 2 → Vec 2) (u : ℝ → Vec 2 → E) (f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E) (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E)
    (hW : ∀ t ∈ Icc t₀ t₁, CoupledWeakIdentity μ ν t₀ t b (u t) f φ dφ du flux F g) :
    IsPrimOn t₀ t₁ (fun t => ∫ x, inner ℝ (u t x) (φ x) ∂μ)
      (fun s => ∫ x, AVRegularity.Weighted.weakIdentityRhs ν b φ dφ du flux F g s x ∂μ) := by
  have hint : IntegrableOn
      (fun s => ∫ x, AVRegularity.Weighted.weakIdentityRhs ν b φ dφ du flux F g s x ∂μ)
      (Ioc t₀ t₁) := (hW t₁ ⟨ht, le_rfl⟩).2.2.2.1
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hint, fun t htt => ?_⟩
  have hid : (∫ x, inner ℝ (u t x) (φ x) ∂μ) - ∫ x, inner ℝ (f x) (φ x) ∂μ =
      ∫ s in Ioc t₀ t, ∫ x, AVRegularity.Weighted.weakIdentityRhs ν b φ dφ du flux F g s x ∂μ :=
    (hW t htt).2.2.2.2
  have hid₀ : (∫ x, inner ℝ (u t₀ x) (φ x) ∂μ) - ∫ x, inner ℝ (f x) (φ x) ∂μ =
      ∫ s in Ioc t₀ t₀, ∫ x, AVRegularity.Weighted.weakIdentityRhs ν b φ dφ du flux F g s x ∂μ :=
    (hW t₀ ⟨le_rfl, ht⟩).2.2.2.2
  rw [Ioc_self, Measure.restrict_empty, integral_zero_measure] at hid₀
  show (∫ x, inner ℝ (u t x) (φ x) ∂μ) = (∫ x, inner ℝ (u t₀ x) (φ x) ∂μ) +
    ∫ σ in t₀..t, ∫ x, AVRegularity.Weighted.weakIdentityRhs ν b φ dφ du flux F g σ x ∂μ
  rw [intervalIntegral.integral_of_le htt.1]
  linarith

/-- At the initial time the integrated identity reads `∫ ⟪u, φ⟫ = ∫ ⟪f, φ⟫`. -/
theorem coupledWeakIdentity_initial_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : Measure (Vec 2)) (ν t₀ : ℝ) (b : ℝ → Vec 2 → Vec 2)
    (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hW : CoupledWeakIdentity μ ν t₀ t₀ b u f φ dφ du flux F g) :
    ∫ x, inner ℝ (u x) (φ x) ∂μ = ∫ x, inner ℝ (f x) (φ x) ∂μ := by
  have hid : (∫ x, inner ℝ (u x) (φ x) ∂μ) - ∫ x, inner ℝ (f x) (φ x) ∂μ =
      ∫ s in Ioc t₀ t₀, ∫ x, AVRegularity.Weighted.weakIdentityRhs ν b φ dφ du flux F g s x ∂μ :=
    hW.2.2.2.2
  rw [Ioc_self, Measure.restrict_empty, integral_zero_measure] at hid
  exact sub_eq_zero.1 hid

/-! ### The torus carrier of a `C¹` periodic test -/

/-- The empty word of the value index differentiates nothing. -/
theorem orderedDerivative_valueIndex2_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec 2 → E) : orderedDerivative (valueIndex2 1).2 g = g :=
  AVRegularity.orderedDerivative_zero g _

/-- A word of length one is one coordinate derivative. -/
theorem orderedDerivative_one_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : DerivativeWord2 1) (g : Vec 2 → E) :
    orderedDerivative α g = fun X => fderiv ℝ g X (basisVec (α 0)) := by
  simp [orderedDerivative, List.ofFn_succ]

/-- The order cast used by the finite-order carrier `periodicHk`. -/
theorem contDiff_one_natCast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : Vec 2 → E} (hψ : ContDiff ℝ 1 ψ) : ContDiff ℝ ((1 : ℕ) : ℕ∞) ψ := by
  exact_mod_cast hψ

/-- The value jet of the carrier of a `C¹` periodic test is a.e. the test. -/
theorem periodicHk_one_value_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (ψ : Vec 2 → E)
    (hψ : ContDiff ℝ ((1 : ℕ) : ℕ∞) ψ) (hψp : AVenhance.IsZ2Periodic ψ) :
    (periodicHk 1 ψ hψ hψp).toFunction.jet (valueIndex2 1)
      =ᵐ[volume.restrict AVenhance.unitCube] ψ :=
  (periodicJetRepresentative_ae (periodicHk 1 ψ hψ hψp).val (valueIndex2 1)).trans
    ((periodicHk_jet_ae 1 ψ hψ hψp (valueIndex2 1)).trans
      (Filter.EventuallyEq.of_eq (orderedDerivative_valueIndex2_one ψ)))

/-- The first-order jets of the carrier of a `C¹` periodic test are a.e. its coordinate
derivatives `∂_j ψ`. -/
theorem periodicHk_one_deriv_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (ψ : Vec 2 → E)
    (hψ : ContDiff ℝ ((1 : ℕ) : ℕ∞) ψ) (hψp : AVenhance.IsZ2Periodic ψ) (j : Fin 2) :
    (periodicHk 1 ψ hψ hψp).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => j⟩
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => fderiv ℝ ψ x (basisVec j) :=
  (periodicJetRepresentative_ae (periodicHk 1 ψ hψ hψp).val
      ⟨⟨1, Nat.one_lt_two⟩, fun _ => j⟩).trans
    ((periodicHk_jet_ae 1 ψ hψ hψp ⟨⟨1, Nat.one_lt_two⟩, fun _ => j⟩).trans
      (Filter.EventuallyEq.of_eq (orderedDerivative_one_eq_fderiv (fun _ => j) ψ)))

/-! ### The coarse defect identity tested against a smooth periodic field -/

/-- The right side of the coarse defect identity `(∂_t + 𝐛·∇ - BΔ) W = div(flux + F_coarse)`
(component `v`, time `s`, point `x`) tested against `ψ`, with `ψ` and `∂_j ψ` in place of the
jets of the test:
`-∑_j b_j ⟪∂_j W_v, ψ⟫ - B ∑_j ⟪∂_j W_v, ∂_j ψ⟫ - ∑_j ⟪flux_j + (F_coarse)_j, ∂_j ψ⟫`. -/
def coarseTestedRhs {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K k : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (ψ : Vec 2 → h v)
    (s : ℝ) (x : Vec 2) : ℝ :=
  -(∑ j : Fin 2, b s x j * inner ℝ (torusJetOrder (W v s) 1 (fun _ => j) x) (ψ x))
    - B * ∑ j : Fin 2, inner ℝ (torusJetOrder (W v s) 1 (fun _ => j) x)
        (fderiv ℝ ψ x (basisVec j))
    - ∑ j : Fin 2, inner ℝ (coarseDefectFlux B D H AD CE Jm W v s x j +
        (Fc v s).toFunction.jet (valueIndex2 k) x j) (fderiv ℝ ψ x (basisVec j))

/-- The weak right side with zero value forcing is `coarseTestedRhs`. -/
theorem weakIdentityRhs_eq_coarseTestedRhs {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K k : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (ψ : Vec 2 → h v)
    (s : ℝ) (x : Vec 2) :
    AVRegularity.Weighted.weakIdentityRhs B b ψ (fun j y => fderiv ℝ ψ y (basisVec j))
        (fun σ j => torusJetOrder (W v σ) 1 (fun _ => j))
        (fun σ y => coarseDefectFlux B D H AD CE Jm W v σ y)
        (fun σ => (Fc v σ).toFunction.jet (valueIndex2 k)) (fun _ _ => 0) s x =
      coarseTestedRhs B b D H AD CE Jm W Fc v ψ s x := by
  simp only [AVRegularity.Weighted.weakIdentityRhs, coarseTestedRhs, inner_zero_left, add_zero]

/-- **The coarse defect identity tested against a `C¹` periodic field** at one time
`t ∈ [t₀, t₁]`: the weak identity of `IsCoarseDefect` with `ψ`, `∂_j ψ` in place of the jets of
the test. -/
theorem coarseDefect_tested_identity {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H k N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hW : IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc) (v : ι) (ψ : Vec 2 → h v)
    (hψ : ContDiff ℝ ((1 : ℕ) : ℕ∞) ψ) (hψp : AVenhance.IsZ2Periodic ψ) (t : ℝ)
    (ht : t ∈ Icc t₀ t₁) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) B t₀ t b
      ((W v t).toFunction.jet (valueIndex2 (k + 1 + D))) ((f v).toFunction.jet (valueIndex2 N))
      ψ (fun j x => fderiv ℝ ψ x (basisVec j)) (fun s j => torusJetOrder (W v s) 1 (fun _ => j))
      (fun s x => coarseDefectFlux B D H AD CE Jm W v s x)
      (fun s => (Fc v s).toFunction.jet (valueIndex2 k)) (fun _ _ => 0) :=
  AVRegularity.CycleJointProofs.coupledWeakIdentity_test_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (periodicHk_one_value_ae ψ hψ hψp) (periodicHk_one_deriv_ae ψ hψ hψp)
    (hW v t ht (periodicHk 1 ψ hψ hψp))

/-- **Tested time identity of the coarse field.** For a `C¹` `ℤ²`-periodic field `ψ`, the cell
pairing `t ↦ ∫_{cell} ⟪W_v(t), ψ⟫` is of integral type on `[t₀, t₁]`, with density the tested
right side `∫_{cell} coarseTestedRhs`. -/
theorem coarseDefect_tested_prim {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H k N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hW : IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc) (ht : t₀ ≤ t₁) (v : ι)
    (ψ : Vec 2 → h v) (hψ : ContDiff ℝ 1 ψ) (hψp : AVenhance.IsZ2Periodic ψ) :
    IsPrimOn t₀ t₁
      (fun t => ∫ x in AVenhance.unitCube,
        inner ℝ ((W v t).toFunction.jet (valueIndex2 (k + 1 + D)) x) (ψ x))
      (fun s => ∫ x in AVenhance.unitCube, coarseTestedRhs B b D H AD CE Jm W Fc v ψ s x) := by
  have hψ1 : ContDiff ℝ ((1 : ℕ) : ℕ∞) ψ := contDiff_one_natCast hψ
  refine (isPrimOn_of_coupledWeakIdentity (volume.restrict AVenhance.unitCube) B ht b
    (fun t => (W v t).toFunction.jet (valueIndex2 (k + 1 + D)))
    ((f v).toFunction.jet (valueIndex2 N)) ψ (fun j x => fderiv ℝ ψ x (basisVec j))
    (fun s j => torusJetOrder (W v s) 1 (fun _ => j))
    (fun s x => coarseDefectFlux B D H AD CE Jm W v s x)
    (fun s => (Fc v s).toFunction.jet (valueIndex2 k)) (fun _ _ => 0)
    (fun t htt => coarseDefect_tested_identity hW v ψ hψ1 hψp t htt)).congr ht
    (fun _ _ => rfl) (fun s _ => ?_)
  beta_reduce
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact weakIdentityRhs_eq_coarseTestedRhs B b D H AD CE Jm W Fc v ψ s x

/-- **The tested coarse field starts at the datum:** `∫_{cell} ⟪W_v(t₀), ψ⟫ = ∫_{cell} ⟪f_v, ψ⟫`
(the weak identity at `t = t₀`). -/
theorem coarseDefect_tested_initial {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H k N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hW : IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc) (ht : t₀ ≤ t₁) (v : ι)
    (ψ : Vec 2 → h v) (hψ : ContDiff ℝ 1 ψ) (hψp : AVenhance.IsZ2Periodic ψ) :
    ∫ x in AVenhance.unitCube, inner ℝ ((W v t₀).toFunction.jet (valueIndex2 (k + 1 + D)) x) (ψ x) =
      ∫ x in AVenhance.unitCube, inner ℝ ((f v).toFunction.jet (valueIndex2 N) x) (ψ x) :=
  coupledWeakIdentity_initial_eq _ _ _ _ _ _ _ _ _ _ _ _
    (coarseDefect_tested_identity hW v ψ (contDiff_one_natCast hψ) hψp t₀ ⟨le_rfl, ht⟩)

end AVRegularity.CycleComparison.Reconstruction
end
end
