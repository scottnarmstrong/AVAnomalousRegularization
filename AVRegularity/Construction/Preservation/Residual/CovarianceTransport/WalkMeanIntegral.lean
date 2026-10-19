-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeMeanActionAssembly
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseSum
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativePreparedTime
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeSplitInput
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVenhance.Infra.Classical.Drift

section
section
/-! Literal scalar mean actions under genuine sequence and source regularity,
without a normalized transverse setting. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Averaging removes the fast metric flux and commutes with the slow derivative. -/
theorem flux_cross_mean {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (v : Vec 2 → Vec 2)
    (Φ Ψ : Vec 2 → Vec 2 → E) (hΦ : GoodField 1 Φ) (hΨ : GoodField 1 Ψ)
    (hv : Continuous v) (X : Vec 2) (k : Fin 2) :
    fieldCellMean (fun z =>
      ((Real.sqrt η * v z k) • Φ X z -
        Real.sqrt η • ∑ j : Fin 2, G X k j • fastPartial j Φ X z) -
        η • ∑ j : Fin 2, G X k j • slowPartial j Ψ X z) =
      fieldCellMean (fun z => (Real.sqrt η * v z k) • Φ X z) -
        η • ∑ j : Fin 2, G X k j •
          fderiv ℝ (fun Y => fieldCellMean (Ψ Y)) X (basisVec j) := by
  have hD : Continuous (fun z => (Real.sqrt η * v z k) • Φ X z) :=
    (continuous_const.mul ((continuous_apply k).comp hv)).smul (hΦ.continuous_slice X)
  have hF : Continuous (fun z => Real.sqrt η •
      ∑ j : Fin 2, G X k j • fastPartial j Φ X z) :=
    (continuous_finsetSum _ fun j _ =>
      ((hΦ.fastPartial j).continuous_slice X).const_smul (G X k j)).const_smul _
  have hS : Continuous (fun z => η • ∑ j : Fin 2, G X k j • slowPartial j Ψ X z) :=
    (continuous_finsetSum _ fun j _ =>
      ((hΨ.slowPartial j).continuous_slice X).const_smul (G X k j)).const_smul _
  have hf0 : fieldCellMean (fun z => Real.sqrt η •
      ∑ j : Fin 2, G X k j • fastPartial j Φ X z) = 0 := by
    rw [fieldCellMean_smul, fieldCellMean_sum Finset.univ
      (f := fun j z => G X k j • fastPartial j Φ X z)
      (fun j _ => ((hΦ.fastPartial j).continuous_slice X).const_smul (G X k j))]
    simp only [fieldCellMean_smul]
    have hz : ∀ j, fieldCellMean (fun z => fastPartial j Φ X z) = 0 :=
      fun j => (GoodField.cent_fastPartial (c := True) hΦ j).2 trivial X
    simp only [hz, smul_zero, Finset.sum_const_zero]
  let d := fun z => (Real.sqrt η * v z k) • Φ X z
  let f := fun z => Real.sqrt η • ∑ j : Fin 2, G X k j • fastPartial j Φ X z
  let s := fun z => η • ∑ j : Fin 2, G X k j • slowPartial j Ψ X z
  change fieldCellMean ((d - f) - s) = _
  calc
    _ = fieldCellMean (d - f) - fieldCellMean s := fieldCellMean_sub (hD.sub hF) hS
    _ = (fieldCellMean d - fieldCellMean f) - fieldCellMean s :=
      congrArg (fun y => y - fieldCellMean s) (fieldCellMean_sub hD hF)
    _ = _ := by
      rw [hf0, sub_zero]
      dsimp only [d, s]
      rw [fieldCellMean_smul, fieldCellMean_sum Finset.univ
        (f := fun j z => G X k j • slowPartial j Ψ X z)
        (fun j _ => ((hΨ.slowPartial j).continuous_slice X).const_smul (G X k j))]
      simp only [fieldCellMean_smul, fieldCellMean_slowPartial hΨ.1 X]

section ScalarSequence
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D N H sX sZ : ℕ} {a b : ℝ}
  {Q : LiftOperatorData ι (fun _ => ℝ) D}
  {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}

/-- The positive-grade literal mean identity with sequence regularity discharged. -/
theorem scalar_positive_mean_of_sequence
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hD : 1 ≤ D)
    (hX : D ≤ sX) (hZ : D ≤ sZ)
    (hh n : ℕ) (hhpos : hh ≠ 0) (hhh : hh ≤ H) (hn : 2 ≤ n)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) (k : Fin 2) (v : ι)
    (hG : ∀ i j, ContDiff ℝ (0 : ℕ∞) (fun Y => Q.G t Y i j))
    (hv : Continuous (Q.v t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z)) :
    fieldCellMean (fun y => liftFluxX Q Cc (fun _ => f) hh n t X y k) v =
      liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k) (fun _ => f) t X z v := by
  apply (positiveMeanFluxCoefficient_literal_apply Q hD Cc hh n hn hhpos f hf k t X z v
    hG hv _ _ _ _ _ hΓ).symm
  · exact liftApply_goodField_of_seq Q hseq (by omega) (by omega) hhh (n - 1) hf ht
  · exact liftApply_centField_of_seq Q hseq (by omega) (by omega) hhh
      (Or.inr (by omega)) hf ht
  · intro m hm α u
    exact ((hseq.2.2.2.2.2.1 hh hhh (n - 1) m α v u t ht).1.1 X).continuous
  · intro j hj m hm α u u'
    exact (hseq.2.2.2.2.2.1 (hh - 1) (by omega) (n - 1 - j) m α u u' t ht).1.mono
      (by omega) (by omega)
  · intro q
    exact liftApply_goodField_of_seq Q hseq hX hZ (by omega) q hf ht

/-- The diagonal literal mean identity retains exactly the molecular degree-two term. -/
theorem scalar_diagonal_mean_of_sequence
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    (n : ℕ) (hn : 2 ≤ n) (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) (k : Fin 2)
    (hv : Continuous (Q.v t)) :
    fieldCellMean (fun y => liftFluxX Q Cc (fun _ => f) 0 n t X y k) =
      liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k) (fun _ => f) t X z := by
  let Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t
  have hΦ : GoodField 1 Φ := liftApply_goodField_of_seq Q hseq hX hZ (Nat.zero_le H)
    (n - 1) hf ht
  have hΨ : GoodField 1 Ψ := liftApply_goodField_of_seq Q hseq hX hZ (Nat.zero_le H)
    (n - 2) hf ht
  have he : (fun y => liftFluxX Q Cc (fun _ => f) 0 n t X y k) = fun y =>
      ((Real.sqrt Q.η * Q.v t y k) • Φ X y -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k j • fastPartial j Φ X y) -
        Q.η • ∑ j : Fin 2, Q.G t X k j • slowPartial j Ψ X y := by
    funext y
    simp only [liftFluxX, ite_eq_left hn, ite_true, Φ, Ψ, sub_eq_add_neg, neg_zero, add_zero]
  rw [he, flux_cross_mean Q.η (Q.G t) (Q.v t) Φ Ψ hΦ hΨ hv X k]
  rw [weakDiagonal_mean_flux_coefficient_vector_apply Q t
    (fun j => continuous_const.mul ((continuous_apply j).comp hv)) Cc n hn f k X z
    (fun m hm α v u => ((hseq.2.2.2.2.2.1 0 (Nat.zero_le H)
      (n - 1) m α v u t ht).1.1 X).continuous)]
  by_cases hn2 : n = 2
  · subst n
    have hΨf : Ψ = fun Y _ => f Y := by
      funext Y y
      exact hseq.1 f hf t ht Y y
    have hm : (fun Y => fieldCellMean (Ψ Y)) = f := by
      funext Y
      rw [hΨf]
      exact fieldCellMean_const _
    rw [hm]
    simp only [ite_true, neg_smul, sub_eq_add_neg, Φ]
  · have hc : CoefField True 1 Ψ := liftApply_centField_of_seq Q hseq hX hZ
      (Nat.zero_le H) (Or.inl (by omega)) hf ht
    have hm : (fun Y => fieldCellMean (Ψ Y)) = fun _ => 0 := funext (hc.2 trivial)
    rw [hm]
    simp only [fderiv_const_apply, zero_apply, smul_zero, Finset.sum_const_zero,
      sub_zero, ite_eq_right hn2, add_zero, Φ]

end ScalarSequence
end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets: scalar coefficients depending on time and space (uniform window data), and
the entries of the Jacobian of an admissible stream velocity. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Uniform window data for a scalar coefficient. -/
structure NativeScalarWindow (a b : ℝ) (K : ℕ) (s : ℝ → Vec 2 → ℝ) : Prop where
  smooth : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (s t)
  periodic : ∀ t ∈ Icc a b, IsZ2Periodic (s t)
  measurable : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => s z.1.1 z.1.2)
  bound : ∀ n ≤ K, ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ n (s t) x‖ ≤ C

/-- A scalar coefficient multiplies fields. -/
theorem ClassicalWindowBound.smul_scalar
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V} {s : ℝ → Vec 2 → ℝ}
    (hs : NativeScalarWindow a b K s) (hf : ClassicalWindowBound a b K f) :
    ClassicalWindowBound a b K (fun t x => s t x • f t x) := by
  let L0 : ℝ →L[ℝ] (V →L[ℝ] V) := ContinuousLinearMap.toSpanSingleton ℝ (ContinuousLinearMap.id ℝ V)
  have hA : NativeUniformCoeff a b K (fun t x => L0 (s t x)) := by
    refine ⟨fun t ht => L0.contDiff.comp (hs.smooth t ht),
      fun t ht n x => by simp only [hs.periodic t ht n x], ?_, fun n hn => ?_⟩
    · exact L0.continuous.measurable.comp hs.measurable
    · obtain ⟨C, hC⟩ := hs.bound n hn
      refine ⟨‖L0‖ * C, fun t ht x => ?_⟩
      exact (L0.norm_iteratedFDeriv_comp_left (f := s t) (x := x)
        ((hs.smooth t ht).contDiffAt) (Nat.cast_le.mpr hn)).trans
        (mul_le_mul_of_nonneg_left (hC t ht x) (norm_nonneg _))
  have h := ClassicalWindowBound.clm_apply hA hf
  simpa [L0] using h

/-- The entries of the Jacobian of an admissible stream velocity. -/
theorem nativeBudget_jacEntry_window (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (a b : ℝ) (K : ℕ) (i j : Fin 2) :
    NativeScalarWindow a b K (fun t x => jacMatrix (streamVel φ t) x i j) := by
  have hv := Infra.Classical.streamVel_smoothPeriodic φ hφ
  have hc (t : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (streamVel φ t) :=
    hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  let L : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec j))
  have hs : ∀ t, (fun x => jacMatrix (streamVel φ t) x i j) = L ∘ fderiv ℝ (streamVel φ t) := by
    intro t; funext x; rfl
  have hcK (t : ℝ) (m : ℕ) : ContDiff ℝ ((m : ℕ) : ℕ∞) (streamVel φ t) :=
    (hc t).of_le (by simp)
  have hsm (t : ℝ) : ContDiff ℝ (K : ℕ) (fun x => jacMatrix (streamVel φ t) x i j) := by
    rw [hs t]
    exact L.contDiff.comp ((hcK t (K + 1)).fderiv_right (m := (K : ℕ∞)) (by norm_cast))
  have hder : ∀ t x (v : Vec 2), fderiv ℝ (streamVel φ t) x v =
      fderiv ℝ (Function.uncurry (streamVel φ)) (t, x) (0, v) := by
    intro t x v
    have hd : DifferentiableAt ℝ (Function.uncurry (streamVel φ)) (t, x) :=
      (hv.smooth.differentiable (by simp)) _
    have hcomp := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    have : fderiv ℝ (streamVel φ t) x = (fderiv ℝ (Function.uncurry (streamVel φ)) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) := hcomp.fderiv
    rw [this]; simp
  refine ⟨fun t _ => hsm t, ?_, ?_, fun n hn => ?_⟩
  · intro t _ k x
    have hp : IsZ2Periodic (streamVel φ t) := fun k x => by
      simpa only [Int.cast_zero, add_zero] using hv.periodic 0 k t x
    show L (fderiv ℝ (streamVel φ t) (x + latticeShift k)) = L (fderiv ℝ (streamVel φ t) x)
    rw [Providers.KernelSup.periodic_fderiv hp k x]
  · have hcont : Continuous (fun p : ℝ × Vec 2 =>
        jacMatrix (streamVel φ p.1) p.2 i j) := by
      have h := (hv.smooth.continuous_fderiv (by simp)).clm_apply
        (continuous_const (y := ((0 : ℝ), basisVec j)))
      have h2 := (continuous_apply i).comp h
      convert h2 using 1
      funext p
      exact congrArg (fun w => w i) (hder p.1 p.2 (basisVec j))
    exact hcont.measurable.comp measurable_subtype_coe
  · obtain ⟨C, hC0, hC⟩ := CycleJointProofs.admissible_stream_spatial_jet_bound φ hφ (n + 1)
    refine ⟨‖L‖ * C, fun t _ x => ?_⟩
    rw [hs t]
    have h1 := L.norm_iteratedFDeriv_comp_left (f := fderiv ℝ (streamVel φ t)) (x := x)
      (N := (n : ℕ∞ω))
      ((hcK t (n + 1)).fderiv_right (m := (n : ℕ∞)) (by norm_cast)).contDiffAt le_rfl
    rw [norm_iteratedFDeriv_fderiv] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hC t x) (norm_nonneg _))

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! The scalar mean leaf instantiated with actual native path sequences. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- Every actual scalar path edge has the qualitative regularity needed by the mean formula. -/
theorem native_path_edge_good (hi : StageSuccessor.Input P Mn G)
    {g : ℕ} (π : StagePath G g) (p : OddSlot) (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v u : Fin (g + 1)) (d : Finset.Icc 2 Dm)
    (γ : Constituent d.1 ℝ ℝ)
    (hγ : γ ∈ (familyLiftData D G.level p.1 (G.actual p).1
      (Mn.lenFactor * liftLength D G.level) (pathEdges G π p (G.actual p))).edge v u d)
    (α : DerivativeWord2 (d.1 - 1)) :
    GoodField 1 (fun Y z => γ.coeff α t Y z) := by
  classical
  change γ ∈ List.map _ (pathEdges G π p (G.actual p) v u d) at hγ
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
  simp only [pathEdges] at hδ
  split_ifs at hδ with hvu hd
  · simp only [List.mem_singleton] at hδ
    subst δ
    apply GoodField.of_forall_apply
    intro k
    have hg := native_stage_goodDat hi p 1 (π.step ⟨u, hvu.2⟩).1
      (π.step ⟨u, hvu.2⟩).2.1 (π.step ⟨u, hvu.2⟩).2.2 t ht d.1 α k
    simpa only [Providers.PathDecomp.stageDat, ite_eq_left (Finset.mem_Icc.mp d.2).2] using hg
  · exact (List.not_mem_nil hδ).elim
  · exact (List.not_mem_nil hδ).elim

/-- Actual native paths satisfy the literal scalar mean action, including order one menus. -/
theorem scalarPathMean : ScalarPathMeanStatement := by
  intro hr _ _ _ D Dm bw j₀ P Mn G hi g π p n hn _hnR
  dsimp only
  intro f hf t ht X z k
  let ρ := Mn.lenFactor * liftLength D G.level
  let A := (G.actual p).1
  let Q := familyLiftData D G.level p.1 A ρ (pathEdges G π p (G.actual p))
  let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 A
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let S := max Dm 1
  have hS : Dm ≤ S := le_max_left _ _
  have hS1 : 1 ≤ S := le_max_right _ _
  have hseq := StageSuccessor.path_lift_family hi π S S p.1 A ⟨(G.actual p).2, p.2⟩
  rw [native_actual_ladderOmega_eq_univ hi p ρ] at hseq
  have hs : IsLiftSequence Q S S a b Mn.N g C :=
    liftSequence_of_on_univ Q S S a b Mn.N g C hseq
  have hv : Continuous (Q.v t) := by
    have hν := weakData_kap_pos D hi.base hi.profile hi.band G.level
    exact (normalizedPulseDrift_contDiff (α := D.α) (q := D.q) (m := G.level)
      (ζ := D.ζ) hi.base hν p.2 t).continuous
  have hG (i j : Fin 2) : ContDiff ℝ (0 : ℕ∞) (fun Y => Q.G t Y i j) :=
    (((familyLiftData_metric_spacetime_smooth D hi.profile G.level p.1 A
      (G.actual p).2.2.2.1 ρ (pathEdges G π p (G.actual p)) i j).comp
      (contDiff_const.prodMk contDiff_id)).of_le (by simp))
  change fieldCellMean (fun y => liftFluxX Q C (fun _ => f) g n t X y k) (Fin.last g) =
    liftApply (n - 1) (actualMeanFluxCoefficient Q C g n k) (fun _ => f) t X z (Fin.last g)
  by_cases hg : g = 0
  · subst g
    simp only [actualMeanFluxCoefficient, ite_true]
    exact congrFun (scalar_diagonal_mean_of_sequence hs hS1 hS1 n hn f hf t ht X z k hv)
      (Fin.last 0)
  · simp only [actualMeanFluxCoefficient, ite_eq_right hg]
    exact scalar_positive_mean_of_sequence hs hi.order hS hS g n hg le_rfl hn
      f hf t ht X z k (Fin.last g) hG hv (native_path_edge_good hi π p t ht)

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Finite spatial regularity suffices for an already proved smooth mean action.
The existing Taylor-jet realization and lift-flux locality transfer the identity
at one slow label; no approximation limit or time regularity is required. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Transfer a smooth cell-mean action to every field at the finite locality reserve. -/
theorem finite_mean_action_of_smooth
    {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h) (Cmean : LiftCoeff ι h)
    (N H g n : ℕ) (τ : ℝ) (X : Vec 2) (k : Fin 2) (v : ι)
    (hDm : 1 ≤ Dm) (hg : g ≤ H) (hn : n ≤ N + Dm)
    (hz : ∀ q ≤ H, ∀ n', N < n' → ∀ m α t Y z v u, Cc q n' m α t Y z v u = 0)
    (hb : ∀ q ≤ H, ∀ n' m α v u,
      IsBoxSmooth Dm Dm (fun Y z => Cc q n' m α τ Y z v u))
    (hG : ∀ j, ContDiff ℝ (0 : ℕ∞) (fun Y => Q.G τ Y k j))
    (hv : ContDiff ℝ (0 : ℕ∞) (fun z => Q.v τ z k))
    (hedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, IsBoxSmooth 0 0 (γ.coeff α τ))
    (hact : ∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f →
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) g n τ X z k v) =
        liftApply (n - 1) Cmean (fun _ => f) τ X 0 v)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ ((N + Dm : ℕ) : ℕ∞) f) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) g n τ X z k v) =
      liftApply (n - 1) Cmean (fun _ => f) τ X 0 v := by
  obtain ⟨f', hf', hj⟩ := smoothJetRealization (N + Dm) f hf X
  have hjet : SameJetAt (N + Dm) X f f' := fun r α hr => (hj r α hr).symm
  have hflux := liftFlux_sameJet Q Cc (fun _ => f) (fun _ => f') g n τ k 0 N H X
    hDm hg hz (by simpa only [Nat.zero_add] using hb) hG hv (fun _ => hedge)
    (by simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm] using hf)
    (hf'.of_le (by simp)) (by simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm] using hjet)
  calc
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) g n τ X z k v) =
        fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f') g n τ X z k v) := by
      exact integral_congr_ae (ae_of_all _ fun z =>
        congrFun (sameJet_zero_iff.mp (hflux z)) v)
    _ = liftApply (n - 1) Cmean (fun _ => f') τ X 0 v := hact f' hf'
    _ = liftApply (n - 1) Cmean (fun _ => f) τ X 0 v := by
      simp only [liftApply]
      refine Finset.sum_congr rfl fun m hm => ?_
      refine Finset.sum_congr rfl fun α _ => ?_
      have hmK : m ≤ N + Dm := by have := Finset.mem_range.mp hm; omega
      rw [hj m α hmK]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets: the commutator flux `commFluxE` of an admissible stream. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- The commutator flux with an admissible stream and a continuous matrix of time. -/
theorem ClassicalWindowBound.commFlux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → E} {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (hH : ∀ i j, Continuous fun t => H t i j) (hf : ClassicalWindowBound a b (K + 1) f) :
    ClassicalWindowBound a b K (fun t x => commFluxE (streamVel φ t) (H t) (f t) x) := by
  refine ClassicalWindowBound.pi (V := fun _ : Fin 2 => E) fun j => ?_
  have hg (l : Fin 2) : ClassicalWindowBound a b K (fun t x => gradE (f t) x l) := by
    have := hf.word (fun _ : Fin 1 => l) (L := K) (by omega)
    simpa only [nativeBudget_gradE_eq] using this
  have e : (fun t x => commFluxE (streamVel φ t) (H t) (f t) x j) = fun t x =>
      -(∑ l : Fin 2, ((∑ c : Fin 2, jacMatrix (streamVel φ t) x j c • (H t c l • gradE (f t) x l)) +
        ∑ c : Fin 2, H t j c • (jacMatrix (streamVel φ t) x l c • gradE (f t) x l))) := by
    funext t x
    simp only [commFluxE, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      add_smul, Finset.sum_smul, mul_smul]
  rw [e]
  refine ClassicalWindowBound.neg (ClassicalWindowBound.sum_fintype fun l => ?_)
  refine ClassicalWindowBound.add (ClassicalWindowBound.sum_fintype fun c => ?_)
    (ClassicalWindowBound.sum_fintype fun c => ?_)
  · exact ClassicalWindowBound.smul_scalar (nativeBudget_jacEntry_window φ hφ a b K j c)
      (ClassicalWindowBound.smul_time (hH c l) (hg l))
  · exact ClassicalWindowBound.smul_time (hH j c)
      (ClassicalWindowBound.smul_scalar (nativeBudget_jacEntry_window φ hφ a b K l c) (hg l))

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets: finite sums over finsets and the covariance polynomials on window bounds. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- Sums over a finset of window bounds. -/
theorem ClassicalWindowBound.sum_finset
    {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f : ι → ℝ → Vec 2 → V} (s : Finset ι)
    (Q : ∀ i ∈ s, ClassicalWindowBound a b K (f i)) :
    ClassicalWindowBound a b K (fun t x => ∑ i ∈ s, f i t x) := by
  have := ClassicalWindowBound.sum_fintype (ι := s) (f := fun i => f i) (fun i => Q i i.2)
  have e : (fun t x => ∑ i ∈ s, f i t x) = fun t x => ∑ i : s, f i t x := by
    funext t x; exact (Finset.sum_coe_sort s (fun i => f i t x)).symm
  rw [e]; exact this

/-- The covariance polynomial `P_p`. -/
theorem ClassicalWindowBound.covP
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → E} {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ i j, Continuous fun t => H t i j) (p : ℕ)
    (hf : ClassicalWindowBound a b (K + 2 * p) f) :
    ClassicalWindowBound a b K (fun t x => covPolyP (H t) p (f t) x) := by
  have e : (fun t x => covPolyP (H t) p (f t) x) = fun t x => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (covOperator (H t))^[l] (f t) x := by
    funext t x; simp only [covPolyP, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine ClassicalWindowBound.sum_finset _ fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  exact ClassicalWindowBound.smul_time continuous_const
    (ClassicalWindowBound.covOp_iterate hH l (hf.mono (by omega)))

/-- The covariance polynomial `Q_p`. -/
theorem ClassicalWindowBound.covQ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → E} {H : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ i j, Continuous fun t => H t i j) (p : ℕ)
    (hf : ClassicalWindowBound a b (K + 2 * p) f) :
    ClassicalWindowBound a b K (fun t x => covPolyQ (H t) p (f t) x) := by
  have e : (fun t x => covPolyQ (H t) p (f t) x) = fun t x => ∑ l ∈ Finset.range (p + 1),
      (((-1 : ℝ) ^ l / (l.factorial : ℝ))) • (covOperator (H t))^[l] (f t) x := by
    funext t x; simp only [covPolyQ, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine ClassicalWindowBound.sum_finset _ fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  exact ClassicalWindowBound.smul_time continuous_const
    (ClassicalWindowBound.covOp_iterate hH l (hf.mono (by omega)))

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets, brick 4b: the covariance-flux terms. Continuity of the covariance primitive
and of the reference flux, and the budget of the last flux. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The menu band value is positive. -/
theorem nativeBudget_kappa_pos {F : Frame D hr Dm bw j₀} (hi : NativeInput F) : 0 < D.κ F.m :=
  CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band (by
    rw [← hi.level]
    exact hi.stage.top)

/-- The covariance primitive is continuous in time, entrywise. -/
theorem nativeBudget_covPrimitive_continuous {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    (i j : Fin 2) : Continuous fun t => menuCovPrimitive D F.Mn F.m t i j :=
  (native_menu_covariance_contDiff D F.Mn F.m hi.stage.base hi.stage.profile
    (nativeBudget_kappa_pos hi) i j).continuous

/-- The reference flux minus the coarse diffusivity is continuous in time, entrywise. -/
theorem nativeBudget_refFlux_continuous {F : Frame D hr Dm bw j₀} (hi : NativeInput F)
    (i j : Fin 2) : Continuous fun t =>
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j := by
  exact (FreshAxes.refFlux_entry_continuous (α := D.α) (q := D.q) (m := F.m)
    hi.stage.base hi.stage.profile (nativeBudget_kappa_pos hi) i j).sub
    (continuous_const (y := (D.κ (F.m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j))

/-- The last flux has the window bound of order one. -/
theorem nativeBudget_lastFlux {F : Frame D hr Dm bw j₀} (hi : NativeInput F) {dZ : F.Field}
    (hc : ClassicalTimeCurve F F.Naux F.aZ dZ) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 1 (F.lastFlux v) := by
  have hres := hi.auxiliary
  have h0 : ClassicalWindowBound F.tp F.tf (F.Naux - 2) (fun t x => F.aZ t x v) := hc.field v
  have h1 : ClassicalWindowBound F.tp F.tf (2 + 2 * F.p) (fun t x => F.aZ t x v) :=
    h0.mono (by omega)
  have h2 := ClassicalWindowBound.covOp_iterate (H := menuCovPrimitive D F.Mn F.m)
    (fun i j => nativeBudget_covPrimitive_continuous hi i j) F.p h1
  have h3 := ClassicalWindowBound.smul_time (s := fun _ => ((F.p.factorial : ℝ)⁻¹))
    continuous_const h2
  exact ClassicalWindowBound.matGrad (nativeBudget_refFlux_continuous hi) (K := 1) h3

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
section
/-! Native budgets, brick 4c: the macro flux, reduced to the budget of the glued pulse mean
flux. The glued mean flux (`NativeGluedMeanBudget`) is the one genuinely new analytic input:
a cutoff-weighted finite sum over the time-dependent pulse set of the Eulerian pulse mean
fluxes. It is linear in the field and loses a bounded number of spatial derivatives. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The spatial loss of the glued pulse mean flux. -/
def nativeGluedLoss (N Dm : ℕ) : ℕ := 4 * (N + Dm) + 12

/-- The glued pulse mean flux of grades `rs ⊆ [0, depth]` and degrees
`ns ⊆ [2, N + Dm]` maps fields with a window bound of order `K + nativeGluedLoss` to a flux with
a window bound of order `K`. -/
def NativeGluedMeanBudget (F : Frame D hr Dm bw j₀) : Prop :=
  NativeInput F → ∀ (rs ns : Finset ℕ), rs ⊆ Finset.Icc 0 F.depth → ns ⊆ Finset.Icc 2 (F.N + Dm) →
    ∀ (a : F.Field) (K : ℕ),
      (∀ v, ClassicalWindowBound F.tp F.tf (K + nativeGluedLoss F.N Dm) (fun t x => a t x v)) →
      ∀ v, ClassicalWindowBound F.tp F.tf K (fun t x =>
        toFluxL (menuGluedMeanFlux F.Mn F.G F.m rs ns F.CcT a t x v))

/-- The macro flux budget of order one, from the glued budget and the prepared curve. -/
theorem nativeBudget_macroFlux {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudget F)
    (hi : NativeInput F) {dRep : F.Field}
    (hp : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf 1 (F.macroFluxField v) := by
  have hres := hi.auxiliary
  have hDm := hi.stage.order
  have ha : ∀ w, ClassicalWindowBound F.tp F.tf (1 + nativeGluedLoss F.N Dm)
      (fun t x => F.aRep t x w) := fun w =>
    (hp.field w).mono (by unfold nativeGluedLoss; omega)
  have h1 : ClassicalWindowBound F.tp F.tf 1 (fun t x => toFluxL (fun j => ∑ l : Fin 2,
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j l •
        gradE (fun y => F.aRep t y v) x l)) :=
    ClassicalWindowBound.matGrad (nativeBudget_refFlux_continuous hi) (K := 1)
      ((hp.field v).mono (by omega))
  have h2 : ClassicalWindowBound F.tp F.tf 1 (fun t x => toFluxL
      (menuGluedMeanFlux F.Mn F.G F.m {0} (Finset.Icc 2 (F.N + 1)) F.CcT F.aRep t x v)) :=
    hg hi {0} _ (by intro r hr; simp at hr; simp [hr]) (by
      intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega) F.aRep 1 ha v
  have h3 : ClassicalWindowBound F.tp F.tf 1 (fun t x => toFluxL (fun j => ∑ l : Fin 2,
      ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l • gradE (fun y => F.aRep t y v) x l)) :=
    ClassicalWindowBound.matGrad (fun i j => FreshAxes.refFlux_entry_continuous (α := D.α)
      (q := D.q) (m := F.m) hi.stage.base hi.stage.profile (nativeBudget_kappa_pos hi) i j)
      (K := 1) ((hp.field v).mono (by omega))
  have h4 : ClassicalWindowBound F.tp F.tf 1 (fun t x => toFluxL
      (menuMeanFluxE F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v)) :=
    hg hi (Finset.Icc 1 F.depth) (Finset.Icc 2 (F.N + Dm)) (by
      intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega) (fun n hn => hn) F.aRep 1 ha v
  have h5 := (h1.add (h2.sub h3)).add h4
  have e : F.macroFluxField v = fun t x => (toFluxL (fun j => ∑ l : Fin 2,
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t - D.κ (F.m - 1) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) j l • gradE (fun y => F.aRep t y v) x l) +
      (toFluxL (menuGluedMeanFlux F.Mn F.G F.m {0} (Finset.Icc 2 (F.N + 1)) F.CcT F.aRep t x v) -
        toFluxL (fun j => ∑ l : Fin 2, ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l •
          gradE (fun y => F.aRep t y v) x l))) +
      toFluxL (menuMeanFluxE F.Mn F.G F.m F.N F.depth F.CcT F.aRep t x v) := by
    funext t x
    rfl
  rw [e]
  exact h5

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Pointwise walk expansion for the native candidate, using qualitative native
certificates rather than a transverse setting. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.PathDecomp
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

/-- Qualitative pointwise expansion, at source orders at least two. -/
theorem native_flux_walk_formula_of_two_le (hi : StageSuccessor.Input P Mn G)
    (hD : 2 ≤ Dm) (H : ℕ) (p : OddSlot) (g n : ℕ)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X z : Vec 2) (k : Fin 2) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
      hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
    let Lift := stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
    let Arise := stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H
    liftFluxX Q (nativeStagePathCandidate hi H p) (fun _ => f) g n t X z k =
      ∑ s : HLIdx G, ∑ q : WalkFrom F g s.1,
        (HLDecomp.hlCtx Q (topOf Lift Arise) t (hlCoord G f s)).formX n g
          (F.walkDat q.2) k X z • walkVec F (hlVec G s) q := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  let Lift := stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
  let Arise := stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H
  let T := topOf Lift Arise
  obtain ⟨hs, _⟩ := native_stage_path_step_hypotheses hi hD p H
    (Mn.N + 1 + Dm) (Mn.N + 1 + Dm) le_rfl le_rfl
  have hT : ∀ h (cd : Fin h → StepDat) j m (α : DerivativeWord2 m),
      GoodField (Mn.N + 1 + Dm) (fun Y y => T h cd j m α t Y y) :=
    hs.goodT (fun _ => 0) ht
  change liftFluxX Q (cand F T) (fun _ => f) g n t X z k = _
  rw [hl_liftFluxX_field_congr Q (cand F T)
    (a' := fun _ Y => ∑ s : HLIdx G,
      (Pi.single s.1 (hlCoord G f s Y • hlVec G s) : ∀ v : CompIn G.comps, hr v.1.root))
    g n t (funext (hl_field_decomp G f))]
  exact HLDecomp.hl_liftFluxX_cand_sum F Q hs.hQ T t hT
    (fun v u γ => hs.hdat v u γ t ht) Finset.univ (w := fun s : HLIdx G => s.1)
    (fun s => hlCoord G f s) (fun s => hl_coord_contDiff G hf s)
    (fun s => hlVec G s) g n X z k

/-- The actual lift of any arising path equals its chain candidate, with the
same top arrays as the native Hilbert candidate. -/
theorem native_path_candidate_of_two_le (hi : StageSuccessor.Input P Mn G)
    (hD : 2 ≤ Dm) (H : ℕ) (p : OddSlot) {g : ℕ} (π : StagePath G g) (hg : g ≤ H) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Cp := fun h (σ : StagePath G h) => StageSuccessor.pathLiftFamily
      hi.base hi.profile hi.band ρ Mn.N σ p.1 (G.actual p).1
    let Lift := stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
    let Arise := stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H
    let cd := pathDat G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) π
    ∀ hh ≤ g, ∀ n, Uniqueness.CoeffEq (Cp g π)
      (cand (chainFam cd) (topOf Lift Arise)) a b hh n := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let A := (G.actual p).1
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Cp := fun h (σ : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N σ p.1 A
  let Lift := stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
  let Arise := stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H
  let Qc := stQc G G.level p.1 A ρ p (G.actual p) H
  let cd := pathDat G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) π
  let Qp := familyLiftData D G.level p.1 A ρ (pathEdges G π p (G.actual p))
  let S := Mn.N + 1 + Dm
  obtain ⟨hs, hsc⟩ := native_stage_path_step_hypotheses hi hD p H S S le_rfl le_rfl
  have hA : Arise g cd := ⟨hg, π, rfl⟩
  have hsp : StepHyp (chainFam cd) Qp Lift Qc Arise S S a b Mn.N Mn.N g := {
    hQ := hasFamFlux_pathEdges G G.level p.1 A ρ p (G.actual p) π
    hab := hs.hab
    hW := hs.hW
    hQc := hs.hQc
    hη := hs.hη
    hG := hs.hG
    hv := hs.hv
    hLs := hs.hLs
    hcd := hs.hcd
    hdat := fun v u γ => hs.hcd g cd hA
      ⟨u.val, by have := γ.down; have := v.isLt; omega⟩
    hGr := hs.hGr
    hvr := hs.hvr
    hD2 := hD
    hsX := le_rfl
    hsZ := le_rfl
    hNr := le_rfl
    hArise := fun _ _ _ q hq => StageSetting.arise_chain hA q hq }
  have hc := StageSuccessor.path_lift_family hi π S S p.1 A ⟨(G.actual p).2, p.2⟩
  rw [native_actual_ladderOmega_eq_univ hi p ρ] at hc
  have hseq : IsLiftSequence Qp S S a b Mn.N g (Cp g π) :=
    WeakEntryProofs.liftSequence_of_on_univ Qp S S a b Mn.N g (Cp g π) hc
  exact decomp hsp (fun L d hAd hLg => hsc L d hAd (hLg.trans hg)) hseq

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Native budgets, brick 4d: the readout flux `menuGFlux` of order `4p+2`, reduced to the
glued pulse budget `NativeGluedMeanBudget`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A time-dependent matrix applied to a gradient, in the sup-norm product. -/
theorem ClassicalWindowBound.matGradPi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → E} {R : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hR : ∀ i j, Continuous fun t => R t i j) (hf : ClassicalWindowBound a b (K + 1) f) :
    ClassicalWindowBound a b K (fun t x (k : Fin 2) => ∑ l : Fin 2,
      R t k l • gradE (f t) x l) := by
  refine ClassicalWindowBound.pi (V := fun _ : Fin 2 => E) fun k => ?_
  refine ClassicalWindowBound.sum_fintype fun l => ?_
  have := ClassicalWindowBound.smul_time (s := fun t => R t k l) (hR k l)
    (hf.word (fun _ : Fin 1 => l) (L := K) (by omega))
  simpa only [nativeBudget_gradE_eq] using this

/-- The glued budget in the sup-norm product. -/
theorem nativeBudget_glued_pi {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudget F)
    (hi : NativeInput F) (rs ns : Finset ℕ) (hrs : rs ⊆ Finset.Icc 0 F.depth)
    (hns : ns ⊆ Finset.Icc 2 (F.N + Dm)) (a : F.Field) (K : ℕ)
    (ha : ∀ v, ClassicalWindowBound F.tp F.tf (K + nativeGluedLoss F.N Dm) (fun t x => a t x v))
    (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf K (fun t x =>
      menuGluedMeanFlux F.Mn F.G F.m rs ns F.CcT a t x v) :=
  (hg hi rs ns hrs hns a K ha v).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).toContinuousLinearMap

/-- The readout flux budget of order `4p+2` in the sup-norm product, from the glued budget and
the readout curve. -/
theorem nativeBudget_gFlux_pi {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudget F)
    (hi : NativeInput F) {dZ : F.Field} (hc : ClassicalTimeCurve F F.Naux F.aZ dZ)
    (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf (4 * F.p + 2)
      (fun t x => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t x) := by
  have hres := hi.auxiliary
  have hDm := hi.stage.order
  have hH := fun i j => nativeBudget_covPrimitive_continuous hi i j
  have hz : ∀ w : CompIn F.G.comps, ClassicalWindowBound F.tp F.tf (F.Naux - 2)
      (fun t x => F.aZ t x w) := fun w => hc.field w
  -- the covariance-polynomial field
  have ha2 : ∀ K : ℕ, K + 2 * F.p ≤ F.Naux - 2 → ∀ w : CompIn F.G.comps,
      ClassicalWindowBound F.tp F.tf K
        (fun t x => covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y => F.aZ t y w) x) :=
    fun K hK w => ClassicalWindowBound.covP (H := menuCovPrimitive D F.Mn F.m) hH F.p
      ((hz w).mono hK)
  have hloss : 4 * F.p + 2 + nativeGluedLoss F.N Dm + 2 * F.p ≤ F.Naux - 2 := by
    unfold nativeGluedLoss; omega
  -- the commutator part
  have hT1 : ClassicalWindowBound F.tp F.tf (4 * F.p + 2) (fun t x =>
      ∑ l ∈ Finset.Icc 1 F.p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
        (covOperator (menuCovPrimitive D F.Mn F.m t))^[a']
          (commFluxE (streamVel (D.Φ (F.m - 1)) t) (menuCovPrimitive D F.Mn F.m t)
            ((covOperator (menuCovPrimitive D F.Mn F.m t))^[l - 1 - a'] (fun y => F.aZ t y v))) x) := by
    refine ClassicalWindowBound.sum_finset _ fun l hl => ?_
    have hl' := Finset.mem_Icc.mp hl
    refine ClassicalWindowBound.smul_time continuous_const ?_
    refine ClassicalWindowBound.sum_finset _ fun a' ha' => ?_
    have ha'' := Finset.mem_range.mp ha'
    have hin : ClassicalWindowBound F.tp F.tf (4 * F.p + 2 + 2 * a' + 1) (fun t x =>
        (covOperator (menuCovPrimitive D F.Mn F.m t))^[l - 1 - a'] (fun y => F.aZ t y v) x) :=
      ClassicalWindowBound.covOp_iterate (H := menuCovPrimitive D F.Mn F.m) hH (l - 1 - a')
        ((hz v).mono (by omega))
    have hcomm := ClassicalWindowBound.commFlux (H := menuCovPrimitive D F.Mn F.m) (D.Φ (F.m - 1))
      (D.hΦ _) hH (K := 4 * F.p + 2 + 2 * a') hin
    exact ClassicalWindowBound.covOp_iterate (H := menuCovPrimitive D F.Mn F.m) hH a' hcomm
  let a2 : F.Field := fun t y w =>
    covPolyP (menuCovPrimitive D F.Mn F.m t) F.p (fun y' => F.aZ t y' w) y
  have hG0 := nativeBudget_glued_pi hg hi {0} (Finset.Icc 2 (F.N + 1))
    (by intro r hr; simp at hr; simp [hr]) (by
      intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega) a2 (4 * F.p + 2)
    (fun w => ha2 _ (by omega) w) v
  have hG1 := nativeBudget_glued_pi hg hi (Finset.Icc 1 F.depth) (Finset.Icc 2 (F.N + Dm))
    (by intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega) (fun n hn => hn) a2 (4 * F.p + 2)
    (fun w => ha2 _ (by omega) w) v
  have hRef := ClassicalWindowBound.matGradPi (K := 4 * F.p + 2)
    (R := ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
    (fun i j => FreshAxes.refFlux_entry_continuous (α := D.α) (q := D.q) (m := F.m)
      hi.stage.base hi.stage.profile (nativeBudget_kappa_pos hi) i j)
    (f := fun t x => a2 t x v) (ha2 (4 * F.p + 2 + 1) (by omega) v)
  exact (hT1.sub (hG0.sub hRef)).sub hG1

/-- The readout flux budget of order `4p+2`, from the glued budget and the readout curve. -/
theorem nativeBudget_gFlux {F : Frame D hr Dm bw j₀} (hg : NativeGluedMeanBudget F)
    (hi : NativeInput F) {dZ : F.Field} (hc : ClassicalTimeCurve F F.Naux F.aZ dZ)
    (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf (4 * F.p + 2)
      (fun t x => toFluxL (menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t x)) :=
  (nativeBudget_gFlux_pi hg hi hc v).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => hr v.1.root)).symm.toContinuousLinearMap

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Scalar walk fluxes in coordinates of their source fibre. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.PathDecomp
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

/-- The scalar flux of an actual walk is its coordinate sum of the common formX. -/
theorem walk_path_flux_basis (hi : StageSuccessor.Input P Mn G)
    (hD : 2 ≤ Dm) (H : ℕ) (p : OddSlot) (g n : ℕ) (hg : g ≤ H)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X z : Vec 2) (k : Fin 2) (u v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
      hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
    let T := topOf (stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp)
      (stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H)
    ∀ q : F.Walk g u v,
      let π := Classical.choose (stage_walk_path q)
      let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
      liftFluxX Qp (Cp g π)
        (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u))))
        g n t X z k (Fin.last g) =
      ∑ i : Fin (Module.finrank ℝ (hr u.1.root)),
        (HLDecomp.hlCtx Q T t (hlCoord G f ⟨u, i⟩)).formX n g (F.walkDat q) k X z *
          ℓ (F.compMap q (hlVec G ⟨u, i⟩)) := by
  classical
  dsimp only
  intro q
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
  let π := Classical.choose (stage_walk_path q)
  let cd := pathDat G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) π
  let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
  let Cp := fun h (σ : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N σ p.1 (G.actual p).1
  let T := topOf (stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp)
    (stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H)
  have he : cd = F.walkDat q := Classical.choose_spec (stage_walk_path q)
  have hc := native_path_candidate_of_two_le hi hD H p π hg
  rw [Uniqueness.liftFluxX_congr Qp (Cp g π) (cand (chainFam cd) T) _ g n t
    (fun h hh n' m α => hc h hh n' t ht m α)]
  have hin : (fun Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u)))) =
      fun Y => ∑ i : Fin (Module.finrank ℝ (hr u.1.root)),
        (Pi.single (0 : Fin (g + 1))
          (hlCoord G f ⟨u, i⟩ Y • ℓ (F.compMap q (hlVec G ⟨u, i⟩))) : Fin (g + 1) → ℝ) := by
    funext Y
    have hb : f Y u = ∑ i : Fin (Module.finrank ℝ (hr u.1.root)),
        hlCoord G f ⟨u, i⟩ Y • hlVec G ⟨u, i⟩ := by
      exact ((Module.finBasis ℝ (hr u.1.root)).sum_repr (f Y u)).symm
    rw [hb, map_sum, map_sum]
    funext j
    by_cases hj : j = 0
    · subst j
      simp only [Finset.sum_apply, Pi.single_eq_same, map_smul]
    · simp only [Finset.sum_apply, Pi.single_eq_of_ne hj, Finset.sum_const_zero]
  rw [hl_liftFluxX_field_congr Qp (cand (chainFam cd) T)
    (a' := fun _ Y => ∑ i : Fin (Module.finrank ℝ (hr u.1.root)),
      (Pi.single (0 : Fin (g + 1))
        (hlCoord G f ⟨u, i⟩ Y • ℓ (F.compMap q (hlVec G ⟨u, i⟩))) : Fin (g + 1) → ℝ))
    g n t hin]
  obtain ⟨hs, _⟩ := native_stage_path_step_hypotheses hi hD p H
    (Mn.N + 1 + Dm) (Mn.N + 1 + Dm) le_rfl le_rfl
  have hA : stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H g cd :=
    ⟨hg, π, rfl⟩
  have hsum := HLDecomp.hl_chain_liftFluxX_last_sum cd Qp
    (hasFamFlux_pathEdges G G.level p.1 (G.actual p).1 ρ p (G.actual p) π) T t
    (hs.goodT (fun _ => 0) ht) (fun i => hs.hcd g cd hA i t ht)
    Finset.univ (fun i => hlCoord G f ⟨u, i⟩)
    (fun i => hl_coord_contDiff G hf ⟨u, i⟩)
    (fun i => ℓ (F.compMap q (hlVec G ⟨u, i⟩))) n X z k
  rw [hsum, he]
  rfl

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Pointwise recombination and mean interchange at source orders at least two. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.PathDecomp
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

/-- Reading the native flux through a functional gives scalar walk fluxes. -/
theorem native_walk_pointwise (hi : StageSuccessor.Input P Mn G)
    (hD : 2 ≤ Dm) (H : ℕ) (p : OddSlot) (g n : ℕ) (hg : g ≤ H)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X z : Vec 2) (k : Fin 2) (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    ℓ (liftFluxX Q (nativeStagePathCandidate hi H p) (fun _ => f) g n t X z k v) =
      ∑ u : CompIn G.comps, ∑ q : F.Walk g u v,
        let π := Classical.choose (stage_walk_path q)
        let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
        let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
        liftFluxX Qp C
          (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u))))
          g n t X z k (Fin.last g) := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  let T := topOf (stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp)
    (stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H)
  rw [native_flux_walk_formula_of_two_le hi hD H p g n f hf t ht X z k]
  rw [HLDecomp.hl_dual_sum_walkVec F Finset.univ (fun s : HLIdx G => s.1)
    (fun s => hlVec G s)
    (fun s q => (HLDecomp.hlCtx Q T t (hlCoord G f s)).formX n g (F.walkDat q.2) k X z) v ℓ]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ i : Fin (Module.finrank ℝ (hr u.1.root)), ∑ q : F.Walk g u v,
    (HLDecomp.hlCtx Q T t (hlCoord G f ⟨u, i⟩)).formX n g (F.walkDat q) k X z *
      ℓ (F.compMap q (hlVec G ⟨u, i⟩))) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  exact (walk_path_flux_basis hi hD H p g n hg f hf t ht X z k u v ℓ q).symm

/-- Continuity needed to commute the literal mean with the native flux functional. -/
theorem native_flux_continuous (hi : StageSuccessor.Input P Mn G)
    (hD : 2 ≤ Dm) (H : ℕ) (p : OddSlot) (g n : ℕ)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X : Vec 2) (k : Fin 2) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    Continuous (fun z => liftFluxX Q (nativeStagePathCandidate hi H p) (fun _ => f) g n t X z k) := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  let T := topOf (stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp)
    (stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H)
  obtain ⟨hs, _⟩ := native_stage_path_step_hypotheses hi hD p H
    (Mn.N + 1 + Dm) (Mn.N + 1 + Dm) le_rfl le_rfl
  have he : (fun z => liftFluxX Q (nativeStagePathCandidate hi H p) (fun _ => f) g n t X z k) =
      fun z => ∑ s : HLIdx G, ∑ q : WalkFrom F g s.1,
        (HLDecomp.hlCtx Q T t (hlCoord G f s)).formX n g (F.walkDat q.2) k X z •
          walkVec F (hlVec G s) q :=
    funext (fun z => native_flux_walk_formula_of_two_le hi hD H p g n f hf t ht X z k)
  rw [he]
  exact HLDecomp.hl_continuous_cand_sum F Q T t (hs.goodT (fun _ => 0) ht)
    (fun v u γ => hs.hdat v u γ t ht) (hs.hGr t ht) (hs.hvr t ht)
    Finset.univ (fun s : HLIdx G => s.1) (fun s => hlCoord G f s)
    (fun s => hl_coord_contDiff G hf s) (fun s => hlVec G s) g n X k

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! The native candidate at orders with no identities. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.PathDecomp
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The empty stage path is unique. -/
theorem empty_stage_path_eq (π σ : StagePath G 0) : π = σ := by
  cases π with
  | mk p hp =>
    cases σ with
    | mk s hs =>
      have he : p = s := funext (fun i => Fin.elim0 i)
      subst he
      rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- With no identities, the actual native candidate is the scalar diagonal lift. -/
theorem small_candidate_diagonal (hi : StageSuccessor.Input P Mn G)
    (hD : Dm < 2) (H : ℕ) (p : OddSlot) (π₀ : StagePath G 0) :
    nativeStagePathCandidate hi H p =
      HLZero.hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root)
        (StageSuccessor.pathLiftFamily hi.base hi.profile hi.band
          (Mn.lenFactor * liftLength D G.level) Mn.N π₀ p.1 (G.actual p).1) := by
  classical
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  let Lift := stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp
  let Arise := stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H
  let T := topOf Lift Arise
  have ht (cd : Fin 0 → StepDat) : T 0 cd = topArr (Cp 0 π₀) := by
    have hA : Arise 0 cd := ⟨Nat.zero_le _, π₀, funext (fun i => Fin.elim0 i)⟩
    rw [show T 0 cd = topArr (Lift 0 cd) from StepHyp.topOf_of_arise hA]
    have he : Lift 0 cd = Cp 0 π₀ := by
      change (if hA : Arise 0 cd then Cp 0 (Classical.choose hA.2) else 0) = _
      rw [dite_eq_left hA, empty_stage_path_eq (Classical.choose hA.2) π₀]
    rw [he]
  have hempty (v u : CompIn G.comps) (γ : F.Γ v u) : False := by
    have h₂ := (G.fam.identity v u γ).two_le
    have h₁ := (G.fam.identity v u γ).le_D
    omega
  have hwalk (g : ℕ) (u v : CompIn G.comps) : IsEmpty (F.Walk (g + 1) u v) :=
    ⟨fun q => hempty v q.1 q.2.2⟩
  change cand F T = HLZero.hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root) (Cp 0 π₀)
  funext g n m α t X z v u
  cases g with
  | zero =>
    by_cases huv : u = v
    · subst v
      simp only [cand, HLZero.hlDiagCoeff, ite_true, HLZero.hlDiagMap, dite_true]
      let : Unique (F.Walk 0 u u) := ⟨⟨⟨rfl⟩⟩, fun q => by cases q; rfl⟩
      rw [Fintype.sum_unique, ht]
      simp only [topArr]
      rfl
    · have : IsEmpty (F.Walk 0 u v) := ⟨fun q => huv q.down⟩
      simp only [cand, Finset.univ_eq_empty, Finset.sum_empty,
        HLZero.hlDiagCoeff, ite_true, HLZero.hlDiagMap, dite_eq_right huv, smul_zero]
  | succ g =>
    have := hwalk g u v
    simp only [cand, Finset.univ_eq_empty, Finset.sum_empty,
      HLZero.hlDiagCoeff, Nat.succ_ne_zero, ite_false]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Finite-sum interchange for the literal native walk means. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.PathDecomp
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}

/-- Each scalar walk flux is continuous in the fast variable. -/
theorem walk_path_flux_continuous (hi : StageSuccessor.Input P Mn G)
    (hD : 2 ≤ Dm) (H : ℕ) (p : OddSlot) (g n : ℕ) (hg : g ≤ H)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X : Vec 2) (k : Fin 2) (u v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    ∀ q : F.Walk g u v,
      let π := Classical.choose (stage_walk_path q)
      let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
      let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
      Continuous (fun z => liftFluxX Qp C
        (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u))))
        g n t X z k) := by
  classical
  dsimp only
  intro q
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily
    hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  let T := topOf (stLift G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H Cp)
    (stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H)
  obtain ⟨hs, _⟩ := native_stage_path_step_hypotheses hi hD p H
    (Mn.N + 1 + Dm) (Mn.N + 1 + Dm) le_rfl le_rfl
  let π := Classical.choose (stage_walk_path q)
  let cd := pathDat G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) π
  let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
  let g₀ := fun Y => ℓ (F.compMap q (f Y u))
  have hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀ :=
    ℓ.contDiff.comp ((F.compMap q).contDiff.comp ((contDiff_pi.mp hf) u))
  have hc := native_path_candidate_of_two_le hi hD H p π hg
  have hA : stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p) H g cd :=
    ⟨hg, π, rfl⟩
  have hT := hs.goodT (fun _ => 0) ht
  have hcd := fun i => hs.hcd g cd hA i t ht
  have hdat : ∀ v u (γ : (chainFam cd).Γ v u),
      GoodDat (Mn.N + 1 + Dm) t ((chainFam cd).dat v u γ) := fun v u γ => hcd _
  have hsum := HLDecomp.hl_liftFluxX_cand_sum (chainFam cd) Qp
    (hasFamFlux_pathEdges G G.level p.1 (G.actual p).1 ρ p (G.actual p) π) T t hT hdat
    ({()} : Finset Unit) (w := fun _ => (0 : Fin (g + 1))) (fun _ => g₀)
    (fun _ => hg₀) (fun _ => (1 : ℝ)) g n X
  have hcont := HLDecomp.hl_continuous_cand_sum (chainFam cd) Qp T t hT hdat
    (hs.hGr t ht) (hs.hvr t ht) ({()} : Finset Unit)
    (fun _ => (0 : Fin (g + 1))) (fun _ => g₀) (fun _ => hg₀) (fun _ => (1 : ℝ)) g n X k
  have he : (fun z => liftFluxX Qp (Cp g π) (fun _ Y => Pi.single (0 : Fin (g + 1)) (g₀ Y))
      g n t X z k) = fun z => ∑ s ∈ ({()} : Finset Unit),
        ∑ q : WalkFrom (chainFam cd) g (0 : Fin (g + 1)),
          (HLDecomp.hlCtx Qp T t g₀).formX n g ((chainFam cd).walkDat q.2) k X z •
            walkVec (chainFam cd) (1 : ℝ) q := by
    funext z
    rw [Uniqueness.liftFluxX_congr Qp (Cp g π) (cand (chainFam cd) T) _ g n t
      (fun h hh n' m α => hc h hh n' t ht m α)]
    simpa only [Finset.sum_singleton, smul_eq_mul, mul_one] using hsum z k
  rw [he]
  exact hcont

/-- The literal cell mean expands over actual walks for orders at least two. -/
theorem walk_mean_of_two_le (hi : StageSuccessor.Input P Mn G)
    (hD : 2 ≤ Dm) (H : ℕ) (p : OddSlot) (g n : ℕ) (hg : g ≤ H)
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (X : Vec 2) (k : Fin 2) (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let F := stageFam G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) p (G.actual p)
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    ℓ (fieldCellMean (fun z => liftFluxX Q (nativeStagePathCandidate hi H p)
      (fun _ => f) g n t X z k v)) =
      ∑ u : CompIn G.comps, ∑ q : F.Walk g u v,
        let π := Classical.choose (stage_walk_path q)
        let Qp := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
        let C := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
        fieldCellMean (fun z => liftFluxX Qp C
          (fun _ Y => Pi.single (0 : Fin (g + 1)) (ℓ (F.compMap q (f Y u))))
          g n t X z k) (Fin.last g) := by
  classical
  dsimp only
  have hc := native_flux_continuous hi hD H p g n f hf t ht X k
  rw [← fieldCellMean_clm ℓ ((continuous_pi_iff.mp hc) v)]
  have he := fun z => native_walk_pointwise hi hD H p g n hg f hf t ht X z k v ℓ
  simp_rw [he]
  have hp := fun u q => walk_path_flux_continuous hi hD H p g n hg f hf t ht X k u v ℓ q
  rw [fieldCellMean_sum Finset.univ (fun u _ => continuous_finsetSum _ (fun q _ => (continuous_pi_iff.mp (hp u q)) (Fin.last g)))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [fieldCellMean_sum Finset.univ (fun q _ => (continuous_pi_iff.mp (hp u q)) (Fin.last g))]
  apply Finset.sum_congr rfl
  intro q hq
  exact fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin (g + 1) => ℝ) (Fin.last g)) (hp u q)

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end
