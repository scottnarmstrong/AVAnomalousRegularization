-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Entry.TerminalResidualClauses
public import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Finite.SeedTransport

/-! Restriction to a later initial time uses the integrated weak identity alone. -/

theorem native_reg_solution_restart {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G : GenStage D ScalarH Dm bw j₀) (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (k : ℕ)
    (f : ∀ i : CompIn G.comps, TorusHk k (ScalarH i.1.root))
    (u : ∀ i : CompIn G.comps, ℝ → TorusHk k (ScalarH i.1.root))
    (w : ∀ i : CompIn G.comps, ℝ → TorusHk (k + 1) (ScalarH i.1.root))
    (y : ∀ i j (_ : G.fam.Γ i j), ℝ → TorusHk (k + Dm - 1) (ScalarH j.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν v k a b f
      (fun _ _ => 0) (fun _ _ => 0) u w y) (s : ℝ) (hs : s ∈ Set.Icc a b) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν v k s b (fun i => u i s)
      (fun _ _ => 0) (fun _ _ => 0) u w y := by
  have hsub : Set.Icc s b ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 le_rfl
  have hμ : volume.restrict (Set.Icc s b) ≤ volume.restrict (Set.Icc a b) :=
    Measure.restrict_mono hsub le_rfl
  refine ⟨(fun i => (hsol.1 i).mono hsub), (fun i => (hsol.2.1 i).mono_measure hμ),
    (fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 i)),
    (fun _ => rfl), (fun i j γ => (hsol.2.2.2.2.1 i j γ).mono_measure hμ),
    (fun i j γ => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.2.2.2.1 i j γ)), ?_⟩
  intro i t ht φ
  exact KernelEnergy.weakIdentity_restart (volume.restrict AVenhance.unitCube) ν a s t hs.1 ht.1 v
    ((u i t).toFunction.jet (valueIndex2 k)) ((u i s).toFunction.jet (valueIndex2 k))
    ((f i).toFunction.jet (valueIndex2 k)) (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (fun r x => ∑ j : CompIn G.comps, ∑ γ : G.fam.Γ i j, ∑ d : ↥(Finset.Icc 2 Dm),
      G.physCoeff i j γ d.1 r x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (y i j γ r).toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x))
    (fun r => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH i.1.root))).toFunction.jet (valueIndex2 k))
    (fun r => (0 : TorusHk k (ScalarH i.1.root)).toFunction.jet (valueIndex2 k))
    (hsol.2.2.2.2.2.2 i t (hsub ht) φ) (hsol.2.2.2.2.2.2 i s hs φ)

end AVRegularity.Finite.SeedTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Finite.SeedTransport

/-! The terminal re-rooting preserves each literal kernel and each physical coefficient. -/

theorem seed_encoding_operators {D : OCData} {Dt Ds : ℕ} {b : ℝ} {j₀ : ℕ}
    (Pt P : ProvParams) (lawT : BirthLaw) (rootM rootR : ℕ → ℝ)
    (seedKt freshKt seedKc freshK : ℕ → KernelSpec)
    (Gt : GenStage D ScalarH Dt b j₀) (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (henc : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι) :
    ∃ e : ∀ v u, Gt.fam.Γ v u ≃ seed.fam.Γ (ι v) (ι u),
      ∀ v u (γ : Gt.fam.Γ v u),
        seed.kernelOf P seedKc freshK (ι v) (ι u) (e v u γ) = Gt.kernelOf Pt seedKt freshKt v u γ ∧
        (seed.fam.identity (ι v) (ι u) (e v u γ)).maxOrder = (Gt.fam.identity v u γ).maxOrder ∧
        ∀ d, seed.physCoeff (ι v) (ι u) (e v u γ) d = Gt.physCoeff v u γ d := by
  rcases henc with ⟨hlevel, _hbirths, _hmass, hactual, hpiece, hweight, e, idx, _hinj, hdata⟩
  refine ⟨e, ?_⟩
  intro v u γ
  rcases hdata v u γ with ⟨hprov, hkernel, hmap, _hrecord, hmax, hflux⟩
  refine ⟨?_, hmax, ?_⟩
  · unfold GenStage.kernelOf
    rw [hprov]
    exact hkernel
  · intro d
    have hdim (p : OddSlot) (d' : ℕ) (I : DerivativeWord2 (d' - 1)) (t : ℝ) (Y z : Vec 2) :
        seed.fam.dimFlux (D.kap seed.level) (D.eps seed.level) (D.eps (seed.level - 1))
          p (seed.actual p) (ι v) (ι u) (e v u γ) d' I t Y z =
        Gt.fam.dimFlux (D.kap Gt.level) (D.eps Gt.level) (D.eps (Gt.level - 1))
          p (Gt.actual p) v u γ d' I t Y z := by
      dsimp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux]
      rw [hflux p (seed.actual p) (Gt.actual p) (hactual p), hlevel]
    funext t x
    dsimp only [GenStage.physCoeff, constituentPhysical]
    simp only [hweight, hpiece, hmap, hmax, hdim]
    rw [hlevel]

/-! The physical flux reads only the shared retained orders, irrespective of ambient caps. -/

def kernelJetArray {K : ℕ} (y : TorusHk K ℝ) (d : ℕ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d - 1) => ℝ) :=
  if h : d - 1 ≤ K then
    WithLp.toLp 2 fun I => y.toFunction.jet ⟨⟨d - 1, Nat.lt_succ_of_le h⟩, I⟩ x
  else 0

theorem kernelJetArray_of_le {K : ℕ} (y : TorusHk K ℝ) (d : ℕ) (h : d - 1 ≤ K) :
    kernelJetArray y d = fun x => WithLp.toLp 2 fun I =>
      y.toFunction.jet ⟨⟨d - 1, Nat.lt_succ_of_le h⟩, I⟩ x := by
  funext x
  exact dite_eq_left h

theorem kernelJetArray_eq_of_value {K L : ℕ} (y : TorusHk K ℝ) (z : TorusHk L ℝ)
    (h : y.val (valueIndex2 K) = z.val (valueIndex2 L)) (d : ℕ)
    (hK : d - 1 ≤ K) (hL : d - 1 ≤ L) : kernelJetArray y d = kernelJetArray z d := by
  have he : truncateTorusHk (min_le_left K L) y = truncateTorusHk (min_le_right K L) z := by
    apply TorusHk.ext_value
    exact h
  have hmin : d - 1 ≤ min K L := le_min hK hL
  rw [kernelJetArray_of_le y d hK, kernelJetArray_of_le z d hL]
  funext x
  apply WithLp.ofLp_injective 2
  funext I
  exact congrArg (fun u : TorusHk (min K L) ℝ =>
    u.toFunction.jet ⟨⟨d - 1, Nat.lt_succ_of_le hmin⟩, I⟩ x) he

theorem physical_order_sum_support {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D ScalarH Dm bw j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (y : TorusHk (0 + Dm - 1) ℝ) (t : ℝ) (x : Vec 2) :
    (∑ d : ↥(Finset.Icc 2 Dm), G.physCoeff v u γ d.1 t x
      (WithLp.toLp 2 fun I => y.toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, I⟩ x)) =
    ∑ d ∈ Finset.Icc 2 (G.fam.identity v u γ).maxOrder,
      G.physCoeff v u γ d t x (kernelJetArray y d x) := by
  classical
  have hsum : (∑ d : ↥(Finset.Icc 2 Dm), G.physCoeff v u γ d.1 t x
      (WithLp.toLp 2 fun I => y.toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, I⟩ x)) =
      ∑ d : ↥(Finset.Icc 2 Dm), G.physCoeff v u γ d.1 t x (kernelJetArray y d.1 x) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [kernelJetArray_of_le _ _ (by have := Finset.mem_Icc.1 d.2; omega)]
  rw [hsum, Finset.sum_coe_sort (Finset.Icc 2 Dm)
    (fun d => G.physCoeff v u γ d t x (kernelJetArray y d x))]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (G.fam.identity v u γ).le_D)
  intro d hd hn
  have hmax : (G.fam.identity v u γ).maxOrder < d := by
    have hlow := (Finset.mem_Icc.1 hd).1
    simp only [Finset.mem_Icc, not_and] at hn
    exact lt_of_not_ge (hn hlow)
  rw [GenStage.physCoeff, CycleJointProofs.constituentPhysical_zero_above_max G.fam _ _ _ G.actual v u γ d hmax t x]
  rfl

end AVRegularity.Finite.SeedTransport
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Finite.SeedTransport

/-! Finite reindexing and weak-jet uniqueness identify the kernel-paid seed flux. -/

theorem seed_flux_reencoding {D : OCData} {Dt Ds : ℕ} {bw : ℝ} {j₀ : ℕ}
    (Pt P : ProvParams) (seedKt freshKt seedKc freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (Gt : GenStage D ScalarH Dt bw j₀) (seed : GenStage D ScalarH Ds bw j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (e : ∀ v u, Gt.fam.Γ v u ≃ seed.fam.Γ (ι v) (ι u))
    (he : ∀ v u (γ : Gt.fam.Γ v u),
      seed.kernelOf P seedKc freshK (ι v) (ι u) (e v u γ) = Gt.kernelOf Pt seedKt freshKt v u γ ∧
      (seed.fam.identity (ι v) (ι u) (e v u γ)).maxOrder = (Gt.fam.identity v u γ).maxOrder ∧
      ∀ d, seed.physCoeff (ι v) (ι u) (e v u γ) d = Gt.physCoeff v u γ d)
    {a b ρ ν : ℝ}
    (R : KernelEnergy.TorusKernelOperator (h := fun w : CompIn seed.comps => ScalarH w.1.root)
      (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) a b ρ ν 0 Ds)
    (hB : R.B = fun w u γ (d : ↥(Finset.Icc 2 Ds)) => seed.physCoeff w u γ d.1)
    (hC : R.C = fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
    (hS : R.S = seed.sysS P seedKc freshK φ₀ hφ₀)
    (w : CompIn Gt.comps → ℝ → TorusHk 1 ℝ)
    (y : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (0 + Dt - 1) ℝ)
    (hy : ∀ v u γ, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (y v u γ t).val (valueIndex2 (0 + Dt - 1)) =
      Gt.sysS Pt seedKt freshKt φ₀ hφ₀ v u γ t
        ((ContinuousLinearMap.id ℝ ℝ).compLp ((w u t).val (valueIndex2 1)))) (v : CompIn Gt.comps) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ x,
      R.kernelRawFlux (fun u => w (ι.symm u)) (ι v) t x =
      ∑ u : CompIn Gt.comps, ∑ γ : Gt.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dt),
        Gt.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun I =>
          (y v u γ t).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, I⟩ x) := by
  classical
  let ws := fun u => w (ι.symm u)
  have hvalue (u : CompIn Gt.comps) (γ : Gt.fam.Γ v u) :
      ∀ᵐ t ∂volume.restrict (Set.Icc a b),
        (y v u γ t).val (valueIndex2 (0 + Dt - 1)) =
        (R.higherInput ws (ι v) (ι u) (e v u γ) t).val (valueIndex2 (0 + Ds - 1)) := by
    filter_upwards [hy v u γ, R.higherInput_value_ae ws (ι v) (ι u) (e v u γ)] with t ht hs
    rw [hs, hC, hS]
    simp only [ws, ι.symm_apply_apply]
    unfold GenStage.sysS
    rw [(he v u γ).1]
    exact ht
  filter_upwards [ae_all_iff.mpr (fun u => ae_all_iff.mpr (hvalue u))] with t ht
  intro x
  unfold KernelEnergy.TorusKernelOperator.kernelRawFlux
  rw [← ι.sum_comp (fun u => ∑ γ : seed.fam.Γ (ι v) u, ∑ d : ↥(Finset.Icc 2 Ds),
    R.B (ι v) u γ d t x (WithLp.toLp 2 fun I =>
      (R.higherInput ws (ι v) u γ t).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, I⟩ x))]
  apply Finset.sum_congr rfl
  intro u _
  rw [← (e v u).sum_comp (fun γ => ∑ d : ↥(Finset.Icc 2 Ds),
    R.B (ι v) (ι u) γ d t x (WithLp.toLp 2 fun I =>
      (R.higherInput ws (ι v) (ι u) γ t).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, I⟩ x))]
  apply Finset.sum_congr rfl
  intro γ _
  rw [hB, physical_order_sum_support, physical_order_sum_support, (he v u γ).2.1]
  apply Finset.sum_congr rfl
  intro d hd
  have hds : d ≤ (seed.fam.identity (ι v) (ι u) (e v u γ)).maxOrder := by
    rw [(he v u γ).2.1]
    exact (Finset.mem_Icc.1 hd).2
  have hKt : d - 1 ≤ 0 + Dt - 1 :=
    by simpa only [Nat.zero_add] using
      Nat.sub_le_sub_right ((Finset.mem_Icc.1 hd).2.trans (Gt.fam.identity v u γ).le_D) 1
  have hKs : d - 1 ≤ 0 + Ds - 1 :=
    by simpa only [Nat.zero_add] using
      Nat.sub_le_sub_right (hds.trans (seed.fam.identity (ι v) (ι u) (e v u γ)).le_D) 1
  rw [(he v u γ).2.2 d, ← kernelJetArray_eq_of_value _ _ (ht u γ) d hKt hKs]

end AVRegularity.Finite.SeedTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.KernelEnergy AVRegularity.KernelEnergy.TorusKernelOperator
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Finite.SeedTransport

/-! A literal kernel flux identity supplies the kernel-paid higher input lift. -/

theorem kernel_solution_of_flux {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)] {a b ρ ν : ℝ} {Ds : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun _ : ι => ℝ)
      (Γ := Γ) (G := fun _ _ _ => ℝ) a b ρ ν 0 Ds)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (f : ι → TorusHk 0 ℝ) (U : ι → ℝ → TorusHk 0 ℝ) (W : ι → ℝ → TorusHk 1 ℝ)
    (Q : ι → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℝ))
    (hu : ∀ i, ContinuousOn (U i) (Set.Icc a b))
    (hw : ∀ i, MemLp (W i) 2 (volume.restrict (Set.Icc a b)))
    (htrace : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncateTorusHk (Nat.le_succ 0) (W i t) = U i t)
    (hinit : ∀ i, U i a = f i)
    (hflux : ∀ i, Q i =ᵐ[volume.restrict (Set.Icc a b)] R.kernelRawFlux W i)
    (hweak : ∀ i, ∀ t ∈ Set.Icc a b, ∀ ψ : TorusHk 1 ℝ,
      CoupledWeakIdentity (volume.restrict unitCube) ν a t (streamVel φ)
        ((U i t).toFunction.jet (valueIndex2 0)) ((f i).toFunction.jet (valueIndex2 0))
        (ψ.toFunction.jet (valueIndex2 1))
        (fun q => ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
        (fun r q => (W i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => q⟩)
        (Q i) (fun _ => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))).toFunction.jet (valueIndex2 0))
        (fun _ => (0 : TorusHk 0 ℝ).toFunction.jet (valueIndex2 0))) :
    IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 Ds R.B R.C R.S f
      (fun _ _ => 0) (fun _ _ => 0) U W (R.higherInput W) := by
  obtain ⟨_hv, _hp, _hd, ⟨V, hV⟩, _hm⟩ := Construction.Preservation.Buffer.stream_kernel_drift_data hφ a b
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hV t ht x).trans (le_max_left _ _)
  refine ⟨hu, hw, htrace, hinit, R.higherInput_memLp W hw, R.higherInput_value_ae W, ?_⟩
  intro i t ht ψ
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hf : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ∀ᵐ x ∂volume.restrict unitCube,
      Q i r x + (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))).toFunction.jet (valueIndex2 0) x =
      R.kernelRawFlux W i r x + (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))).toFunction.jet (valueIndex2 0) x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hflux i)] with r hr
    exact Filter.Eventually.of_forall (fun x => congrArg (fun F => F x + _) hr)
  have hpoint : ∀ r ∈ Set.Ioc a t, Integrable (fun x =>
      -(∑ q : Fin 2, streamVel φ r x q * inner ℝ
        ((W i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => q⟩ x) (ψ.toFunction.jet (valueIndex2 1) x)) -
      ν * ∑ q : Fin 2, inner ℝ ((W i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => q⟩ x)
        (ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ x) -
      ∑ q : Fin 2, inner ℝ (R.kernelRawFlux W i r x q +
        (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))).toFunction.jet (valueIndex2 0) x q)
        (ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ x) +
      inner ℝ ((0 : TorusHk 0 ℝ).toFunction.jet (valueIndex2 0) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) (volume.restrict unitCube) := by
    intro r hr
    have hi := (torusRawSpatialRhs_integrable_and_integral (h := fun _ : ι => ℝ)
      (fun _ => 0) 0 ν ρ R.radius_pos a b r (hsub hr) (streamVel φ)
      (_hv r (hsub hr)).continuous
      (max V 0) hV0 (hbV r (hsub hr)) noLocalCoefficient
      (noLocalSeminorm (h := fun _ : ι => ℝ) (k := 0) (ρ := ρ) (a := a) (b := b))
      (fun j j' d => (noLocalSmoothOnInterval (h := fun _ : ι => ℝ) (k := 0) r (hsub hr) j j' d).continuous)
      (fun j s => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))) + R.carrierFlux W j s)
      (fun _ _ => 0) (fun j => W j r) i ψ).1
    apply hi.congr
    filter_upwards [R.totalCarrierFlux_raw_ae W (fun _ _ => 0) i r (hsub hr)] with x hx
    dsimp only [torusRawSpatialRhs]
    change _ - (∑ q : Fin 2, inner ℝ ((torusRawCouplingFlux (fun _ => 0) 0 r noLocalCoefficient
      (fun j => W j r) i x + (0 + R.carrierFlux W i r).toFunction.jet (valueIndex2 0) x) q) _) + _ = _
    rw [hx]
    rfl
  exact KernelEnergy.weakIdentity_flux_congr_time (volume.restrict unitCube) ν a t (streamVel φ)
    ((U i t).toFunction.jet (valueIndex2 0)) ((f i).toFunction.jet (valueIndex2 0))
    (ψ.toFunction.jet (valueIndex2 1))
    (fun q => ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (W i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => q⟩)
    (Q i) (fun _ => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))).toFunction.jet (valueIndex2 0))
    (R.kernelRawFlux W i) (fun _ => (0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))).toFunction.jet (valueIndex2 0))
    (fun _ => (0 : TorusHk 0 ℝ).toFunction.jet (valueIndex2 0)) hf hpoint (hweak i t ht ψ)

end AVRegularity.Finite.SeedTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Finite.SeedTransport

/-! Order-zero re-rooting with the seed kernel's own Sobolev lift. -/

theorem reencoded_reg_solution {D : OCData} {Dt Ds : ℕ} {bw : ℝ} {j₀ : ℕ}
    (Pt P : ProvParams) (lawT : BirthLaw) (rootM rootR : ℕ → ℝ)
    (seedKt freshKt seedKc freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (Gt : GenStage D ScalarH Dt bw j₀) (seed : GenStage D ScalarH Ds bw j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (henc : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    {sn tf ρ ν : ℝ} {φ : ℝ → Vec 2 → ℝ}
    (R : KernelEnergy.TorusKernelOperator (h := fun w : CompIn seed.comps => ScalarH w.1.root)
      (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) sn tf ρ ν 0 Ds)
    (hB : R.B = fun w u γ (d : ↥(Finset.Icc 2 Ds)) => seed.physCoeff w u γ d.1)
    (hC : R.C = fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
    (hS : R.S = seed.sysS P seedKc freshK φ₀ hφ₀) (hφ : IsAdmissibleStream φ)
    (f : CompIn Gt.comps → TorusHk 0 ℝ)
    (Ut : CompIn Gt.comps → ℝ → TorusHk 0 ℝ)
    (Wt : CompIn Gt.comps → ℝ → TorusHk 1 ℝ)
    (Yt : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (0 + Dt - 1) ℝ)
    (hrest : Gt.IsRegSolution Pt seedKt freshKt φ₀ hφ₀ ν (streamVel φ) 0 sn tf f
      (fun _ _ => 0) (fun _ _ => 0) Ut Wt Yt) :
    seed.IsRegSolution P seedKc freshK φ₀ hφ₀ ν (streamVel φ) 0 sn tf (fun v => f (ι.symm v))
      (fun _ _ => 0) (fun _ _ => 0) (fun v => Ut (ι.symm v)) (fun v => Wt (ι.symm v))
      (R.higherInput (fun v => Wt (ι.symm v))) := by
  classical
  obtain ⟨e, he⟩ := seed_encoding_operators Pt P lawT rootM rootR seedKt freshKt seedKc freshK
    Gt seed ι henc
  let Us : CompIn seed.comps → ℝ → TorusHk 0 ℝ := fun v => Ut (ι.symm v)
  let Ws : CompIn seed.comps → ℝ → TorusHk 1 ℝ := fun v => Wt (ι.symm v)
  let Qt (v : CompIn Gt.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℝ) :=
    ∑ u : CompIn Gt.comps, ∑ γ : Gt.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dt),
      Gt.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun I =>
        (Yt v u γ t).toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, I⟩ x)
  have hflux (v : CompIn seed.comps) :
      Qt (ι.symm v) =ᵐ[volume.restrict (Set.Icc sn tf)] R.kernelRawFlux Ws v := by
    have h := seed_flux_reencoding Pt P seedKt freshKt seedKc freshK φ₀ hφ₀ Gt seed ι e he
      R hB hC hS Wt Yt hrest.2.2.2.2.2.1 (ι.symm v)
    filter_upwards [h] with t ht
    funext x
    let fluxAt (z : CompIn seed.comps) : PiLp 2 (fun _ : Fin 2 => ℝ) := R.kernelRawFlux Ws z t x
    have hindex : fluxAt (ι (ι.symm v)) = fluxAt v := congrArg fluxAt (ι.apply_symm_apply v)
    exact (ht x).symm.trans hindex
  have hsol := kernel_solution_of_flux R hφ (fun v => f (ι.symm v)) Us Ws
    (fun v => Qt (ι.symm v))
    (fun v => hrest.1 (ι.symm v)) (fun v => hrest.2.1 (ι.symm v))
    (fun v => hrest.2.2.1 (ι.symm v)) (fun v => hrest.2.2.2.1 (ι.symm v)) hflux
    (fun v t ht ψ => hrest.2.2.2.2.2.2 (ι.symm v) t ht ψ)

  simpa only [GenStage.IsRegSolution, hB, hC, hS] using hsol

/-! The order-zero native kernel-energy budget gives uniqueness without a positive-jet
drift estimate. The stream facts are supplied by OCData itself. -/

def seedKernelOperator {D : OCData} {Ds : ℕ} {bw : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedKc freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (seed : GenStage D ScalarH Ds bw j₀) (M : ℕ) (sn tf ρ θ : ℝ)
    (π : CompIn seed.comps → ℝ) (cker : ℕ → ℝ) (hsn : sn ≤ tf)
    (hρ : 0 < ρ) (hν : 0 < D.κ (M - 1)) (hDs : 2 ≤ Ds)
    (hπ : ∀ w, 0 < π w) (hθ : θ ≤ 1 / 8)
    (hcoeff : ∀ w u (γ : seed.fam.Γ w u) (d : ↥(Finset.Icc 2 Ds)),
        (Measurable fun q : Set.Icc sn tf × Vec 2 => seed.physCoeff w u γ d.1 q.1 q.2) ∧
        (∀ t ∈ Set.Icc sn tf, ContDiff ℝ (0 : ℕ) (seed.physCoeff w u γ d.1 t)) ∧
        (∀ t ∈ Set.Icc sn tf, AVenhance.IsZ2Periodic (seed.physCoeff w u γ d.1 t)) ∧
        coefficientSeminorm ρ 0 sn tf (seed.physCoeff w u γ d.1) ≠ ⊤)
    (hkernel : ∀ w u (γ : seed.fam.Γ w u),
        0 < (seed.kernelOf P seedKc freshK w u γ).width ∧
        IsSpatialRegularizerTorus ρ 0 Ds sn tf cker (seed.kernelOf P seedKc freshK w u γ).width
          (seed.sysS P seedKc freshK φ₀ hφ₀ w u γ))
    (hschur : SchurBound θ (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun w => ScalarH w.1.root)
        (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.κ (M - 1)) ρ π 0 Ds sn tf cker
        (fun w u γ => (seed.kernelOf P seedKc freshK w u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun w u γ d => seed.physCoeff w u γ d.1)))
    : KernelEnergy.TorusKernelOperator (h := fun w : CompIn seed.comps => ScalarH w.1.root)
      (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) sn tf ρ (D.κ (M - 1)) 0 Ds :=
{
    htime := hsn
    radius_pos := hρ
    diffusivity_pos := hν
    order_ge_two := hDs
    π := π
    hπ := hπ
    B := fun w u γ d => seed.physCoeff w u γ d.1
    hB_meas := fun w u γ d => (hcoeff w u γ d).1
    hB_smooth := fun w u γ d => (hcoeff w u γ d).2.1
    hB_per := fun w u γ d => (hcoeff w u γ d).2.2.1
    hB_fin := fun w u γ d => (hcoeff w u γ d).2.2.2
    C := fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root)
    S := seed.sysS P seedKc freshK φ₀ hφ₀
    c := cker
    r := fun w u γ => (seed.kernelOf P seedKc freshK w u γ).width
    hr := fun w u γ => (hkernel w u γ).1
    hS := fun w u γ => (hkernel w u γ).2
    θ := θ
    hθ := hθ
    hschur := hschur
  }

theorem seed_order_zero_unique {D : OCData} {Ds : ℕ} {bw : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (seed : GenStage D ScalarH Ds bw j₀) (M : ℕ) {sn tf ρ : ℝ}
    (R : KernelEnergy.TorusKernelOperator (h := fun w : CompIn seed.comps => ScalarH w.1.root)
      (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) sn tf ρ (D.κ (M - 1)) 0 Ds)
    (hB : R.B = fun w u γ (d : ↥(Finset.Icc 2 Ds)) => seed.physCoeff w u γ d.1)
    (hC : R.C = fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
    (hS : R.S = seed.sysS P seedK freshK φ₀ hφ₀)
    (f : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root))
    (U V : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
    (Uw Vw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
    (Uk Vk : ∀ w u (_ : seed.fam.Γ w u), ℝ → TorusHk (0 + Ds - 1) (ScalarH u.1.root))
    (hU : seed.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1)))
      0 sn tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk)
    (hV : seed.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1)))
      0 sn tf f (fun _ _ => 0) (fun _ _ => 0) V Vw Vk) :
    ∀ w, ∀ t ∈ Set.Icc sn tf, U w t = V w t := by
  have hsmall : (1 : ℝ) * ρ / (2 * ρ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) R.radius_pos)).mpr
    ring_nf
    exact le_rfl
  exact Construction.Preservation.FullLift.native_reg_solution_unique P seedK freshK φ₀ hφ₀ seed
    R hB hC hS (D.hΦ (M - 1)) 0 1 (2 * ρ) (le_refl 0) (le_refl 1)
    (mul_pos (by norm_num) R.radius_pos) hsmall
    (by simpa using (div_pos R.diffusivity_pos (by norm_num)).le)
    (fun _ _ _ hl _ => by omega) f U V Uw Vw Uk Vk hU hV

theorem seed_order_zero_unique_of_budget {D : OCData} {Ds : ℕ} {bw : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedKc freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (seed : GenStage D ScalarH Ds bw j₀) (M : ℕ) (sn tf ρ θ : ℝ)
    (π : CompIn seed.comps → ℝ) (cker : ℕ → ℝ) (hsn : sn ≤ tf)
    (hρ : 0 < ρ) (hν : 0 < D.κ (M - 1)) (hDs : 2 ≤ Ds)
    (hπ : ∀ w, 0 < π w) (hθ : θ ≤ 1 / 8)
    (hcoeff : ∀ w u (γ : seed.fam.Γ w u) (d : ↥(Finset.Icc 2 Ds)),
        (Measurable fun q : Set.Icc sn tf × Vec 2 => seed.physCoeff w u γ d.1 q.1 q.2) ∧
        (∀ t ∈ Set.Icc sn tf, ContDiff ℝ (0 : ℕ) (seed.physCoeff w u γ d.1 t)) ∧
        (∀ t ∈ Set.Icc sn tf, AVenhance.IsZ2Periodic (seed.physCoeff w u γ d.1 t)) ∧
        coefficientSeminorm ρ 0 sn tf (seed.physCoeff w u γ d.1) ≠ ⊤)
    (hkernel : ∀ w u (γ : seed.fam.Γ w u),
        0 < (seed.kernelOf P seedKc freshK w u γ).width ∧
        IsSpatialRegularizerTorus ρ 0 Ds sn tf cker (seed.kernelOf P seedKc freshK w u γ).width
          (seed.sysS P seedKc freshK φ₀ hφ₀ w u γ))
    (hschur : SchurBound θ (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun w => ScalarH w.1.root)
        (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.κ (M - 1)) ρ π 0 Ds sn tf cker
        (fun w u γ => (seed.kernelOf P seedKc freshK w u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun w u γ d => seed.physCoeff w u γ d.1)))

    (f : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root))
    (U V : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
    (Uw Vw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
    (Uk Vk : ∀ w u (_ : seed.fam.Γ w u), ℝ → TorusHk (0 + Ds - 1) (ScalarH u.1.root))
    (hU : seed.IsRegSolution P seedKc freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1)))
      0 sn tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk)
    (hV : seed.IsRegSolution P seedKc freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1)))
      0 sn tf f (fun _ _ => 0) (fun _ _ => 0) V Vw Vk) :
    ∀ w, ∀ t ∈ Set.Icc sn tf, U w t = V w t := by
  let R := seedKernelOperator P seedKc freshK φ₀ hφ₀ seed M sn tf ρ θ π cker
    hsn hρ hν hDs hπ hθ hcoeff hkernel hschur
  exact seed_order_zero_unique P seedKc freshK φ₀ hφ₀ seed M R rfl rfl rfl f U V Uw Vw Uk Vk hU hV

end AVRegularity.Finite.SeedTransport
end
end
end
