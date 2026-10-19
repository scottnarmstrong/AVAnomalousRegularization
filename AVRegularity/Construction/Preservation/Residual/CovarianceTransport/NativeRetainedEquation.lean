-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.NativeWeakLiftFamilies
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeKernelFluxTime
import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
public import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovarianceFluxRegLiftFlux
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVenhance.Infra.Classical.Drift

/-! Reserved native fluxes of the actual retained solution. The solution's existing
higher kernel representatives, rather than a new kernel-energy existence argument,
are used throughout. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Set Filter
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

section NativeMeanCoefficientReserves
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift AVRegularity.WeakEntryProofs

/-- Genuine native predecessor models and primitive models produce a bounded local
model of every actual mean coefficient, including degrees above the lift cutoff. -/
theorem native_mean_coefficient_local_reserve {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Dm : ℕ} (H : ℕ) (hDm : 1 ≤ Dm) (hDH : Dm ≤ H)
    (a b : ℝ) (hab : a ≤ b) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (Q Q' : LiftOperatorData ι (fun _ => ℝ) Dm) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ) (hn : 2 ≤ n)
    (P : LocalFullLiftPredecessorData (H + Dm + 2) a b Ω Y₀
      (weakLiftInverseCoefficients Q inv N) N hh n)
    (V : Set (Vec 2)) (hV : IsOpen V) (hYV : Y₀ ∈ V)
    (hG : ∀ t ∈ Icc a b, ∀ Y ∈ V, Q.G t Y = Q'.G t Y)
    (hΓ : ∀ t ∈ Icc a b, SlowOpenEdgeEq V t Q.edge Q'.edge)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => Q'.G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => Q'.v t z i))
    (Qedge : ∀ v u d, ∀ γ ∈ Q'.edge v u d, ∀ β,
      JointSourceReserve H (fun t z Y => γ.coeff β t Y z))
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (v u : ι) (k : Fin 2) :
    ∃ (U : Set (Vec 2)) (f : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧ Nonempty (JointSourceReserve H f) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        f t z Y = actualMeanFluxCoefficient Q (weakLiftInverseCoefficients Q inv N)
          hh n k m α t Y z v u 1 := by
  let Cc := weakLiftInverseCoefficients Q inv N
  obtain ⟨χ, hs, hone, ⟨Qc⟩⟩ := weakLiftInverseCoefficients_local_cutoff_reserve
    a b hab Ω hΩ Y₀ hYΩ Q inv N hh n P.initial_zero P.local_reserve
  obtain ⟨W, hW, hYW, hWΩ, hχ⟩ := unit_cutoff_open_neighborhood χ Ω hΩ Y₀ hYΩ hone
  let U := W ∩ V
  let Dc := fullLiftLocalCutoff χ a b Cc
  have hzero p (hp : p ≠ 0) : Cc p 0 = 0 := by
    funext l β t Y z v u
    exact weakLiftInverseCoefficients_positive_grade_zero Q inv N p (by omega) l β t Y z v u
  have hmean p q (hpq : p < hh ∨ (p = hh ∧ q < n)) (hne : p ≠ 0 ∨ q ≠ 0)
      l (hl : l ≤ q) (β : DerivativeWord2 l) t Y v u ξ :
      fieldCellMean (fun z => Dc p q l β t Y z v u ξ) = 0 :=
    fullLiftLocalCutoff_rank_mean_zero χ a b hab Ω hs Cc p q hne (hzero p)
      l β v u (fun t ht Y hY ξ => P.mean_zero p q hpq hne l hl β t ht Y hY v u ξ) t Y ξ
  have hperm β (σ : Equiv.Perm (Fin m)) : Dc hh (n - 1) m (β ∘ σ) = Dc hh (n - 1) m β :=
    fullLiftLocalCutoff_perm χ a b Cc hh (n - 1) m β σ
      (weakLiftInverseCoefficients_perm Q inv N hh (n - 1) m β σ)
  let R := actualMeanCoefficientReserve H hDm hDH Q' Dc hh n hn m hm α v u k
    QG Qv Qc Qedge hmean hperm
  refine ⟨U, _, hW.inter hV, ⟨hYW, hYV⟩, fun _ hY => hWΩ hY.1, ⟨R⟩, ?_⟩
  intro t ht Y hYU z
  have he := actualMeanFluxCoefficient_slow_local_primitive_congr U (hW.inter hV)
    Q Q' hη hv Cc Dc hh n (by omega) t (fun Y hY => hG t ht Y hY.2)
    ((hΓ t ht).mono (fun _ hY => hY.2))
    (fun p q _ l _ β X hX z v u =>
      (fullLiftLocalCutoff_copy χ a b Cc p q l β t ht X (hχ X hX.1) z v u).symm)
    k m hm α Y hYU z v u
  exact (congrArg (fun L => L (1 : ℝ)) he).symm

/-- At every finite order, each actual path mean coefficient has a genuine
bounded local model throughout the closed pulse window and the whole slow space. -/
theorem native_stage_path_mean_coefficient_local_reserve
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
    {G : GenStage D hr Dm bw j₀} (hi : StageSuccessor.Input P Mn G)
    {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (R hh n m : ℕ) (hhh : hh ≤ h) (hn : 2 ≤ n) (hm : m ≤ n - 1)
    (α : DerivativeWord2 m) (v u : Fin (h + 1)) (k : Fin 2) (Y₀ : Vec 2) :
    let ρ := Mn.lenFactor * liftLength D G.level
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
    let Cc := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
    ∃ (U : Set (Vec 2)) (f : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve R f) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        f t z Y = actualMeanFluxCoefficient Q Cc hh n k m α t Y z v u 1 := by
  classical
  dsimp only
  rw [native_stage_path_family_eq_inverse hi π p]
  let ρ := Mn.lenFactor * liftLength D G.level
  let A := (G.actual p).1
  let edge := pathEdges G π p (G.actual p)
  let Q := familyLiftData D G.level p.1 A ρ edge
  let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  have hab : a < b := weakData_lift_window_strict D hi.base hi.profile hi.band G.level p.1
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y =>
    nativeWindowResponseLinear D hi.profile G.level p.1 p.2 A ρ edge 1 le_rfl a b hab.le Y
  let Cc := weakLiftInverseCoefficients Q inv Mn.N
  let H := max R Dm
  let S := H + Dm + 2
  let base := S + 2 * Dm + 5
  obtain ⟨kI, hcontext⟩ := hi.context
  have hE : ∀ L Y, Y ∈ (univ : Set (Vec 2)) → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)), IsOpen V ∧ Y ∈ V ∧
      (∀ t ∈ Icc a b, SlowOpenEdgeEq V t Q.edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve L (fun t z Y => γ.coeff β t Y z)) := by
    intro L Y _
    apply StageSuccessor.context_path_local_reserves hi.base hi.profile hi.band hi.bandwidth
      G hcontext π p.1 p.2 ρ A (G.actual p).2 L Y
    rw [native_actual_ladderOmega_eq_univ hi p ρ]
    exact mem_univ Y
  have hp := native_full_lift_rank_induction D hi.profile hi.base G.level
    (weakData_kap_pos D hi.base hi.profile hi.band G.level) p.1 p.2 A (G.actual p).2.2.2.1
    ρ edge a b hab 1 le_rfl base Mn.N h hi.order (by dsimp only [base]; omega)
    univ isOpen_univ hE
  have Pd : LocalFullLiftPredecessorData S a b univ Y₀ Cc Mn.N hh n := by
    apply localFullLiftPredecessors_of_rank_properties S a b univ Y₀ (mem_univ _) Cc Mn.N hh n
      (fun p q => weakLiftRankReserve Dm base Mn.N h p q)
    · intro p q _ _ _
      exact (show S ≤ base + 1 by dsimp only [base]; omega).trans
        (weakLiftRankReserve_base Dm base Mn.N h p q)
    · intro p q hpq hq hqN l hl β v u
      exact hp p q (by rcases hpq with hp | ⟨rfl, _⟩ <;> omega) hq hqN l hl β v u
    · intro p hp
      funext l β t Y z v u
      exact weakLiftInverseCoefficients_positive_grade_zero Q inv Mn.N p (by omega) l β t Y z v u
    · exact weakLiftInverseCoefficients_cutoff Q inv Mn.N
  obtain ⟨V, edge', hV, hYV, he, ⟨Qedge⟩⟩ := hE H Y₀ (mem_univ _)
  obtain ⟨Q', W, hW, hYW, hη, hv, hG, hΓ, ⟨QG⟩, ⟨Qv⟩, ⟨Qe⟩, _hvm⟩ :=
    native_local_primitive_source_model D hi.profile hi.base G.level
      (weakData_kap_pos D hi.base hi.profile hi.band G.level) p.1 p.2 A (G.actual p).2.2.2.1
      ρ edge a b hab.le H Y₀ V hV hYV edge' he Qedge
  obtain ⟨U, f, hU, hYU, _hUΩ, ⟨Qf⟩, hf⟩ := native_mean_coefficient_local_reserve H hi.order
    (le_max_right R Dm) a b hab.le univ isOpen_univ Y₀ (mem_univ _) Q Q' hη hv inv Mn.N hh n hn
    Pd W hW hYW hG hΓ QG Qv Qe m hm α v u k
  exact ⟨U, f, hU, hYU, ⟨(independentReserveOfJoint Qf).restrictOrder R (le_max_left R Dm)⟩, hf⟩

section NativeMeanPaths
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}
/-- The native path mean coefficient: scalar path means multiplied by the fixed
ordered root maps of their walks. This is an actual finite coefficient array. -/
def nativeStagePathMeanCoefficient (hi : StageSuccessor.Input P Mn G) (p : OddSlot)
    (g n : ℕ) (k : Fin 2) : LiftCoeff (CompIn G.comps) (fun v => hr v.1.root) := by
  classical
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level)
    (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily hi.base hi.profile hi.band
    ρ Mn.N π p.1 (G.actual p).1
  exact fun m α t Y z v u => ∑ q : F.Walk g u v,
    let π := Classical.choose (Providers.PathDecomp.stage_walk_path q)
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
    actualMeanFluxCoefficient Q (Cp g π) g n k m α t Y z (Fin.last g) 0 1 • F.compMap q

/-- The finite native path mean sum has local independent reserves at every
spatial order, before time and slow labels are chosen. -/
theorem native_stage_path_mean_coefficient_models (hi : StageSuccessor.Input P Mn G)
    (p : OddSlot) (g n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n - 1)
    (α : DerivativeWord2 m) (v u : CompIn G.comps) (k : Fin 2) (R : ℕ) (Y : Vec 2) :
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    ∃ (U : Set (Vec 2)) (f : ℝ → Vec 2 → Vec 2 → (hr u.1.root →L[ℝ] hr v.1.root)),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (IndependentParameterSourceReserve R f) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z,
        f t z Z = nativeStagePathMeanCoefficient hi p g n k m α t Z z v u := by
  classical
  dsimp only
  let ρ := Mn.lenFactor * liftLength D G.level
  let F := Providers.PathDecomp.stageFam G (D.cellScaleSq G.level)
    (ρ / D.eps (G.level - 1)) p (G.actual p)
  let Cp := fun h (π : StagePath G h) => StageSuccessor.pathLiftFamily hi.base hi.profile hi.band
    ρ Mn.N π p.1 (G.actual p).1
  let π := fun q : F.Walk g u v => Classical.choose (Providers.PathDecomp.stage_walk_path q)
  let Q := fun q : F.Walk g u v =>
    familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G (π q) p (G.actual p))
  let c := fun (q : F.Walk g u v) t z Z =>
    actualMeanFluxCoefficient (Q q) (Cp g (π q)) g n k m α t Z z (Fin.last g) 0 1
  let L := fun q : F.Walk g u v => (ContinuousLinearMap.id ℝ ℝ).smulRight (F.compMap q)
  change ∃ U f, IsOpen U ∧ Y ∈ U ∧ Nonempty (IndependentParameterSourceReserve R f) ∧
    ∀ t ∈ _, ∀ Z ∈ U, ∀ z, f t z Z = ∑ q : F.Walk g u v, L q (c q t z Z)
  apply native_local_reserve_fintype_sum R (fun q t z Z => L q (c q t z Z)) _ Y (mem_univ _)
  intro q Z _
  obtain ⟨U, f, hU, hZU, ⟨Qf⟩, hf⟩ := native_stage_path_mean_coefficient_local_reserve hi
    (π q) p R g n m le_rfl hn hm α (Fin.last g) 0 k Z
  refine ⟨U, _, hU, hZU, ⟨Qf.map (L q)⟩, ?_⟩
  intro t ht X hX z
  exact congrArg (L q) (hf t ht X hX z)

/-- Word permutations preserve the native finite path mean array. The actual
scalar lift sequences supply its intrinsic symmetry, including the diagonal. -/
theorem native_stage_path_mean_coefficient_perm
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm bw j₀}
    (hi : StageSuccessor.Input P Mn G) (p : OddSlot) (g n : ℕ) (k : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    nativeStagePathMeanCoefficient hi p g n k m (α ∘ σ) = nativeStagePathMeanCoefficient hi p g n k m α := by
  classical
  funext t Y z v u
  simp only [nativeStagePathMeanCoefficient]
  apply Finset.sum_congr rfl
  intro q _
  let π := Classical.choose (Providers.PathDecomp.stage_walk_path q)
  let ρ := Mn.lenFactor * liftLength D G.level
  let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (pathEdges G π p (G.actual p))
  let Cp := StageSuccessor.pathLiftFamily hi.base hi.profile hi.band ρ Mn.N π p.1 (G.actual p).1
  have hseq := StageSuccessor.path_lift_family hi π 0 0 p.1 (G.actual p).1 ⟨(G.actual p).2, p.2⟩
  rw [native_actual_ladderOmega_eq_univ hi p ρ] at hseq
  have hs := WeakEntryProofs.liftSequence_of_on_univ Q 0 0 _ _ Mn.N g Cp hseq
  have hp : actualMeanFluxCoefficient Q Cp g n k m (α ∘ σ) = actualMeanFluxCoefficient Q Cp g n k m α := by
    by_cases hg0 : g = 0
    · simp only [actualMeanFluxCoefficient, ite_eq_left hg0]
      exact setting_diagonal_mean_flux_coefficient_perm 0 0 Cp hs n k m α σ
    · simpa only [actualMeanFluxCoefficient, ite_eq_right hg0] using
        EntryWeakProofs.positiveMeanFluxCoefficient_intrinsic_perm Q Cp g n k m
          (hs.2.2.2.2.1 g le_rfl (n - 1) m) α σ
  congr 1
  exact congrArg (fun C => C t Y z (Fin.last g) 0 1) hp

end NativeMeanPaths

/-- The literal mean flux of the native finite path candidate is the finite
scalar-path mean operator. This is the shared stage/menu algebraic identity,
separate from the proved local coefficient reserves. -/
def NativeStagePathMeanActionStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)]
    (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (P : ProvParams) (Mn : SuccMenu)
    (G : GenStage D hr Dm bw j₀) (hi : StageSuccessor.Input P Mn G)
    (H : ℕ) (p : OddSlot) (g n : ℕ), g ≤ H → 2 ≤ n → n ≤ Mn.N + Dm →
    let ρ := Mn.lenFactor * liftLength D G.level
    let Q := familyLiftData D G.level p.1 (G.actual p).1 ρ (G.fam.fiber p (G.actual p))
    let a := D.slotStart G.level p.1 / D.cellScaleSq G.level
    let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    ∀ f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Icc a b, ∀ X : Vec 2, ∀ k : Fin 2, ∀ v : CompIn G.comps,
      fieldCellMean (fun z =>
        liftFluxX Q (nativeStagePathCandidate hi H p) (fun _ => f) g n t X z k v) =
      liftApply (n - 1) (nativeStagePathMeanCoefficient hi p g n k) (fun _ => f) t X 0 v

end NativeMeanCoefficientReserves

open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise

/-- Physical slow lattice translations commute with the literal lift flux,
including its epsilon-derived source term, without a time regularity premise. -/
theorem native_lift_flux_slow_shift {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (t : ℝ) (hab : ∀ Y, b t Y = a t (Y + T))
    (hG : ∀ X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh n : ℕ) (X z : Vec 2) (κ : Fin 2) :
    liftFluxX Q (slowShiftSequence T Cc) b hh n t X z κ =
      liftFluxX Q Cc a hh n t (X + T) z κ := by
  have hL (q p : ℕ) : liftApply q (slowShiftCoeff T (Cc p q)) b t =
      fun X' z' => liftApply q (Cc p q) a t (X' + T) z' := by
    funext X' z'
    exact liftApply_slowShift q (Cc p q) a b T t hab X' z'
  have hS (j : ℕ) (ε : ℝ) :
      sourceFlux Q.edge Q.η ε t (liftApply (n - j) (slowShiftCoeff T (Cc (hh - 1) (n - j))) b t)
        κ X z = sourceFlux Q.edge Q.η ε t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) κ (X + T) z := by
    rw [hL]
    exact sourceFlux_slowShift Q.edge Q.η ε t _ T
      (fun v u d γ hγ α X z => hc v u d γ hγ α X z) κ X z
  have hD (j : ℕ) : iteratedDeriv (j - 1) (fun ε =>
      sourceFlux Q.edge Q.η ε t (liftApply (n - j) (slowShiftCoeff T (Cc (hh - 1) (n - j))) b t)
        κ X z) 0 = iteratedDeriv (j - 1) (fun ε =>
      sourceFlux Q.edge Q.η ε t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) κ (X + T) z) 0 := by
    rw [show (fun ε => sourceFlux Q.edge Q.η ε t
        (liftApply (n - j) (slowShiftCoeff T (Cc (hh - 1) (n - j))) b t) κ X z) = _ from
      funext (hS j)]
  simp only [liftFluxX, slowShiftSequence, hD]
  simp only [hL, fastPartial_slowShift, slowPartial_slowShift, hG]

/-- A fixed linear transformation preserves every finite coefficient reserve. -/
theorem NativeUniformCoeff.map
    {V W X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {a b : ℝ} {K : ℕ} {A : ℝ → Vec 2 → V →L[ℝ] W} (Q : NativeUniformCoeff a b K A)
    (L : (V →L[ℝ] W) →L[ℝ] (X →L[ℝ] Y)) :
    NativeUniformCoeff a b K (fun t x => L (A t x)) := by
  refine ⟨fun t ht => L.contDiff.comp (Q.smooth t ht),
    fun t ht l x => congrArg L (Q.periodic t ht l x),
    L.continuous.measurable.comp Q.measurable, fun n hn => ?_⟩
  obtain ⟨C, hC⟩ := Q.bound n hn
  refine ⟨‖L‖ * C, fun t ht x => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (Q.smooth t ht).contDiffAt
    (Nat.cast_le.mpr hn)).trans
      (mul_le_mul_of_nonneg_left (hC t ht x) (norm_nonneg L))

/-- Global coefficient budgets restrict to spatial budgets on any label set. -/
theorem NativeUniformCoeff.compact_spatial_budget
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [MeasurableSpace W]
    {a b : ℝ} {A : ℝ → Vec 2 → V →L[ℝ] W}
    (Q : ∀ K, NativeUniformCoeff a b K A) (R : ℕ) (X : Set (Vec 2)) :
    NativeCompactSpatialBudget a b R X A := by
  refine ⟨(Q R).smooth, ?_⟩
  obtain ⟨C, hC⟩ := (Q R).bound R le_rfl
  exact ⟨|C|, abs_nonneg C, fun t ht x _hx => (hC t ht x).trans (le_abs_self C)⟩

/-- The finite collection of physical word jets through order N. -/
abbrev NativePhysicalJet (N : ℕ) (ι : Type*) (h : ι → Type*) :=
  ∀ m : Fin (N + 1), DerivativeWord2 m → ∀ u : ι, h u

/-- A coordinate block of the finite physical jet reconstructs the full
multilinear derivative by one fixed continuous linear map. -/
theorem native_physical_jet_word_projection
    {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    (K r : ℕ) (hrK : r ≤ K) (u : ι) :
    ∃ P : NativePhysicalJet K ι h →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) (h u),
      ∀ (f : Vec 2 → ∀ i, h i), ContDiff ℝ (K : ℕ∞) (fun y => f y u) → ∀ x,
        P (fun _q w i => orderedDerivative w (fun y => f y i) x) =
          iteratedFDeriv ℝ r (fun y => f y u) x := by
  classical
  obtain ⟨R, hR⟩ := native_multilinear_word_retraction (V := h u) r
  let q : Fin (K + 1) := ⟨r, by omega⟩
  let B : NativePhysicalJet K ι h →L[ℝ] (DerivativeWord2 r → h u) :=
    ContinuousLinearMap.pi fun w => (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : DerivativeWord2 r => ∀ i, h i) w).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun q : Fin (K + 1) => DerivativeWord2 q → ∀ i, h i) q))
  refine ⟨R.comp B, ?_⟩
  intro f hf x
  change R (B (fun _q w i => orderedDerivative w (fun y => f y i) x)) = _
  rw [← hR (iteratedFDeriv ℝ r (fun y => f y u) x)]
  apply congrArg R
  funext w
  exact congrFun (orderedDerivative_eq_iteratedFDeriv w (hf.of_le (Nat.cast_le.mpr hrK))) x

section NativeMeanFrameCalculus
local instance nativeMeanFrameMultilinearMeasurableSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V) := borel _
local instance nativeMeanFrameMultilinearBorelSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V) := ⟨rfl⟩
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {F : Frame D hr Dm bw j₀}
/-- The shared native path mean identity applies to the stored array at its
actual cell time, on every stage/menu frame. -/
theorem native_input_mean_flux_apply_of_path_action
    (hmean : NativeStagePathMeanActionStatement) (hi : NativeInput F) (p : OddSlot)
    (g n : ℕ) (hg : g ≤ F.depth) (hn : 2 ≤ n) (hnN : n ≤ F.N + Dm)
    (f : Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ)
    (ht : t ∈ Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m))
    (X : Vec 2) (k : Fin 2) (v : CompIn F.G.comps) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
      (F.G.fam.fiber p (F.G.actual p))
    fieldCellMean (fun z => liftFluxX Q (F.CcT p.1) (fun _ => f) g n t X z k v) =
      liftApply (n - 1) (nativeStagePathMeanCoefficient hi.stage p g n k)
        (fun _ => f) t X 0 v := by
  dsimp only
  have hnM : n ≤ F.Mn.N + Dm := by rw [hi.menuN]; exact hnN
  have hA : (F.G.actual p).1 = nativeChain F.G.level p.1 := hi.stage.natural.2.2.1 p
  have htG : t ∈ Icc (D.slotStart F.G.level p.1 / D.cellScaleSq F.G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.G.level) / D.cellScaleSq F.G.level) := by
    simpa only [hi.level] using ht
  have ha := hmean hr D Dm bw j₀ F.P F.Mn F.G hi.stage F.depth p g n hg hn hnM f hf t htG X k v
  rw [Uniqueness.liftFluxX_congr _ (F.CcT p.1)
    (nativeStagePathCandidate hi.stage F.depth p) (fun _ => f) g n t]
  · simpa only [hA, hi.level] using ha
  · intro q hq n' m α
    have he := native_input_coefficients_eq_paths hi p q (hq.trans hg) n'
    rw [hi.level] at he
    exact he t ht m α

/-- The actual native mean array inherits the physical slow lattice from its
literal action and intrinsic word symmetry. -/
theorem native_input_mean_coefficient_slow_shift_of_path_action
    (hmean : NativeStagePathMeanActionStatement) (hi : NativeInput F) (p : OddSlot)
    (hρ : F.Mn.lenFactor * liftLength D F.m ≠ 0) (l : Fin 2 → ℤ)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : 2 ≤ n) (hnN : n ≤ F.N + Dm) (hm : m ≤ n - 1)
    (α : DerivativeWord2 m) (t : ℝ)
    (ht : t ∈ Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m))
    (X : Vec 2) (v u : CompIn F.G.comps) (k : Fin 2) :
    nativeStagePathMeanCoefficient hi.stage p g n k m α t
      (X + (F.Mn.lenFactor * liftLength D F.m)⁻¹ • AVenhance.latticeShift l) 0 v u =
      nativeStagePathMeanCoefficient hi.stage p g n k m α t X 0 v u := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let T := ρ⁻¹ • AVenhance.latticeShift l
  let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
    (F.G.fam.fiber p (F.G.actual p))
  let C := nativeStagePathMeanCoefficient hi.stage p g n k
  have hperm : ∀ β (σ : Equiv.Perm (Fin m)), C m (β ∘ σ) = C m β :=
    fun β σ => native_stage_path_mean_coefficient_perm hi.stage p g n k m β σ
  have hperm' : ∀ β (σ : Equiv.Perm (Fin m)),
      slowShiftCoeff T C m (β ∘ σ) = slowShiftCoeff T C m β := by
    intro β σ
    unfold slowShiftCoeff
    rw [hperm β σ]
  have hlevel : 1 ≤ F.m := by have := hi.stage.level; rw [hi.level] at this; omega
  have hmetric : ∀ Y i j, Q.G t (Y + T) i j = Q.G t Y i j := by
    intro Y i j
    exact congrFun (congrFun (FullLift.native_familyLiftData_metric_shift D F.m hlevel p.1
      hρ (F.G.fam.fiber p (F.G.actual p)) l t Y) i) j
  have htorus := GenStage.isTorusCompatible_of_shiftInvariant hi.stage.natural hi.shift
  have hedge : ∀ v' u' d, ∀ γ ∈ Q.edge v' u' d, ∀ β Y z,
      γ.coeff β t (Y + T) z = γ.coeff β t Y z := by
    intro v' u' d γ hγ β Y z
    have hγ' : γ ∈ (familyLiftData D F.G.level p.1 (nativeChain F.G.level p.1) ρ
        (F.G.fam.fiber p (F.G.actual p))).edge v' u' d := by
      simpa only [Q, hi.level] using hγ
    exact FullLift.native_familyLiftData_edge_coeff_shift F.G htorus p hρ l
      v' u' d γ hγ' β t Y z
  symm
  refine symmetric_lift_coefficient_eq_of_operator_eq (n - 1) m hm C
    (slowShiftCoeff T C) hperm hperm' t X 0 v u ?_ α
  intro a₀ ha₀
  let a₁ := fun Y : Vec 2 => a₀ (Y - T)
  have ha₁ : ContDiff ℝ (⊤ : ℕ∞) a₁ := ha₀.comp (contDiff_id.sub contDiff_const)
  have hshift : ∀ Y, (fun (_ : ℝ) => a₀) t Y = (fun (_ : ℝ) => a₁) t (Y + T) := by
    intro Y
    simp only [a₁, add_sub_cancel_right]
  rw [liftApply_slowShift (n - 1) C (fun _ => a₁) (fun _ => a₀) T t hshift X 0]
  rw [← native_input_mean_flux_apply_of_path_action hmean hi p g n hg hn hnN a₀ ha₀ t ht X k v,
    ← native_input_mean_flux_apply_of_path_action hmean hi p g n hg hn hnN a₁ ha₁ t ht (X + T) k v]
  apply congrArg fieldCellMean
  funext z
  have hf := native_lift_flux_slow_shift Q (F.CcT p.1) (fun _ => a₁) (fun _ => a₀)
    T t hshift hmetric hedge g n X z k
  rw [Uniqueness.liftFluxX_congr Q (slowShiftSequence T (F.CcT p.1)) (F.CcT p.1)
    (fun _ => a₀) g n t] at hf
  · exact congrFun hf v
  · intro q hq n' m' β
    funext Y z v' u'
    exact native_input_coefficient_slow_shift hi p hρ l q (hq.trans hg) n' m' β t ht Y z v' u'

open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- The native input provides every finite spatial lift-data reserve on its
own closed cell window. No joint continuity in time is required. -/
theorem native_input_lift_spatial_data (hi : NativeInput F) (p : OddSlot) (R : ℕ)
    (τ : ℝ) (ht : τ ∈ Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m)) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
      (F.G.fam.fiber p (F.G.actual p))
    (∀ q ≤ F.depth, ∀ n m (α : DerivativeWord2 m) (v u : CompIn F.G.comps),
      IsBoxSmooth R R (fun X z => F.CcT p.1 q n m α τ X z v u)) ∧
    (∀ k j, ContDiff ℝ (R : ℕ∞) (fun X => Q.G τ X k j)) ∧
    (∀ k, ContDiff ℝ (R : ℕ∞) (fun z => Q.v τ z k)) ∧
    (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, IsBoxSmooth R R (γ.coeff α τ)) := by
  dsimp only
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
    (F.G.fam.fiber p (F.G.actual p))
  have hb (q : ℕ) (hq : q ≤ F.depth) (n' m : ℕ) (α : DerivativeWord2 m)
      (v' u : CompIn F.G.comps) :
      IsBoxSmooth R R (fun X z => F.CcT p.1 q n' m α τ X z v' u) := by
    have he := native_input_coefficients_eq_paths hi p q hq n'
    rw [hi.level] at he
    have heq : (fun X z => F.CcT p.1 q n' m α τ X z v' u) =
        fun X z => nativeStagePathCandidate hi.stage F.depth p q n' m α
          τ X z v' u := by
      funext X z
      exact congrFun (congrFun (congrFun (congrFun (he _ ht m α) X) z) v') u
    rw [heq]
    apply Weighted.isBoxSmooth_of_joint_contDiff
    apply native_stage_path_candidate_joint_contDiff hi.stage F.depth p (R + R) q hq n' m α v' u
    rw [hi.level]
    exact ht
  have hAl : (nativeChain F.m p.1).slots.length = (nativeChain F.m p.1).children.length + 1 := by
    have hl := (F.G.actual p).2.2.2.1
    rw [hi.stage.natural.2.2.1 p, hi.level] at hl
    exact hl
  have hmetric (k j : Fin 2) : ContDiff ℝ (R : ℕ∞)
      (fun X => Q.G τ X k j) :=
    ((WeakEntryProofs.familyLiftData_metric_spacetime_smooth D hi.stage.profile F.m p.1
      (nativeChain F.m p.1) hAl ρ (F.G.fam.fiber p (F.G.actual p)) k j).comp
        (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hdrift (k : Fin 2) : ContDiff ℝ (R : ℕ∞)
      (fun z => Q.v τ z k) := by
    exact ((contDiff_apply ℝ ℝ k).comp (EntryWeakProofs.normalizedPulseDrift_contDiff
      hi.stage.base (EntryWeakProofs.weakData_kap_pos D hi.stage.base hi.stage.profile hi.stage.band F.m)
      p.2 τ)).of_le (by simp)
  obtain ⟨kI, hctx, hres⟩ := hi.incoming_context
  have hedge := native_lift_fiber_boxSmooth hctx
    (native_context_slot_transverse hi.stage.base hi.stage.bandwidth hctx) hi.stage.natural
    (by have := hi.stage.level; omega) (by have := hi.stage.level; omega) hi.stage.bandwidth
    (Construction.Stream.ocEpsilon_pos hi.stage.base) hi.stage.base hi.stage.profile hi.stage.band
    hres (fun u => GenStage.compReserve_le_two kI u.1) p ρ R R
  simp only [hi.level] at hedge
  exact ⟨hb, hmetric, hdrift, fun v u d γ hγ α => hedge v u d γ hγ α τ ht⟩

/-- Native lift fluxes of finite-regularity fields are continuous on each fast
cell. This is the integrability input for commuting the cell mean and projection. -/
theorem native_input_lift_flux_slice_continuous (hi : NativeInput F) (p : OddSlot)
    (g n : ℕ) (hg : g ≤ F.depth)
    (f : Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) f) (τ : ℝ)
    (ht : τ ∈ Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m))
    (X : Vec 2) (k : Fin 2) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
      (F.G.fam.fiber p (F.G.actual p))
    Continuous (fun z => liftFluxX Q (F.CcT p.1) (fun _ => f) g n τ X z k) := by
  dsimp only
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
    (F.G.fam.fiber p (F.G.actual p))
  obtain ⟨hb, hmetric, hdrift, hedge⟩ := native_input_lift_spatial_data hi p Dm τ ht
  have hc := CovFluxReg.liftFluxX_box Q (F.CcT p.1) (fun _ => f) g n τ k 0 F.N F.depth
    hi.stage.order hg ((F.lift.1 p.1 p.2).2.2.1)
    (by simpa only [Nat.zero_add] using hb)
    (fun j => (hmetric k j).of_le (by simp)) ((hdrift k).of_le (by simp))
    (fun _hg v u d γ hγ α => (hedge v u d γ hγ α).mono (Nat.zero_le _) (Nat.zero_le _))
    (by simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm] using hf)
  exact (hc.1 X).continuous

/-- The actual path mean/chart factor has all-order compact spatial reserves and
joint measurability. Its time extension is clamped to its own cell window;
the cutoff makes its literal value independent of that extension. -/
theorem native_input_mean_word_operator_data (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n - 1) (k : Fin 2)
    (α : DerivativeWord2 m) (c : OrderedFinpartition m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label)) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    ∃ L : ℝ → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root,
      (∀ R X, IsCompact X → NativeCompactSpatialBudget F.tp F.tf R X L) ∧
      Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc F.tp F.tf} => L p.1.1 p.1.2) ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ x A,
        L t x A = ocCutoff D.α D.q D.Λ F.m p.1 t •
          nativeStagePathMeanCoefficient hi.stage p g n k m α ((D.cellScaleSq F.m)⁻¹ * t)
            (ρ⁻¹ • label t x) 0 v u
            ((c.compAlongOrderedFinpartition A
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i)))) := by
  classical
  dsimp only
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let a := D.slotStart F.m p.1 / D.cellScaleSq F.m
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m
  have hab : a ≤ b := (EntryWeakProofs.weakData_lift_window_strict
    D hi.stage.base hi.stage.profile hi.stage.band F.m p.1).le
  let σ := fun t : ℝ => (projIcc a b hab ((D.cellScaleSq F.m)⁻¹ * t) : ℝ)
  have hσ : Measurable σ := continuous_projIcc.subtype_val.measurable.comp
    (continuous_const.mul continuous_id).measurable
  let f := fun t z Y => nativeStagePathMeanCoefficient hi.stage p g n k m α t Y z v u
  have hmodel (R : ℕ) (Y : Vec 2) : ∃ U f', IsOpen U ∧ Y ∈ U ∧
      Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R f') ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ Z ∈ U, ∀ z, f' t z Z = f (σ t) z Z := by
    have hOld := native_stage_path_mean_coefficient_models hi.stage p g n m hn hm α v u k R Y
    rw [hi.level] at hOld
    obtain ⟨U, f', hU, hYU, ⟨Q⟩, he⟩ := hOld
    refine ⟨U, _, hU, hYU, ⟨Q.timeReparam σ hσ⟩, ?_⟩
    intro t _ Z hZ z
    exact he _ (projIcc a b hab ((D.cellScaleSq F.m)⁻¹ * t)).2 Z hZ z
  let Γ := fun t x => ((0 : Vec 2), ρ⁻¹ • label t x)
  have hΓ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Γ) :=
    contDiff_const.prodMk ((contDiff_const (c := ρ⁻¹)).smul hlabel)
  let C := fun t x => f (σ t) (Γ t x).1 (Γ t x).2
  have hC : ∀ R X, IsCompact X → NativeCompactSpatialBudget F.tp F.tf R X C :=
    fun R X hX => native_local_reserve_sample_spatial_budget R (hmodel R) Γ hΓ X hX
  have hCm : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc F.tp F.tf} => C p.1.1 p.1.2) :=
    native_local_reserve_sample_measurable (hmodel 0) Γ hΓ.continuous.measurable
  let Φ := fun t Y => chart t (ρ • Y)
  let Ψ := fun t x => ρ⁻¹ • label t x
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ) :=
    hchart.comp (contDiff_fst.prodMk ((contDiff_const (c := ρ)).smul contDiff_snd))
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Ψ) := (contDiff_const (c := ρ⁻¹)).smul hlabel
  obtain ⟨J, hJ, heJ⟩ := native_pullback_word_smooth_operator (V := hr u.1.root) α c Φ Ψ hΦ hΨ
  have hJt := native_smooth_uniform_time_data J hJ (a := F.tp) (b := F.tf)
  let O := ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root
  let B := ContinuousLinearMap.compL ℝ
    (ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root))
    (hr u.1.root) (hr v.1.root)
  let T := fun t x => B (C t x) (J t x)
  have hT : ∀ R X, IsCompact X → NativeCompactSpatialBudget F.tp F.tf R X T :=
    fun R X hX => by
      change NativeCompactSpatialBudget F.tp F.tf R X (fun t x => B (C t x) (J t x))
      exact native_uniform_bilinear_spatial_budget (Z := O) B hC hJt.spatial R X hX
  have hTm : Measurable (fun p : {p : ℝ × Vec 2 // p.1 ∈ Icc F.tp F.tf} => T p.1.1 p.1.2) :=
    (((B.continuous.comp continuous_fst).clm_apply continuous_snd).measurable).comp
      (hCm.prodMk hJt.measurable)
  let cut := fun t (_x : Vec 2) => ocCutoff D.α D.q D.Λ F.m p.1 t
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry cut) :=
    (CycleReference.ocCutoff_contDiff hi.stage.base p.1).comp contDiff_fst
  have hcutT := native_smooth_uniform_time_data cut hcut (a := F.tp) (b := F.tf)
  let nativeMeanOperatorNormedSpace : NormedSpace ℝ O := inferInstance
  let nativeMeanOperatorBoundedSMul : IsBoundedSMul ℝ O :=
    IsBoundedSMul.of_norm_smul_le (α := ℝ) (β := O) (fun r x => NormedSpace.norm_smul_le r x)
  let S := ContinuousLinearMap.lsmul (E := O) ℝ ℝ
  let L := fun t x => S (cut t x) (T t x)
  refine ⟨L, ?_, ?_, ?_⟩
  · intro R X hX
    change NativeCompactSpatialBudget F.tp F.tf R X (fun t x => S (cut t x) (T t x))
    exact native_uniform_bilinear_spatial_budget (Z := O) S hcutT.spatial hT R X hX
  · exact (((S.continuous.comp continuous_fst).clm_apply continuous_snd).measurable).comp
      (hcutT.measurable.prodMk hTm)
  · intro t _ht x A
    change cut t x • C t x (J t x A) = _
    rw [heJ]
    by_cases hw : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
    · simp only [cut, hw, zero_smul]
    have htcell : (D.cellScaleSq F.m)⁻¹ * t ∈ Icc a b := by
      have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
        (Construction.Stream.ocTau_pos hi.stage.base : 0 < ocTau D.α D.q D.Λ F.m) hw
      have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile hi.stage.band F.m
      rw [inv_mul_eq_div]
      exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩
    have heσ : σ t = (D.cellScaleSq F.m)⁻¹ * t := by
      dsimp only [σ]
      rw [projIcc_of_mem hab htcell]
    dsimp only [C, Γ, f]
    rw [heσ]

/-- The native mean word factor has global periodic coefficient bounds at every
order, from its compact reserves and the literal path mean action. -/
theorem native_input_mean_word_operator_coeff_of_path_action
    (hmean : NativeStagePathMeanActionStatement) (hi : NativeInput F) (p : OddSlot)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : 2 ≤ n) (hnN : n ≤ F.N + Dm) (hm : m ≤ n - 1)
    (k : Fin 2) (α : DerivativeWord2 m) (c : OrderedFinpartition m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (hcper : ∀ t l y, chart t (y + AVenhance.latticeShift l) = chart t y + AVenhance.latticeShift l)
    (hlper : ∀ t l y, label t (y + AVenhance.latticeShift l) = label t y + AVenhance.latticeShift l) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    ∃ L : ℝ → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Vec 2) (hr u.1.root) →L[ℝ] hr v.1.root,
      (∀ K, NativeUniformCoeff F.tp F.tf K L) ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ x A,
        L t x A = ocCutoff D.α D.q D.Λ F.m p.1 t •
          nativeStagePathMeanCoefficient hi.stage p g n k m α ((D.cellScaleSq F.m)⁻¹ * t)
            (ρ⁻¹ • label t x) 0 v u
            ((c.compAlongOrderedFinpartition A
              (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i)))) := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  have htop : F.m - 1 ≤ D.term := by have := hi.stage.top; rw [hi.level] at this; omega
  have hρ : ρ ≠ 0 :=
    (mul_pos hi.stage.length_factor (Real.sqrt_pos.mpr
      (mul_pos (CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band htop)
        (Construction.Stream.ocTauPP_pos hi.stage.base)))).ne'
  obtain ⟨L, hL, hLm, heL⟩ := native_input_mean_word_operator_data hi p g n m hn hm k α c v u
    chart label hchart hlabel
  have hper : ∀ t ∈ Icc F.tp F.tf, AVenhance.IsZ2Periodic (L t) := by
    intro t ht l x
    ext A
    rw [heL t ht, heL t ht]
    by_cases hz : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
    · simp only [hz, zero_smul]
    have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
      (Construction.Stream.ocTau_pos hi.stage.base : 0 < ocTau D.α D.q D.Λ F.m) hz
    have hclock := EntryWeakProofs.weakData_cellScaleSq_pos
      D hi.stage.base hi.stage.profile hi.stage.band F.m
    have htcell : (D.cellScaleSq F.m)⁻¹ * t ∈
        Icc (D.slotStart F.m p.1 / D.cellScaleSq F.m)
          ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) := by
      rw [inv_mul_eq_div]
      exact ⟨div_le_div_of_nonneg_right htw.1 hclock.le,
        div_le_div_of_nonneg_right htw.2 hclock.le⟩
    have hj (i : Fin c.length) :
        iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
          (ρ⁻¹ • label t x + ρ⁻¹ • AVenhance.latticeShift l) =
        iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y)) (ρ⁻¹ • label t x) := by
      apply native_quasiperiodic_positive_jet _ _ (AVenhance.latticeShift l)
      · intro Y
        rw [CycleComparison.Assembly.smul_add_inv_smul hρ, hcper]
      · exact c.partSize_pos i
    rw [hlper, smul_add]
    dsimp only [ρ] at hj
    simp_rw [hj]
    rw [native_input_mean_coefficient_slow_shift_of_path_action hmean hi p hρ l g n m hg hn hnN hm α _ htcell]
  exact ⟨L, fun K => native_uniform_coeff_of_spatial_data hL hLm hper K, heL⟩

end NativeMeanFrameCalculus

/-- A fixed finite sum preserves every finite coefficient reserve. -/
theorem NativeUniformCoeff.sum_finset
    {ι V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    {a b : ℝ} {K : ℕ} (s : Finset ι) (A : ι → ℝ → Vec 2 → V →L[ℝ] W)
    (Q : ∀ i ∈ s, NativeUniformCoeff a b K (A i)) :
    NativeUniformCoeff a b K (fun t x => ∑ i ∈ s, A i t x) := by
  classical
  refine ⟨fun t ht => ContDiff.sum (fun i hi => (Q i hi).smooth t ht),
    fun t ht l x => Finset.sum_congr rfl (fun i hi => (Q i hi).periodic t ht l x),
    Finset.measurable_sum s (fun i hi => (Q i hi).measurable), fun n hn => ?_⟩
  choose C hC using fun i : s => (Q i i.2).bound n hn
  refine ⟨∑ i : s, C i, fun t ht x => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    ((Q i hi).smooth t ht).of_le (Nat.cast_le.mpr hn) |>.contDiffAt),
    ← Finset.sum_coe_sort s]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hC i t ht x))

/-- One Eulerian mean word is a fixed physical-jet operator with all-order
periodic coefficient budgets, independent of the datum and requested order. -/
def NativeMeanPhysicalWordOperatorStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {F : Frame D hr Dm bw j₀},
    ∀ (hi : NativeInput F) (p : OddSlot) (g n m : ℕ),
      g ≤ F.depth → 2 ≤ n → n ≤ F.N + Dm → m ≤ n - 1 →
    ∀ (k j : Fin 2) (α : DerivativeWord2 m) (c : OrderedFinpartition m)
      (v u : CompIn F.G.comps) (εc : ℝ),
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m p.1)
    let label := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m p.1) y s
    ∃ T : ℝ → Vec 2 → NativePhysicalJet (F.N + Dm) (CompIn F.G.comps)
        (fun u => hr u.1.root) →L[ℝ] hr v.1.root,
      (∀ K, NativeUniformCoeff F.tp F.tf K T) ∧
      ∀ (f : Vec 2 → ∀ w : CompIn F.G.comps, hr w.1.root),
        ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) (fun y => f y u) →
        ∀ t ∈ Icc F.tp F.tf, ∀ x,
          T t x (fun _q w u => orderedDerivative w (fun y => f y u) x) =
            (jacMatrix (chart t) (label t x) j k * (-((D.cellScaleSq F.m)⁻¹ * εc ^ n * ρ))) •
              (ocCutoff D.α D.q D.Λ F.m p.1 t •
                nativeStagePathMeanCoefficient hi.stage p g n k m α ((D.cellScaleSq F.m)⁻¹ * t)
                  (ρ⁻¹ • label t x) 0 v u
                  ((c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (fun y => f y u) x)
                    (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
                      (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i)))))

private instance nativeRetainedEquationTorusESeminormed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (K : ℕ) :
    ESeminormedAddMonoid (TorusHk K E) := inferInstance

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {F : Frame D hr Dm bw j₀}

/-- Every actual retained coupling flux has one native time-L² representative at
one order above the desired time derivative. This includes empty edge sets. -/
theorem native_input_retained_kernel_flux (hi : NativeInput F) :
    ∃ Q : ∀ v : CompIn F.Gr.comps,
        ℝ → TorusHk (F.Naux - 1) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)),
      (∀ v, MemLp (Q v) 2 (volume.restrict (Icc F.tp F.tf))) ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ v,
        (Q v t).toFunction.jet (valueIndex2 (F.Naux - 1)) =ᵐ[
          volume.restrict AVenhance.unitCube] fun x =>
          ∑ u : CompIn F.Gr.comps, ∑ γ : F.Gr.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dm),
            F.Gr.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun w : DerivativeWord2 (d.1 - 1) =>
              (hi.Yk v u γ t).toFunction.jet
                ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, w⟩ x) := by
  classical
  obtain ⟨hn, hs, k, hc, hr0⟩ := native_input_retained_certificates hi
  have hl : F.Gr.level = F.G.level - 1 := by
    rw [hi.retained]
    exact hi.actual.2.1
  have hlev := hi.stage.level
  have hε : 0 < D.eps (F.Gr.level - 1) := Construction.Stream.ocEpsilon_pos hi.stage.base
  have hcoeff (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) :=
    native_context_physical_fields hi.stage.base hi.stage.bandwidth
      (show 1 ≤ F.Gr.level by omega) (show j₀ ≤ F.Gr.level by omega)
      hc hn hs hr0 F.tp F.tf (F.Naux - 1) d.1 v u γ
  let Qe (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) :
      ℝ → TorusHk (F.Naux - 1) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
    nativeKernelFluxPath (K := F.Naux - 1) (r := d.1 - 1) hε
      (F.Gr.physCoeff v u γ d.1) (hcoeff v u γ d).2.2
      (fun t ht => ((hcoeff v u γ d).1 t ht).1)
      (fun t ht => ((hcoeff v u γ d).1 t ht).2) hi.window
      (fun t => truncateTorusHk (show F.Naux - 1 + (d.1 - 1) ≤ F.Naux + Dm - 1 by
        have := Finset.mem_Icc.1 d.2; omega) (hi.Yk v u γ t))
  have hYk (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u) :
      MemLp (hi.Yk v u γ) 2 (volume.restrict (Icc F.tp F.tf)) :=
    hi.solution.2.2.2.2.1 v u γ
  have hQe (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) :
      MemLp (Qe v u γ d) 2 (volume.restrict (Icc F.tp F.tf)) := by
    have hlo : F.Naux - 1 + (d.1 - 1) ≤ F.Naux + Dm - 1 := by
      have := Finset.mem_Icc.1 d.2; omega
    have hy := (truncateTorusHk (E := hr u.1.root) hlo).comp_memLp' (hYk v u γ)
    exact native_kernel_flux_memLp (G := hr u.1.root) (H := hr v.1.root)
      (K := F.Naux - 1) (r := d.1 - 1) hε (F.Gr.physCoeff v u γ d.1)
      (hcoeff v u γ d).2.2 (fun t ht => ((hcoeff v u γ d).1 t ht).1)
      (fun t ht => ((hcoeff v u γ d).1 t ht).2) hi.window (hcoeff v u γ d).2.1
      (fun t => truncateTorusHk hlo (hi.Yk v u γ t)) hy
  refine ⟨fun v t => ∑ u, ∑ γ, ∑ d, Qe v u γ d t, ?_, ?_⟩
  · intro v
    let nativeRetainedFluxNormed : NormedAddCommGroup
        (TorusHk (F.Naux - 1) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) := inferInstance
    let nativeRetainedFluxESeminormed : ESeminormedAddMonoid
        (TorusHk (F.Naux - 1) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) := inferInstance
    refine memLp_finsetSum Finset.univ
      (f := fun u t => ∑ γ, ∑ d, Qe v u γ d t) (fun u _ => ?_)
    refine memLp_finsetSum Finset.univ
      (f := fun γ t => ∑ d, Qe v u γ d t) (fun γ _ => ?_)
    exact memLp_finsetSum Finset.univ (f := fun d t => Qe v u γ d t)
      (fun d _ => hQe v u γ d)
  · intro t ht v
    apply torusJet_sum_ae_of_eq
    intro u
    apply torusJet_sum_ae_of_eq
    intro γ
    apply torusJet_sum_ae_of_eq
    intro d
    have hd := Finset.mem_Icc.1 d.2
    have hlo : F.Naux - 1 + (d.1 - 1) ≤ F.Naux + Dm - 1 := by omega
    have hv := native_kernel_flux_value_ae (K := F.Naux - 1) (r := d.1 - 1) hε
      (F.Gr.physCoeff v u γ d.1) (hcoeff v u γ d).2.2
      (fun t ht => ((hcoeff v u γ d).1 t ht).1)
      (fun t ht => ((hcoeff v u γ d).1 t ht).2)
      ⟨t, ht⟩ (truncateTorusHk hlo (hi.Yk v u γ t))
    have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ w : DerivativeWord2 (d.1 - 1),
        (truncateTorusHk hlo (hi.Yk v u γ t)).toFunction.jet
          (prefixJetIndex w (valueIndex2 (F.Naux - 1))) x =
        (hi.Yk v u γ t).toFunction.jet ⟨⟨d.1 - 1, by omega⟩, w⟩ x := by
      apply ae_all_iff.mpr
      intro w
      have hjt := truncateTorusHk_toFunction_jet_ae hlo (hi.Yk v u γ t)
        (prefixJetIndex w (valueIndex2 (F.Naux - 1)))
      simp only [prefixJetIndex, valueIndex2, valueIndex, truncateJetIndex,
        Fin.val_zero, Nat.add_zero, Fin.append_elim0, Function.comp_def, Fin.cast_eq_self] at hjt ⊢
      exact hjt
    change (nativeKernelFluxPath _ _ _ _ _ hi.window _ t).toFunction.jet _ =ᵐ[_] _
    simp only [nativeKernelFluxPath, projIcc_of_mem hi.window ht]
    filter_upwards [hv, hj] with x hx hjx
    exact hx.trans (congrArg (F.Gr.physCoeff v u γ d.1 t x) (PiLp.ext hjx))

/-- The actual retained drift also has a time-L² native source representative.
Admissibility is already carried by OCData.hΦ; no stream premise is added. -/
theorem native_input_retained_transport (hi : NativeInput F) :
    ∃ T : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux - 2) (hr v.1.root),
      (∀ v, MemLp (T v) 2 (volume.restrict (Icc F.tp F.tf))) ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ v,
        (T v t).val (valueIndex2 (F.Naux - 2)) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => ∑ k : Fin 2, streamVel (D.Φ (F.m - 1)) t x k •
            (hi.Yw v t).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x := by
  classical
  let K := F.Naux - 2
  let bv := streamVel (D.Φ (F.m - 1))
  have hφ := D.hΦ (F.m - 1)
  have hv := AVenhance.Infra.Classical.streamVel_smoothPeriodic _ hφ
  have hc : ∀ t ∈ Icc F.tp F.tf, ContDiff ℝ (↑(⊤ : ℕ∞)) (bv t) :=
    fun t _ => hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hp : ∀ t ∈ Icc F.tp F.tf, AVenhance.IsZ2Periodic (bv t) := by
    intro t _ k x
    simpa only [bv, Int.cast_zero, add_zero] using hv.periodic 0 k t x
  have hm : Measurable (fun z : Icc F.tp F.tf × Vec 2 => bv z.1 z.2) :=
    hv.smooth.continuous.measurable.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨C, _, hC⟩ := CycleJointProofs.admissible_stream_coefficient_array_budget _ hφ K
  let B : CompIn F.Gr.comps → Fin (K + 1) → ℝ := fun _ _ => C
  have hB : ∀ t ∈ Icc F.tp F.tf, ∀ v l x,
      ‖coefficientDerivativeArray (driftCoefficient (bv t)) l.val x‖ ≤ B v l :=
    fun t _ _ l x => hC l.val (Nat.le_of_lt_succ l.isLt) t x
  obtain ⟨V, hV, hVb⟩ := AVenhance.Infra.Classical.streamVel_global_derivative_bound _ hφ 0
  have hbound : ∀ t ∈ Icc F.tp F.tf, ∀ x, ‖bv t x‖ ≤ V := by
    intro t _ x
    simpa only [norm_iteratedFDeriv_zero, Function.uncurry, bv] using hVb (t, x)
  have hlo : K + 1 ≤ F.Naux + 1 := by omega
  let w : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (K + 1) (hr v.1.root) :=
    fun v t => truncateTorusHk hlo (hi.Yw v t)
  have hw (v : CompIn F.Gr.comps) : MemLp (w v) 2 (volume.restrict (Icc F.tp F.tf)) :=
    (truncateTorusHk (E := hr v.1.root) hlo).comp_memLp' (hi.solution.2.1 v)
  let T := plainTransportCarrierPath (fun _ : CompIn F.Gr.comps => K) F.tp F.tf bv hc hp B hB w
  refine ⟨T, fun v => plainTransportCarrierPath_memLp
    (fun _ : CompIn F.Gr.comps => K) F.tp F.tf bv hc hp B hB hi.window 1 zero_lt_one
    hm V hV hbound w hw v, ?_⟩
  intro t ht v
  have he := CoupledEnergy.Variational.torusTransportCarrier_value_ae (bv t) (hc t ht)
    (hp t ht) (B v) (hB t ht v) (w v t)
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      (w v t).val ⟨⟨1, by omega⟩, fun _ => k⟩ x =
        (hi.Yw v t).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x := by
    apply ae_all_iff.mpr
    intro k
    exact (CoupledEnergy.Variational.torusRawJet_ae (hi.Yw v t) _).symm
  change ((plainTransportCarrierPath (fun _ : CompIn F.Gr.comps => K)
    F.tp F.tf bv hc hp B hB w) v t).val _ =ᵐ[_] _
  simp only [plainTransportCarrierPath, dite_eq_left ht]
  filter_upwards [he, hj] with x hx hjx
  exact hx.trans (Finset.sum_congr rfl (fun k _ => congrArg (fun y => bv t x k • y) (hjx k)))

/-- The total diffusion and coupling flux of the actual retained equation,
with one derivative order reserved for the divergence. -/
theorem native_input_retained_total_flux (hi : NativeInput F) :
    ∃ B : ∀ v : CompIn F.Gr.comps,
        ℝ → TorusHk (F.Naux - 2 + 1) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)),
      (∀ v, MemLp (B v) 2 (volume.restrict (Icc F.tp F.tf))) ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ v,
        torusHkValueCLM (B v t) =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
          D.κ (F.m - 1) • WithLp.toLp 2
            (fun k : Fin 2 => (hi.Yw v t).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x) +
          ∑ u : CompIn F.Gr.comps, ∑ γ : F.Gr.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dm),
            F.Gr.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun w : DerivativeWord2 (d.1 - 1) =>
              (hi.Yk v u γ t).toFunction.jet
                ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, w⟩ x) := by
  classical
  obtain ⟨Q, hQLp, hQraw⟩ := native_input_retained_kernel_flux hi
  have hres := hi.auxiliary
  have hK : (F.Naux - 2) + 1 ≤ F.Naux - 1 := by omega
  have hW : (F.Naux - 2) + 2 ≤ F.Naux + 1 := by omega
  let R (v : CompIn F.Gr.comps) (t : ℝ) :
      TorusHk ((F.Naux - 2) + 1) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
    CoupledEnergy.Variational.torusGradientTensorCLM (E := hr v.1.root) ((F.Naux - 2) + 1)
      (truncateTorusHk (E := hr v.1.root) hW (hi.Yw v t))
  let B (v : CompIn F.Gr.comps) (t : ℝ) :
      TorusHk ((F.Naux - 2) + 1) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
    D.κ (F.m - 1) • R v t + truncateTorusHk hK (Q v t)
  have hRLp (v : CompIn F.Gr.comps) :
      MemLp (R v) 2 (volume.restrict (Icc F.tp F.tf)) := by
    have hw : MemLp (fun t => truncateTorusHk (E := hr v.1.root) hW (hi.Yw v t))
        2 (volume.restrict (Icc F.tp F.tf)) :=
      (truncateTorusHk (E := hr v.1.root) hW).comp_memLp' (hi.solution.2.1 v)
    have hg := CoupledEnergy.Variational.torusGradientTensor_carrier_memLp
      (E := hr v.1.root) ((F.Naux - 2) + 1) F.tp F.tf
      (fun t => truncateTorusHk (E := hr v.1.root) hW (hi.Yw v t)) hw
    simpa only [R, CoupledEnergy.Variational.torusGradientTensorCLM_apply] using hg
  have hBLp (v : CompIn F.Gr.comps) :
      MemLp (B v) 2 (volume.restrict (Icc F.tp F.tf)) := by
    have hq : MemLp (fun t => truncateTorusHk
        (E := PiLp 2 (fun _ : Fin 2 => hr v.1.root)) hK (Q v t))
        2 (volume.restrict (Icc F.tp F.tf)) :=
      (hQLp v).continuousLinearMap_comp (truncateTorusHk hK)
    exact ((hRLp v).const_smul (D.κ (F.m - 1))).add hq
  refine ⟨B, ?_, ?_⟩
  · intro v
    exact hBLp v
  intro t ht v
  have hQr := (CoupledEnergy.Variational.torusRawValue_ae (Q v t)).symm.trans (hQraw t ht v)
  have hRr : torusHkValueCLM (R v t) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => WithLp.toLp 2 (fun k : Fin 2 =>
        (hi.Yw v t).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x) :=
    native_torus_gradient_value_ae hW (hi.Yw v t)
  exact native_torus_value_smul_add_ae hK (D.κ (F.m - 1)) (R v t) (Q v t)
    _ _ hRr hQr

/-- The retained PDE selects its Sobolev time derivative once for all H¹ tests. -/
theorem native_input_retained_strong_time (hi : NativeInput F) :
    ∃ dY : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux - 2) (hr v.1.root),
      (∀ v, MemLp (dY v) 2 (volume.restrict (Icc F.tp F.tf))) ∧
      ∀ v, CycleEvolution.StrongTimeRegularity F.tp F.tf
        (fun t => truncateTorusHk (E := hr v.1.root) (Nat.sub_le F.Naux 2) (F.Y v t)) (dY v) := by
  classical
  obtain ⟨B, hBLp, hBraw⟩ := native_input_retained_total_flux hi
  obtain ⟨T, hTLp, hTraw⟩ := native_input_retained_transport hi
  let S (v : CompIn F.Gr.comps) (t : ℝ) : TorusHk (F.Naux - 2) (hr v.1.root) := -(T v t)
  have hSLp (v : CompIn F.Gr.comps) :
      MemLp (S v) 2 (volume.restrict (Icc F.tp F.tf)) := (hTLp v).neg
  let dY (v : CompIn F.Gr.comps) (t : ℝ) : TorusHk (F.Naux - 2) (hr v.1.root) :=
    S v t + nativeTorusDivergenceCLM (E := hr v.1.root) (F.Naux - 2) (B v t)
  refine ⟨dY, ?_, ?_⟩
  · intro v
    have hdiv : MemLp (fun t => nativeTorusDivergenceCLM (E := hr v.1.root) (F.Naux - 2) (B v t))
        2 (volume.restrict (Icc F.tp F.tf)) :=
      (hBLp v).continuousLinearMap_comp (nativeTorusDivergenceCLM (E := hr v.1.root) (F.Naux - 2))
    change MemLp (fun t => S v t + nativeTorusDivergenceCLM (E := hr v.1.root)
      (F.Naux - 2) (B v t)) 2 (volume.restrict (Icc F.tp F.tf))
    exact (hSLp v).add hdiv
  intro v
  let du (t : ℝ) (k : Fin 2) :=
    (hi.Yw v t).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩
  let q (t : ℝ) (x : Vec 2) :=
    ∑ u : CompIn F.Gr.comps, ∑ γ : F.Gr.fam.Γ v u, ∑ d : ↥(Finset.Icc 2 Dm),
      F.Gr.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun w : DerivativeWord2 (d.1 - 1) =>
        (hi.Yk v u γ t).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, w⟩ x)
  apply native_torus_strong_time_of_raw_weak hi.window (D.κ (F.m - 1))
    (streamVel (D.Φ (F.m - 1))) _ (S v) (B v) du q
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hi.window).mpr
      ((hSLp v).integrable (by norm_num))
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hi.window).mpr
      ((hBLp v).integrable (by norm_num))
  · intro t ht
    have hv : torusHkValueCLM (T v t) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => ∑ k : Fin 2, streamVel (D.Φ (F.m - 1)) t x k • du t k x :=
      hTraw t ht v
    filter_upwards [hv, Lp.coeFn_neg (torusHkValueCLM (T v t))] with x hx hn
    change (-(torusHkValueCLM (T v t))) x = _
    rw [hn]
    exact congrArg Neg.neg hx
  · exact fun t ht => hBraw t ht v
  · intro t ht φ
    have hw := hi.solution.2.2.2.2.2.2 v t ht φ
    have hu := truncateTorusHk_toFunction_jet_ae (Nat.sub_le F.Naux 2)
      (F.Y v t) (valueIndex2 (F.Naux - 2))
    have hf := truncateTorusHk_toFunction_jet_ae (Nat.sub_le F.Naux 2)
      (F.Y v F.tp) (valueIndex2 (F.Naux - 2))
    have hinit := hi.solution.2.2.2.1 v
    have hf0 : (F.Y v F.tp).toFunction.jet (valueIndex2 F.Naux) =ᵐ[
        volume.restrict AVenhance.unitCube] (hi.Y0 v).toFunction.jet (valueIndex2 F.Naux) := by
      rw [hinit]
    simp only [truncateJetIndex, valueIndex2, valueIndex, Fin.val_zero] at hu hf
    have hf1 := hf0.symm.trans hf.symm
    apply CycleJointProofs.coupledWeakIdentity_integrands_congr
      (volume.restrict AVenhance.unitCube) (D.κ (F.m - 1)) F.tp t
      (streamVel (D.Φ (F.m - 1))) (streamVel (D.Φ (F.m - 1))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (h := hw)
    · exact hu.symm.mono (fun x hx => congrArg (fun z => inner ℝ z
        (φ.toFunction.jet (valueIndex2 1) x)) hx)
    · exact hf1.mono (fun x hx => congrArg (fun z => inner ℝ z
        (φ.toFunction.jet (valueIndex2 1) x)) hx)
    · intro r _
      have hF0 := (CoupledEnergy.Variational.torusRawValue_ae
        (0 : TorusHk F.Naux (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))).trans
          (Lp.coeFn_zero _ 2 (volume.restrict AVenhance.unitCube))
      have hg0 := (CoupledEnergy.Variational.torusRawValue_ae
        (0 : TorusHk F.Naux (hr v.1.root))).trans
          (Lp.coeFn_zero _ 2 (volume.restrict AVenhance.unitCube))
      filter_upwards [hF0, hg0] with x hfx hgx
      simp only [Weighted.weakIdentityRhs, hfx, hgx, Pi.zero_apply,
        PiLp.zero_apply, add_zero, inner_zero_left]
      rfl

/-- Finite readout preserves the actual native continuity, time L² derivative,
and strong time equation before selecting any classical representatives. -/
theorem native_input_readout_sobolev_time (hi : NativeInput F) :
    let Z := fun (v : CompIn F.G.comps) (t : ℝ) =>
      succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun c => F.Y c t) v
    ∃ dZ : ∀ v : CompIn F.G.comps, ℝ → TorusHk (F.Naux - 2) (hr v.1.root),
      (∀ v, ContinuousOn (Z v) (Icc F.tp F.tf)) ∧
      (∀ v, MemLp (dZ v) 2 (volume.restrict (Icc F.tp F.tf))) ∧
      ∀ v, CycleEvolution.StrongTimeRegularity F.tp F.tf
        (fun t => truncateTorusHk (Nat.sub_le F.Naux 2) (Z v t)) (dZ v) := by
  classical
  obtain ⟨dY, hYLp, hYtime⟩ := native_input_retained_strong_time hi
  let Z (v : CompIn F.G.comps) (t : ℝ) : TorusHk F.Naux (hr v.1.root) :=
    succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun c => F.Y c t) v
  let dZ (v : CompIn F.G.comps) (t : ℝ) : TorusHk (F.Naux - 2) (hr v.1.root) :=
    succReadout F.m (D.eps (F.m - 1)) F.η₀ (F.Naux - 2) (fun c => dY c t) v
  have hZtime (v : CompIn F.G.comps) : CycleEvolution.StrongTimeRegularity F.tp F.tf
      (fun t => truncateTorusHk (Nat.sub_le F.Naux 2) (Z v t)) (dZ v) := by
    have hs := native_succReadout_strong_time F.m (D.eps (F.m - 1)) F.η₀
      (fun c t => truncateTorusHk (E := hr c.1.root) (Nat.sub_le F.Naux 2) (F.Y c t))
      dY hYtime v
    simpa only [Z, dZ, FullLift.truncate_succReadout] using hs
  have hZcont (v : CompIn F.G.comps) : ContinuousOn (Z v) (Icc F.tp F.tf) :=
    native_succReadout_continuousOn F.m (D.eps (F.m - 1)) F.η₀ F.Y hi.solution.1 v
  have hdZLp (v : CompIn F.G.comps) :
      MemLp (dZ v) 2 (volume.restrict (Icc F.tp F.tf)) :=
    FullLift.memLp_succReadout F.m (D.eps (F.m - 1)) F.η₀ dY hYLp v
  exact ⟨dZ, hZcont, hdZLp, hZtime⟩

/-- The actual retained weak solution gives the entire classical readout time
package, with one derivative field selected before any test or spatial point. -/
theorem native_input_readout_time (hi : NativeInput F) :
    ∃ dZ : F.Field, ClassicalTimeCurve F F.Naux F.aZ dZ := by
  obtain ⟨dZ, hZcont, hdZLp, hZtime⟩ := native_input_readout_sobolev_time hi
  have hres := hi.auxiliary
  apply native_classical_time_curve_exists F F.Naux (by omega) hi.window
    (fun v t => succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun c => F.Y c t) v)
    dZ F.aZ
  · intro v t ht
    exact FullLift.classicalRep_order_mono _ _ (F.readout v t ht) (Nat.sub_le F.Naux 2)
  · exact hZcont
  · exact hdZLp
  · exact hZtime

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
