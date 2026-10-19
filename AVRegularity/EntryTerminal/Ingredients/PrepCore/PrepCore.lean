-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.PrepCore.JetFacts
import AVRegularity.EntryTerminal.Ingredients.PrepInterp.PrepInterp
import AVRegularity.EntryTerminal.Ingredients.PrepAnchor.PrepAnchor
public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The kernel flux at the identity is the plain flux at descending slots** (`PrepCorePart`).

Take a time where every kernel image `y_{vuγ}` has the value of `w_u` (identity kernels), and let
the slots `K ≤ k` be descending. Then the flux of the kernel weak identity at the order `k`, over
all orders `2 ≤ d ≤ D`, is the flux of the plain coupled identity at the slots `K` over the
admissible orders `K_v + d ≤ K_u + 2`:
- every non-admissible order exceeds the identity's maximal order (descending slots), so its
  coefficient vanishes (`constituentPhysical_zero_above_max`);
- at an admissible order `d - 1 ≤ K_u + 1 ≤ k + 1`, the jets of `y` and of `w_u` agree (equal values,
  `torusHk_jet_eq_of_value`).

Degenerate cases:
- No edges: both fluxes are `0`.
- Constant slots `K ≡ k`: only the orders `d ≤ 2` are admissible, and descending forces
  `D_γ ≤ 2`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The flux match** at a time where the kernel images are the identity images. -/
theorem flux_match (G : GenStage D hr Dm b j₀) (k : ℕ) (K : CompIn G.comps → ℕ)
    (hK : ∀ v, K v ≤ k) (hdesc : G.fam.IsDescending K)
    (W : ∀ v : CompIn G.comps, TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), TorusHk (k + Dm - 1) (hr u.1.root))
    (hY : ∀ v u γ, (Y v u γ).val (valueIndex2 (k + Dm - 1)) = (W u).val (valueIndex2 (k + 1)))
    (s : ℝ) (v : CompIn G.comps) (x : Vec 2) :
    (∑ i' : CompIn G.comps, ∑ d : admissibleOrders K Dm v i',
      edgeCoefficient G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) G.actual K
        v i' d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (truncateTorusHk (Nat.succ_le_succ (hK i')) (W i')).toFunction.jet
            ⟨⟨d.1 - 1, by
              have h := Finset.mem_filter.1 d.2
              have := Finset.mem_Icc.1 h.1
              omega⟩, word⟩ x)) =
      ∑ j : CompIn G.comps, ∑ α : G.fam.Γ v j, ∑ d : ↥(Finset.Icc 2 Dm),
        G.physCoeff v j α d.1 s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Y v j α).toFunction.jet
            ⟨⟨d.1 - 1, by
              have := Finset.mem_Icc.1 d.2
              omega⟩, word⟩ x) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  rw [sum_subtype_filter_eq (Finset.Icc 2 Dm) (fun d => K v + d ≤ K j + 2) _ ?_]
  · refine Finset.sum_congr rfl fun d _ => ?_
    have hd := Finset.mem_filter.1 d.2
    have hdI := Finset.mem_Icc.1 hd.1
    simp only [edgeCoefficient, physicalCoefficient, FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [GenStage.physCoeff]
    congr 2
    funext word
    rw [toFunction_jet_truncate]
    exact congrFun (torusHk_jet_eq_of_value (hY v j α).symm (by have := hK j; omega)
      (by omega) _ _ word) x
  · intro d hd
    refine Finset.sum_eq_zero fun α _ => ?_
    have hmax := hdesc v j α
    have hdI := Finset.mem_Icc.1 d.2
    rw [GenStage.physCoeff, CycleJointProofs.constituentPhysical_zero_above_max G.fam _ _ _
      G.actual v j α d.1 (by omega) s x]
    rfl
end

/-! **The zero-width kernel solution solves the plain coupled system at descending slots**
(`PrepCorePart`). Let `U` solve the kernel system of a stage with paired kernels of width zero
(the identity, `isoPairedKernel_zero_op`) at the order `k`. Then for descending slots `K ≤ k`,
`u = trunc_K U` solves the plain coupled system with the edge coefficients at the slots `K`, on
every sub-window `[t₀, t₁']`.
- The carrier `w` is `trunc_{K+1} W` at the good times, where every kernel image has the value of
  its source (almost every time). Elsewhere it is `0`, where the right-hand side vanishes almost
  everywhere and so is integrable.
- At good times the two right-hand sides agree (`flux_match`), and the identity transfers
  (`coupledWeakIdentity_congr`).

Degenerate cases:
- `K ≡ 0`: the order-zero plain system.
- `t₁' = t₀`: a single time.
- No edges: the scalar equations. -/

section
theorem compLp_id_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure (Vec 2)}
    (f : Lp E 2 μ) : (ContinuousLinearMap.id ℝ E).compLp f = f :=
  Lp.ext (by
    filter_upwards [(ContinuousLinearMap.id ℝ E).coeFn_compLp f] with a ha
    rw [ha]
    rfl)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The plain flux at slots `K` of a carrier `w`. -/
def plainFlux (G : GenStage D hr Dm b j₀) (K : CompIn G.comps → ℕ)
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)) (v : CompIn G.comps) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root) := fun s x =>
  ∑ i' : CompIn G.comps, ∑ d : admissibleOrders K Dm v i',
    edgeCoefficient G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) G.actual K
      v i' d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (w i' s).toFunction.jet
          ⟨⟨d.1 - 1, by
            have h := Finset.mem_filter.1 d.2
            have := Finset.mem_Icc.1 h.1
            omega⟩, word⟩ x)

/-- The kernel flux at the order `k` of the kernel images `Y`. -/
def kernelFlux (G : GenStage D hr Dm b j₀) (k : ℕ)
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (v : CompIn G.comps) : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root) := fun s x =>
  ∑ j : CompIn G.comps, ∑ α : G.fam.Γ v j, ∑ d : ↥(Finset.Icc 2 Dm),
    G.physCoeff v j α d.1 s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (Y v j α s).toFunction.jet
        ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x)

/-- **The identity transfers** from the kernel system to the plain system, for a carrier equal
to the truncated kernel carrier at good times and to `0` elsewhere. -/
theorem coupled_identity_of_kernel (G : GenStage D hr Dm b j₀) (k : ℕ)
    (K : CompIn G.comps → ℕ) (hK : ∀ v, K v ≤ k) (hdesc : G.fam.IsDescending K) (ν : ℝ)
    (bv : ℝ → Vec 2 → Vec 2) (t₀ t : ℝ) (v : CompIn G.comps)
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)) (good : Set ℝ)
    (hgood : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₀ t)), s ∈ good)
    (hYg : ∀ s ∈ good, ∀ v u (γ : G.fam.Γ v u),
      (Y v u γ s).val (valueIndex2 (k + Dm - 1)) = (W u s).val (valueIndex2 (k + 1)))
    (hwg : ∀ s ∈ good, ∀ v, w v s = truncateTorusHk (Nat.succ_le_succ (hK v)) (W v s))
    (hwb : ∀ s ∉ good, ∀ v, w v s = 0) (u₀ f fg : Vec 2 → hr v.1.root) (hfg : fg = f)
    (φ : TorusHk 1 (hr v.1.root))
    (hk : CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν t₀ t bv u₀ f
      (φ.toFunction.jet (valueIndex2 1))
      (fun m => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m⟩)
      (fun s m => (W v s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩)
      (kernelFlux G k Y v)
      (fun _ => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))).toFunction.jet
        (valueIndex2 k))
      (fun _ => (0 : TorusHk k (hr v.1.root)).toFunction.jet (valueIndex2 k))) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν t₀ t bv u₀ fg
      (φ.toFunction.jet (valueIndex2 1))
      (fun m => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m⟩)
      (fun s m => (w v s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩,
        fun _ => m⟩)
      (plainFlux G K w v)
      (fun _ => (0 : TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))).toFunction.jet
        (valueIndex2 (K v)))
      (fun _ => (0 : TorusHk (K v) (hr v.1.root)).toFunction.jet (valueIndex2 (K v))) := by
  subst hfg
  have hflux : ∀ s ∈ good, ∀ x, plainFlux G K w v s x = kernelFlux G k Y v s x := by
    intro s hs x
    unfold plainFlux kernelFlux
    simp only [hwg s hs]
    exact flux_match G k K hK hdesc (fun u => W u s) (fun v u γ => Y v u γ s) (hYg s hs) s v x
  have hdu : ∀ s ∈ good, ∀ (m : Fin 2) (x : Vec 2),
      (w v s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => m⟩ x =
        (W v s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩ x := by
    intro s hs m x
    rw [hwg s hs v, toFunction_jet_truncate]
    rfl
  refine coupledWeakIdentity_congr hk ?_ ?_
  · filter_upwards [hgood] with s hs
    exact cwiRhs_congr_at s (hdu s hs) (hflux s hs) (fun x => rfl) (fun x => rfl)
  · intro s hsI
    by_cases hs : s ∈ good
    · exact ((coupledWeakIdentity_iff.mp hk).2.2.1 s hsI).congr (Filter.EventuallyEq.of_eq
        (cwiRhs_congr_at s (hdu s hs) (hflux s hs) (fun x => rfl) (fun x => rfl)).symm)
    · have hz : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (i' : CompIn G.comps)
          (a : JetIndex2 (K i' + 1)),
          (0 : TorusHk (K i' + 1) (hr i'.1.root)).toFunction.jet a x = 0 :=
        ae_all_iff.2 fun i' => ae_all_iff.2 fun a => torusHk_zero_jet_ae a
      refine cwiRhs_integrable_of_ae_zero s (fun m => ?_) ?_ (torusHk_zero_jet_ae _)
        (torusHk_zero_jet_ae _)
      · rw [hwb s hs v]
        exact torusHk_zero_jet_ae _
      · filter_upwards [hz] with x hx
        unfold plainFlux
        simp only [hwb s hs, hx, Pi.zero_apply]
        refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun d _ => ?_
        have h0 : (WithLp.toLp 2 fun _ : DerivativeWord2 (d.1 - 1) => (0 : hr i'.1.root)) = 0 :=
          rfl
        rw [h0, map_zero]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The kernel images of the zero-width paired kernels are the identity images at almost every
time. -/
theorem zeroWidth_good (G : GenStage D hr Dm b j₀) (P : ProvParams) (n : ℕ+) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (hmass : ∫ z, φ₀ z = 1) (k : ℕ) {t₀ t₁ : ℝ}
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hY : ∀ v u (γ : G.fam.Γ v u), ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)),
      (Y v u γ s).val (valueIndex2 (k + Dm - 1)) =
        G.sysS P (fun _ => isoPairedKernel 0 n) (fun _ => isoPairedKernel 0 n) φ₀ hφ₀ v u γ s
          ((ContinuousLinearMap.id ℝ (hr u.1.root)).compLp ((W u s).val (valueIndex2 (k + 1))))) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), ∀ v u (γ : G.fam.Γ v u),
      (Y v u γ s).val (valueIndex2 (k + Dm - 1)) = (W u s).val (valueIndex2 (k + 1)) := by
  have hS : ∀ v u (γ : G.fam.Γ v u) s,
      G.sysS P (fun _ => isoPairedKernel 0 n) (fun _ => isoPairedKernel 0 n) φ₀ hφ₀ v u γ s =
        ContinuousLinearMap.id ℝ _ := by
    intro v u γ s
    unfold GenStage.sysS GenStage.kernelOf
    split <;> exact isoPairedKernel_zero_op hφ₀ hmass n s
  filter_upwards [ae_all_iff.2 fun v => ae_all_iff.2 fun u => ae_all_iff.2 fun γ => hY v u γ]
    with s hs v u γ
  rw [hs v u γ, hS, ContinuousLinearMap.id_apply, compLp_id_eq]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- A carrier equal to the truncated carrier on a set of times and to `0` off it. -/
theorem exists_goodCarrier (G : GenStage D hr Dm b j₀) (k : ℕ) (K : CompIn G.comps → ℕ)
    (hK : ∀ v, K v ≤ k) (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (good : Set ℝ) :
    ∃ w : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root),
      (∀ s ∈ good, ∀ v, w v s = truncateTorusHk (Nat.succ_le_succ (hK v)) (W v s)) ∧
        ∀ s ∉ good, ∀ v, w v s = 0 := by
  classical
  exact ⟨fun v s => if s ∈ good then truncateTorusHk (Nat.succ_le_succ (hK v)) (W v s) else 0,
    fun s hs v => by simp only [hs, ↓reduceIte], fun s hs v => by simp only [hs, ↓reduceIte]⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The carrier field: `w` is square integrable on the sub-window. -/
theorem goodCarrier_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k K : ℕ} (hK : K ≤ k)
    {t₀ t₁ t₁' : ℝ} (ht : t₁' ≤ t₁) (W : ℝ → TorusHk (k + 1) E) (w : ℝ → TorusHk (K + 1) E)
    (good : Set ℝ) (hgood : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), s ∈ good)
    (hmem : MemLp W 2 (volume.restrict (Set.Icc t₀ t₁)))
    (hwg : ∀ s ∈ good, w s = truncateTorusHk (Nat.succ_le_succ hK) (W s)) :
    MemLp w 2 (volume.restrict (Set.Icc t₀ t₁')) := by
  have hsub : volume.restrict (Set.Icc t₀ t₁') ≤ volume.restrict (Set.Icc t₀ t₁) :=
    Measure.restrict_mono (Set.Icc_subset_Icc le_rfl ht) le_rfl
  refine ((hmem.mono_measure hsub).continuousLinearMap_comp
    (truncateTorusHk (Nat.succ_le_succ hK))).ae_eq ?_
  filter_upwards [ae_mono hsub hgood] with s hs
  exact (hwg s hs).symm

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The carrier field: `w` truncates to `u` at almost every time of the sub-window. -/
theorem goodCarrier_trunc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k K : ℕ} (hK : K ≤ k)
    {t₀ t₁ t₁' : ℝ} (ht : t₁' ≤ t₁) (U : ℝ → TorusHk k E) (W : ℝ → TorusHk (k + 1) E)
    (w : ℝ → TorusHk (K + 1) E) (good : Set ℝ)
    (hgood : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), s ∈ good)
    (htr : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), truncateTorusHk (Nat.le_succ k) (W s) = U s)
    (hwg : ∀ s ∈ good, w s = truncateTorusHk (Nat.succ_le_succ hK) (W s)) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁')),
      truncateTorusHk (Nat.le_succ K) (w s) = truncateTorusHk hK (U s) := by
  have hsub : volume.restrict (Set.Icc t₀ t₁') ≤ volume.restrict (Set.Icc t₀ t₁) :=
    Measure.restrict_mono (Set.Icc_subset_Icc le_rfl ht) le_rfl
  filter_upwards [ae_mono hsub hgood, ae_mono hsub htr] with s hs hts
  rw [hwg s hs, ← hts]
  rfl

/-- **The plain coupled solution from the components of the zero-width kernel solution.** -/
theorem coupled_of_parts (G : GenStage D hr Dm b j₀) (ν : ℝ) (bv : ℝ → Vec 2 → Vec 2) (k : ℕ)
    {t₀ t₁ : ℝ} (t₁' : ℝ) (ht : t₁' ≤ t₁)
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hcont : ∀ v, ContinuousOn (U v) (Set.Icc t₀ t₁))
    (hmem : ∀ v, MemLp (W v) 2 (volume.restrict (Set.Icc t₀ t₁)))
    (htr : ∀ v, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)),
      truncateTorusHk (Nat.le_succ k) (W v s) = U v s)
    (hinit : ∀ v, U v t₀ = f v)
    (hid : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, ∀ φ : TorusHk 1 (hr v.1.root),
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν t₀ t bv
        ((U v t).toFunction.jet (valueIndex2 k)) ((f v).toFunction.jet (valueIndex2 k))
        (φ.toFunction.jet (valueIndex2 1))
        (fun m => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m⟩)
        (fun s m => (W v s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩)
        (kernelFlux G k Y v)
        (fun _ => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))).toFunction.jet
          (valueIndex2 k))
        (fun _ => (0 : TorusHk k (hr v.1.root)).toFunction.jet (valueIndex2 k)))
    (K : CompIn G.comps → ℕ) (hK : ∀ v, K v ≤ k)
    (f' : ∀ v : CompIn G.comps, TorusHk (K v) (hr v.1.root))
    (hf' : ∀ v, f' v = truncateTorusHk (hK v) (f v)) (hdesc : G.fam.IsDescending K)
    (good : Set ℝ) (hgood : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), s ∈ good)
    (hYg : ∀ s ∈ good, ∀ v u (γ : G.fam.Γ v u),
      (Y v u γ s).val (valueIndex2 (k + Dm - 1)) = (W u s).val (valueIndex2 (k + 1)))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root))
    (hwg : ∀ s ∈ good, ∀ v, w v s = truncateTorusHk (Nat.succ_le_succ (hK v)) (W v s))
    (hwb : ∀ s ∉ good, ∀ v, w v s = 0) :
    IsCoupledWeakSolutionTorus ν t₀ t₁' bv Dm K
      (edgeCoefficient G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) G.actual K)
      f' (fun _ _ => 0) (fun _ _ => 0) (fun v t => truncateTorusHk (hK v) (U v t)) w := by
  refine ⟨fun v => ?_, fun v => goodCarrier_memLp (hK v) ht (W v) (w v) good hgood (hmem v)
      (fun s hs => hwg s hs v),
    fun v => goodCarrier_trunc (hK v) ht (U v) (W v) (w v) good hgood (htr v)
      (fun s hs => hwg s hs v), fun v => ?_, fun v t ht' φ => ?_⟩
  · exact (truncateTorusHk (hK v)).continuous.comp_continuousOn
      ((hcont v).mono (Set.Icc_subset_Icc le_rfl ht))
  · show truncateTorusHk (hK v) (U v t₀) = f' v
    rw [hf' v, hinit v]
  · have hIoc : Set.Ioc t₀ t ⊆ Set.Icc t₀ t₁ :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl (ht'.2.trans ht))
    have hfg : (f' v).toFunction.jet (valueIndex2 (K v)) = (f v).toFunction.jet (valueIndex2 k) := by
      rw [hf' v, toFunction_jet_truncate]
      rfl
    exact coupled_identity_of_kernel G k K hK hdesc ν bv t₀ t v W Y w good
      (ae_restrict_of_ae_restrict_of_subset hIoc hgood) hYg hwg hwb _ _ _ hfg φ
      (hid v t ⟨ht'.1, ht'.2.trans ht⟩ φ)

/-- **The zero-width kernel solution, truncated to descending slots, solves the plain coupled
system** on every sub-window. -/
theorem zeroWidth_coupled (G : GenStage D hr Dm b j₀) (P : ProvParams) (n : ℕ+)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (hmass : ∫ z, φ₀ z = 1) (ν : ℝ)
    (bv : ℝ → Vec 2 → Vec 2) (k : ℕ) {t₀ t₁ : ℝ} (t₁' : ℝ) (ht : t₁' ≤ t₁)
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P (fun _ => isoPairedKernel 0 n) (fun _ => isoPairedKernel 0 n) φ₀ hφ₀
      ν bv k t₀ t₁ f (fun _ _ => 0) (fun _ _ => 0) U W Y)
    (K : CompIn G.comps → ℕ) (hK : ∀ v, K v ≤ k)
    (f' : ∀ v : CompIn G.comps, TorusHk (K v) (hr v.1.root))
    (hf' : ∀ v, f' v = truncateTorusHk (hK v) (f v)) (hdesc : G.fam.IsDescending K) :
    ∃ w : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root),
      IsCoupledWeakSolutionTorus ν t₀ t₁' bv Dm K
        (edgeCoefficient G.fam (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) G.actual K)
        f' (fun _ _ => 0) (fun _ _ => 0) (fun v t => truncateTorusHk (hK v) (U v t)) w := by
  obtain ⟨hcont, hmem, htr, hinit, -, hY, hid⟩ := hsol
  have hgood := zeroWidth_good G P n hφ₀ hmass k W Y hY
  obtain ⟨w, hwg, hwb⟩ := exists_goodCarrier G k K hK W {s | ∀ v u (γ : G.fam.Γ v u),
    (Y v u γ s).val (valueIndex2 (k + Dm - 1)) = (W u s).val (valueIndex2 (k + 1))}
  exact ⟨w, coupled_of_parts G ν bv k t₁' ht f U W Y hcont hmem htr hinit hid K hK f' hf' hdesc _
    hgood (fun s hs => hs) w hwg hwb⟩
end

/-! **The core of the preparation** (`PrepCorePart`). Let `U` be the paired
weak solution with the identity kernels (width `0`) and `V` the one with the paired kernels
`S_{r_w}`, both from `U₀` at `a_M`.
- For descending slots `K ≤ K_w`, `u = trunc_K U` is the plain coupled solution of `G_w` from
  `trunc_K V(a_M) = trunc_K U₀` on `[a_M, t_p]` (`zeroWidth_coupled`). Here
  `t_p = (l₀ + 3/2) h ≤ a + T₀` at late levels (`prepAnchor_deadline`).
- `V(t_p) - u(t_p)` at the order `0` is `-(U - V)(t_p)`. Its weighted `L²` norm is at most the
  strong energy of `U - V` at `c_K x` (the order-`0` norm does not see the radius), so it is at most
  `C_K x^{χ_w + σ_w L_t}‖f‖` (`IsWeakPaired`).

Degenerate cases:
- An edge-free family: `u` solves the scalar equations.
- `K ≡ 0`: the order-zero plain system.
- `L_t = L_p^T`: the least admissible kernel order. -/

section
open AVRegularity.EntryTerminal.Route

/-- The weighted norm of a negation. -/
theorem weightedNorm_neg {S : Finset Comp} {K : ℕ} (ρ : ℝ) (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (f : ∀ _v : CompIn S, TorusHk K ℝ) :
    weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) (-f) =
      weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) f := by
  simp only [weightedNorm, one_pow, div_one]
  rw [← CoupledEnergy.Variational.massWeightedCarrierCLM_norm (fun _ => K) ρ π hπ (-f), map_neg,
    norm_neg, CoupledEnergy.Variational.massWeightedCarrierCLM_norm (fun _ => K) ρ π hπ f]

/-- The order-zero weighted norm does not see the radius. -/
theorem weightedNorm_zero_radius {S : Finset Comp} (r ρ : ℝ) (π : CompIn S → ℝ)
    (f : ∀ _v : CompIn S, TorusHk 0 ℝ) :
    weightedNorm (hr := fun _ => ℝ) r π (fun _ => 1) f =
      weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) f := by
  unfold weightedNorm massNormSq
  congr 1

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The plain coupled solution from the datum `V(t₀) = U₀` of the paired solutions. -/
theorem core_coupled (G : GenStage D hr Dm b j₀) (P : ProvParams) (n : ℕ+) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (hmass : ∫ z, φ₀ z = 1) (ν : ℝ) (bv : ℝ → Vec 2 → Vec 2) (k : ℕ)
    {t₀ t₁ : ℝ} (t₁' : ℝ) (ht : t₁' ≤ t₁) (U₀ : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U V : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hU : G.IsRegSolution P (fun _ => isoPairedKernel 0 n) (fun _ => isoPairedKernel 0 n) φ₀ hφ₀
      ν bv k t₀ t₁ U₀ (fun _ _ => 0) (fun _ _ => 0) U Uw Uk)
    (hV0 : ∀ v, V v t₀ = U₀ v) (K : CompIn G.comps → ℕ) (hK : ∀ v, K v ≤ k)
    (hdesc : G.fam.IsDescending K) (ν' e E : ℝ) (hν' : D.kap G.level = ν')
    (he : D.eps G.level = e) (hE : D.eps (G.level - 1) = E) :
    ∃ w : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root),
      IsCoupledWeakSolutionTorus ν t₀ t₁' bv Dm K (edgeCoefficient G.fam ν' e E G.actual K)
        (fun v => truncateTorusHk (hK v) (V v t₀)) (fun _ _ => 0) (fun _ _ => 0)
        (fun v t => truncateTorusHk (hK v) (U v t)) w := by
  subst hν' he hE
  exact zeroWidth_coupled G P n hφ₀ hmass ν bv k t₁' ht U₀ U Uw Uk hU K hK
    (fun v => truncateTorusHk (hK v) (V v t₀)) (fun v => by rw [hV0 v]) hdesc

end Generic

/-- The core error: the order-zero gap between `V` and `u = trunc_K U` at a time of the window is
at most the strong energy of `U - V`. -/
theorem core_error_le {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v) {Kw : ℕ}
    (K : CompIn S → ℕ) (hK : ∀ v, K v ≤ Kw) (ρ B : ℝ) {t₀ t₁ tp E : ℝ}
    (htp : tp ∈ Set.Icc t₀ t₁) (hE : 0 ≤ E) (U V : ∀ _v : CompIn S, ℝ → TorusHk Kw ℝ)
    (Uw Vw : ∀ _v : CompIn S, ℝ → TorusHk (Kw + 1) ℝ)
    (hSE : strongEnergy ρ B π t₀ t₁ (fun v t => U v t - V v t) (fun v t => Uw v t - Vw v t) ≤
      ENNReal.ofReal E) :
    weightedNorm (hr := fun _ => ℝ) 1 π (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le Kw) (V v tp) -
          truncateTorusHk (Nat.zero_le (K v)) (truncateTorusHk (hK v) (U v tp))) ≤ E := by
  have hfun : (fun v => truncateTorusHk (Nat.zero_le Kw) (V v tp) -
      truncateTorusHk (Nat.zero_le (K v)) (truncateTorusHk (hK v) (U v tp))) =
      -(fun v => truncateTorusHk (Nat.zero_le Kw) (U v tp - V v tp)) := by
    funext v
    simp only [Pi.neg_apply, map_sub, neg_sub]
    rfl
  rw [hfun, weightedNorm_neg 1 _ hπ, weightedNorm_zero_radius 1 ρ]
  exact (weightedNorm_truncate_le (Nat.zero_le Kw) _ _ hπ _).trans
    (weightedNorm_le_of_strongEnergy hπ htp hE (fun v t => U v t - V v t)
      (fun v t => Uw v t - Vw v t) hSE)

/-- **The core of the preparation.** -/
theorem prepCore : PrepCorePart := by
  intro X
  refine ⟨128, le_rfl, fun PA hΛ hPA Kout => ⟨0, fun Kw Lt nW hk₀w cr _ _ _ hcr _ cK CK CL Cχ
    kW hcK _ _ _ _ _ _ => ?_⟩⟩
  show ∃ Ccore : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    PrepCoreAtM PA Kw Lt nW cK CK CL Cχ kW Ccore j₀ M
  have hT : 0 < PA.T₀ := hPA.2.2.2.1.2.1.trans hPA.2.2.2.1.2.2.1
  obtain ⟨M₀, hM₀⟩ := prepAnchor_deadline X hΛ PA.Jw hT
  refine ⟨max CK 0, fun j₀ => ⟨max M₀ 2, fun M hM => ?_⟩⟩
  intro D hD a lawW PW Gw aM hW K hK hdesc f U₀ U V Uw Vw Uk Vk hpair
  obtain ⟨hDα, hDq, hDΛ, -, -, -, hterm⟩ := hD
  have hlevW : Gw.level = M := hW.2.2.1
  have haM2 : aM ≤ a + 6 * PA.Jw * ocTauPP X.α X.q PA.Λ (M + 1) := by
    have h := hW.2.1
    rwa [hDα, hDq, hDΛ] at h
  obtain ⟨hint1, hU, hV, -, hdiff⟩ := hpair
  have hΛ1 : 1 ≤ PA.Λ := by omega
  have hh : 0 < ocTauPP X.α X.q PA.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  obtain ⟨hlo, hhi⟩ := prepBlock_spec (aM := aM) hh
  have h6 := hM₀ M (le_trans (le_max_left _ _) hM)
  have hJ : (0 : ℝ) ≤ 6 * PA.Jw * ocTauPP X.α X.q PA.Λ (M + 1) :=
    mul_nonneg (by positivity) (Construction.Stream.ocTauPP_pos hΛ1).le
  have htpE : ((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) + 3 / 2) * ocTauPP X.α X.q PA.Λ M ≤
      a + PA.T₀ := by
    nlinarith
  have haE : aM ≤ ((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) + 3 / 2) *
      ocTauPP X.α X.q PA.Λ M := by
    nlinarith
  have hV0 : ∀ v, V v aM = U₀ v := by
    obtain ⟨-, -, -, h4, -⟩ := hV
    exact h4
  have hkap : D.kap Gw.level = D.κ M := by
    rw [hlevW]
    unfold OCData.kap
    rw [hterm, min_self]
  have heps : D.eps Gw.level = ocEpsilon X.q PA.Λ M := by
    rw [hlevW]
    simp only [OCData.eps, hDq, hDΛ]
  have heps1 : D.eps (Gw.level - 1) = ocEpsilon X.q PA.Λ (M - 1) := by
    rw [hlevW]
    simp only [OCData.eps, hDq, hDΛ]
  obtain ⟨w, hw⟩ := core_coupled Gw PW nW PA.hφ₀ hint1 (D.κ M) (streamVel (D.Φ M)) Kw _ htpE
    U₀ U V Uw Uk hU hV0 K hK hdesc _ _ _ hkap heps heps1
  have hq1 : 1 < D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ hΛ
  have hπ : ∀ v, 0 < Gw.mass lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD lawW v.1
  have hF : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  have hE0 : 0 ≤ D.eps M ^ (PA.χw + PA.σw * Lt) :=
    Real.rpow_nonneg (Scales.epsilon_basic (m := M) hq1 hΛD).1.le _
  exact ⟨fun v t => truncateTorusHk (hK v) (U v t), w, hw,
    core_error_le (Gw.mass lawW) hπ K hK (D.termRStar cK M) (D.κ M) ⟨haE, htpE⟩
      (mul_nonneg (mul_nonneg (le_max_right _ _) hE0) hF) U V Uw Vw
      (hdiff.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0) hF)))⟩
end

end AVRegularity.EntryTerminal.Ingredients
end
