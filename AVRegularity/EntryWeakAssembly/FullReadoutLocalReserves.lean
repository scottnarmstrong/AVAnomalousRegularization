-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.WeakQuietCoefficientOfIngredients
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.LiftOn.Omega

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs

/-! **The raw system of the weak stage** (`WeakEntryRawSolutionStatement`).
* `weakEncoding_physCoeff`: along a weak encoding the physical coefficients agree. They read the
  weights, pieces, maps and maximal orders of the identities and the fluxes at the actual contexts,
  all of which the encoding keeps, at the same level.
* `sysS_constKernel`: with one kernel for every provenance, the regularizing operator of an
  identity is that kernel's operator.
* `isRegSolution_reindex`: a solution of the regularized system transports along bijections of
  the components and of the identities that keep the coefficients and the operators; the kernel
  lifts are pulled back through the bijection of the identities.
* `weak_entry_raw_solution`: the reduction's passage into the level `M` solves the raw system of
  the stage `M` from the trace of `U^{(M)}` at `a_M = t_{M+1}` (its initial value clause), at the
  level `M`, where `D.kap M = D.κ M`; the encoding transports it to `Gw`. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **Along a weak encoding the physical coefficients agree.** -/
theorem weakEncoding_physCoeff {N J : ℕ} {η₀ : ℝ} {rootM rootR : ℕ → ℝ}
    {G Gw : GenStage D ScalarH Dm b j₀} {ι : CompIn G.comps ≃ CompIn Gw.comps}
    (henc : IsWeakEncoding N J η₀ rootM rootR G Gw ι) :
    ∃ e : ∀ v u, G.fam.Γ v u ≃ Gw.fam.Γ (ι v) (ι u),
      ∀ v u (γ : G.fam.Γ v u) d, Gw.physCoeff (ι v) (ι u) (e v u γ) d = G.physCoeff v u γ d := by
  obtain ⟨hlev, -, -, hact, hpiece, hweight, Cθ, e, idx, -, -, hid⟩ := henc
  refine ⟨e, fun v u γ d => ?_⟩
  obtain ⟨-, hmap, -, -, -, -, -, -, hmax, hfl⟩ := hid v u γ
  have hk : D.kap Gw.level = D.kap G.level := by rw [hlev]
  have he : D.eps Gw.level = D.eps G.level := by rw [hlev]
  have hE : D.eps (Gw.level - 1) = D.eps (G.level - 1) := by rw [hlev]
  funext t x
  unfold GenStage.physCoeff constituentPhysical
  rw [hk, he, hE]
  refine finsum_congr fun p => ?_
  rw [hweight p t, hpiece p, hmax, hmap]
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux,
    hfl p (Gw.actual p) (G.actual p) (hact p)]

/-- With one kernel for every provenance, the regularizing operator of an identity is that
kernel's operator. -/
theorem sysS_constKernel {G : GenStage D ScalarH Dm b j₀} (P : ProvParams) (κs : KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    G.sysS P (fun _ => κs) (fun _ => κs) φ₀ hφ₀ v u γ = κs.op φ₀ hφ₀ := by
  funext t
  unfold GenStage.sysS GenStage.kernelOf
  cases ((G.prov v u γ).tags P).kernel <;> rfl

section Reindex

variable {ι₁ ι₂ : Type*} {Γ₁ : ι₁ → ι₁ → Type*} {Γ₂ : ι₂ → ι₂ → Type*}

/-- The bijection of the identities over bijections of components and edges. -/
def edgeSigmaMap (σ : ι₁ ≃ ι₂) (e : ∀ i j, Γ₁ i j ≃ Γ₂ (σ i) (σ j)) :
    (Σ i j, Γ₁ i j) → Σ i' j', Γ₂ i' j' :=
  fun τ => ⟨σ τ.1, σ τ.2.1, e τ.1 τ.2.1 τ.2.2⟩

theorem edgeSigmaMap_bijective (σ : ι₁ ≃ ι₂) (e : ∀ i j, Γ₁ i j ≃ Γ₂ (σ i) (σ j)) :
    Function.Bijective (edgeSigmaMap σ e) := by
  constructor
  · rintro ⟨a, b', c⟩ ⟨a', b'', c'⟩ h
    simp only [edgeSigmaMap, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := σ.injective h1
    obtain ⟨h3, h4⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
    obtain rfl := σ.injective h3
    obtain rfl := (e a b').injective (eq_of_heq h4)
    rfl
  · rintro ⟨i', j', α'⟩
    obtain ⟨i, rfl⟩ := σ.surjective i'
    obtain ⟨j, rfl⟩ := σ.surjective j'
    obtain ⟨α, rfl⟩ := (e i j).surjective α'
    exact ⟨⟨i, j, α⟩, rfl⟩

/-- Edge-indexed data pulled back along the bijection of the identities. -/
theorem exists_edge_pullback {β : Type*} (σ : ι₁ ≃ ι₂) (e : ∀ i j, Γ₁ i j ≃ Γ₂ (σ i) (σ j))
    (Y : ∀ i j, Γ₁ i j → β) :
    ∃ Y' : ∀ i j, Γ₂ i j → β, ∀ i j (α : Γ₁ i j), Y' (σ i) (σ j) (e i j α) = Y i j α := by
  let E := Equiv.ofBijective (edgeSigmaMap σ e) (edgeSigmaMap_bijective σ e)
  let Ys : (Σ i j, Γ₁ i j) → β := fun τ => Y τ.1 τ.2.1 τ.2.2
  exact ⟨fun i' j' α' => Ys (E.symm ⟨i', j', α'⟩), fun i j α =>
    congrArg Ys (Equiv.ofBijective_symm_apply_apply _ (edgeSigmaMap_bijective σ e) ⟨i, j, α⟩)⟩

/-- **A scalar solution of the kernel-regularized system transports along a relabeling** of the
components and of the identities that keeps the coefficients and the operators. -/
theorem isKernelWeakSolutionTorus_reindex [Fintype ι₁] [Fintype ι₂] [∀ i j, Fintype (Γ₁ i j)]
    [∀ i j, Fintype (Γ₂ i j)] (σ : ι₁ ≃ ι₂) (e : ∀ i j, Γ₁ i j ≃ Γ₂ (σ i) (σ j))
    {ν t₀ t₁ : ℝ} {bv : ℝ → Vec 2 → Vec 2} {k Dm : ℕ}
    {B₁ : ∀ (i j : ι₁) (_ : Γ₁ i j) (d : ↥(Finset.Icc 2 Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => ℝ))}
    {B₂ : ∀ (i j : ι₂) (_ : Γ₂ i j) (d : ↥(Finset.Icc 2 Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => ℝ))}
    {S₁ : ∀ i j (_ : Γ₁ i j), ℝ → (Lp ℝ 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp ℝ 2 (volume.restrict AVenhance.unitCube))}
    {S₂ : ∀ i j (_ : Γ₂ i j), ℝ → (Lp ℝ 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp ℝ 2 (volume.restrict AVenhance.unitCube))}
    (hB : ∀ i j (α : Γ₁ i j) d, B₂ (σ i) (σ j) (e i j α) d = B₁ i j α d)
    (hS : ∀ i j (α : Γ₁ i j), S₂ (σ i) (σ j) (e i j α) = S₁ i j α)
    {f : ι₁ → TorusHk k ℝ} {u : ι₁ → ℝ → TorusHk k ℝ} {w : ι₁ → ℝ → TorusHk (k + 1) ℝ}
    {y : ∀ i j (_ : Γ₁ i j), ℝ → TorusHk (k + Dm - 1) ℝ}
    (h : IsKernelWeakSolutionTorus (h := fun _ : ι₁ => ℝ) (Γ := Γ₁) (G := fun _ _ _ => ℝ)
      ν t₀ t₁ bv k Dm B₁ (fun _ _ _ => ContinuousLinearMap.id ℝ ℝ) S₁ f (fun _ _ => 0)
      (fun _ _ => 0) u w y) :
    ∃ y' : ∀ i j (_ : Γ₂ i j), ℝ → TorusHk (k + Dm - 1) ℝ,
      IsKernelWeakSolutionTorus (h := fun _ : ι₂ => ℝ) (Γ := Γ₂) (G := fun _ _ _ => ℝ)
        ν t₀ t₁ bv k Dm B₂ (fun _ _ _ => ContinuousLinearMap.id ℝ ℝ) S₂ (fun i => f (σ.symm i))
        (fun _ _ => 0) (fun _ _ => 0) (fun i => u (σ.symm i)) (fun i => w (σ.symm i)) y' := by
  obtain ⟨y', hy⟩ := exists_edge_pullback σ e y
  refine ⟨y', ?_⟩
  obtain ⟨hcont, hmem, htr, hinit, hymem, hyval, hid⟩ := h
  refine ⟨fun i' => hcont (σ.symm i'), fun i' => hmem (σ.symm i'), fun i' => htr (σ.symm i'),
    fun i' => hinit (σ.symm i'), ?_, ?_, ?_⟩
  · intro i' j' α'
    obtain ⟨i, rfl⟩ := σ.surjective i'
    obtain ⟨j, rfl⟩ := σ.surjective j'
    obtain ⟨α, rfl⟩ := (e i j).surjective α'
    rw [hy]
    exact hymem i j α
  · intro i' j' α'
    obtain ⟨i, rfl⟩ := σ.surjective i'
    obtain ⟨j, rfl⟩ := σ.surjective j'
    obtain ⟨α, rfl⟩ := (e i j).surjective α'
    simp only [hy, hS, Equiv.symm_apply_apply]
    exact hyval i j α
  · intro i' t ht φ
    obtain ⟨i, rfl⟩ := σ.surjective i'
    have hflux : (fun s x => ∑ j' : ι₂, ∑ α' : Γ₂ (σ i) j', ∑ d : ↥(Finset.Icc 2 Dm),
        B₂ (σ i) j' α' d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y' (σ i) j' α' s).toFunction.jet ⟨⟨d.1 - 1, by
            have := Finset.mem_Icc.1 d.2
            omega⟩, word⟩ x)) =
        (fun s x => ∑ j : ι₁, ∑ α : Γ₁ i j, ∑ d : ↥(Finset.Icc 2 Dm),
        B₁ i j α d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y i j α s).toFunction.jet ⟨⟨d.1 - 1, by
            have := Finset.mem_Icc.1 d.2
            omega⟩, word⟩ x)) := by
      funext s x
      rw [← σ.sum_comp]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← (e i j).sum_comp]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [hB, hy]
    simp only [Equiv.symm_apply_apply]
    rw [hflux]
    exact hid i t ht φ

end Reindex

/-- **A solution of the regularized system of a scalar stage transports along a relabeling** that
keeps the physical coefficients and the regularizing operators. -/
theorem isRegSolution_reindex {G Gw : GenStage D ScalarH Dm b j₀}
    (ι : CompIn G.comps ≃ CompIn Gw.comps) (e : ∀ v u, G.fam.Γ v u ≃ Gw.fam.Γ (ι v) (ι u))
    {P P' : ProvParams} {seedK freshK seedK' freshK' : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀}
    (hB : ∀ v u (γ : G.fam.Γ v u) d, Gw.physCoeff (ι v) (ι u) (e v u γ) d = G.physCoeff v u γ d)
    (hS : ∀ v u (γ : G.fam.Γ v u), Gw.sysS P' seedK' freshK' φ₀ hφ₀ (ι v) (ι u) (e v u γ) =
      G.sysS P seedK freshK φ₀ hφ₀ v u γ)
    {ν : ℝ} {bv : ℝ → Vec 2 → Vec 2} {k : ℕ} {t₀ t₁ : ℝ}
    {f : ∀ v : CompIn G.comps, TorusHk k (ScalarH v.1.root)}
    {U : ∀ v : CompIn G.comps, ℝ → TorusHk k (ScalarH v.1.root)}
    {W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (ScalarH v.1.root)}
    {Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (ScalarH u.1.root)}
    (h : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    ∃ Y' : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (ScalarH u.1.root),
      Gw.IsRegSolution P' seedK' freshK' φ₀ hφ₀ ν bv k t₀ t₁ (fun v => f (ι.symm v))
        (fun _ _ => 0) (fun _ _ => 0) (rerootFamily ι U) (rerootFamily ι W) Y' :=
  (isKernelWeakSolutionTorus_reindex (Γ₁ := G.fam.Γ) (Γ₂ := Gw.fam.Γ) ι e
    (B₁ := fun v u γ d => G.physCoeff v u γ d.1) (B₂ := fun v u γ d => Gw.physCoeff v u γ d.1)
    (fun v u γ d => hB v u γ d.1) hS h : _)

/-- **The raw system of the weak stage** (`WeakEntryRawSolutionStatement`). -/
theorem weak_entry_raw_solution (plan : Assembly.WeakEntryGluePlan) :
    Assembly.WeakEntryRawSolutionStatement plan := by
  intro B A R C x g s f θ hθ r
  have hJ := A.Jw_pos
  have hp := ((r.reduction.2.2.2 (x.M + 1) (by omega) (by omega)).2.2.2.2.2)
  obtain ⟨Ub₀, -, hsol⟩ := hp
  have hsol' : (g.stage x.M).IsRegSolution x.P (fun _ => isoPairedKernel 0 R.nW)
      (fun _ => isoPairedKernel 0 R.nW) A.φ₀ A.hφ₀ (x.D.kap (g.stage x.M).level)
      (streamVel (x.D.Φ (g.stage x.M).level)) R.Kw (s.tq (x.M + 1)) (x.a + A.T₀) Ub₀
      (fun _ _ => 0) (fun _ _ => 0) (r.Ur x.M) (r.Urw x.M) (r.Urk x.M) := hsol
  have hlev : (g.stage x.M).level = x.M :=
    EntryWeakProofs.weakConstruction_level x.P _ x.M A.Jw 0 _ g.stage g.construction x.M le_rfl
      (by omega)
  have hkap : x.D.kap x.M = x.D.κ x.M := by
    unfold OCData.kap
    rw [x.terminal, min_self]
  rw [hlev, hkap] at hsol'
  have hUb : Ub₀ = fun w => r.Ur x.M w (s.tq (x.M + 1)) :=
    funext fun w => (hsol'.2.2.2.1 w).symm
  subst hUb
  obtain ⟨e, hB⟩ := weakEncoding_physCoeff g.encoding
  exact isRegSolution_reindex g.relabel e hB
    (fun v u γ => by rw [sysS_constKernel, sysS_constKernel]) hsol'

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Downward composition of the actual glued readouts. No lift equation is
needed to define the finite chain, and no solution is chosen in this module. -/

/-- Any supplied lift coefficients admit the finite readout chain. -/
theorem weak_readout_chain (plan : WeakEntryGluePlan) : WeakReadoutChainStatement plan := by
  intro B A R C x g CcR
  let T := x.M + A.Jw
  let V := fun i => ℝ → (CompIn (g.stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ
  have hr : (⟨0, []⟩ : Comp) ∈ (g.stage T).comps := by
    rw [g.construction.2.1.2.1]
    exact Finset.mem_singleton_self _
  let step : ∀ k, k < T → V (k + 1) → V k := fun k _ w t f =>
    w t (weakGluedLift (k + 1) A.Nw (A.Jw * A.Rw) (g.stage (k + 1))
      (CcR (k + 1)) t (weakReadoutStep (k + 1) A.η₀ (g.stage (k + 1)) (g.stage k) f))
  let root : V T := fun _ f y => f ⟨⟨0, []⟩, hr⟩ y
  let W : ∀ i, V i := fun i => if hi : i ≤ T then
    Nat.decreasingInduction (motive := fun i _ => V i) step root hi else fun _ _ _ => 0
  refine ⟨W, ?_, ?_⟩
  · intro t f y hr'
    change W T t f y = _
    simp only [W, dite_eq_left (Nat.le_refl T), Nat.decreasingInduction_self, root]
  · intro i hi hit
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
    intro t f
    change W k t f = W (k + 1) t _
    have hk : k ≤ T := by omega
    dsimp only [W]
    rw [dite_eq_left hk, dite_eq_left hit,
      Nat.decreasingInduction_succ_left (motive := fun i _ => V i) step root hit hk]
    rfl

end AVRegularity.WeakEntryProofs.Assembly
end

section
open Homogenization MeasureTheory Set Filter Topology Metric
open AVRegularity.Sobolev AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs
open AVRegularity.Providers.GenSem
namespace AVRegularity.Providers.WeakGen

/-! Full-fibre counterpart of the path-edge local reserve construction.
No new PDE or compact-jet estimate is used. -/

/-- Smoothness, window measurability, and local compact jets of a lifted path coefficient. -/
private theorem full_fiber_edge_local_data {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D ScalarH Dm b j₀) (hgen : WeakHolGen G)
    (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A)
    (v u : CompIn G.comps) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ)
    (hγ : γ ∈ (familyLiftData D G.level k A ρ (G.fam.fiber ⟨k, hk⟩ ⟨A, hA⟩)).edge v u d)
    (β : DerivativeWord2 (d.1 - 1)) (c : Fin 2) :
    let Ω := ladderOmega D b j₀ G.level k A ρ
    let T := Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
    (∀ t ∈ T, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun X : Vec 2 × Vec 2 => γ.coeff β t X.2 X.1 c) {X | X.2 ∈ Ω}) ∧
    (∀ Y ∈ Ω, Measurable (fun Z : T × Vec 2 => γ.coeff β Z.1 Y Z.2 c)) ∧
    (∀ K : Set (Vec 2 × Vec 2), IsCompact K → K ⊆ {X | X.2 ∈ Ω} → ∀ n,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ T, ∀ X ∈ K,
        ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => γ.coeff β t Z.2 Z.1 c) X‖ ≤ B) := by
  have hc := weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  simp only [familyLiftData, liftEdges, List.mem_map] at hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  change γ₀ ∈ (Finset.univ.toList : List (G.fam.Γ v u)).filterMap _ at hγ₀
  obtain ⟨γ₁, _, hγ₁⟩ := List.mem_filterMap.mp hγ₀
  split_ifs at hγ₁ with hd
  · simp only [Option.some.injEq] at hγ₁
    subst γ₀
    obtain ⟨f, F, hF, hval⟩ := hgen v u γ₁ d.1 β c
    let T := Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
    let Ω := ladderOmega D b j₀ G.level k A ρ
    have hclock : MapsTo (fun t => D.cellScaleSq G.level * t) T
        (ocPulseWindow D.α D.q D.Λ G.level k) :=
      fun _ ht => cellScaleSq_mul_mem_ocPulseWindow hc ht
    obtain ⟨hr, hm, hj⟩ := holomorphic_recenter_data hΛ hb (hF ⟨k, hk⟩).2 A ρ T
      (fun t => D.cellScaleSq G.level * t) (continuous_const.mul continuous_id) hclock
    have he t (ht : t ∈ T) (X : Vec 2 × Vec 2) (hX : X.2 ∈ Ω) :
        G.fam.flux ⟨k, hk⟩ ⟨A, hA⟩ _ _ γ₁ d.1 β
            (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • X.2) X.1 c =
          f ⟨k, hk⟩ (D.cellScaleSq G.level * t) (A.recenter D (ρ • X.2)) X.1 := by
      rw [hval ⟨k, hk⟩ ⟨A, hA⟩ _ (hclock ht), smul_smul, mul_div_cancel₀ _ hε]
      simp only [show IsAdmissibleChain D b j₀ G.level k (A.recenter D (ρ • X.2)) from hX,
        ↓reduceIte]
    refine ⟨fun t ht => (hr t ht).congr (fun X hX => he t ht X hX), ?_, ?_⟩
    · intro Y hY
      convert hm Y hY using 1
      funext Z
      exact he Z.1 Z.1.2 (Z.2, Y) hY
    · intro K hK hKO n
      obtain ⟨B, hB, hbound⟩ := hj K hK hKO n
      refine ⟨B, hB, fun t ht X hX => ?_⟩
      have heq : (fun Z : Vec 2 × Vec 2 =>
          G.fam.flux ⟨k, hk⟩ ⟨A, hA⟩ _ _ γ₁ d.1 β
            (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • Z.2) Z.1 c) =ᶠ[𝓝 X]
          (fun Z => f ⟨k, hk⟩ (D.cellScaleSq G.level * t) (A.recenter D (ρ • Z.2)) Z.1) := by
        filter_upwards [((AVRegularity.Providers.GenSem.isOpen_ladderOmega D b j₀ G.level k A ρ).preimage
          continuous_snd).mem_nhds (hKO hX)] with Z hZ
        exact he t ht Z hZ
      rw [(heq.iteratedFDeriv ℝ n).self_of_nhds]
      exact hbound t ht X hX

/-- One common cutoff gives reserved edge models on a neighborhood of each admissible offset. -/
theorem weak_full_fiber_local_reserves {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D ScalarH Dm b j₀) (hgen : WeakHolGen G)
    (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A) :
    let Ω := ladderOmega D b j₀ G.level k A ρ
    let a := D.slotStart G.level k / D.cellScaleSq G.level
    let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
    let edge := (familyLiftData D G.level k A ρ (G.fam.fiber ⟨k, hk⟩ ⟨A, hA⟩)).edge
    ∀ H Y₀, Y₀ ∈ Ω → ∃ (V : Set (Vec 2))
      (edge' : ConstituentEdges Dm (fun _ : CompIn G.comps => ℝ)), IsOpen V ∧ Y₀ ∈ V ∧
      (∀ t ∈ Icc a b₁, SlowOpenEdgeEq V t edge edge') ∧
      Nonempty (∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) := by
  classical
  dsimp only
  intro H Y₀ hY
  let Ω := ladderOmega D b j₀ G.level k A ρ
  let a := D.slotStart G.level k / D.cellScaleSq G.level
  let b₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let edge := (familyLiftData D G.level k A ρ (G.fam.fiber ⟨k, hk⟩ ⟨A, hA⟩)).edge
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp (AVRegularity.Providers.GenSem.isOpen_ladderOmega D b j₀ G.level k A ρ) Y₀ hY
  let U := ball Y₀ (r / 2)
  have hU : IsOpen U := isOpen_ball
  have hsub : closure U ⊆ Ω := by
    rw [closure_ball Y₀ (div_pos hr (by norm_num)).ne']
    intro Y hY
    exact hrΩ (mem_ball.mpr ((mem_closedBall.mp hY).trans_lt (half_lt_self hr)))
  have hK : IsCompact (closure U) := by
    rw [closure_ball Y₀ (div_pos hr (by norm_num)).ne']
    exact isCompact_closedBall _ _
  obtain ⟨χ, Qχ, hs, hχ⟩ := local_slow_cutoff_reserve_exists H U hU Y₀
    (mem_ball_self (div_pos hr (by norm_num)))
  obtain ⟨δ, hδ, hδχ⟩ := Metric.mem_nhds_iff.mp hχ
  let V := ball Y₀ δ
  let edge' := weakCutoffEdges χ (weakTimeClampEdges a b₁ edge)
  refine ⟨V, edge', isOpen_ball, mem_ball_self hδ, ?_, ?_⟩
  · intro t ht v u d
    have ht' : t ∈ Icc a b₁ := ht
    dsimp only [edge', weakCutoffEdges, weakTimeClampEdges]
    rw [List.map_map, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun γ _ => ⟨rfl, fun β Y hY z => by
      simp only [Function.comp_apply, min_eq_right ht'.2, max_eq_right ht'.1,
        show χ Y = 1 from hδχ hY, one_smul]⟩
  · have hres : ∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
        Nonempty (JointSourceReserve H (fun t z Y => γ.coeff β t Y z)) := by
      intro v u d γ hγ β
      obtain ⟨γ₁, hγ₁, rfl⟩ := List.mem_map.mp hγ
      obtain ⟨γ₀, hγ₀, rfl⟩ := List.mem_map.mp hγ₁
      have hQ (c : Fin 2) : Nonempty (JointSourceReserve H
          (fun t z Y => χ Y * γ₀.coeff β (max a (min b₁ t)) Y z c)) := by
        obtain ⟨hf, hm, hj⟩ := full_fiber_edge_local_data hΛ hζ hκ hb G hgen k hk ρ A hA
          v u d γ₀ hγ₀ β c
        exact compact_window_cutoff_reserve H a b₁
          (weakData_lift_window D hΛ hζ hκ G.level k) Ω U hU hK hsub χ hs Qχ
          (fun t z Y => γ₀.coeff β t Y z c)
          (fun t ht => (hf t ht).of_le (by exact_mod_cast (show (H : ℕ∞) ≤ ⊤ from le_top)))
          (fun t Y j z => congrFun (γ₀.periodic β t Y j z) c) hm hj
      exact ⟨vectorJointReserve H _ (fun c => (hQ c).some)⟩
    exact ⟨fun v u d γ hγ β => (hres v u d γ hγ β).some⟩


open AVRegularity.WeakEntryProofs.Assembly in
/-- The carried holomorphic-generation input needed to instantiate the generic
full-fibre reserve theorem for the weak-entry schedule. -/
def WeakEntryHolGenerationStatement (plan : WeakEntryGluePlan) : Prop :=
  WeakEntryCommonOK plan →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)}, 400 ≤ C.Υ →
    ∀ {x : WeakEntryData plan C} (g : WeakEntryStages x) (i : ℕ), x.M < i → i ≤ x.M + A.Jw →
    WeakHolGen (g.stage i)

open AVRegularity.WeakEntryProofs.Assembly in
/-- The full native readout models, from generation of every incoming
stage. Native chains have no child boundary, so every slow offset is admissible. -/
theorem weak_full_readout_models_of_generation (plan : WeakEntryGluePlan)
    (hgen : WeakEntryHolGenerationStatement plan) : WeakFullReadoutModelsStatement plan := by
  intro hplan B A R C hΥ x g i hi hit k hk H Y₀
  have hl := weakConstruction_level x.P _ x.M A.Jw 0 _ g.stage g.construction i (by omega) hit
  have hn : (g.stage i).IsNatural (x.M + A.Jw) := by
    by_cases he : i = x.M + A.Jw
    · subst i
      exact g.construction.2.1.2.2.2
    · exact weakConstruction_output_natural x.P _ x.M A.Jw 0 _ g.stage g.construction i
        (by omega) (by omega)
  have hj : x.j₀ ≤ i := by
    have ha := ((g.stage i).actual ⟨k, hk⟩).2
    rw [hn.2.2.1 ⟨k, hk⟩] at ha
    have hh := ha.2.1
    simpa only [nativeChain, List.length_nil, Nat.add_zero, hl,
      Nat.sub_add_cancel (show 1 ≤ i by omega)] using hh
  have hA : IsAdmissibleChain x.D A.bw x.j₀ (g.stage i).level k (nativeChain i k) := by
    have hh := ((g.stage i).actual ⟨k, hk⟩).2
    rw [hn.2.2.1 ⟨k, hk⟩] at hh
    simpa only [hl] using hh
  have hctx : (g.stage i).actual ⟨k, hk⟩ = ⟨nativeChain i k, hA⟩ :=
    Subtype.ext ((hn.2.2.1 ⟨k, hk⟩).trans (congrArg (fun j => nativeChain j k) hl))
  have hΛ : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  have hζ : IsFastProfile x.D.ζ := by rw [x.profile_eq]; exact B.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.alpha, x.q_eq, x.base_eq, x.profile_eq, x.terminal]
    exact x.band
  have hY : Y₀ ∈ ladderOmega x.D A.bw x.j₀ (g.stage i).level k (nativeChain i k)
      (x.D.eps (i - 1)) := by
    rw [ladderOmega, Set.mem_ofPred_eq, hl]
    exact QuietAtlas.isAdmissibleChain_nativeChain_recenter (D := x.D) (b := A.bw)
      (by omega) hj ⟨k, hk⟩ _
  have h := weak_full_fiber_local_reserves hΛ hζ hband A.bw_pos (g.stage i)
    (hgen hplan hΥ g i hi hit) k hk (x.D.eps (i - 1)) (nativeChain i k) hA H Y₀ hY
  rw [hctx]
  simpa only [hl] using h

open AVRegularity.WeakEntryProofs.Assembly in
/-- The common carrier and floors supply generation of every actual readout stage. -/
theorem weak_entry_hol_generation (plan : WeakEntryGluePlan) :
    WeakEntryHolGenerationStatement plan := by
  intro hplan B A R C _hΥ x g i hi hit
  exact weakCommonCase_holGen R ((hplan.1 B).trans x.base_ge) x.j₀ x.carrier400 x.M
    ((hplan.2 R C x.j₀).trans x.level_ge) x.D x.alpha x.q_eq x.base_eq x.profile_eq
    x.streams x.band x.terminal x.Dm x.order_ge x.P g.stage g.construction i hi.le hit

open AVRegularity.WeakEntryProofs.Assembly in
/-- All full native fibres have local reserved models, under the plan conditions. -/
theorem weak_full_readout_models (plan : WeakEntryGluePlan) : WeakFullReadoutModelsStatement plan :=
  weak_full_readout_models_of_generation plan (weak_entry_hol_generation plan)

end AVRegularity.Providers.WeakGen
end
