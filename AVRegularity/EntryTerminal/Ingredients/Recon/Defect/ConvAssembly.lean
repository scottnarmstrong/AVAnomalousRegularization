-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.MacroSwapLettersReg
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncPulsePeriodic
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FineDefectTime
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof

section
section
/-! **Macro swap, step (ii): regularity of the menu's macro flux** (`ReconMacroFluxReg`).

* `macroFlux_contDiff`: `menuMacroFlux` of a `C^{1 + D_m + N}` field is `C^1` in the position
  (the `SplitInput`-free glued-flux regularity `covTruncReg_gluedMeanFlux_contDiff`);
* `macroFlux_periodic`: it is `ℤ²`-periodic for a periodic `C²` field, given the periodicity of
  the glued mean flux of periodic fields on the grades `≤ depth` (`CovTruncGluedPeriodicBounded`;
  only the grades `0` and `1, …, depth` are read);
* `reconMacroFluxReg`: `ReconMacroFluxReg c` at a terminal context, from the floors and that
  periodicity.

Special cases: `a = 0` (all three terms vanish); `depth = 0` (no mean-flux terms beyond the
diagonal). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **`menuMacroFlux` is `C^1` in the position** for a field `C^{1 + D_m + N}`. -/
theorem macroFlux_contDiff (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (hm : G.level = m) (hN : N = Mn.N)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hord : 1 ≤ Dm)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k)
          (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        Mn.sX Mn.sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) Mn.N depth
        (CcT k))
    (hdepth : 1 ≤ depth → ActualFluxJointSmooth G)
    (hsX : 1 + Dm ≤ Mn.sX) (hsZ : 1 + Dm ≤ Mn.sZ)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (hg : ∀ v, ContDiff ℝ ((1 + Dm + Mn.N : ℕ) : ℕ∞) (fun x => g t x v)) (v : CompIn G.comps) :
    ContDiff ℝ (1 : ℕ∞) (fun y => menuMacroFlux Mn G m N depth CcT g v t y) := by
  subst hN
  subst hm
  have ha : ContDiff ℝ ((1 + Dm + Mn.N : ℕ) : ℕ∞) (g t) :=
    contDiff_pi.mpr fun w => hg w
  have hga : ContDiff ℝ ((1 + 1 : ℕ) : ℕ∞) (fun y => g t y v) :=
    (hg v).of_le (by exact_mod_cast (by omega : 1 + 1 ≤ 1 + Dm + Mn.N))
  have hgrad : ContDiff ℝ (1 : ℕ∞) (fun y => fun j : Fin 2 => ∑ l : Fin 2,
      ((ocRefFlux D.α D.q D.Λ D.ζ G.level (D.κ G.level) t - D.κ (G.level - 1) • 1) j l) •
        gradE (fun y' => g t y' v) y l) :=
    contDiff_pi.mpr fun j => ContDiff.sum fun l _ =>
      ContDiff.smul contDiff_const (gradE_contDiff 1 hga l)
  have hgrad2 : ContDiff ℝ (1 : ℕ∞) (fun y => fun j : Fin 2 => ∑ l : Fin 2,
      ocRefFlux D.α D.q D.Λ D.ζ G.level (D.κ G.level) t j l • gradE (fun y' => g t y' v) y l) :=
    contDiff_pi.mpr fun j => ContDiff.sum fun l _ =>
      ContDiff.smul contDiff_const (gradE_contDiff 1 hga l)
  have hd0 : ContDiff ℝ (1 : ℕ∞) (fun y => menuGluedMeanFlux Mn G G.level {0}
      (Finset.Icc 2 (Mn.N + 1)) CcT g t y v) :=
    covTruncReg_gluedMeanFlux_contDiff Mn G depth CcT hbase hprof hband hord hlift 1 hsX hsZ
      {0} (Finset.Icc 2 (Mn.N + 1)) (fun r hr => by simp at hr; omega)
      (fun ⟨r, hr, hr0⟩ => absurd (Finset.mem_singleton.mp hr) hr0) g t ha v
  have hm0 : ContDiff ℝ (1 : ℕ∞) (fun y => menuGluedMeanFlux Mn G G.level (Finset.Icc 1 depth)
      (Finset.Icc 2 (Mn.N + Dm)) CcT g t y v) :=
    covTruncReg_gluedMeanFlux_contDiff Mn G depth CcT hbase hprof hband hord hlift 1 hsX hsZ
      (Finset.Icc 1 depth) (Finset.Icc 2 (Mn.N + Dm)) (fun r hr => (Finset.mem_Icc.mp hr).2)
      (fun ⟨r, hr, hr0⟩ => hdepth (by have := Finset.mem_Icc.mp hr; omega)) g t ha v
  unfold menuMacroFlux menuDiagFluxPhys menuMeanFluxE
  exact (hgrad.add (hd0.sub hgrad2)).add hm0

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **`menuMacroFlux` is periodic** for a periodic `C²` field, given the periodicity of the glued
mean flux of periodic fields. -/
theorem macroFlux_periodic (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (hm : G.level = m)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (v : CompIn G.comps)
    (hglue : CovTruncGluedPeriodicBounded Mn G m depth CcT t v)
    (hg : ContDiff ℝ (2 : ℕ∞) (fun x => g t x v))
    (hper : ∀ w, IsZ2Periodic (fun x => g t x w)) :
    IsZ2Periodic (fun y => menuMacroFlux Mn G m N depth CcT g v t y) := by
  subst hm
  have hga : ∀ l, IsZ2Periodic (fun x => gradE (fun y => g t y v) x l) := fun l =>
    covTruncReg_gradE_periodic (hg.differentiable (by norm_num)) (hper v) l
  have g1 := hglue {0} (Finset.Icc 2 (N + 1)) g
    (fun r hr => (Finset.mem_singleton.1 hr).symm ▸ Nat.zero_le _) hper
  have g2 := hglue (Finset.Icc 1 depth) (Finset.Icc 2 (N + Dm)) g
    (fun r hr => (Finset.mem_Icc.1 hr).2) hper
  intro n x
  have e1 := g1 n x
  have e2 := g2 n x
  have e3 : ∀ l, gradE (fun y => g t y v) (x + latticeShift n) l = gradE (fun y => g t y v) x l :=
    fun l => hga l n x
  beta_reduce at e1 e2
  simp only [menuMacroFlux, menuDiagFluxPhys, menuMeanFluxE, e1, e2,
    e3]

end Stage

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- **`ReconMacroFluxReg` at a terminal context**, from the floors `1 + D_t ≤ s_X, s_Z`,
`1 + D_t + N_T ≤ K̂ - 2p_T` and the periodicity of the glued mean flux of periodic fields
on the grades `≤ d_W` (`CovTruncGluedBoundedAt`). -/
theorem reconMacroFluxReg (x : TermResAux c) (hΛ : 1 ≤ A.Λ) (hV : A.Valid) (h1 : 1 ≤ M)
    (hj : j₀ ≤ M) (hX : 1 + A.Dt ≤ sXT) (hZ : 1 + A.Dt ≤ sZT)
    (hK : 1 + A.Dt + A.NT ≤ A.Khat Kout - 2 * A.pT)
    (hglue : CovTruncGluedBoundedAt c) :
    ReconMacroFluxReg c := by
  have hE := covTruncReg_actualFluxJointSmooth c x hΛ hV h1 hj
  have hlev : c.Gw.level = M := c.weak.2.2.1
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, hterm⟩ := c.data
  have hbase : 1 ≤ c.D.Λ := hDΛ ▸ hΛ
  have hprof : IsFastProfile c.D.ζ := hDζ ▸ X.hζ
  have hband' : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have hord : 1 ≤ A.Dt := by
    have : 2 ≤ A.Dt := le_max_left _ _
    omega
  intro v s hs
  have hs' : s ∈ Set.Icc c.tp (c.a + A.T₀) := by rwa [tp_add_rTobs] at hs
  have hrep : ∀ w, ContDiff ℝ ((A.Khat Kout - 2 * A.pT : ℕ) : ℕ∞) (fun y => c.aRep s y w) ∧
      IsZ2Periodic (fun y => c.aRep s y w) := fun w => by
    obtain ⟨-, hd, hp, -⟩ := (c.lift.2.1 w s hs').2
    exact ⟨by exact_mod_cast hd, hp⟩
  have hg : ∀ w, ContDiff ℝ ((1 + A.Dt + A.NT : ℕ) : ℕ∞) (fun y => c.aRep s y w) := fun w =>
    ((hrep w).1).of_le (by exact_mod_cast hK)
  have hc := macroFlux_contDiff (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW hlev rfl c.CcT hbase
    hprof hband' hord c.lift.1 (fun _ => hE) hX hZ c.aRep s hg v
  have hp := macroFlux_periodic (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW hlev c.CcT c.aRep s v
    (hglue v s hs') ((hrep v).1.of_le (by exact_mod_cast (by omega : 2 ≤ A.Khat Kout - 2 * A.pT)))
    (fun w => (hrep w).2)
  exact ⟨fun k => (contDiff_pi.mp hc) k, fun k n y => congrFun (hp n y) k⟩

end Terminal

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Macro swap, step (ii): jet locality of the classical letters' flux**.

If two fields `C^D` have the same `D`-jets at `x`, `D = N_T + D_t`, the classical letters' fluxes
(`ClassicalDefectFlux`) are `C¹` with the same `1`-jet at `x` (`classicalFlux_triple`), so
their divergences at `x` agree (`divE_eq_of_sameJet`).

Special cases: `a₁ = a₂`; `AD = CE = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.EntryTerminal.Ingredients.Recon

theorem orderedDerivative_one' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec 2 → E) (i : Fin 2) (x : Vec 2) :
    orderedDerivative (fun _ : Fin 1 => i) f x = fderiv ℝ f x (basisVec i) := by
  simp [orderedDerivative, List.ofFn_succ]

/-- The divergence at `x` only depends on the `1`-jets of the components at `x`. -/
theorem divE_eq_of_sameJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Vec 2 → Fin 2 → E} {x : Vec 2}
    (h : ∀ j, SameJetAt 1 x (fun y => F y j) (fun y => G y j)) : divE F x = divE G x := by
  unfold divE
  refine Finset.sum_congr rfl fun j _ => ?_
  have := h j 1 (fun _ => j) le_rfl
  rwa [orderedDerivative_one', orderedDerivative_one'] at this

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **Jet locality of the classical flux.** -/
theorem classicalFlux_triple (B : ℝ) (D H : ℕ) (hD : 2 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a₁ a₂ : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ)
    (x : Vec 2)
    (h₁ : ∀ u, ContDiff ℝ (D : ℕ∞) (fun y => a₁ s y u))
    (h₂ : ∀ u, ContDiff ℝ (D : ℕ∞) (fun y => a₂ s y u))
    (hj : ∀ u, SameJetAt D x (fun y => a₁ s y u) (fun y => a₂ s y u))
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s)) (k : Fin 2) :
    Triple 1 x (fun y => ClassicalDefectFlux B D H AD CE Jm a₁ v s y k)
      (fun y => ClassicalDefectFlux B D H AD CE Jm a₂ v s y k) := by
  have W : ∀ u (m : ℕ) (α : DerivativeWord2 m), 1 + m ≤ D →
      Triple 1 x (orderedDerivative α (fun y => a₁ s y u))
        (orderedDerivative α (fun y => a₂ s y u)) := fun u m α hm =>
    ⟨AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff α 1 _
      ((h₁ u).of_le (by exact_mod_cast hm)),
     AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff α 1 _
      ((h₂ u).of_le (by exact_mod_cast hm)),
     sameJet_orderedDerivative α (sameJet_mono hm (hj u))⟩
  unfold ClassicalDefectFlux
  refine triple_add (triple_add ?_ ?_) ?_
  · exact triple_sum _ fun l _ => triple_smul _ (W v 1 _ (by omega))
  · refine triple_sum _ fun d _ => triple_sum _ fun α _ => ?_
    have hc : ContDiff ℝ ((1 : ℕ) : ℕ∞) (fun y => (AD d s y (WithLp.toLp 2 (Pi.single α
        (1 : ℝ)))).ofLp k) :=
      (contDiff_piLp 2).1 (((hAD d).clm_apply contDiff_const : ContDiff ℝ 1 fun y =>
        AD d s y (WithLp.toLp 2 (Pi.single α (1 : ℝ))))) k
    exact triple_mul hc (W v (d.1 - 1) α (by have := (Finset.mem_Icc.mp d.2).2; omega))
  · refine triple_sum _ fun r hr => triple_sum _ fun u _ =>
      triple_sum _ fun d _ => ?_
    have hd := (Finset.mem_Icc.mp d.2).2
    have hv₁ : ContDiff ℝ ((1 : ℕ) : ℕ∞) (fun y => (WithLp.toLp 2 fun α :
        DerivativeWord2 (d.1 - 1) => orderedDerivative α (fun y' => a₁ s y' u) y :
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u))) :=
      PiLp.contDiff_toLp.comp (contDiff_pi.2 fun α => (W u (d.1 - 1) α (by omega)).1)
    have hv₂ : ContDiff ℝ ((1 : ℕ) : ℕ∞) (fun y => (WithLp.toLp 2 fun α :
        DerivativeWord2 (d.1 - 1) => orderedDerivative α (fun y' => a₂ s y' u) y :
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u))) :=
      PiLp.contDiff_toLp.comp (contDiff_pi.2 fun α => (W u (d.1 - 1) α (by omega)).2.1)
    have hjv : SameJetAt 1 x (fun y => (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative α (fun y' => a₁ s y' u) y : PiLp 2 (fun _ => h u)))
        (fun y => (WithLp.toLp 2 fun α : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative α (fun y' => a₂ s y' u) y : PiLp 2 (fun _ => h u))) := by
      have hp := sameJet_pi (r := 1) (x := x)
        (f := fun y (α : DerivativeWord2 (d.1 - 1)) => orderedDerivative α (fun y' => a₁ s y' u) y)
        (g := fun y (α : DerivativeWord2 (d.1 - 1)) => orderedDerivative α (fun y' => a₂ s y' u) y)
        (fun α => (W u (d.1 - 1) α (by omega)).1) (fun α => (W u (d.1 - 1) α (by omega)).2.1)
        (fun α => (W u (d.1 - 1) α (by omega)).2.2)
      exact sameJet_clm (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap
        (contDiff_pi.2 fun α => (W u (d.1 - 1) α (by omega)).1)
        (contDiff_pi.2 fun α => (W u (d.1 - 1) α (by omega)).2.1) hp
    have hB := sameJet_bilin (ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : DerivativeWord2
      (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v))) x 1 (CE r v u d s) _ _
      (hCE r hr v u d) hv₁ hv₂ hjv
    have hcc := (hCE r hr v u d).clm_apply hv₁
    have hcc₂ := (hCE r hr v u d).clm_apply hv₂
    refine ⟨(contDiff_piLp 2).1 hcc k, (contDiff_piLp 2).1 hcc₂ k, ?_⟩
    exact sameJet_clm (PiLp.proj 2 (fun _ : Fin 2 => h v) k) hcc hcc₂ hB

end Generic

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Macro swap, step (ii): the macro flux and the classical letters' flux by grades**.

* `macroFlux_decomp`: `menuMacroFlux = -κ ∇a + ∑_{r ≤ depth} (glued mean flux of grade r)`;
* `classicalFlux_decomp`: `ClassicalDefectFlux = -B ∂_k a + ∑_{r ≤ H}
  classicalGradeFlux r`;
* `divE_add`, `divE_sum`: additivity of the divergence at a point for fluxes whose
  components are differentiable there.

Special cases: `depth = 0` (one grade); `a = 0`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.EntryTerminal.Ingredients.Recon

theorem sum_range_succ_eq_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1), f r = f 0 + ∑ r ∈ Finset.Icc 1 n, f r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    abel

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The glued mean flux is the sum over the grades. -/
theorem gluedMeanFlux_sum_rs (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m : ℕ)
    (rs ns : Finset ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) :
    menuGluedMeanFlux Mn G m rs ns CcT a t x v =
      ∑ r ∈ rs, menuGluedMeanFlux Mn G m {r} ns CcT a t x v := by
  unfold menuGluedMeanFlux
  simp only [Finset.sum_singleton]
  exact Finset.sum_comm

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The macro flux by grades.** -/
theorem macroFlux_decomp (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (y : Vec 2) :
    menuMacroFlux Mn G m N depth CcT g v t y =
      (fun j => -(D.κ (m - 1)) • gradE (fun y' => g t y' v) y j) +
        ∑ r ∈ Finset.range (depth + 1), menuGluedMeanFlux Mn G m {r}
          (if r = 0 then Finset.Icc 2 (N + 1) else Finset.Icc 2 (N + Dm)) CcT g t y v := by
  rw [sum_range_succ_eq_Icc]
  simp only [↓reduceIte]
  have hs : ∑ r ∈ Finset.Icc 1 depth, menuGluedMeanFlux Mn G m {r}
      (if r = 0 then Finset.Icc 2 (N + 1) else Finset.Icc 2 (N + Dm)) CcT g t y v =
      menuGluedMeanFlux Mn G m (Finset.Icc 1 depth) (Finset.Icc 2 (N + Dm)) CcT g t y v := by
    rw [gluedMeanFlux_sum_rs]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
    simp only [hr0, ↓reduceIte]
  rw [hs]
  unfold menuMacroFlux menuDiagFluxPhys menuMeanFluxE
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    sub_smul, Finset.sum_sub_distrib, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, neg_smul]
  abel

end Stage

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The divergence at a point is additive for fluxes with differentiable components there. -/
theorem divE_add (F G : Vec 2 → Fin 2 → E) (x : Vec 2)
    (hF : ∀ j, DifferentiableAt ℝ (fun y => F y j) x)
    (hG : ∀ j, DifferentiableAt ℝ (fun y => G y j) x) :
    divE (fun y j => F y j + G y j) x = divE F x + divE G x := by
  unfold divE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show fderiv ℝ (fun y => F y j + G y j) x (basisVec j) = _
  rw [fderiv_fun_add (hF j) (hG j)]
  rfl

/-- The divergence at a point of a finite sum of fluxes. -/
theorem divE_sum {κ : Type*} (S : Finset κ) (F : κ → Vec 2 → Fin 2 → E) (x : Vec 2)
    (hF : ∀ r ∈ S, ∀ j, DifferentiableAt ℝ (fun y => F r y j) x) :
    divE (fun y j => ∑ r ∈ S, F r y j) x = ∑ r ∈ S, divE (F r) x := by
  unfold divE
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_sum (fun r hr => hF r hr j)]
  simp

end Generic

section Classical

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The classical letters' flux by grades.** -/
theorem classicalFlux_decomp (B : ℝ) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ)
    (y : Vec 2) (k : Fin 2) :
    ClassicalDefectFlux B D H AD CE Jm a v s y k =
      -B • fderiv ℝ (fun y' => a s y' v) y (basisVec k) +
        ∑ r ∈ Finset.range (H + 1), classicalGradeFlux D r AD CE Jm a v s y k := by
  rw [sum_range_succ_eq_Icc]
  have hs : ∑ r ∈ Finset.Icc 1 H, classicalGradeFlux D r AD CE Jm a v s y k =
      ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (CE r v u d s y (WithLp.toLp 2 fun α => orderedDerivative α (fun y' => a s y' u) y)) k := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
    simp only [classicalGradeFlux, hr0, ↓reduceIte]
  rw [hs]
  unfold ClassicalDefectFlux classicalGradeFlux
  simp only [↓reduceIte, orderedDerivative_one', sub_smul, Finset.sum_sub_distrib,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, neg_smul]
  abel

end Classical

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
section
/-! **Macro swap, step (ii): the divergences agree** (`ReconMacroDivEqCl`).

Route (a): both divergences at `x` depend on finitely many jets of `aRep` at `x`
(`gluedMeanFlux_triple`, `classicalFlux_triple`); replace `aRep` at `x` by a smooth
periodic field with the same jets (`periodic_jet_realization`); for it, (i) and
`IsMeanPresentation` give the divergence identity grade by grade.

Special cases: `aRep` smooth (the replacement is the identity); one grade (`dW = 0`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **Each grade of the classical flux is `C¹` in the position.** -/
theorem classicalGrade_contDiff (D : ℕ) (hD : 2 ≤ D) (r : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (v : ι) (s : ℝ)
    (ha : ∀ u, ContDiff ℝ (D : ℕ∞) (fun y => a s y u))
    (hAD : r = 0 → ∀ d, ContDiff ℝ 1 (AD d s))
    (hCE : r ≠ 0 → ∀ v u d, ContDiff ℝ 1 (CE r v u d s)) (k : Fin 2) :
    ContDiff ℝ 1 (fun y => classicalGradeFlux D r AD CE Jm a v s y k) := by
  by_cases hr : r = 0
  · simp only [classicalGradeFlux, hr, ↓reduceIte]
    refine (ContDiff.sum fun l _ => ContDiff.smul contDiff_const ?_).add
      (ContDiff.sum fun d _ => ContDiff.sum fun α _ => ContDiff.smul ?_ ?_)
    · exact gradE_contDiff
        1 ((ha v).of_le (by exact_mod_cast hD)) l
    · exact (contDiff_piLp 2).1 (((hAD hr d).clm_apply contDiff_const : ContDiff ℝ 1 fun y =>
        AD d s y (WithLp.toLp 2 (Pi.single α (1 : ℝ))))) k
    · exact AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff _ 1 _
        ((ha v).of_le (by have := (Finset.mem_Icc.mp d.2).2; exact_mod_cast (by omega :
          1 + (d.1 - 1) ≤ D)))
  · simp only [classicalGradeFlux, hr, ↓reduceIte]
    refine ContDiff.sum fun u _ => ContDiff.sum fun d _ => ?_
    refine (contDiff_piLp 2).1 ((hCE hr v u d).clm_apply ?_) k
    refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun α => ?_)
    exact AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff _ 1 _
      ((ha u).of_le (by have := (Finset.mem_Icc.mp d.2).2; exact_mod_cast (by omega :
        1 + (d.1 - 1) ≤ D)))

end Generic

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The partial derivatives of two `C²` fields with equal `2`-jets form a triple of order `1`. -/
theorem gradE_triple {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Vec 2 → E}
    {x : Vec 2} (hf : ContDiff ℝ ((2 : ℕ) : ℕ∞) f) (hg : ContDiff ℝ ((2 : ℕ) : ℕ∞) g)
    (hj : SameJetAt 2 x f g)
    (l : Fin 2) : Triple 1 x (fun y => gradE f y l) (fun y => gradE g y l) :=
  ⟨AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg.gradE_contDiff
      1 hf l,
    AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg.gradE_contDiff
      1 hg l, (sameJet_succ_iff.1 hj).2 l⟩

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **Jet locality of the macro flux.** -/
theorem macroFlux_triple (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (hm : G.level = m) (hN : N = Mn.N)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hord : 1 ≤ Dm)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k)
          (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        Mn.sX Mn.sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) Mn.N depth
        (CcT k))
    (hE : ActualFluxJointSmooth G) (hX : 1 + Dm ≤ Mn.sX) (hZ : 1 + Dm ≤ Mn.sZ)
    (a₁ a₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (h₁ : ContDiff ℝ ((1 + Dm + Mn.N : ℕ) : ℕ∞) (a₁ t))
    (h₂ : ContDiff ℝ ((1 + Dm + Mn.N : ℕ) : ℕ∞) (a₂ t))
    (hj : SameJetAt (1 + Dm + Mn.N) x (a₁ t) (a₂ t)) (v : CompIn G.comps) :
    Triple 1 x (fun y => menuMacroFlux Mn G m N depth CcT a₁ v t y)
      (fun y => menuMacroFlux Mn G m N depth CcT a₂ v t y) := by
  subst hm hN
  have e : ∀ g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      (fun y => menuMacroFlux Mn G G.level Mn.N depth CcT g v t y) =
        fun y => (fun j => -(D.κ (G.level - 1)) • gradE (fun y' => g t y' v) y j) +
          ∑ r ∈ Finset.range (depth + 1), menuGluedMeanFlux Mn G G.level {r}
            (if r = 0 then Finset.Icc 2 (Mn.N + 1) else Finset.Icc 2 (Mn.N + Dm)) CcT g t y v :=
    fun g => funext fun y => macroFlux_decomp Mn G G.level Mn.N depth CcT g v t y
  rw [e a₁, e a₂]
  have hv₁ : ContDiff ℝ ((2 : ℕ) : ℕ∞) (fun y => a₁ t y v) :=
    ((contDiff_pi.1 h₁) v).of_le (by exact_mod_cast (by omega : 2 ≤ 1 + Dm + Mn.N))
  have hv₂ : ContDiff ℝ ((2 : ℕ) : ℕ∞) (fun y => a₂ t y v) :=
    ((contDiff_pi.1 h₂) v).of_le (by exact_mod_cast (by omega : 2 ≤ 1 + Dm + Mn.N))
  have hjv : SameJetAt 2 x (fun y => a₁ t y v) (fun y => a₂ t y v) :=
    sameJet_mono (by omega : 2 ≤ 1 + Dm + Mn.N)
      (sameJet_clm (ContinuousLinearMap.proj v :
        (∀ w : CompIn G.comps, hr w.1.root) →L[ℝ] hr v.1.root) h₁ h₂ hj)
  refine triple_add ?_ (triple_sum _ fun r hr => ?_)
  · have T : ∀ l, Triple 1 x (fun y => -(D.κ (G.level - 1)) • gradE (fun y' => a₁ t y' v) y l)
        (fun y => -(D.κ (G.level - 1)) • gradE (fun y' => a₂ t y' v) y l) := fun l =>
      triple_smul _ (gradE_triple hv₁ hv₂ hjv l)
    exact ⟨contDiff_pi.2 fun l => (T l).1, contDiff_pi.2 fun l => (T l).2.1,
      sameJet_pi (fun l => (T l).1) (fun l => (T l).2.1) fun l => (T l).2.2⟩
  · exact gluedMeanFlux_triple Mn G depth CcT hbase hprof hband hord hlift 1 (by omega)
      (by omega) {r} _ (fun r' hr' => by
        rw [Finset.mem_singleton] at hr'; have := Finset.mem_range.mp hr; omega)
      (fun _ => hE) a₁ a₂ t x h₁ h₂ hj v

end Stage

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **`ReconMacroDivEqCl` at a terminal context**, from the floors, (i) and the mean
presentations (both in the hypotheses of the statement). -/
theorem reconMacroDivEqCl (x : TermResAux c) (hΛ : 1 ≤ A.Λ) (hV : A.Valid) (h1 : 1 ≤ M)
    (hj : j₀ ≤ M) (hX : 1 + A.Dt ≤ sXT) (hZ : 1 + A.Dt ≤ sZT) (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT) : ReconMacroDivEqCl c kc hW hf := by
  have hE := covTruncReg_actualFluxJointSmooth c x hΛ hV h1 hj
  have hlev : c.Gw.level = M := c.weak.2.2.1
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, hterm⟩ := c.data
  have hbase : 1 ≤ c.D.Λ := hDΛ ▸ hΛ
  have hprof : IsFastProfile c.D.ζ := hDζ ▸ X.hζ
  have hband' : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have hord : 1 ≤ A.Dt := by
    have : 2 ≤ A.Dt := le_max_left _ _
    omega
  intro aC B₀C lamC AD CE Aedge Cstar Θc hlet hG hJ v s hs x0
  have hset := hlet.1
  have hD2 : 2 ≤ A.NT + A.Dt := by
    have : 2 ≤ A.Dt := le_max_left _ _
    omega
  have hN : 1 ≤ kc + (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4) := by
    have : 0 < (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4) := by positivity
    omega
  have hs' : s ∈ Set.Icc c.tp (c.a + A.T₀) := by
    rwa [show c.tp + rTobs c = c.a + A.T₀ by simp [rTobs]] at hs
  have hrep : ∀ w, ContDiff ℝ ((A.Khat Kout - 2 * A.pT : ℕ) : ℕ∞) (fun y => c.aRep s y w) ∧
      IsZ2Periodic (fun y => c.aRep s y w) := fun w => by
    obtain ⟨-, hd, hp, -⟩ := (c.lift.2.1 w s hs').2
    exact ⟨by exact_mod_cast hd, hp⟩
  have hcd : ∀ w, ContDiff ℝ ((1 + A.Dt + A.NT : ℕ) : ℕ∞) (fun y => c.aRep s y w) := fun w =>
    (hrep w).1.of_le (by exact_mod_cast (by omega : 1 + A.Dt + A.NT ≤ A.Khat Kout - 2 * A.pT))
  have hreal : ∀ w : CompIn c.Gw.comps, ∃ g : Vec 2 → ScalarH w.1.root,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ IsZ2Periodic g ∧ ∀ (r : ℕ) (I : DerivativeWord2 r),
        r ≤ 1 + A.Dt + A.NT →
        orderedDerivative I g x0 = orderedDerivative I (fun y => c.aRep s y w) x0 :=
    fun w => periodic_jet_realization (1 + A.Dt + A.NT) _ (by exact_mod_cast hcd w) x0
  choose P hPs hPp hPj using hreal
  let a' : ℝ → Vec 2 → ∀ w : CompIn c.Gw.comps, ScalarH w.1.root := fun _ y w => P w y
  have ha's : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a' t) := fun t => contDiff_pi.2 hPs
  have ha'p : ∀ t, IsZ2Periodic (a' t) := fun t n y => funext fun w => hPp w n y
  have hjet : ∀ w, SameJetAt (1 + A.Dt + A.NT) x0 (fun y => c.aRep s y w) (P w) :=
    fun w r I hr => (hPj w r I hr).symm
  have hP1 : ContDiff ℝ ((1 + A.Dt + A.NT : ℕ) : ℕ∞) (c.aRep s) := contDiff_pi.2 hcd
  have hP2 : ContDiff ℝ ((1 + A.Dt + A.NT : ℕ) : ℕ∞) (a' s) :=
    (ha's s).of_le (by exact_mod_cast le_top)
  have hJ' : SameJetAt (1 + A.Dt + A.NT) x0 (c.aRep s) (a' s) :=
    sameJet_pi hcd (fun w => (hPs w).of_le (by exact_mod_cast le_top)) hjet
  -- the divergence of the macro flux depends on the jets only
  have hmacro : divE (fun y k => menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT
      c.aRep v s y k) x0 = divE (fun y k => menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT
      A.dW c.CcT a' v s y k) x0 := by
    refine divE_eq_of_sameJet fun j => ?_
    have T := macroFlux_triple (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW hlev rfl c.CcT
      hbase hprof hband' hord c.lift.1 hE hX hZ c.aRep a' s x0 hP1 hP2 hJ' v
    exact sameJet_clm (ContinuousLinearMap.proj j :
      (Fin 2 → ScalarH v.1.root) →L[ℝ] ScalarH v.1.root) T.1 T.2.1 T.2.2
  -- the divergence of the classical letters' flux depends on the jets only
  have hADs : ∀ d, ContDiff ℝ 1 (AD d s) := fun d =>
    (hset.AD_smooth d s hs).of_le (by exact_mod_cast hN)
  have hCEs : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u d, ContDiff ℝ 1 (CE r v u d s) := fun r hr v u d =>
    (hset.CE_smooth r hr v u d s hs).of_le (by exact_mod_cast hN)
  have hcdD : ∀ w, ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (fun y => c.aRep s y w) := fun w =>
    (hcd w).of_le (by exact_mod_cast (by omega : A.NT + A.Dt ≤ 1 + A.Dt + A.NT))
  have hcdD' : ∀ w, ContDiff ℝ ((A.NT + A.Dt : ℕ) : ℕ∞) (fun y => a' s y w) := fun w =>
    (hPs w).of_le (by exact_mod_cast le_top)
  have hJD : ∀ u, SameJetAt (A.NT + A.Dt) x0 (fun y => c.aRep s y u) (fun y => a' s y u) :=
    fun u => sameJet_mono (by omega) (hjet u)
  have hcl : divE (fun y k => ClassicalDefectFlux (c.D.κ (M - 1)) (A.NT + A.Dt) A.dW AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) c.aRep v s y k) x0 =
      divE (fun y k => ClassicalDefectFlux (c.D.κ (M - 1)) (A.NT + A.Dt) A.dW AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) a' v s y k) x0 :=
    divE_eq_of_sameJet fun k => (classicalFlux_triple (c.D.κ (M - 1)) (A.NT + A.Dt)
      A.dW hD2 AD CE (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) c.aRep a' v s x0 hcdD hcdD'
      hJD hADs hCEs k).2.2
  -- the smooth case, grade by grade
  let nsr : ℕ → Finset ℕ := fun r => if r = 0 then Finset.Icc 2 (A.NT + 1) else
    Finset.Icc 2 (A.NT + A.Dt)
  let Gr : ℕ → Vec 2 → Fin 2 → ScalarH v.1.root := fun r y =>
    menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {r} (nsr r) c.CcT a' s y v
  let CG : ℕ → Vec 2 → Fin 2 → ScalarH v.1.root := fun r y k =>
    classicalGradeFlux (A.NT + A.Dt) r AD CE (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))
      a' v s y k
  let Q : Vec 2 → Fin 2 → ScalarH v.1.root := fun y j =>
    -(c.D.κ (M - 1)) • gradE (fun y' => a' s y' v) y j
  have e1 : (fun y k => menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT a' v s y k)
      = fun y k => Q y k + ∑ r ∈ Finset.range (A.dW + 1), Gr r y k := by
    funext y k
    rw [macroFlux_decomp]
    simp [Q, Gr, nsr, Pi.add_apply, Finset.sum_apply]
  have e2 : (fun y k => ClassicalDefectFlux (c.D.κ (M - 1)) (A.NT + A.Dt) A.dW AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) a' v s y k) =
      fun y k => Q y k + ∑ r ∈ Finset.range (A.dW + 1), CG r y k := by
    funext y k
    rw [classicalFlux_decomp]
    rfl
  have hQ : ∀ j, DifferentiableAt ℝ (fun y => Q y j) x0 := fun j =>
    ((gradE_contDiff 1 ((hcdD' v).of_le (by exact_mod_cast (by omega :
      1 + 1 ≤ A.NT + A.Dt))) j).const_smul _).differentiable (by simp) |>.differentiableAt
  have hGd : ∀ r ∈ Finset.range (A.dW + 1), ∀ j, DifferentiableAt ℝ (fun y => Gr r y j) x0 := by
    intro r hr j
    have T := gluedMeanFlux_triple_m (A.Mt M sXT sZT c.tp cr) c.Gw M A.dW hlev c.CcT hbase
      hprof hband' hord c.lift.1 1 hX hZ {r} (nsr r)
      (fun r' hr' => by rw [Finset.mem_singleton] at hr'; have := Finset.mem_range.mp hr; omega)
      (fun _ => hE) a' a' s x0 hP2 hP2 (fun _ _ _ => rfl) v
    exact (((contDiff_pi.1 T.1) j).differentiable (by simp)) x0
  have hCd : ∀ r ∈ Finset.range (A.dW + 1), ∀ j, DifferentiableAt ℝ (fun y => CG r y j) x0 := by
    intro r hr j
    have := classicalGrade_contDiff (A.NT + A.Dt) hD2 r AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) a' v s hcdD'
      (fun hr0 d => hADs d)
      (fun hr0 v u d => hCEs r (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hr0,
        by have := Finset.mem_range.mp hr; omega⟩) v u d) j
    exact (this.differentiable (by simp)) x0
  have hsum : ∀ r ∈ Finset.range (A.dW + 1), divE (Gr r) x0 = divE (CG r) x0 := by
    intro r hr
    have g1 := hG r hr a' ha's ha'p s hs x0 v
    have g2 := hlet.2 r hr a' ha's ha'p s hs x0 v
    exact neg_injective (g1.symm.trans g2)
  have hsm : divE (fun y k => menuMacroFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT a'
      v s y k) x0 = divE (fun y k => ClassicalDefectFlux (c.D.κ (M - 1)) (A.NT + A.Dt) A.dW
      AD CE (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) a' v s y k) x0 := by
    rw [e1, e2, divE_add _ _ x0 hQ (fun j => DifferentiableAt.fun_sum fun r hr =>
      hGd r hr j), divE_add _ _ x0 hQ (fun j => DifferentiableAt.fun_sum fun r hr =>
      hCd r hr j), divE_sum _ _ x0 hGd, divE_sum _ _ x0 hCd]
    exact congrArg _ (Finset.sum_congr rfl hsum)
  exact hmacro.trans (hsm.trans hcl.symm)

end Terminal

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **`ReconMacroSwapAt` at a terminal context** (macro swap, step (ii)).

`reconMacroSwapAt`: the macro flux of the menu is replaced by the letters' flux, from the
regularity of the macro flux (`reconMacroFluxReg`, with the periodicity of the glued mean flux
on the grades `≤ d_W`, `CovTruncGluedBoundedAt`), the regularity of the classical
letters' flux (`reconLettersFluxRegCl`) and the divergence identity
(`reconMacroDivEqCl`), by the torus integration by parts.

Special cases: `a = 0` (both fluxes vanish); equal fluxes. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **(ii) at a terminal context**, with the periodicity of the glued mean flux as hypothesis. -/
theorem reconMacroSwapAt (x : TermResAux c) (hΛ : 1 ≤ A.Λ) (hV : A.Valid) (h1 : 1 ≤ M)
    (hj : j₀ ≤ M) (hX : 1 + A.Dt ≤ sXT) (hZ : 1 + A.Dt ≤ sZT) (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (hglue : CovTruncGluedBoundedAt c) :
    ReconMacroSwapAt c kc hW hf :=
  reconMacroSwapAt_of_classical_steps c kc hW hf
    (reconMacroFluxReg c x hΛ hV h1 hj hX hZ (by omega) hglue)
    (fun aC B₀C lamC AD CE Aedge Cstar Θc hlet =>
      reconLettersFluxRegCl c kc hW aC B₀C lamC AD CE Aedge Cstar Θc hlet)
    (reconMacroDivEqCl c x hΛ hV h1 hj hX hZ kc hW hf)

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The readout smoothness is proved**.

`reconReadoutSmoothAt_of_certificate`: both readouts are `C^{2p_T}`, from the certificate `x.cert`
and the prefix floors. `termReconReadoutSmooth_proof`: `TermReconReadoutSmoothStatement`.

Special cases: `x.aZ = 0 = x.aY` (everything is zero); `2 p_T = 0` (continuity only: the proof
is uniform in `p_T`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **Both readouts are `C^{2p_T}`, from the certificate and the floors.** -/
theorem reconReadoutSmoothAt_of_certificate
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hA : A.Valid) (hΛ : 128 ≤ A.Λ)
    {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hK : 2 * A.pT + A.Dt + 2 ≤ A.Khat Kout) :
    ReconReadoutSmoothAt c x := by
  intro v t ht
  have hST := termCtx_slotTransverse c x hA hΛ hCH hΥ hcar hX hZ
  have hSH := termCtx_shiftInvariant c hΛ
  have hφ := hA.2.1
  have hcoef := fun v u γ d => termCtx_physCoeff c x x.cert hST hSH hA hΛ hj hM2
    (2 * A.pT) v u γ d t
  refine ⟨?_, ?_⟩
  · have hflux := rootFluxDefect_smooth (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
      A.φ₀ hφ.1 hφ.2.2.2 c.Gw c.Gt' x.aZ t (2 * A.pT) hcoef
      (fun u => by
        obtain ⟨-, h1, h2, -⟩ := x.repZ u t ht
        exact ⟨h1.of_le (WithTop.coe_le_coe.2 (Nat.cast_le.2 (by omega))), h2⟩)
    have hro := readoutFlux_smooth (hr := ScalarH) M (c.D.eps (M - 1)) A.η₀
      (S := c.Gw.comps) (S' := c.Gt'.comps) (fun _ => True)
      (fun v' s y' => rootFluxDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
        c.Gw c.Gt' x.aZ v' s y') t (2 * A.pT) (fun v' => hflux v') v
    exact PiLp.contDiff_ofLp.comp hro.1
  · have h := termInnerSmoothAt_of_certificate c x 0 x.cert hA hΛ hCH hΥ hcar hX hZ hj hM2
      (by omega)
    have h1 := (h v t ht).1
    rw [zero_add] at h1
    exact h1

/-- **Readout smoothness with the prefix.** -/
theorem termReconReadoutSmooth_proof : TermReconReadoutSmoothStatement := by
  intro ℓ X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ?_⟩⟩
  set S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 with hS
  refine ⟨S, S, 2 * A.pT + A.Dt + 2, fun sXT sZT hX hZ Kout hKout => ⟨0, ?_⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ hcr0 hcr1 hcr _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker hcP
  refine ⟨(), 1, 1, le_rfl, one_pos, fun j₀ hcar => ⟨j₀ + 2, fun M hM c x => ?_⟩⟩
  exact reconReadoutSmoothAt_of_certificate c x hV hΛ le_rfl le_rfl hcar hX hZ (by omega)
    (by omega) (le_trans hKout (le_max_left _ _))

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The conversion to the coarse defect, assembled**. At a context it is the assembly
`reconDefectConvPlusAt_of_glued_swap` with
- the glued means (step (i)) from `reconGluedMeanAt_all`. It uses the lift sequence and
  setting, which are premises of `ReconDefectConvAt` itself, so it is applied after the intros;
- the macro swap (step (ii)) from `reconMacroSwapAt`.
Its two inputs are proved:
- the glue `CovTruncGluedBoundedAt` (periodicity of the glued mean flux on the grades `≤ d_W`):
  `covTruncGluedPeriodicBounded`, carried from `TermResPrefix` to `ReconPrefix` by
  `reconPrefix_of_termResPrefix`;
- the readout smoothness `ReconReadoutSmoothAt`: `termReconReadoutSmooth_proof`.
The floors of `reconGluedMeanAt_all` and `reconMacroSwapAt` (`1 ≤ Λ`, `1 ≤ N_T`, `1 ≤ M`, `j₀ ≤ M`, `1 + D_t ≤ s_X, s_Z`) are prefix
floors. `termReconDefectConv`: `TermReconDefectConvStatement`.

Special cases:
- `j₀ = 0`: the floor `M₀ ≥ j₀ + 1` is `M ≥ 1`, which is the floor `1 ≤ M` of `reconGluedMeanAt_all`.
- `D_t = 2` (the least value, `A.Dt = max 2 _`): the floors are `s_X, s_Z ≥ 3`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section At

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **The conversion at a context**, given the glue and the readout smoothness. -/
theorem reconDefectConvAt_of_glue (x : TermResAux c) (kc ℓ : ℕ) (hΛ : 1 ≤ A.Λ) (hV : A.Valid)
    (h1 : 1 ≤ M) (hj : j₀ ≤ M) (hX : 1 + A.Dt ≤ sXT) (hZ : 1 + A.Dt ≤ sZT)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (hglue : CovTruncGluedBoundedAt c) (hRs : ReconReadoutSmoothAt c x) :
    ReconDefectConvAt c x kc ℓ hW hf F1 F2 F3 := by
  intro hWk hreal hTR hseq CGl Cw' Ca Sb Cg hset
  exact reconDefectConvPlusAt_of_glued_swap c x kc ℓ hW hf F1 F2 F3
    (reconGluedMeanAt_all c hΛ h1 (le_trans (by norm_num) (two_le_NT_of_valid A hV)) x ℓ
      CGl Cw' Ca Sb Cg hseq hset)
    (reconMacroSwapAt c x hΛ hV h1 hj hX hZ kc hW hf hglue)
    hRs hWk hreal hTR hseq CGl Cw' Ca Sb Cg hset

end At

/-- **A `TermResPrefix` statement without the flux constants is a `ReconPrefix` statement**, at
every offset `ℓ` (take `C_fl := 0` and `C := C₀`). -/
theorem reconPrefix_of_termResPrefix
    {Q : ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
      {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
      {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
      (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
        cker j₀ M), TermResAux c → ℕ → Prop}
    (h : TermResPrefix fun c x kc _ _ _ _ => Q c x kc) :
    ReconPrefix (κ := Unit) fun c x kc _ _ => Q c x kc := by
  intro _ℓ X
  obtain ⟨Λ₀, h128, h⟩ := h X
  refine ⟨Λ₀, h128, fun A hΛ hV => ?_⟩
  obtain ⟨kc₀, h⟩ := h A hΛ hV
  refine ⟨kc₀, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, h⟩ := h kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, h⟩ := h sXT sZT hX hZ Kout hK
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP => ?_⟩
  obtain ⟨C₀, _cgap, _Cg, _hcgap, CH, Υ, hCH, hΥ, h⟩ :=
    h Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan hLan hJm
      cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP 0
  exact ⟨(), CH, Υ, hCH, hΥ, fun j₀ hj₀ => h C₀ le_rfl j₀ hj₀⟩

/-- **The glue with the prefix.** -/
def TermReconGlueStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ _ _ _ => CovTruncGluedBoundedAt c

/-- **The glue is proved** (`covTruncGluedPeriodicBounded`). -/
theorem termReconGlue : TermReconGlueStatement :=
  reconPrefix_of_termResPrefix (Q := fun c _ _ => CovTruncGluedBoundedAt c)
    covTruncGluedPeriodicBounded

/-- **The conversion with the prefix**, given the glue and the readout smoothness. -/
theorem termReconDefectConv_of_glue (hg : TermReconGlueStatement)
    (hr : TermReconReadoutSmoothStatement) : TermReconDefectConvStatement := by
  intro ℓ X
  obtain ⟨Λ₀, h128, hall⟩ := ReconPrefix.and hg hr ℓ X
  refine ⟨Λ₀, h128, fun A hΛ hV => ?_⟩
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) (le_trans h128 hΛ)
  obtain ⟨kc₀, hall⟩ := hall A hΛ hV
  refine ⟨kc₀, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hall⟩ := hall kc hkc
  refine ⟨max SX (1 + A.Dt), max SZ (1 + A.Dt), Kf, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hall⟩ := hall sXT sZT (le_trans (le_max_left _ _) hX)
    (le_trans (le_max_left _ _) hZ) Kout hK
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP => ?_⟩
  obtain ⟨_k, CH, Υ, hCH, hΥ, hall⟩ :=
    hall Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan hLan hJm
      cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
  refine ⟨(), CH, Υ, hCH, hΥ, fun j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hall⟩ := hall j₀ hj₀
  refine ⟨max M₀ (j₀ + 1), fun M hM c x hW hf F1 F2 F3 => ?_⟩
  have hMj : j₀ + 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hgc, hrc⟩ := hall M (le_trans (le_max_left _ _) hM) c x
  exact reconDefectConvAt_of_glue c x kc ℓ hΛ1 hV (by omega) (by omega)
    (le_trans (le_max_right _ _) hX) (le_trans (le_max_right _ _) hZ) hW hf F1 F2 F3 hgc hrc

/-- **The conversion `TermReconDefectConvStatement` is proved.** -/
theorem termReconDefectConv : TermReconDefectConvStatement :=
  termReconDefectConv_of_glue termReconGlue termReconReadoutSmooth_proof

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
