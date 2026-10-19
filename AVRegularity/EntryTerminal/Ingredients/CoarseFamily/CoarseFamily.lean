-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.PlaneFluxTerm
import AVRegularity.CycleComparison.Error.Main
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The trace of the first coarse family**: `g` on the old components, `0` on the new
ones (`IsTerminalTrace`). Its mass-weighted norm is at most that of `g` when the old components keep
their masses (`IsTerminalLaw` keeps the root masses; old components have no births).

Degenerate cases:
- An empty weak family: the trace is `0`.
- An empty retained family: the left sum is empty.
- `g = 0`: both sides vanish. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The trace of the first coarse family: `g` on the old components, `0` on the new ones. -/
def terminalTrace (Gw Gt : GenStage D ScalarH Dm b j₀) {K : ℕ}
    (g : ∀ v : CompIn Gw.comps, TorusHk K (ScalarH v.1.root)) :
    ∀ v' : CompIn Gt.comps, TorusHk K (ScalarH v'.1.root) :=
  fun v' => if hv : v'.1 ∈ Gw.comps then g ⟨v'.1, hv⟩ else 0

theorem terminalTrace_isTrace (Gw Gt : GenStage D ScalarH Dm b j₀) {K : ℕ}
    (g : ∀ v : CompIn Gw.comps, TorusHk K (ScalarH v.1.root)) :
    IsTerminalTrace Gw Gt g (terminalTrace Gw Gt g) :=
  ⟨fun _ hv => by simp only [terminalTrace, hv, ↓reduceDIte],
    fun _ hv => by simp only [terminalTrace, hv, ↓reduceDIte]⟩

/-- A sum over one finset of components, restricted to a second, is at most the sum over the
second (nonnegative terms). -/
theorem sum_compIn_ite_le {S S' : Finset Comp} (f : Comp → ℝ) (hf : ∀ c ∈ S, 0 ≤ f c) :
    ∑ v : CompIn S', (if v.1 ∈ S then f v.1 else 0) ≤ ∑ v : CompIn S, f v.1 := by
  rw [Finset.sum_coe_sort S' (fun c => if c ∈ S then f c else 0), Finset.sum_coe_sort S f,
    ← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => (Finset.mem_filter.mp hc).2)
    (fun c hc _ => hf c hc)

/-- **The trace norm.** If every old component keeps its mass, the weighted norm of the trace is
at most that of `g`. -/
theorem terminalTrace_weightedNorm_le (Gw Gt : GenStage D ScalarH Dm b j₀) (lawW lawT : BirthLaw)
    (ρ : ℝ) {K : ℕ} (g : ∀ v : CompIn Gw.comps, TorusHk K (ScalarH v.1.root))
    (hmass : ∀ (v' : CompIn Gt.comps) (hv : v'.1 ∈ Gw.comps),
      Gt.mass lawT v' = Gw.mass lawW ⟨v'.1, hv⟩)
    (hpos : ∀ v, 0 ≤ Gw.mass lawW v) :
    weightedNorm ρ (Gt.mass lawT) (fun _ => 1) (terminalTrace Gw Gt g) ≤
      weightedNorm ρ (Gw.mass lawW) (fun _ => 1) g := by
  unfold weightedNorm massNormSq
  apply Real.sqrt_le_sqrt
  let F : Comp → ℝ := fun c => if hc : c ∈ Gw.comps then
    (Gw.mass lawW ⟨c, hc⟩ / 1 ^ 2)⁻¹ * factorialNormSq ρ (g ⟨c, hc⟩).val else 0
  have hterm : ∀ v' : CompIn Gt.comps,
      (Gt.mass lawT v' / 1 ^ 2)⁻¹ * factorialNormSq ρ (terminalTrace Gw Gt g v').val =
        if v'.1 ∈ Gw.comps then F v'.1 else 0 := by
    intro v'
    by_cases hv : v'.1 ∈ Gw.comps
    · simp only [terminalTrace, hv, ↓reduceDIte, ↓reduceIte, F, hmass v' hv]
    · simp only [terminalTrace, hv, ↓reduceDIte, ↓reduceIte, ZeroMemClass.coe_zero]
      rw [show factorialNormSq ρ (0 : JetL2 _ K (ScalarH v'.1.root)) = 0 by
        simp [factorialNormSq, derivativeNormSq]]
      ring
  have hgw : ∀ v : CompIn Gw.comps, (Gw.mass lawW v / 1 ^ 2)⁻¹ * factorialNormSq ρ (g v).val =
      F v.1 := by
    intro v
    simp only [F, v.2, ↓reduceDIte]
  calc _ = ∑ v' : CompIn Gt.comps, (if v'.1 ∈ Gw.comps then F v'.1 else 0) :=
        Finset.sum_congr rfl fun v' _ => hterm v'
    _ ≤ ∑ v : CompIn Gw.comps, F v.1 := by
        refine sum_compIn_ite_le F fun c hc => ?_
        simp only [F, hc, ↓reduceDIte]
        exact mul_nonneg (inv_nonneg.mpr (div_nonneg (hpos _) (by positivity)))
          (Finset.sum_nonneg fun j _ => mul_nonneg
            (div_nonneg (by rw [pow_mul]; positivity) (by positivity))
            (derivativeNormSq_nonneg _ _))
    _ = _ := Finset.sum_congr rfl fun v _ => (hgw v).symm
end

/-! **The kernel operator of the retained terminal family.** The certificate
`TerminalRetainedClauses` of the retained family, at the radius `ρ = c_r √(B h)` and the order `K`,
is the data of a `TorusKernelOperator`:
- the coefficients `B` are the physical coefficients;
- the operators `C` are identities;
- the regularizers `S` are the family's kernel operators;
- the masses `π` are the component masses;
- the widths `r` are the kernel widths.

The scalar premises are the time order, the positivity of the radius, the diffusivity, the
masses and the widths, and `2 ≤ Dm`.

Degenerate cases:
- An empty retained family: every field is about an empty product; the Schur bound is vacuous.
- One component without identities: no coefficient, regularizer or width.
- `K = 0`: the coefficient clauses at order zero. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The operator of the retained family.** -/
def retainedOperator (lawT : BirthLaw) (Pt : ProvParams) (seedKt freshKt : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (cker : ℕ → ℝ) (M K : ℕ) (cr tp tf : ℝ)
    (Gt : GenStage D ScalarH Dm b j₀)
    (hR : TerminalRetainedClauses lawT Pt seedKt freshKt φ₀ hφ₀ cker M K cr tp tf Gt)
    (htime : tp ≤ tf) (hρ : 0 < D.termRho cr M) (hν : 0 < D.κ (M - 1)) (hDm : 2 ≤ Dm)
    (hπ : ∀ v, 0 < Gt.mass lawT v)
    (hwidth : ∀ v u (γ : Gt.fam.Γ v u), 0 < (Gt.kernelOf Pt seedKt freshKt v u γ).width) :
    KernelEnergy.TorusKernelOperator (h := fun v : CompIn Gt.comps => ScalarH v.1.root)
      (Γ := Gt.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) tp tf (D.termRho cr M) (D.κ (M - 1))
      K Dm where
  htime := htime
  radius_pos := hρ
  diffusivity_pos := hν
  order_ge_two := hDm
  π := fun v => Gt.mass lawT v
  hπ := hπ
  B := fun v u γ d => Gt.physCoeff v u γ d.1
  hB_meas := fun v u γ d => (hR.2.2 v u γ d).1
  hB_smooth := fun v u γ d => (hR.2.2 v u γ d).2.1
  hB_per := fun v u γ d => (hR.2.2 v u γ d).2.2.1
  hB_fin := fun v u γ d => (hR.2.2 v u γ d).2.2.2
  C := fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root)
  S := fun v u γ => Gt.sysS Pt seedKt freshKt φ₀ hφ₀ v u γ
  c := cker
  r := fun v u γ => (Gt.kernelOf Pt seedKt freshKt v u γ).width
  hr := hwidth
  hS := fun v u γ => hR.2.1 v u γ _ hρ K le_rfl
  θ := 1 / 8
  hθ := le_rfl
  hschur := hR.1 K le_rfl
end

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The outgoing seed datum of the first coarse family** (`CoarseFamilyStatement`). The datum
on the seed is `f_n = Z(s_n)` truncated to order `0`, carried by the bijection `ι`. Its norm with
the root masses is the retained `L²` norm at `s_n`, since `IsSeedEncoding` gives the seed roots the
retained masses. That norm is at most the strong
energy, because `s_n` lies in the window.

Degenerate cases:
- An empty retained family: both sides vanish.
- `s_n = t_p`: the slice at the start of the window.
- `Z = 0`: `f_n = 0`. -/

/-- **A time slice is below the strong energy.** -/
theorem slice_le_strongEnergy_sq {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {ρ B : ℝ} {π : ι → ℝ} (hπ : ∀ v, 0 < π v) {t₀ t₁ : ℝ} {K : ℕ}
    (U : ∀ v, ℝ → TorusHk K (h v)) (Uw : ∀ v, ℝ → TorusHk (K + 1) (h v)) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) :
    ENNReal.ofReal (∑ v, (π v)⁻¹ * factorialNormSq ρ (U v s).val) ≤
      strongEnergy ρ B π t₀ t₁ U Uw ^ (2 : ℝ) := by
  unfold strongEnergy
  rw [← ENNReal.rpow_mul]
  norm_num
  rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
    (factorialNormSq_nonneg ρ _)]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact le_trans (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc t₀ t₁) =>
    ENNReal.ofReal (factorialNormSq ρ (U v t).val)) s hs) le_self_add

/-- The order-zero factorial norm does not depend on the radius. -/
theorem factorialNormSq_zero_radius {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (ρ ρ' : ℝ) (X : TorusHk 0 E) :
    factorialNormSq ρ X.val = factorialNormSq ρ' X.val := by
  simp [factorialNormSq, factorialWeight]

variable {D : OCData} {Dm Ds : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The seed datum bound.** If the retained family's strong energy on a window containing `s` is
at most `E`, then the order-zero datum `Z(s)`, carried to the seed by `ι`, has root-mass-weighted
norm at most `E`. -/
theorem seedDatum_weightedNorm_le (Gt : GenStage D ScalarH Dm b j₀)
    (seed : GenStage D ScalarH Ds b j₀) (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (rootM : ℕ → ℝ) (lawT : BirthLaw) (hroot : ∀ v, rootM (ι v).1.root = Gt.mass lawT v)
    (hπ : ∀ v, 0 < Gt.mass lawT v) (ρ ν tp tf s E : ℝ) (hs : s ∈ Set.Icc tp tf) (hE0 : 0 ≤ E)
    {K : ℕ} (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk K (ScalarH v.1.root))
    (Zw : ∀ v : CompIn Gt.comps, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
    (hE : strongEnergy ρ ν (Gt.mass lawT) tp tf Z Zw ≤ ENNReal.ofReal E) :
    weightedNorm (hr := ScalarH) 1 (fun v : CompIn seed.comps => rootM v.1.root) (fun _ => 1)
        (fun w : CompIn seed.comps => truncateTorusHk (Nat.zero_le K) (Z (ι.symm w) s)) ≤ E := by
  unfold weightedNorm massNormSq
  -- the seed sum is the retained order-zero sum at `s`
  have hsum : (∑ w : CompIn seed.comps, (rootM w.1.root / 1 ^ 2)⁻¹ *
        factorialNormSq 1 (truncateTorusHk (Nat.zero_le K) (Z (ι.symm w) s)).val) =
      ∑ v : CompIn Gt.comps, (Gt.mass lawT v)⁻¹ *
        factorialNormSq ρ (truncateTorusHk (Nat.zero_le K) (Z v s)).val := by
    rw [← Equiv.sum_comp ι]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hroot v, one_pow, div_one]
    rw [factorialNormSq_zero_radius 1 ρ]
    generalize hv' : ι.symm (ι v) = v'
    rw [Equiv.symm_apply_apply] at hv'
    subst hv'
    rfl
  rw [hsum]
  have hle : (∑ v : CompIn Gt.comps, (Gt.mass lawT v)⁻¹ *
        factorialNormSq ρ (truncateTorusHk (Nat.zero_le K) (Z v s)).val) ≤
      ∑ v : CompIn Gt.comps, (Gt.mass lawT v)⁻¹ * factorialNormSq ρ (Z v s).val :=
    Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
      (CycleComparison.Error.factorialNormSq_truncateTorusHk_le (Nat.zero_le K) ρ (Z v s)) (inv_nonneg.2 (hπ v).le)
  have hsq : ENNReal.ofReal (∑ v : CompIn Gt.comps, (Gt.mass lawT v)⁻¹ *
      factorialNormSq ρ (Z v s).val) ≤ ENNReal.ofReal (E ^ 2) := by
    refine (slice_le_strongEnergy_sq (B := ν) hπ Z Zw hs).trans ?_
    calc strongEnergy ρ ν (Gt.mass lawT) tp tf Z Zw ^ (2 : ℝ)
        ≤ ENNReal.ofReal E ^ (2 : ℝ) := ENNReal.rpow_le_rpow hE (by norm_num)
      _ = ENNReal.ofReal (E ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num), Real.rpow_two]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg E)).1 hsq
  calc Real.sqrt _ ≤ Real.sqrt (E ^ 2) := Real.sqrt_le_sqrt (hle.trans hreal)
    _ = E := Real.sqrt_sq hE0

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The first coarse family at one level** (`CoarseFamilyStatement`).

The proof at a fixed level `M`:
- The trace `Z₀` is `g` on the old components and `0` on the new ones. Its weighted norm is at
  most that of `g` (`IsTerminalLaw` keeps root masses, and old components have no births).
- The retained certificate gives the kernel operator (`retainedOperator`).
- The drift data of `streamVel (Φ (M-1))` at the coarse radius `√(B h)` (constants `a, B₀, lam`)
  pass to `ρ = c_r √(B h) ≤ √(B h)`.
- Existence of the regular solution is `native_reg_solution_exists`; its strong energy is at most
  `√2 |g|_ρ` (`native_reg_solution_strongEnergy_of_initial_norm`).
- The seed datum `Z(s_n)` has norm at most the strong energy.

The constants are `C ≥ (1 + √2) max(C_P, 0)` and `C_entry = √2 max(C_P, 0)`.

Degenerate cases:
- `g = 0`: `Z₀ = 0`, and the bounds are `0 ≤ 0`.
- An empty retained family: every clause is about an empty product.
- `t_p` at the deadline: the window `[t_p, a+T₀]` still contains `s_n = t_p + h`.
- `C_P < 0`: then `g = 0` or `f = 0`; the constants use `max(C_P, 0)`. -/

section
/-- The drift data of the coarse system at level `M`: the stream `Φ (M-1)` at the coarse radius
`√(B h)` with constants `a, B₀, lam` (`coarse_drift_small`). -/
def CoarseDriftAt (D : OCData) (M : ℕ) (B₀ : ℝ) : Prop :=
  ∃ aD lam : ℝ, 0 ≤ aD ∧ 0 < lam ∧
    B₀ * Real.sqrt (D.κ (M - 1) * D.termH M) / lam ≤ 1 / 2 ∧
    aD * B₀ * Real.sqrt (D.κ (M - 1) * D.termH M) ^ 2 ≤ D.κ (M - 1) / 8 ∧
    ∀ l : ℕ, 1 ≤ l → ∀ (t : ℝ) (x : Vec 2),
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (M - 1)) t)) l x‖ ≤
        aD * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Every kernel of a family with paired kernels of positive widths has positive width. -/
theorem kernelOf_width_pos (Pt : ProvParams) (r₁ r₂ : ℝ) (n₁ n₂ : ℕ+) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (G : GenStage D ScalarH Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    0 < (G.kernelOf Pt (fun _ => isoPairedKernel r₁ n₁) (fun _ => isoPairedKernel r₂ n₂) v u
      γ).width := by
  unfold GenStage.kernelOf
  split <;> simpa only [isoPairedKernel]

/-- The old components keep their masses under the terminal law. -/
theorem terminal_old_mass {Gw Gt : GenStage D ScalarH Dm b j₀} {lawW lawT : BirthLaw}
    (hroots : ∀ v : CompIn Gw.comps, v.1.births = []) (hroot : lawT.rootMass = lawW.rootMass)
    (v' : CompIn Gt.comps) (hv : v'.1 ∈ Gw.comps) :
    Gt.mass lawT v' = Gw.mass lawW ⟨v'.1, hv⟩ := by
  show compMass D.q D.Λ lawT v'.1 = compMass D.q D.Λ lawW v'.1
  unfold compMass
  rw [hroots ⟨v'.1, hv⟩, hroot]
  simp only [List.map_nil, List.prod_nil]

/-- **The coarse solution and its energy.** From the retained certificate, the drift data and a
trace datum `g`: a regular solution from the trace, with strong energy at most `√2 |g|_ρ`. -/
theorem coarse_solution (Pt : ProvParams) (seedKt freshKt : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (cker : ℕ → ℝ) (M K : ℕ) (cr tp tf : ℝ) (lawW lawT : BirthLaw)
    (Gw Gt : GenStage D ScalarH Dm b j₀)
    (hret : TerminalRetainedClauses lawT Pt seedKt freshKt φ₀ hφ₀ cker M K cr tp tf Gt)
    (htime : tp ≤ tf) (hρ : 0 < D.termRho cr M) (hν : 0 < D.κ (M - 1)) (hDm : 2 ≤ Dm)
    (hπT : ∀ v, 0 < Gt.mass lawT v)
    (hwidth : ∀ v u (γ : Gt.fam.Γ v u), 0 < (Gt.kernelOf Pt seedKt freshKt v u γ).width)
    (hπW : ∀ v, 0 ≤ Gw.mass lawW v)
    (hmass : ∀ (v' : CompIn Gt.comps) (hv : v'.1 ∈ Gw.comps),
      Gt.mass lawT v' = Gw.mass lawW ⟨v'.1, hv⟩)
    (B₀ : ℝ) (hB₀ : 1 ≤ B₀) (hdrift : CoarseDriftAt D M B₀) (hcr1 : cr ≤ 1)
    (g : ∀ v : CompIn Gw.comps, TorusHk K (ScalarH v.1.root)) :
    ∃ (U : ∀ v : CompIn Gt.comps, ℝ → TorusHk K (ScalarH v.1.root))
      (W : ∀ v : CompIn Gt.comps, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
      (Y : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (K + Dm - 1) (ScalarH u.1.root)),
      Gt.IsRegSolution Pt seedKt freshKt φ₀ hφ₀ (D.termB M) (streamVel (D.Φ (M - 1))) K tp tf
        (terminalTrace Gw Gt g) (fun _ _ => 0) (fun _ _ => 0) U W Y ∧
      strongEnergy (D.termRho cr M) (D.termB M) (Gt.mass lawT) tp tf U W ≤
        ENNReal.ofReal (Real.sqrt 2 * weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g) := by
  obtain ⟨aD, lam, haD, hlam, hsm, hst, hjets⟩ := hdrift
  have hB₀0 : 0 ≤ B₀ := le_trans zero_le_one hB₀
  have hsqrt : D.termRho cr M ≤ Real.sqrt (D.κ (M - 1) * D.termH M) := by
    have hcr0 : 0 ≤ cr := by
      by_contra h
      have : D.termRho cr M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp h))
        (Real.sqrt_nonneg _)
      linarith only [this, hρ]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hcr1
  have hsmall : B₀ * D.termRho cr M / lam ≤ 1 / 2 :=
    le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hB₀0) hlam.le) hsm
  have hstrain : aD * B₀ * D.termRho cr M ^ 2 ≤ D.κ (M - 1) / 8 :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hsqrt 2)
      (mul_nonneg haD hB₀0)) hst
  have hjets' : ∀ t ∈ Set.Icc tp tf, ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (M - 1)) t)) l x‖ ≤
        aD * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l) :=
    fun t _ l hl _ x => hjets l hl t x
  obtain ⟨U, W, Y, hsol⟩ := Construction.Preservation.FullLift.native_reg_solution_exists Pt
    seedKt freshKt φ₀ hφ₀ Gt
    (retainedOperator lawT Pt seedKt freshKt φ₀ hφ₀ cker M K cr tp tf Gt hret htime hρ hν hDm hπT
      hwidth) rfl rfl rfl (D.hΦ (M - 1)) aD B₀ lam haD hB₀ hlam hsmall hstrain hjets'
    (terminalTrace Gw Gt g)
  have hE := Construction.Preservation.FullLift.native_reg_solution_strongEnergy_of_initial_norm Pt
    seedKt freshKt φ₀ hφ₀ Gt lawT
    (retainedOperator lawT Pt seedKt freshKt φ₀ hφ₀ cker M K cr tp tf Gt hret htime hρ hν hDm hπT
      hwidth) rfl rfl rfl (D.hΦ (M - 1)) aD B₀ lam haD hB₀ hlam hsmall hstrain hjets'
    (terminalTrace Gw Gt g) U W Y hsol (fun _ => 1) (by funext v; simp [retainedOperator]) _
    (terminalTrace_weightedNorm_le Gw Gt lawW lawT _ g hmass hπW)
  have hπfun : (fun v => Gt.mass lawT v / (fun _ => (1 : ℝ)) v ^ 2) = Gt.mass lawT := by
    funext v
    simp
  rw [hπfun] at hE
  exact ⟨U, W, Y, hsol, hE⟩
end

/-! **The first coarse family**: `coarseFamily : CoarseFamilyStatement`.

At each level, `coarse_atM` combines the trace, the coarse solution and its energy
(`coarse_solution`), and the seed datum (`seedDatum_weightedNorm_le`). The drift data come from
`coarse_drift_small` at `m = M` (`2 ≤ M`). The constants are `C₀ = (1 + √2) max(C_P, 0)` and
`C_entry = √2 max(C_P, 0)`; the threshold is `M₀ = 2`.

Degenerate cases:
- `g = 0`: the solution from the zero trace; the bounds are `0 ≤ 0`.
- An empty retained family: every clause is about an empty product.
- `t_p` at the deadline: the window still contains `s_n = t_p + h`.
- `K_out = 0`: `K̂ = max (2k₀+2) (N_T+2p_T+k₀+2)`, unchanged argument.
- One component without identities: the scalar heat equation with drift. -/

/-- **The first coarse family at one level**, from the drift data at that level. -/
theorem coarse_atM {X : TermConstruction} (A : TermArgs X) (hΛ : 128 ≤ A.Λ) (Kout : ℕ)
    (nW : ℕ+) (cr cP CP cH : ℝ) (cker : ℕ → ℝ) (hcr : 0 < cr) (hcr1 : cr ≤ 1) (C Centry : ℝ)
    (hC : (1 + Real.sqrt 2) * max CP 0 ≤ C) (hCe : Real.sqrt 2 * max CP 0 ≤ Centry)
    (B₀ : ℝ) (hB₀ : 1 ≤ B₀) (M : ℕ)
    (hdrift : ∀ D : OCData, IsTermData X A.Λ M D → CoarseDriftAt D M B₀) :
    CoarseAtM A Kout nW cr cP CP cH cker C Centry M := by
  intro j₀ D hD sXT sZT a aM tp Cw lawW lawT Gw Gt' seed rootM rootR seedKc ι _ hroots _ hdead
    hlaw _ henc hret f g hg
  have hdr := hdrift D hD
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := hD
  have hq1 : 1 < D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ hΛ
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ
  have hεM : 0 < D.eps M := (Scales.epsilon_basic hq1 hΛD).1
  have hεM1 : 0 < D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD).1
  have hh : 0 < D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hν : 0 < D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hρ : 0 < D.termRho cr M := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hh))
  have hτ : 0 ≤ ocTau X.α X.q A.Λ (M - 1) := (Construction.Stream.ocTau_pos hΛ1).le
  have hτ'' : 0 ≤ ocTauPP X.α X.q A.Λ (M - 1) := (Construction.Stream.ocTauPP_pos hΛ1).le
  have hsnT : tp + D.termH M ≤ a + A.T₀ := by linarith only [hdead, hτ, hτ'']
  have htime : tp ≤ a + A.T₀ := by linarith only [hsnT, hh]
  have hsn : tp + D.termH M ∈ Set.Icc tp (a + A.T₀) := ⟨by linarith only [hh], hsnT⟩
  have hπT : ∀ v, 0 < (Gt'.retained M 1 A.RT).mass lawT v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD lawT v.1
  have hπW : ∀ v, 0 ≤ Gw.mass lawW v := fun v =>
    (Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD lawW v.1).le
  have hwidth := kernelOf_width_pos (A.Pt D Cw cr M) (D.termRW A.σw M) (D.termRNew cr A.tT M) nW
    A.nT (Real.rpow_pos_of_pos hεM _) (mul_pos hρ (Real.rpow_pos_of_pos hεM1 _))
    (Gt'.retained M 1 A.RT)
  obtain ⟨U, W, Y, hsol, hE⟩ := coarse_solution (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
    A.φ₀ A.hφ₀ cker M (A.Khat Kout) cr tp (a + A.T₀) lawW lawT Gw (Gt'.retained M 1 A.RT) hret
    htime hρ hν (le_max_left _ _) hπT hwidth hπW (terminal_old_mass hroots hlaw.1) B₀ hB₀ hdr hcr1
    g
  have hA0 : 0 ≤ weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g := Real.sqrt_nonneg _
  have hf0 : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  have hAf : weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g ≤
      max CP 0 * Real.sqrt (l2NormSq f) :=
    hg.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hf0)
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨U, terminalTrace Gw _ g, W, Y, terminalTrace_isTrace Gw _ g, hsol, ?_, ?_⟩
  · calc ENNReal.ofReal (weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g) +
          strongEnergy (D.termRho cr M) (D.termB M) ((Gt'.retained M 1 A.RT).mass lawT) tp
            (a + A.T₀) U W
        ≤ ENNReal.ofReal (weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g) +
          ENNReal.ofReal (Real.sqrt 2 *
            weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g) := add_le_add le_rfl hE
      _ = ENNReal.ofReal ((1 + Real.sqrt 2) *
            weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g) := by
          rw [← ENNReal.ofReal_add hA0 (mul_nonneg hs2 hA0)]
          ring_nf
      _ ≤ ENNReal.ofReal (C * Real.sqrt (l2NormSq f)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc (1 + Real.sqrt 2) * weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g
              ≤ (1 + Real.sqrt 2) * (max CP 0 * Real.sqrt (l2NormSq f)) :=
                mul_le_mul_of_nonneg_left hAf (by positivity)
            _ = ((1 + Real.sqrt 2) * max CP 0) * Real.sqrt (l2NormSq f) := by ring
            _ ≤ C * Real.sqrt (l2NormSq f) := mul_le_mul_of_nonneg_right hC hf0
  · refine ⟨fun w => truncateTorusHk (Nat.zero_le _) (U (ι.symm w) (tp + D.termH M)),
      fun v => ?_, ?_⟩
    · show truncateTorusHk (Nat.zero_le _) (U (ι.symm (ι v)) (tp + D.termH M)) =
        truncateTorusHk (Nat.zero_le _) (U v (tp + D.termH M))
      generalize hv' : ι.symm (ι v) = v'
      rw [Equiv.symm_apply_apply] at hv'
      subst hv'
      rfl
    · refine (seedDatum_weightedNorm_le (Gt'.retained M 1 A.RT) seed ι rootM lawT
        (fun v => (henc.2.2.1 v).1) hπT _ _ tp (a + A.T₀) _ _ hsn (mul_nonneg hs2 hA0) U W hE).trans
        ?_
      calc Real.sqrt 2 * weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g
          ≤ Real.sqrt 2 * (max CP 0 * Real.sqrt (l2NormSq f)) :=
            mul_le_mul_of_nonneg_left hAf hs2
        _ = (Real.sqrt 2 * max CP 0) * Real.sqrt (l2NormSq f) := by ring
        _ ≤ Centry * Real.sqrt (l2NormSq f) := mul_le_mul_of_nonneg_right hCe hf0

/-- **The first coarse family.** -/
theorem coarseFamily : CoarseFamilyStatement := by
  intro X
  obtain ⟨ΛD, B₀, _, hΛD, hB₀, _, hdr⟩ := CycleComparison.Assembly.coarse_drift_small X.α X.s
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨ΛD, hΛD, fun A hΛ _ Kout nW cr hcr hcr1 cP CP cH cker _ _ => ?_⟩
  have hdrift : ∀ M : ℕ, 2 ≤ M → ∀ D : OCData, IsTermData X A.Λ M D → CoarseDriftAt D M B₀ := by
    intro M hM D hD
    obtain ⟨hDα, hDq, hDΛ, -, hstream, hband, -⟩ := hD
    obtain ⟨aD, lam, haD, hlam, hsm, hst, -, hjets, -⟩ :=
      hdr A.Λ hΛ D.Φ hstream M D.κ hband M hM le_rfl (D.κ M) (D.κ (M - 1)) rfl rfl
    have hH : D.termH M = ocTauPP X.α X.q A.Λ M := by
      show ocTauPP D.α D.q D.Λ M = _
      rw [hDα, hDq, hDΛ]
    refine ⟨aD, lam, haD, hlam, ?_, ?_, hjets⟩
    · rw [hH]
      exact hsm
    · rw [hH]
      exact hst
  exact ⟨(1 + Real.sqrt 2) * max CP 0, Real.sqrt 2 * max CP 0, fun C hC => ⟨2, fun M hM =>
    coarse_atM A (hΛD.trans hΛ) Kout nW cr cP CP cH cker hcr hcr1 C _ hC le_rfl B₀ hB₀ M
      (hdrift M hM)⟩⟩

end AVRegularity.EntryTerminal.Ingredients
end
