-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.DirRecord

section
section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the structural norm of one node.** Single-node equations of `genNorm` for the
nodes of the lift layer, at a node that is not a certified leaf: the fast derivative costs `2π`
and one fast weight, the slow derivative at fixed internal phase its Cauchy factor and one reserve
step, the cell mean and the family-as-cell node restart the fast weight at the inner rate,
restriction keeps the norm, a constant has its absolute value, and the geometric and drift letters
have the weighted sums of their profiles. -/

open AVRegularity.Providers.Majorant

variable (D : OCData) (κc : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

theorem genNorm_dInternal_eq {i : ℕ} {p : ℤ} {x : Gen .cell i p}
    (hl : leaf (Gen.dInternal x) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.dInternal x) a mres L t =
      ENNReal.ofReal (2 * Real.pi) * genNorm D κc Δ a₀ leaf x a mres (L + 1) t := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_dSlowCell_eq {i : ℕ} {p : ℤ} (j : Fin 2) {x : Gen .cell i p}
    (hl : leaf (Gen.dSlowCell j x) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.dSlowCell j x) a mres L t =
      if mres + Δ ≤ 2 then κc.Cslow / ENNReal.ofReal (D.eps (i - 1) * Δ) *
        genNorm D κc Δ a₀ leaf x a (mres + Δ) L t else ⊤ := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_famCell_eq {i : ℕ} {p : ℤ} {c : Gen .fam i p}
    (hl : leaf (Gen.famCell c) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.famCell c) a mres L t =
      genNorm D κc Δ a₀ leaf c a₀ mres 0 t := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_mean_eq {i : ℕ} {p : ℤ} {w : Gen .cell i p}
    (hl : leaf (Gen.mean w) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.mean w) a mres L t =
      genNorm D κc Δ a₀ leaf w a₀ mres 0 t := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_restrict_eq {i : ℕ} {p : ℤ} {x : Gen .ctx i p}
    (hl : leaf (Gen.restrict x) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.restrict x) a mres L t =
      genNorm D κc Δ a₀ leaf x a mres L t := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_const_eq {s : GenSort} {i : ℕ} {p : ℤ} (c : ℝ)
    (hl : leaf (Gen.time (s := s) (i := i) (p := p) (.const c)) = none) (a mres : ℝ) (L : ℕ)
    (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.time (s := s) (i := i) (p := p) (.const c)) a mres L t =
      ENNReal.ofReal |c| := by
  simp only [genNorm, hl, Option.elim, TimeLetter.eval]

theorem genNorm_geo_eq {i : ℕ} {p : ℤ} (fr : GenFrame) (Lt : GeoLetter)
    (hl : leaf (Gen.geo (i := i) (p := p) fr Lt) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.geo (i := i) (p := p) fr Lt) a mres L t =
      wsum a L (κc.geo fr Lt) := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_drift_eq {i : ℕ} {p : ℤ} (c : Fin 2)
    (hl : leaf (Gen.drift (i := i) (p := p) c) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.drift (i := i) (p := p) c) a mres L t =
      wsum a L (κc.drift c) := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_transPrim_succ_eq {i : ℕ} {p : ℤ} {w : Gen .cell i p}
    (hl : leaf (Gen.transPrim w) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.transPrim w) a mres (L + 1) t =
      ENNReal.ofReal Real.pi⁻¹ * genNorm D κc Δ a₀ leaf w a mres L t := by
  simp only [genNorm, hl, Option.elim, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

theorem genNorm_cellInv_eq {i : ℕ} {p : ℤ} (F : Fin 2 → Gen .cell i p) (t₀ : ℝ)
    (ι : Gen .cell i p) (hl : leaf (Gen.cellInv F t₀ ι) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.cellInv F t₀ ι) a mres L t =
      genNorm D κc Δ a₀ leaf ι a mres L t₀ +
        ENNReal.ofReal (4 / 3) * cGain *
          ⨆ s ∈ Set.Icc t₀ t, genNorm D κc Δ a₀ leaf (F (transverseIndex p)) a mres (L + 1) s := by
  simp only [genNorm, hl, Option.elim]

end AVRegularity.Providers.CascadeInvariants
end
end

section
/-! **Ledger: graded uniform representations.** The quantitative form of the uniform
representations `UEnv.IsURep`. A *profile* `(r, w, C)` of a bound function
`f : reserve → fast weight → [0,∞]` says that `f mres L ≤ C` whenever `r` reserve steps and `w`
fast weights are available: `mres + r Δ ≤ μ₀` and `L + w ≤ L₀` (`GCtx.Prof`).

`V.IsURepP X φ r w C`: `φ` is uniformly represented by a cell expression without uncertified
solved node whose structural norm at the inner rate has the profile `(r, w, C)` at every time of
`X.T`. The closure rules: sums add and products multiply the sizes; a fast
derivative costs `2π` and one fast weight; a slow derivative at fixed internal phase costs
`|ρ| C_slow/(ε_{i-1} Δ) ≤ S` and one reserve step; the cell mean restarts the fast weight; the
metric and the normalized drift are letters with bounded profiles. The sizes are nonnegative reals
built from the constants `S, K_g, K_d` of the context, hence finite and independent of the data. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity.Providers.CascadeInvariants

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- The context of the graded calculus: carrier constants, reserve step, inner rate, leaf map,
reserve and fast-weight budgets, and the times. -/
structure GCtx where
  /-- The carrier constants. -/
  κ : MajConsts
  /-- The reserve step. -/
  Δ : ℝ
  /-- The inner rate. -/
  a₀ : ℝ
  /-- The certified leaves. -/
  leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)
  /-- The reserve budget. -/
  μ₀ : ℝ
  /-- The fast-weight budget. -/
  L₀ : ℕ
  /-- The times. -/
  T : Set ℝ
  /-- The bound of the cost of one slow derivative. -/
  S : ℝ≥0
  /-- The bound of the geometric letter profiles on the fast weights up to `L₀`. -/
  Kg : ℝ≥0
  /-- The bound of the drift letter profiles on the fast weights up to `L₀`. -/
  Kd : ℝ≥0

namespace GCtx

/-- The standing hypotheses of the graded calculus: a nonnegative reserve step, a budget inside
the outer reserve, and leaves only among the context expressions other than geometric letters. -/
structure Ok (X : GCtx) : Prop where
  /-- The reserve step is nonnegative. -/
  hΔ : 0 ≤ X.Δ
  /-- The reserve budget lies inside the outer reserve. -/
  hμ : X.μ₀ ≤ 2
  /-- Cell and family expressions are never leaves. -/
  hleaf : ∀ (s : GenSort) (i : ℕ) (p : ℤ) (e : Gen s i p), s ≠ .ctx → X.leaf e = none
  /-- The own-frame geometric letters are never leaves. -/
  hgeo : ∀ (i : ℕ) (p : ℤ) (Lt : GeoLetter),
    X.leaf (Gen.geo (i := i) (p := p) .own Lt) = none
  /-- The geometric letters are bounded by `Kg`. -/
  hKg : ∀ L, L ≤ X.L₀ → geoW X.κ X.a₀ L ≤ X.Kg
  /-- The drift letters are bounded by `Kd`. -/
  hKd : ∀ (k : Fin 2) (L : ℕ), L ≤ X.L₀ → wsum X.a₀ L (X.κ.drift k) ≤ X.Kd
  /-- All times are allowed (the history suprema of the inverses). -/
  hT : ∀ t, t ∈ X.T

/-- The profile `(r, w, C)` of a bound function. -/
def Prof (X : GCtx) (f : ℝ → ℕ → ℝ≥0∞) (r w : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ mres L, mres + r * X.Δ ≤ X.μ₀ → L + w ≤ X.L₀ → f mres L ≤ C

theorem Prof.mono {X : GCtx} (hX : X.Ok) {f : ℝ → ℕ → ℝ≥0∞} {r w r' w' : ℕ} {C C' : ℝ≥0∞}
    (h : X.Prof f r w C) (hr : r ≤ r') (hw : w ≤ w') (hC : C ≤ C') : X.Prof f r' w' C' := by
  intro mres L hm hL
  have hrr : (r : ℝ) * X.Δ ≤ r' * X.Δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hX.hΔ
  exact (h mres L (by linarith) (by omega)).trans hC

theorem cell_ne_ctx : GenSort.cell ≠ GenSort.ctx := by intro h; cases h

theorem fam_ne_ctx : GenSort.fam ≠ GenSort.ctx := by intro h; cases h

end GCtx

end AVRegularity.Providers.CascadeInvariants

namespace AVRegularity.Providers.GenSem.UEnv

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant
open scoped NNReal

variable {Λ : Type} {V : UEnv Λ} {X : GCtx}

/-- **Graded uniform representation**: `φ` is uniformly represented by a cell expression without
uncertified solved node, of profile `(r, w, C)` at every time of `X.T`. -/
def IsURepP (V : UEnv Λ) (X : GCtx) (φ : Λ → Vec 2 → Vec 2 → ℝ) (r w : ℕ) (C : ℝ≥0) : Prop :=
  ∃ e : Gen .cell V.E.i V.E.p, V.URep φ e ∧ Gen.SolvedFree X.leaf e ∧
    ∀ t ∈ X.T, X.Prof (fun mres L => genNorm V.E.D X.κ X.Δ X.a₀ X.leaf e X.a₀ mres L t) r w C

theorem IsURepP.mono (hX : X.Ok) {φ : Λ → Vec 2 → Vec 2 → ℝ} {r w r' w' : ℕ} {C C' : ℝ≥0}
    (h : V.IsURepP X φ r w C) (hr : r ≤ r') (hw : w ≤ w') (hC : C ≤ C') :
    V.IsURepP X φ r' w' C' := by
  obtain ⟨e, he, hs, hn⟩ := h
  exact ⟨e, he, hs, fun t ht => (hn t ht).mono hX hr hw (ENNReal.coe_le_coe.mpr hC)⟩

theorem IsURepP.congr {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C : ℝ≥0}
    (h : V.IsURepP X φ r w C) (hφψ : ∀ l ∈ V.W, ∀ X ∈ V.U l, ∀ z, ψ l X z = φ l X z) :
    V.IsURepP X ψ r w C := by
  obtain ⟨e, he, hs, hn⟩ := h
  exact ⟨e, he.congr hφψ, hs, hn⟩

theorem isURepP_const (hX : X.Ok) (V : UEnv Λ) (c : ℝ) :
    V.IsURepP X (fun _ _ _ => c) 0 0 (Real.toNNReal |c|) := by
  refine ⟨_, urep_const V c, trivial, fun t _ mres L _ _ => ?_⟩
  show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.time (.const c)) X.a₀ mres L t ≤ _
  rw [genNorm_const_eq _ _ _ _ _ c (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx)]
  exact le_rfl

theorem isURepP_zero (hX : X.Ok) (V : UEnv Λ) (r w : ℕ) :
    V.IsURepP X (fun _ _ _ => 0) r w 0 :=
  (isURepP_const hX V 0).mono hX (Nat.zero_le _) (Nat.zero_le _) (by simp)

theorem IsURepP.add (hX : X.Ok) {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C₁ C₂ : ℝ≥0}
    (ha : V.IsURepP X φ r w C₁) (hb : V.IsURepP X ψ r w C₂) :
    V.IsURepP X (fun l X z => φ l X z + ψ l X z) r w (C₁ + C₂) := by
  obtain ⟨a, ha, hsa, hna⟩ := ha
  obtain ⟨b, hb, hsb, hnb⟩ := hb
  refine ⟨Gen.add a b, ha.add hb, Or.inr ⟨hsa, hsb⟩, fun t ht mres L hm hL => ?_⟩
  show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.add a b) X.a₀ mres L t ≤ _
  rw [genNorm_add_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx), ENNReal.coe_add]
  exact add_le_add (hna t ht mres L hm hL) (hnb t ht mres L hm hL)

theorem IsURepP.mul (hX : X.Ok) {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C₁ C₂ : ℝ≥0}
    (ha : V.IsURepP X φ r w C₁) (hb : V.IsURepP X ψ r w C₂) :
    V.IsURepP X (fun l X z => φ l X z * ψ l X z) r w (C₁ * C₂) := by
  obtain ⟨a, ha, hsa, hna⟩ := ha
  obtain ⟨b, hb, hsb, hnb⟩ := hb
  refine ⟨Gen.mul a b, ha.mul hb, Or.inr ⟨hsa, hsb⟩, fun t ht mres L hm hL => ?_⟩
  show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.mul a b) X.a₀ mres L t ≤ _
  rw [genNorm_mul_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx), ENNReal.coe_mul]
  exact mul_le_mul' (hna t ht mres L hm hL) (hnb t ht mres L hm hL)

theorem IsURepP.smul (hX : X.Ok) {φ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C : ℝ≥0}
    (h : V.IsURepP X φ r w C) (c : ℝ) :
    V.IsURepP X (fun l X z => c * φ l X z) r w (Real.toNNReal |c| * C) :=
  ((isURepP_const hX V c).mono hX (Nat.zero_le _) (Nat.zero_le _) le_rfl).mul hX h

theorem IsURepP.neg (hX : X.Ok) {φ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C : ℝ≥0}
    (h : V.IsURepP X φ r w C) : V.IsURepP X (fun l X z => -φ l X z) r w C :=
  ((h.smul hX (-1)).mono hX le_rfl le_rfl (by simp)).congr fun _ _ _ _ _ => by ring

theorem IsURepP.sub (hX : X.Ok) {φ ψ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C₁ C₂ : ℝ≥0}
    (ha : V.IsURepP X φ r w C₁) (hb : V.IsURepP X ψ r w C₂) :
    V.IsURepP X (fun l X z => φ l X z - ψ l X z) r w (C₁ + C₂) :=
  (ha.add hX (hb.neg hX)).congr fun _ _ _ _ _ => by ring

/-- Finite sums of graded representations: the sizes add. -/
theorem IsURepP.sum (hX : X.Ok) {ι : Type*} (s : Finset ι) {φ : ι → Λ → Vec 2 → Vec 2 → ℝ}
    {r w : ℕ} {C : ι → ℝ≥0} (h : ∀ k ∈ s, V.IsURepP X (φ k) r w (C k)) :
    V.IsURepP X (fun l X z => ∑ k ∈ s, φ k l X z) r w (∑ k ∈ s, C k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isURepP_zero hX V r w
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add hX
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    rw [Finset.sum_insert ha]
    exact h1.congr fun l _ X _ z => by simp [Finset.sum_insert ha]

/-- A finite sum of graded representations with a common size. -/
theorem IsURepP.sum_le (hX : X.Ok) {ι : Type*} (s : Finset ι) {φ : ι → Λ → Vec 2 → Vec 2 → ℝ}
    {r w : ℕ} {C : ℝ≥0} (h : ∀ k ∈ s, V.IsURepP X (φ k) r w C) :
    V.IsURepP X (fun l X z => ∑ k ∈ s, φ k l X z) r w (s.card * C) := by
  have := IsURepP.sum hX s h
  rwa [Finset.sum_const, nsmul_eq_mul] at this

/-! ### Letters -/

/-- The metric entries: a geometric letter with a bounded profile. -/
theorem isURepP_metric (hX : X.Ok) (V : UEnv Λ) (a b : Fin 2) :
    V.IsURepP X
      (fun l Y _ => ((V.base l).recenter V.E.D (V.E.ρ • Y)).famMetric V.E.D (V.time l) a b) 0 0
      X.Kg := by
  refine ⟨_, urep_metric V a b, Or.inr trivial, fun t _ mres L _ hL => ?_⟩
  show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.restrict (Gen.geo .own (.metric a b))) X.a₀ mres L
    t ≤ _
  rw [genNorm_restrict_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx)]
  exact (genNorm_geo_le _ _ _ _ _ _ _ (hX.hgeo _ _ _) _ _ _ _).trans (hX.hKg L (by omega))

/-- The normalized pulse drift `√(κ_i/κ_{i-1}) · 𝐛` at the lift time: the drift letter. -/
theorem isURepP_drift (hX : X.Ok) (V : UEnv Λ) (lt : Λ → ℝ)
    (hc : ∀ l, V.time l = V.E.D.cellScaleSq V.E.i * lt l) (hc0 : V.E.D.cellScaleSq V.E.i ≠ 0)
    (k : Fin 2) :
    V.IsURepP X (fun l _ z => Real.sqrt (V.E.D.kap V.E.i / V.E.D.kap (V.E.i - 1)) *
      ocPulseCellDrift V.E.D.α V.E.D.q V.E.D.Λ V.E.D.ζ V.E.i (V.E.D.kap V.E.i) V.E.p (lt l) z k)
      0 0 X.Kd := by
  have h1 : V.URep (fun l _ z => Real.sqrt (V.E.D.kap V.E.i / V.E.D.kap (V.E.i - 1)) *
      ocPulseCellDrift V.E.D.α V.E.D.q V.E.D.Λ V.E.D.ζ V.E.i (V.E.D.kap V.E.i) V.E.p
        (V.time l / V.E.D.cellScaleSq V.E.i) z k) (Gen.drift (i := V.E.i) (p := V.E.p) k) :=
    ⟨.drift k, .drift k, driftSem V.E.D V.E.i V.E.p k, .drift k, fun _ _ _ _ _ => rfl,
      fun l _ Y _ z s => driftSem_phase V.E.D V.E.i V.E.p k (V.time l)
        ((V.base l).recenter V.E.D (V.E.ρ • Y)) z s⟩
  refine ⟨_, h1.congr fun l _ Y _ z => ?_, trivial, fun t _ mres L _ hL => ?_⟩
  · have hτ : V.time l / V.E.D.cellScaleSq V.E.i = lt l := by
      rw [hc l]; field_simp
    simp only [hτ]
  · show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.drift k) X.a₀ mres L t ≤ _
    rw [genNorm_drift_eq _ _ _ _ _ k (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx)]
    exact hX.hKd k L (by omega)

/-! ### Derivatives and the mean -/

/-- A fast derivative costs `2π` and one fast weight. -/
theorem IsURepP.fastPartial (hX : X.Ok) {φ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C : ℝ≥0}
    (h : V.IsURepP X φ r w C) (j : Fin 2) :
    V.IsURepP X (fun l => AVRegularity.fastPartial j (φ l)) r (w + 1)
      (Real.toNNReal (2 * Real.pi) * C) := by
  rcases fin2_cases V.E.p j with hj | hj
  · subst hj
    obtain ⟨e, he, hs, hn⟩ := h
    refine ⟨Gen.dInternal e, he.dInternal, Or.inr hs, fun t ht mres L hm hL => ?_⟩
    show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.dInternal e) X.a₀ mres L t ≤ _
    rw [genNorm_dInternal_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx), ENNReal.coe_mul]
    exact mul_le_mul_right (hn t ht mres (L + 1) hm (by omega)) _
  · subst hj
    obtain ⟨e, he, -, -⟩ := h
    refine ⟨_, urep_fastPartial_of_invariant _ he.invariant, trivial,
      fun t _ mres L _ _ => ?_⟩
    show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.time (.const 0)) X.a₀ mres L t ≤ _
    rw [genNorm_const_eq _ _ _ _ _ 0 (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx)]
    simp

/-- The cost of one slow derivative at fixed internal phase: `|ρ| C_slow/(ε_{i-1} Δ)`. -/
def slowC (V : UEnv Λ) (X : GCtx) : ℝ≥0∞ :=
  ENNReal.ofReal |V.E.ρ| * (X.κ.Cslow / ENNReal.ofReal (V.E.D.eps (V.E.i - 1) * X.Δ))

/-- A slow derivative costs `|ρ| C_slow/(ε_{i-1} Δ)` and one reserve step. -/
theorem IsURepP.slowPartial (hX : X.Ok) (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0)
    (hU : ∀ l ∈ V.W, IsOpen (V.U l)) {φ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C : ℝ≥0}
    (hS : slowC V X ≤ X.S) (h : V.IsURepP X φ r w C)
    (hd : ∀ l ∈ V.W, ∀ Y ∈ V.U l, ∀ z, DifferentiableAt ℝ (fun Y' => φ l Y' z) Y) (j : Fin 2) :
    V.IsURepP X (fun l => AVRegularity.slowPartial j (φ l)) (r + 1) w (X.S * C) := by
  obtain ⟨e, he, hs, hn⟩ := h
  refine ⟨_, he.slowPartial hζ hρ hU hd j, Or.inr ⟨trivial, Or.inr hs⟩,
    fun t ht mres L hm hL => ?_⟩
  show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf
    (Gen.mul (Gen.time (.const V.E.ρ)) (Gen.dSlowCell j e)) X.a₀ mres L t ≤ _
  have hΔ := hX.hΔ
  have hμ := hX.hμ
  have hr0 : (0 : ℝ) ≤ (r : ℝ) * X.Δ := mul_nonneg (Nat.cast_nonneg r) hΔ
  have hm' : mres + X.Δ + r * X.Δ ≤ X.μ₀ := by
    push_cast at hm
    linarith
  have h2 : mres + X.Δ ≤ 2 := by linarith
  rw [genNorm_mul_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx),
    genNorm_const_eq _ _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx),
    genNorm_dSlowCell_eq _ _ _ _ _ j (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx)]
  simp only [h2, ↓reduceIte]
  rw [← mul_assoc, ENNReal.coe_mul]
  exact mul_le_mul' hS (hn t ht (mres + X.Δ) L hm' hL)

/-- The cell mean restarts the fast weight. -/
theorem IsURepP.meanCell (hX : X.Ok) {φ : Λ → Vec 2 → Vec 2 → ℝ} {r w : ℕ} {C : ℝ≥0}
    (h : V.IsURepP X φ r w C) (hw : w ≤ X.L₀) :
    V.IsURepP X (fun l Y _ => fieldCellMean (φ l Y)) r 0 C := by
  obtain ⟨e, he, hs, hn⟩ := h
  refine ⟨_, he.meanCell, Or.inr (Or.inr hs), fun t ht mres L hm _ => ?_⟩
  show genNorm V.E.D X.κ X.Δ X.a₀ X.leaf (Gen.famCell (Gen.mean e)) X.a₀ mres L t ≤ _
  rw [genNorm_famCell_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.cell_ne_ctx),
    genNorm_mean_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx)]
  exact hn t ht mres 0 hm (by omega)

end AVRegularity.Providers.GenSem.UEnv
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.GenSem.UEnv

/-! **Ledger: graded coefficient arrays.** `V.URepArrP X A n w C`: the time-indexed array `A`
has *degree* `n`: its entry of tested order `m` is graded-represented with the reserve cost
`n - m`, the fast weight `w` and the size `C` — "a coefficient of degree `n` and tested order `d`
has received at most `n - d` slow derivatives". The closure
rules mirror `UEnv.URepArr`: a slow array raises the degree by one at the cost `S + 1`, a fast array costs `2π` and one fast weight, the mean restarts the fast
weight, and a composition `compArr J C B` of degrees `J` and `K` has degree `J + K`: Leibniz
distributes the slow derivatives, and the reserve is the sum of degree minus tested order. -/

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

variable {Λ : Type} {V : UEnv Λ} {X : GCtx}

/-- **Graded array of degree `n`.** -/
def URepArrP (V : UEnv Λ) (X : GCtx) (A : Λ → CArr) (n w : ℕ) (C : ℝ≥0) : Prop :=
  ∀ m α, V.IsURepP X (fun l => A l m α) (n - m) w C

theorem URepArrP.mono (hX : X.Ok) {A : Λ → CArr} {n w n' w' : ℕ} {C C' : ℝ≥0}
    (h : V.URepArrP X A n w C) (hn : n ≤ n') (hw : w ≤ w') (hC : C ≤ C') :
    V.URepArrP X A n' w' C' := fun m α => (h m α).mono hX (by omega) hw hC

theorem URepArrP.congr {A B : Λ → CArr} {n w : ℕ} {C : ℝ≥0} (h : V.URepArrP X A n w C)
    (hAB : ∀ l ∈ V.W, B l = A l) : V.URepArrP X B n w C := fun m α =>
  (h m α).congr fun l hl Y _ z => by rw [hAB l hl]

theorem urepArrP_zero (hX : X.Ok) (V : UEnv Λ) (n w : ℕ) :
    V.URepArrP X (fun _ => 0) n w 0 := fun _ _ =>
  (isURepP_zero hX V _ w).congr fun _ _ _ _ _ => rfl

theorem URepArrP.add (hX : X.Ok) {A B : Λ → CArr} {n w : ℕ} {C₁ C₂ : ℝ≥0}
    (hA : V.URepArrP X A n w C₁) (hB : V.URepArrP X B n w C₂) :
    V.URepArrP X (fun l => A l + B l) n w (C₁ + C₂) := fun m α =>
  ((hA m α).add hX (hB m α)).congr fun _ _ _ _ _ => rfl

theorem URepArrP.smul (hX : X.Ok) {A : Λ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hA : V.URepArrP X A n w C) (c : ℝ) :
    V.URepArrP X (fun l => c • A l) n w (Real.toNNReal |c| * C) := fun m α =>
  ((hA m α).smul hX c).congr fun _ _ _ _ _ => rfl

theorem URepArrP.neg (hX : X.Ok) {A : Λ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hA : V.URepArrP X A n w C) : V.URepArrP X (fun l => -A l) n w C := fun m α =>
  ((hA m α).neg hX).congr fun _ _ _ _ _ => rfl

theorem URepArrP.sub (hX : X.Ok) {A B : Λ → CArr} {n w : ℕ} {C₁ C₂ : ℝ≥0}
    (hA : V.URepArrP X A n w C₁) (hB : V.URepArrP X B n w C₂) :
    V.URepArrP X (fun l => A l - B l) n w (C₁ + C₂) := fun m α =>
  ((hA m α).sub hX (hB m α)).congr fun _ _ _ _ _ => rfl

theorem URepArrP.sum (hX : X.Ok) {ι : Type*} (s : Finset ι) {A : ι → Λ → CArr} {n w : ℕ}
    {C : ι → ℝ≥0} (h : ∀ k ∈ s, V.URepArrP X (A k) n w (C k)) :
    V.URepArrP X (fun l => ∑ k ∈ s, A k l) n w (∑ k ∈ s, C k) := fun m α =>
  (IsURepP.sum hX s fun k hk => h k hk m α).congr fun l _ Y _ z => by
    simp [Finset.sum_apply]

theorem URepArrP.sum_le (hX : X.Ok) {ι : Type*} (s : Finset ι) {A : ι → Λ → CArr} {n w : ℕ}
    {C : ℝ≥0} (h : ∀ k ∈ s, V.URepArrP X (A k) n w C) :
    V.URepArrP X (fun l => ∑ k ∈ s, A k l) n w (s.card * C) := by
  have := URepArrP.sum hX s h
  rwa [Finset.sum_const, nsmul_eq_mul] at this

theorem isURepP_slowExtra (hX : X.Ok) (j : Fin 2) {A : Λ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hA : V.URepArrP X A n w C) (m : ℕ) (β : DerivativeWord2 m) :
    V.IsURepP X (fun l => slowExtra j (A l) m β) (n + 1 - m) w C := by
  cases m with
  | zero =>
    exact ((isURepP_zero hX V _ w).mono hX le_rfl le_rfl (by simp)).congr fun _ _ _ _ _ => rfl
  | succ m =>
    by_cases hc : β (Fin.last m) = j
    · exact ((hA m (Fin.init β)).mono hX (by omega) le_rfl le_rfl).congr fun l _ Y _ z => by
        simp [slowExtra, hc]
    · exact ((isURepP_zero hX V _ w).mono hX le_rfl le_rfl (by simp)).congr fun l _ Y _ z => by
        simp [slowExtra, hc]

/-- **Slow arrays raise the degree by one.** -/
theorem URepArrP.slowArr (hX : X.Ok) (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0)
    (hU : ∀ l ∈ V.W, IsOpen (V.U l)) {A : Λ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hS : slowC V X ≤ X.S) (hA : V.URepArrP X A n w C) (hsupp : ∀ l ∈ V.W, ArrSupp n (A l))
    (hs : ∀ l ∈ V.W, ArrSlowSmooth 1 (A l)) (j : Fin 2) :
    V.URepArrP X (fun l => slowArr j (A l)) (n + 1) w (X.S * C + C) := by
  intro m β
  have h2 := isURepP_slowExtra hX j hA m β
  by_cases hm : m ≤ n
  · have h1 := (hA m β).slowPartial hX hζ hρ hU hS (fun l hl Y _ z =>
      (hs l hl m β z).differentiable (by simp) Y) j
    exact ((h1.mono hX (by omega) le_rfl le_rfl).add hX h2).congr fun _ _ _ _ _ => rfl
  · have h1 : V.IsURepP X (fun l => AVRegularity.slowPartial j (A l m β)) (n + 1 - m) w
        (X.S * C) :=
      ((isURepP_zero hX V _ w).mono hX le_rfl le_rfl (by simp)).congr fun l hl Y _ z => by
        rw [hsupp l hl m (by omega) β]
        simp [slowPartial]
    exact (h1.add hX h2).congr fun _ _ _ _ _ => rfl

/-- Fast arrays cost `2π` and one fast weight. -/
theorem URepArrP.fastArr (hX : X.Ok) {A : Λ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hA : V.URepArrP X A n w C) (j : Fin 2) :
    V.URepArrP X (fun l => fastArr j (A l)) n (w + 1) (Real.toNNReal (2 * Real.pi) * C) :=
  fun m α => (hA m α).fastPartial hX j

theorem URepArrP.mulArr (hX : X.Ok) {g : Λ → Vec 2 → Vec 2 → ℝ} {wg : ℕ} {Cg : ℝ≥0}
    (hg : V.IsURepP X g 0 wg Cg) {A : Λ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hA : V.URepArrP X A n w C) :
    V.URepArrP X (fun l => mulArr (g l) (A l)) n (max wg w) (Cg * C) := fun m α =>
  ((hg.mono hX (Nat.zero_le _) (le_max_left _ _) le_rfl).mul hX
    ((hA m α).mono hX le_rfl (le_max_right _ _) le_rfl)).congr fun _ _ _ _ _ => rfl

/-- The mean restarts the fast weight. -/
theorem URepArrP.meanArr (hX : X.Ok) {A : Λ → CArr} {n w : ℕ} {C : ℝ≥0}
    (hA : V.URepArrP X A n w C) (hw : w ≤ X.L₀) :
    V.URepArrP X (fun l => meanArr (A l)) n 0 C := fun m α => (hA m α).meanCell hX hw

/-- **Iterated slow arrays.** -/
theorem URepArrP.iterSlow (hX : X.Ok) (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0)
    (hU : ∀ l ∈ V.W, IsOpen (V.U l)) (hS : slowC V X ≤ X.S) :
    ∀ {k : ℕ} (α : DerivativeWord2 k) {B : Λ → CArr} {n w : ℕ} {C : ℝ≥0},
      V.URepArrP X B n w C → (∀ l ∈ V.W, ArrSupp n (B l)) →
      (∀ l ∈ V.W, ArrSlowSmooth k (B l)) →
      V.URepArrP X (fun l => iterSlow k α (B l)) (n + k) w ((X.S + 1) ^ k * C)
  | 0, _, _, _, _, _, hB, _, _ => hB.mono hX le_rfl le_rfl (by simp)
  | k + 1, α, _, n, w, C, hB, hsupp, hs => by
    have h1 := hB.slowArr hX hζ hρ hU hS hsupp (fun l hl => (hs l hl).mono (by omega)) (α 0)
    have h2 := URepArrP.iterSlow hX hζ hρ hU hS (fun i => α i.succ) h1
      (fun l hl => arrSupp_slowArr _ (hsupp l hl))
      (fun l hl => arrSlowSmooth_slowArr (r := k) _ (hs l hl))
    refine h2.mono hX (by omega) le_rfl (le_of_eq ?_)
    ring

/-- **Composition `compArr J C B z0`** of an array `C` of degree `J` with a `z`-independent array
`B` of degree `K`: degree `J + K`. -/
theorem URepArrP.compArr (hX : X.Ok) (hζ : IsFastProfile V.E.D.ζ) (hρ : V.E.ρ ≠ 0)
    (hU : ∀ l ∈ V.W, IsOpen (V.U l)) (hS : slowC V X ≤ X.S) (J : ℕ) {Cm B : Λ → CArr}
    (z0 : Vec 2) {K wC wB : ℕ}
    {cC cB : ℝ≥0} (hC : V.URepArrP X Cm J wC cC) (hB : V.URepArrP X B K wB cB)
    (hsupp : ∀ l ∈ V.W, ArrSupp K (B l)) (hz : ∀ l ∈ V.W, RepEnv.ArrZConst (B l))
    (hs : ∀ l ∈ V.W, ArrSlowSmooth J (B l)) :
    V.URepArrP X (fun l => compArr J (Cm l) (B l) z0) (J + K) (max wC wB)
      (∑ m ∈ Finset.range (J + 1), ((Finset.univ : Finset (DerivativeWord2 m)).card : ℝ≥0) *
        (cC * ((X.S + 1) ^ m * cB))) := by
  intro m' β
  have h : V.IsURepP X (fun l Y z => ∑ m ∈ Finset.range (J + 1), ∑ α : DerivativeWord2 m,
      Cm l m α Y z * AVRegularity.Providers.GenSem.iterSlow m α (B l) m' β Y z) (J + K - m')
      (max wC wB)
      (∑ m ∈ Finset.range (J + 1), ((Finset.univ : Finset (DerivativeWord2 m)).card : ℝ≥0) *
        (cC * ((X.S + 1) ^ m * cB))) := by
    refine IsURepP.sum hX _ fun m hm => IsURepP.sum_le hX _ fun α _ => ?_
    have hmJ : m ≤ J := by simpa [Nat.lt_succ_iff] using hm
    by_cases hm' : m' ≤ K + m
    · have hI := URepArrP.iterSlow hX hζ hρ hU hS α hB hsupp
        (fun l hl => (hs l hl).mono hmJ) m' β
      exact ((hC m α).mono hX (by omega) (le_max_left _ _) le_rfl).mul hX
        (hI.mono hX (by omega) (le_max_right _ _) le_rfl)
    · refine ((isURepP_zero hX V _ _).mono hX le_rfl le_rfl (by simp)).congr
        fun l hl Y _ z => ?_
      have h0 := arrSupp_iterSlow α (hsupp l hl) m' (by omega) β
      rw [h0]
      simp
  exact h.congr fun l hl Y _ z => by
    simp only [GenSem.compArr, (RepEnv.arrZConst_iterSlow _ (hz l hl)) _ _ Y z z0]

end AVRegularity.Providers.GenSem.UEnv
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.GenSem.UEnv

/-! **Ledger: graded family representations.** `V.FamURepP X ψ r C`: `ψ` is represented
(`UEnv.FamURep`) by a family expression without uncertified solved node whose structural
norm at the inner rate and fast weight zero — the argument of the child evaluation `evalChild` —
is at most `C` whenever `r` reserve steps are available. Closed under sums, products and
constants; the cell mean at the offset `0` of a graded cell function is a graded family function
with the same reserve cost and size (the mean is the coefficient of the mode zero and keeps the
profile). -/

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

variable {Λ : Type} {V : UEnv Λ} {X : GCtx}

/-- **Graded family representation** with the reserve cost `r` and the size `C`. -/
def FamURepP (V : UEnv Λ) (X : GCtx) (ψ : Λ → ℝ) (r : ℕ) (C : ℝ≥0) : Prop :=
  ∃ c : Gen .fam V.E.i V.E.p, V.FamURep ψ c ∧ Gen.SolvedFree X.leaf c ∧
    ∀ t ∈ X.T, ∀ mres, mres + r * X.Δ ≤ X.μ₀ →
      genNorm V.E.D X.κ X.Δ X.a₀ X.leaf c X.a₀ mres 0 t ≤ C

theorem FamURepP.mono (hX : X.Ok) {ψ : Λ → ℝ} {r r' : ℕ} {C C' : ℝ≥0}
    (h : V.FamURepP X ψ r C) (hr : r ≤ r') (hC : C ≤ C') : V.FamURepP X ψ r' C' := by
  obtain ⟨c, hc, hs, hn⟩ := h
  refine ⟨c, hc, hs, fun t ht mres hm => (hn t ht mres ?_).trans (ENNReal.coe_le_coe.mpr hC)⟩
  have hrr : (r : ℝ) * X.Δ ≤ r' * X.Δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hX.hΔ
  linarith

theorem FamURepP.congr {ψ ψ' : Λ → ℝ} {r : ℕ} {C : ℝ≥0} (h : V.FamURepP X ψ r C)
    (hψ : ∀ l ∈ V.W, ψ' l = ψ l) : V.FamURepP X ψ' r C := by
  obtain ⟨c, hc, hs, hn⟩ := h
  exact ⟨c, hc.congr hψ, hs, hn⟩

theorem famURepP_const (hX : X.Ok) (V : UEnv Λ) (a : ℝ) :
    V.FamURepP X (fun _ => a) 0 (Real.toNNReal |a|) := by
  refine ⟨_, famURep_const V a, trivial, fun t _ mres _ => ?_⟩
  rw [genNorm_const_eq _ _ _ _ _ a (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx)]
  exact le_rfl

theorem FamURepP.add (hX : X.Ok) {ψ φ : Λ → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0}
    (ha : V.FamURepP X ψ r C₁) (hb : V.FamURepP X φ r C₂) :
    V.FamURepP X (fun l => ψ l + φ l) r (C₁ + C₂) := by
  obtain ⟨a, ha, hsa, hna⟩ := ha
  obtain ⟨b, hb, hsb, hnb⟩ := hb
  refine ⟨Gen.add a b, ha.add hb, Or.inr ⟨hsa, hsb⟩, fun t ht mres hm => ?_⟩
  rw [genNorm_add_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx), ENNReal.coe_add]
  exact add_le_add (hna t ht mres hm) (hnb t ht mres hm)

theorem FamURepP.mul (hX : X.Ok) {ψ φ : Λ → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0}
    (ha : V.FamURepP X ψ r C₁) (hb : V.FamURepP X φ r C₂) :
    V.FamURepP X (fun l => ψ l * φ l) r (C₁ * C₂) := by
  obtain ⟨a, ha, hsa, hna⟩ := ha
  obtain ⟨b, hb, hsb, hnb⟩ := hb
  refine ⟨Gen.mul a b, ha.mul hb, Or.inr ⟨hsa, hsb⟩, fun t ht mres hm => ?_⟩
  rw [genNorm_mul_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx), ENNReal.coe_mul]
  exact mul_le_mul' (hna t ht mres hm) (hnb t ht mres hm)

theorem FamURepP.smul (hX : X.Ok) {ψ : Λ → ℝ} {r : ℕ} {C : ℝ≥0} (h : V.FamURepP X ψ r C)
    (a : ℝ) : V.FamURepP X (fun l => a * ψ l) r (Real.toNNReal |a| * C) :=
  ((famURepP_const hX V a).mono hX (Nat.zero_le _) le_rfl).mul hX h

theorem FamURepP.sub (hX : X.Ok) {ψ φ : Λ → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0}
    (ha : V.FamURepP X ψ r C₁) (hb : V.FamURepP X φ r C₂) :
    V.FamURepP X (fun l => ψ l - φ l) r (C₁ + C₂) :=
  (ha.add hX ((hb.smul hX (-1)).mono hX le_rfl (by simp))).congr fun _ _ => by ring

/-- **The mean at the offset `0`** of a graded cell function is a graded family function. -/
theorem IsURepP.mean0 (hX : X.Ok) (hζ : IsFastProfile V.E.D.ζ) {φ : Λ → Vec 2 → Vec 2 → ℝ}
    {r w : ℕ} {C : ℝ≥0} (h : V.IsURepP X φ r w C) (hw : w ≤ X.L₀)
    (h0 : ∀ l ∈ V.W, (0 : Vec 2) ∈ V.U l) :
    V.FamURepP X (fun l => fieldCellMean (φ l 0)) r C := by
  obtain ⟨e, he, hs, hn⟩ := h
  refine ⟨Gen.mean e, he.mean0 hζ h0, Or.inr hs, fun t ht mres hm => ?_⟩
  rw [genNorm_mean_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx)]
  exact hn t ht mres 0 hm (by omega)

end AVRegularity.Providers.GenSem.UEnv
end
end
