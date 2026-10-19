-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Entry.TerminalResidualClauses
public import AVRegularity.Statements.Intermediate.Readout.RepresentationValue
public import AVRegularity.Statements.Intermediate.Readout.RepresentationMap
public import AVRegularity.Statements.Intermediate.Readout.IsRepresentationAt
public import AVRegularity.Statements.Intermediate.Readout.RepresentedSize
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The summation of the cascade.

* `ampRef D C Q n A₀ j`: the stored reference `A_j` of the cascade, `A_n = A₀`,
  `A_{j-1} = [1 + C(ε_{j-1}^Q + ε_{j-1}^δ)]A_j`, i.e. `A_j = A₀ ∏_{j < k ≤ n}(1 + C(ε_{k-1}^Q +
  ε_{k-1}^δ))`.
* `recurrence_product_bound`: a recurrence `X_j ≤ (1 + g_j)X_{j-1} + c_j`,
  `m₀ < j ≤ n`, with `g_j, c_j ≥ 0` and `X_{m₀} ≥ 0`, gives
  `X_n ≤ exp(∑_{m₀ < j ≤ n} g_j)(X_{m₀} + ∑_{m₀ < j ≤ n} c_j)`. -/

/-- The stored reference `A_j` of the cascade from `A_n = A₀`. -/
def ampRef (D : OCData) (C Q : ℝ) (n : ℕ) (A₀ : ℝ) (j : ℕ) : ℝ :=
  A₀ * ∏ k ∈ Finset.Ioc j n,
    (1 + C * (D.eps (k - 1) ^ Q + D.eps (k - 1) ^ ocDelta D.α D.q))

/-- **The represented product**: the summation of a near-unit recurrence. -/
theorem recurrence_product_bound (X g c : ℕ → ℝ) (m₀ : ℕ) (hX : 0 ≤ X m₀)
    (hg : ∀ j, 0 ≤ g j) (hc : ∀ j, 0 ≤ c j)
    (hrec : ∀ j, m₀ < j → X j ≤ (1 + g j) * X (j - 1) + c j) :
    ∀ n, m₀ ≤ n →
      X n ≤ Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j) * (X m₀ + ∑ j ∈ Finset.Ioc m₀ n, c j) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hS : 0 ≤ ∑ j ∈ Finset.Ioc m₀ n, g j := Finset.sum_nonneg fun j _ => hg j
    have hT : 0 ≤ ∑ j ∈ Finset.Ioc m₀ n, c j := Finset.sum_nonneg fun j _ => hc j
    have hsplitg : ∑ j ∈ Finset.Ioc m₀ (n + 1), g j = (∑ j ∈ Finset.Ioc m₀ n, g j) + g (n + 1) :=
      Finset.sum_Ioc_succ_top (by omega) g
    have hsplitc : ∑ j ∈ Finset.Ioc m₀ (n + 1), c j = (∑ j ∈ Finset.Ioc m₀ n, c j) + c (n + 1) :=
      Finset.sum_Ioc_succ_top (by omega) c
    have h1 := hrec (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    have hge : 1 + g (n + 1) ≤ Real.exp (g (n + 1)) := by
      have := Real.add_one_le_exp (g (n + 1)); linarith
    have hE1 : 1 ≤ Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j + g (n + 1)) :=
      Real.one_le_exp (by linarith [hg (n + 1)])
    have hpos : 0 ≤ X m₀ + ∑ j ∈ Finset.Ioc m₀ n, c j := by linarith
    rw [hsplitg, hsplitc, Real.exp_add]
    have hA : (1 + g (n + 1)) * X n ≤
        Real.exp (g (n + 1)) * (Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j) *
          (X m₀ + ∑ j ∈ Finset.Ioc m₀ n, c j)) := by
      calc (1 + g (n + 1)) * X n
          ≤ (1 + g (n + 1)) * (Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j) *
              (X m₀ + ∑ j ∈ Finset.Ioc m₀ n, c j)) :=
            mul_le_mul_of_nonneg_left ih (by linarith [hg (n + 1)])
        _ ≤ _ := mul_le_mul_of_nonneg_right hge (mul_nonneg (Real.exp_pos _).le hpos)
    have hB : c (n + 1) ≤
        Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j) * Real.exp (g (n + 1)) * c (n + 1) := by
      rw [← Real.exp_add]
      exact le_mul_of_one_le_left (hc _) hE1
    calc X (n + 1) ≤ (1 + g (n + 1)) * X n + c (n + 1) := h1
      _ ≤ Real.exp (g (n + 1)) * (Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j) *
            (X m₀ + ∑ j ∈ Finset.Ioc m₀ n, c j)) +
          Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j) * Real.exp (g (n + 1)) * c (n + 1) :=
        add_le_add hA hB
      _ = _ := by ring

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! The weighted component space `𝗁_π`, the constant readout
on it, and time-dependent representations.

* `CompSpace S`: the component space of a family with components `S`, in **normalized
  coordinates**: the vector `z = (z_v)` with mass weights `π_v` is stored as `(π_v^{-1/2} z_v)_v`
  in the Euclidean space `PiLp 2 (CompIn S → ℝ)`, so that the Euclidean norm is the weighted norm
  `|z|_{𝗁_π} = (∑_v π_v^{-1} |z_v|²)^{1/2}` (the norm of `weightedNorm 1 π 1` pointwise). The
  scalar components are real (`ScalarH`), as for every family of the cascade after entry.
* `toCompSpace π z`, `compField π a`: a component vector, and a classical component field
  `x ↦ a x`, in normalized coordinates.
* `readoutMatrix m E η₀ π π'`, `readoutCLM`: the constant readout `𝖱` of the passage `m → m-1`,
  `(𝖱Y)_v = ∑_{𝔱} E^{η₀|𝔱|} Y_{(v,𝔱)}` (`succReadout`; that is, `R_jY = ∑_σ β^{|σ|}Y_σ` with
  `β = E^{η₀}`), as a continuous linear map between the normalized component spaces of the
  retained family (masses `π'`) and the incoming family (masses `π`).
* `TimeRep H`: a representation whose base and profiles depend on time, with labels fixed
  (norms are formed at a fixed time; a time supremum is taken afterwards);
  `TimeRep.atTime t` is the `Representation` at the fixed time `t`; `TimeRep.map R`
  copies base and profiles through a constant map, labels unchanged.
* `IsRepOf π U F`: the normalized field `F` is a classical representative of the `L²`/Sobolev
  family `U` (componentwise, almost everywhere on the unit cell). -/

section
/-- The component space `𝗁_π` in normalized coordinates. -/
abbrev CompSpace (S : Finset Comp) : Type := PiLp 2 (fun _ : CompIn S => ℝ)

/-- A component vector `z` with masses `π`, in normalized coordinates `π_v^{-1/2} z_v`. -/
def toCompSpace {S : Finset Comp} (π : CompIn S → ℝ) (z : ∀ v : CompIn S, ScalarH v.1.root) :
    CompSpace S :=
  WithLp.toLp 2 (fun v => (Real.sqrt (π v))⁻¹ * z v)

/-- A classical component field in normalized coordinates. -/
def compField {S : Finset Comp} (π : CompIn S → ℝ) (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) :
    Vec 2 → CompSpace S :=
  fun x => toCompSpace π (a x)

/-- The matrix of the readout `𝖱` of the passage `m → m-1` in normalized coordinates:
`𝖱_{v v'} = π_v^{-1/2} E^{η₀|𝔱(v')|} π'_{v'}^{1/2}` when `v'` is born from `v`, zero otherwise. -/
def readoutMatrix (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp} (π : CompIn S → ℝ)
    (π' : CompIn S' → ℝ) : Matrix (CompIn S) (CompIn S') ℝ :=
  fun v v' => if compParent m v'.1 = v.1 then
    (Real.sqrt (π v))⁻¹ * E ^ (η₀ * ((compWord m v'.1).length : ℝ)) * Real.sqrt (π' v') else 0

/-- The constant readout `𝖱 : 𝗁_{π'} → 𝗁_π` of the passage `m → m-1`. -/
def readoutCLM (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp} (π : CompIn S → ℝ)
    (π' : CompIn S' → ℝ) : CompSpace S' →L[ℝ] CompSpace S :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (readoutMatrix m E η₀ π π'))

/-- A time-dependent representation: base and profiles depend on time, labels do not. -/
structure TimeRep (H : Type*) where
  /-- The base field `F(t)`. -/
  base : ℝ → Vec 2 → H
  /-- The profiles `G_l(t)` with their labels `λ_l`. -/
  profiles : List ((ℝ → Vec 2 → H) × ℝ)

namespace TimeRep

variable {H H' : Type*}

/-- The representation at the time `t`. -/
def atTime (r : TimeRep H) (t : ℝ) : Representation H where
  base := r.base t
  profiles := r.profiles.map fun p => (p.1 t, p.2)

/-- Copy through a constant map, labels unchanged. -/
def map [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (R : H →L[ℝ] H') (r : TimeRep H) : TimeRep H' where
  base := fun t x => R (r.base t x)
  profiles := r.profiles.map fun p => ((fun t x => R (p.1 t x)), p.2)

/-- Append profiles. -/
def append (r : TimeRep H) (l : List ((ℝ → Vec 2 → H) × ℝ)) : TimeRep H where
  base := r.base
  profiles := r.profiles ++ l

end TimeRep

/-- `F` (normalized coordinates, masses `π`) is a classical representative of the family `U`. -/
def IsRepOf {S : Finset Comp} {k : ℕ} (π : CompIn S → ℝ)
    (U : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root)) (F : Vec 2 → CompSpace S) : Prop :=
  ∀ v, (U v).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
    fun x => Real.sqrt (π v) * WithLp.ofLp (F x) v
end

/-! The objects of one passage `m → m-1` of the cascade.

Notation of the passage: `e = ε_m`, `E = ε_{m-1}`; `Y` the retained outgoing solution (family
`Gr`, level `m-1`), `U` the incoming solution (family `G`, level `m`), both on the successor window
`W = [t_p, t_f]`; `𝖱` the constant readout (`readoutCLM`, and `fieldReadout` on classical fields);
`P_p` the covariance polynomial of the current primitive with its original anchor
(`covPolyP (covPrimitive D m t) p`, as in `IsLiftedField`); `S_r` the profile kernel (a moving paired
kernel, `KernelSpec.applyClassical`); `T` the glued Eulerian lift of the actual level-`m` cell
recursion (`passageLift`, the formula of `IsLiftedField`).

* `fieldReadout`, `fieldCov`, `fieldKernel`, `passageLift`: these operators on classical
  time-dependent component fields `ℝ → Vec 2 → ∀ v, ScalarH v.1.root`.
* `IsPassageLift`: the lift coefficients `CcT` solve the actual level-`m` lift sequence on every
  odd slot (the first clause of `IsLiftedField`).
* `passageProfiles`: the five profiles of the passage split, in normalized
  coordinates of `𝗁_π` (`π` the masses of `G`), with their labels `E, e, E, e, e`:
  `H_E = 𝖱(P_p - I)S_rY`, `H_e = (T - I)P_p𝖱S_rY`, `D_E = 𝖱(P_p - I)(I - S_r)Y`,
  `D_e = (T - I)P_p𝖱(I - S_r)Y`, `𝓔 = U - TP_p𝖱Y`.
* `passageRepAt`: a representation of `Y(t)` copied by `𝖱` with the five profiles appended.
* `IsSmoothRep`: a classical, periodic, `C^K` representative of a Sobolev family.
* `iterZ α q s K = 1 + s + c(K+1)` (`Z_K`; `c = ocC α q = γ/2 + δ`) and
  `IsPassageOrders`: the passage order requests:
  `N_aux ≥ 2J_r + N + 2p + L` with `J_r = K + 2`,
  `σ₀L > P + max{Z_K, q(1+s)} + 4`, profile moments through `L` (`2n_k - 1 ≥ L`). The width
  condition is `IsCascadeWidths` (which implies `σ₀ < δ/8`,
  `σ₀D_* < δ/8` and `σ₀ < λ_c < λ_entry`); `N_out ≥ N_aux + 4p` is in `IsSuccessorSchedule`; the
  buffer order `n_b ≥ max{2J_r, N_aux}` is internal to the proof.
* `IsCascadeWidths α q lamE a σ Dstar`: the width choice:
  `0 < a < σ`, `3σ < min{λ_entry, λ_c, δ/[8(1 + D_*)]}`,
  `λ_c = ½ min{λ_entry, (q-1)(1+c)}`.
* `PassageClauses`: the exact profile proposition on the window `W`.
* `PassageJetClauses`: at every time of `W`, the high-order jets
  (`|U|_{ρ⋆,2J_r;π} + |TP_p𝖱Y|_{ρ⋆,2J_r;π} ≤ CA`) and the interpolated physical error
  (`|𝓔|_{ρ⋆,J_r;π} ≤ CE^{Q/2}A`), for given classical representatives and lift coefficients. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The constant readout `𝖱` of the passage `m → m-1` on classical component fields. -/
def fieldReadout (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root :=
  fun t x v => ∑ v' : CompIn S', if compParent m v'.1 = v.1 then
    E ^ (η₀ * ((compWord m v'.1).length : ℝ)) * a t x v' else 0

/-- The covariance polynomial `P_p` of the level-`m` primitive (original anchor), at each time. -/
def fieldCov (D : OCData) (m p : ℕ) {S : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root :=
  fun t => covPolyP (covPrimitive D m t) p (a t)

/-- The moving paired kernel `S_r` on a classical component field, at each time. -/
def fieldKernel (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec) {S : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root :=
  fun t => Sr.applyClassical φ₀ t (a t)

/-- The glued Eulerian lift `T` of the actual level-`m` cell recursion (`IsLiftedField`). -/
def passageLift (D : OCData) (m N depth : ℕ) {S : Finset Comp}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn S) (fun v => ScalarH v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root :=
  fun t x => gluedLift (ocObsPulses D.α D.q D.Λ m t t) (fun k => ocCutoff D.α D.q D.Λ m k)
    (D.cellScaleSq m) (liftLength D m) (D.eps m)
    (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / liftLength D m) N depth CcT
    (fun k s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
    (fun k s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') a t x

/-- The lift coefficients of the actual level-`m` lift sequence (first clause of
`IsLiftedField`). -/
def IsPassageLift (G : GenStage D ScalarH Dm b j₀) (m N depth sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) : Prop :=
  ∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N depth (CcT k)

/-- A classical, `ℤ²`-periodic, `C^K` representative of a family at one time. -/
def IsSmoothRep {S : Finset Comp} {k : ℕ} (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root))
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) (K : ℕ) : Prop :=
  ContDiff ℝ K a ∧ AVenhance.IsZ2Periodic a ∧
    ∀ v, (X v).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => a x v

/-- The five profiles of the passage `m → m-1`, labels `E, e, E, e, e`. -/
def passageProfiles (D : OCData) (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) :
    List ((ℝ → Vec 2 → CompSpace G.comps) × ℝ) :=
  let E := D.eps (m - 1)
  let e := D.eps m
  let SY := fieldKernel φ₀ Sr aY
  let DY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root := aY - SY
  let F : (ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) → ℝ → Vec 2 → CompSpace G.comps :=
    fun a t => compField (G.mass law) (a t)
  let R : (ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) →
      ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root := fieldReadout m E η₀
  let T := passageLift D m N depth CcT
  [(F (R (fieldCov D m p SY - SY)), E),
    (F (T (fieldCov D m p (R SY)) - fieldCov D m p (R SY)), e),
    (F (R (fieldCov D m p DY - DY)), E),
    (F (T (fieldCov D m p (R DY)) - fieldCov D m p (R DY)), e),
    (F (aU - T (fieldCov D m p (R aY))), e)]

/-- A representation of `Y(t)` copied by `𝖱`, with the five profiles at the time `t` appended. -/
def passageRepAt (D : OCData) (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ)
    (rY : Representation (CompSpace Gr.comps)) : Representation (CompSpace G.comps) where
  base := (rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).base
  profiles := (rY.map (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law))).profiles ++
    (passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => (q.1 t, q.2)

/-- `Z_K = 1 + s + c(K+1)`, `c = ocC α q`: the power-loss exponent `Z` of display (13.2) of the
paper, at the order `K`. -/
def iterZ (α q s : ℝ) (K : ℕ) : ℝ := 1 + s + ocC α q * ((K : ℝ) + 1)

/-- The passage order requests. The order floor of display (13.3) of the paper follows from
them. -/
def IsPassageOrders (α q s : ℝ) (K : ℕ) (P σ₀ : ℝ) (L N p nk Naux : ℕ) : Prop :=
  2 * (K + 2) + N + 2 * p + L ≤ Naux ∧
    σ₀ * L > P + max (iterZ α q s K) (q * (1 + s)) + 4 ∧
    L + 1 ≤ 2 * nk

/-- The width choice: the width exponents are small, as in display (13.4) of the paper. -/
def IsCascadeWidths (α q lamE a σ : ℝ) (Dstar : ℕ) : Prop :=
  0 < a ∧ a < σ ∧
    3 * σ < min lamE (min ((1 / 2) * min lamE ((q - 1) * (1 + ocC α q)))
      (ocDelta α q / (8 * (1 + Dstar))))

/-- The exact profile proposition on the window `[t_p, t_f]`: classical
representatives of `U` and `Y` (order `K + N + 2p + 2`) exist on the window; for all such
representatives (unique, being continuous), every actual lift, and every time,
the profile bounds; and for every representation `r_Y` of `Y(t)` at
the wavelength `E`, the copied-and-appended representation is a representation of `U(t)` at the
wavelength `e` with the size recurrence. The exponents are
`μ_s` (`mu`), `δ - 2σ₀` (`wexp`) and `5η₀/4`. -/
def PassageClauses (D : OCData) (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K : ℕ) (s η₀ mu wexp P C A tp tf : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root)) : Prop :=
  (∃ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) ∧
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2))) ∧
  ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) →
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)) →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N depth sX sZ CcT →
    ∀ t ∈ Set.Icc tp tf,
      (let E := D.eps (m - 1)
       let e := D.eps m
       let prof := (passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
         fun q => q.1 t
       let YE := profileSeminorm E K s (compField (Gr.mass law) (aY t))
       profileNorm E K s (prof.getD 0 0) ≤ ENNReal.ofReal (C * E ^ wexp) * YE ∧
       profileNorm e K s (prof.getD 1 0) ≤ ENNReal.ofReal (C * E ^ mu) * YE ∧
       profileNorm E K s (prof.getD 2 0) + profileNorm e K s (prof.getD 3 0) +
           profileNorm e K s (prof.getD 4 0) ≤ ENNReal.ofReal (C * E ^ P * A) ∧
       ∀ rY : Representation (CompSpace Gr.comps), IsRepresentationAt E K rY →
         rY.value = compField (Gr.mass law) (aY t) →
         IsRepresentationAt e K (passageRepAt D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY t rY) ∧
         (passageRepAt D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY t rY).value =
           compField (G.mass law) (aU t) ∧
         representedSize s K e (passageRepAt D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY t rY) ≤
           ENNReal.ofReal (1 + C * (E ^ (5 * η₀ / 4) + E ^ mu + E ^ wexp)) *
               representedSize s K E rY + ENNReal.ofReal (C * E ^ P * A))

/-- At every time of the window `[t_p, t_f]`, for the classical representatives `aU`, `aY` and the
lift coefficients `CcT`: the high-order jets, `|U|_{ρ⋆,2J_r;π} + |TP_p𝖱Y|_{ρ⋆,2J_r;π} ≤ CA`
(`J_r = K + 2`; molecular buffer and full lift), and the interpolated physical error
`|𝓔|_{ρ⋆,J_r;π} ≤ CE^{Q/2}A` for `𝓔 = U - TP_p𝖱Y`, the derivatives of the actual error on
its window (`ρ⋆ = rhoStar D c₀ m`). The weights are the unmarked masses `π` of `G`. -/
def PassageJetClauses (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth K : ℕ)
    (η₀ Q C c₀ A tp tf : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) : Prop :=
  ∀ t ∈ Set.Icc tp tf,
    (∃ Un Uh : ∀ v : CompIn G.comps, TorusHk (2 * (K + 2)) (ScalarH v.1.root),
      (∀ v, (Un v).toFunction.jet (valueIndex2 (2 * (K + 2)))
          =ᵐ[volume.restrict AVenhance.unitCube] fun x => aU t x v) ∧
      (∀ v, (Uh v).toFunction.jet (valueIndex2 (2 * (K + 2)))
          =ᵐ[volume.restrict AVenhance.unitCube] fun x => passageLift D m N depth CcT
            (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ aY)) t x v) ∧
      weightedNorm (rhoStar D c₀ m) (G.mass law) (fun _ => 1) Un +
          weightedNorm (rhoStar D c₀ m) (G.mass law) (fun _ => 1) Uh ≤ C * A) ∧
    ∃ En : ∀ v : CompIn G.comps, TorusHk (K + 2) (ScalarH v.1.root),
      (∀ v, (En v).toFunction.jet (valueIndex2 (K + 2))
          =ᵐ[volume.restrict AVenhance.unitCube] fun x => aU t x v - passageLift D m N depth CcT
            (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ aY)) t x v) ∧
      weightedNorm (rhoStar D c₀ m) (G.mass law) (fun _ => 1) En ≤
        C * D.eps (m - 1) ^ (Q / 2) * A
end

/-! The state carried by one passage `m → m-1`.

Notation: `G` the incoming stage (level `m`), `G'` its actual extended successor,
`Gr = G'.retained m H J` the retained stage `G_-` (level `m-1`); `t_A` the history-window start,
`s₀` the preparation start, `t_f` the common final time, `W = [t_p, t_f]`; `e = ε_m`, `E = ε_{m-1}`,
`ν = κ_m`, `B = κ_{m-1}`, `ρ⋆ = rhoStar D k_I.c₀ m`, `ρ = rhoEnh D k_I.c_r m`,
`τ = min{δ/4, τ_e}`. One constant `C` serves for every constant (`C_err`, `C_jet`,
`C_amp^step`, `C_reg`, `C_R`): they are all chosen at the same binder; only the factor
`1 + C(E^Q + E^δ)` multiplies the amplitude between passages.

* `PassageFrame` (datum-independent part): the common preparation `(t_p, 𝐏_reg)` from `s₀`
  with the buffer before the preparation `s₀ + ρ⋆²/ν ≤ t_p` and the quiet margin of `t_p`
  (half-width `τ'_m`); `NextFamilyClauses`; the outgoing
  stage is a cascade stage and satisfies the propagated invariant `Inv_{m-1}(G_-; t_A + 3τ_m, t_f)`
  (the globally selected constants, `stage_invariant_propagation`); the readout in normalized
  coordinates has `‖𝖱‖ ≤ 1 + CE^{5η₀/4}`.
* `PassageDatum` (per datum `f`, amplitude `A`, incoming order-zero solution `U` from `f` at `s₀`
  and retained order-zero solution `Y`): the marked amplitude
  `sup_W ‖d_-Y‖_{π_-} ≤ [1 + C(E^Q + E^δ)]A`; the regenerated solution `Y^{(N_aux)}` from the same
  trace with `Y = truncate Y^{(N_aux)}` on `W`, its bounds
  `sup_W |d_-Y|_{ρ,N_aux;π_-} ≤ CA`, `𝓔^B_{ρ,N_aux;π_-}(d_-Y; W) ≤ CA`, and the physical comparison
  `ComparisonClauses` (`Û = T_mP_pZ`, `Z = 𝖱Y`, `sup_W‖𝓔‖ + √ν‖∇𝓔‖ ≤ CE^QA`); the exact profile
  proposition `PassageClauses`; and, for all classical representatives and lifts,
  `PassageJetClauses` (the jets and the error).
* `PassageOutput`: for every datum and incoming solution, the retained solution exists and every
  retained solution satisfies `PassageDatum`.
* `PassageErrorOutput`: the datum part of the physical-error jet bound. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The datum-independent part of the passage certificate. -/
def PassageFrame (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ) (kI : InvConsts) (CI τe : ℝ)
    (seed G Gr : GenStage D ScalarH Dm b j₀) (m : ℕ) (η₀ : ℝ) (Kres Tw p Nout Naux : ℕ)
    (Q CQ C tA s₀ tf tp : ℝ)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))) : Prop :=
  IsCommonPreparation law P seedK freshK φ₀ hφ₀ G kI.cr Q CQ C p Nout Naux s₀ tf tp Preg ∧
    s₀ + rhoStar D kI.c₀ m ^ 2 / D.κ m ≤ tp ∧
    Set.Icc (tp - ocTauP D.α D.q D.Λ m) (tp + ocTauP D.α D.q D.Λ m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ m ∧
    NextFamilyClauses law P seedK freshK kI seed G Gr m η₀ Kres Tw tp tf ∧
    IsCascadeStage D P Mn seed Gr ∧
    IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat kI (tA + 3 * ocTau D.α D.q D.Λ m) tf
      (CI * D.eps (m - 1) ^ min (ocDelta D.α D.q / 4) τe)
      (CI * D.eps ((m - 1) - 1) ^ (D.q * min (ocDelta D.α D.q / 4) τe)) Gr ∧
    ‖readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law)‖ ≤
      1 + C * D.eps (m - 1) ^ (5 * η₀ / 4)

/-- The per-datum clauses of the passage certificate. -/
def PassageDatum (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K Naux : ℕ) (s η₀ mu wexp Pacc Q C cr c₀ A s₀ tp tf : ℝ) (Sr : KernelSpec)
    {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root)) : Prop :=
  (∀ t ∈ Set.Icc tp tf, weightedNorm 1 (Gr.mass law) (Gr.marker law) (fun v => Y v t) ≤
      (1 + C * (D.eps (m - 1) ^ Q + D.eps (m - 1) ^ ocDelta D.α D.q)) * A) ∧
  (∃ (YN0 : ∀ v : CompIn Gr.comps, TorusHk Naux (ScalarH v.1.root))
      (YN : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (ScalarH v.1.root))
      (YNw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (ScalarH v.1.root))
      (YNk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m p tp (Preg f) YN0 ∧
    Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf
      YN0 (fun _ _ => 0) (fun _ _ => 0) YN YNw YNk ∧
    (∀ v, ∀ t ∈ Set.Icc tp tf, truncateTorusHk (Nat.zero_le Naux) (YN v t) = Y v t) ∧
    (∀ t ∈ Set.Icc tp tf,
      weightedNorm (rhoEnh D cr m) (Gr.mass law) (Gr.marker law) (fun v => YN v t) ≤ C * A) ∧
    strongEnergy (rhoEnh D cr m) (D.κ (m - 1)) (fun v => Gr.mass law v / Gr.marker law v ^ 2)
        tp tf YN YNw ≤ ENNReal.ofReal (C * A) ∧
    ComparisonClauses law P seedK freshK φ₀ hφ₀ G Gr m p Naux N depth sX sZ η₀ s₀ tp tf
      (C * D.eps (m - 1) ^ Q * A) (C * D.eps (m - 1) ^ Q * A) f YN) ∧
  PassageClauses D law G Gr m p N depth sX sZ K s η₀ mu wexp Pacc C A tp tf φ₀ Sr U Y ∧
  ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) →
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)) →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N depth sX sZ CcT →
      PassageJetClauses law G Gr m p N depth K η₀ Q C c₀ A tp tf CcT aU aY

/-- The datum part of the passage for the preparation `𝐏_reg`: for every datum `f` with
`A ≥ ‖df‖_π` and the actual incoming solution `U` from `f` at `s₀`, the retained outgoing solution
`Y` from `Q_p(t_p)𝐏_reg f` exists, and every such `Y` satisfies `PassageDatum`. -/
def PassageOutput (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K Naux : ℕ) (s η₀ mu wexp Pacc Q C cr c₀ s₀ tp tf : ℝ) (Sr : KernelSpec)
    {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))) : Prop :=
  ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ),
    weightedNorm 1 (G.mass law) (G.marker law) f ≤ A →
  ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f
      (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
  (∃ (Y0 : ∀ v' : CompIn Gr.comps, TorusHk 0 (ScalarH v'.1.root))
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m p tp (Preg f) Y0 ∧
    Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) 0 tp tf
      Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk) ∧
  ∀ (Y0 : ∀ v' : CompIn Gr.comps, TorusHk 0 (ScalarH v'.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m p tp (Preg f) Y0 →
    Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) 0 tp tf
      Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    PassageDatum law P seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C
      cr c₀ A s₀ tp tf Sr Preg f U Y

/-- The datum part of the physical-error jet bound:
for every datum, incoming solution, retained solution, actual lift and classical
representatives on the window, `PassageJetClauses`. -/
def PassageErrorOutput (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K : ℕ) (η₀ Q C c₀ s₀ tp tf : ℝ) {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))) : Prop :=
  ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ),
    weightedNorm 1 (G.mass law) (G.marker law) f ≤ A →
  ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f
      (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
  ∀ (Y0 : ∀ v' : CompIn Gr.comps, TorusHk 0 (ScalarH v'.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m p tp (Preg f) Y0 →
    Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) 0 tp tf
      Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
    IsPassageLift G m N depth sX sZ CcT →
  ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) →
    (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)) →
    PassageJetClauses law G Gr m p N depth K η₀ Q C c₀ A tp tf CcT aU aY
end

/-! The run of the cascade from an interior seed.

Three times per level `j`: the history-window start `a_j` (`hist j`), the birth time
`s_j` of the solved field (`st j`), and the preparation start `r_j = max{s_j, a_j + 3τ_j}`
(`cascadeRestart`). They obey `a_n = s_n = t_S`, `a_{j-1} = a_j + 3τ_j`, `s_{j-1} = t_p^{(j)}`, and
the preparation of passage `j` is applied to the trace `U_j(r_j)` (restart uniqueness identifies
the restarted solution with `U_j`). The wait is `∑(3τ_j + 4τ_j'')` (`cascade_wait`).

* `cascadeRestart D hist st j = max{s_j, a_j + 3τ_j}`.
* `CascadeFrame`: the datum-independent run from the seed at level `n` down to `m₀`:
  `stage n = seed`; for `m₀ ≤ j ≤ n` the stage has level `j`, is a cascade stage, satisfies
  `Inv_j(G_j; a_j, t_f)`, `a_j ≤ s_j` and `s_j - s_n ≤ ∑_{k=j+1}^n(3τ_k + 4τ_k'')`; for
  `m₀ < j ≤ n` the actual successor `ext j`, `stage (j-1) = Π(ext j)`, the history and birth
  recursions, the remaining-window inequality `r_j + 4τ_j'' ≤ t_f`, and the passage frame
  (`PassageFrame`) from `r_j`; `s_{m₀} ≤ s_n + t₀`.
* `CascadeOutput`: for a datum `f_n` on the seed components, the actual order-zero families `U_j`
  (`U_n` from `f_n` at `s_n`, `U_{j-1}` the retained solution `Y_j` of passage `j` from
  `Q_p(t_p)𝐏_reg U_j(r_j)` in the old roots and zero in new words), each also the solution
  restarted at `r_j`; the stored amplitudes `sup_{[s_j,t_f]}‖d_jU_j‖_{π_j} ≤ A_j` (`ampRef`);
  for each passage the trace, the per-datum certificate `PassageDatum` with
  `A = A_j`, and the lift coefficients; classical representatives of order `K + N + 2p + 2` of
  `U_j` and `U_{j-1}` on each passage window and of `U_n` on `I_*`; and the specified
  representation: `rep m₀ = (U_{m₀}, [])`, `rep j = (rep (j-1)).map 𝖱_j ++` the five profiles
  of passage `j` (so `F_n = R_n⋯R_{m₀+1}U_{m₀}` and the labels are as above); on
  `I_* = [s_n + t₀, t_f]`, at every time, `rep n` is a representation of `U_n(t)` at `ε_n`, and
  `ess sup_{I_*} X_{ε_n}(U_n; K) ≤ C‖f_n‖_{π_n}`. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The preparation start `r_j = max{s_j, a_j + 3τ_j}` of passage `j`. -/
def cascadeRestart (D : OCData) (hist st : ℕ → ℝ) (j : ℕ) : ℝ :=
  max (st j) (hist j + 3 * ocTau D.α D.q D.Λ j)

/-- The datum-independent run of the cascade from the seed at level `n` down to `m₀`. -/
def CascadeFrame (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ) (kI : InvConsts) (CI τe η₀ : ℝ)
    (Kres Tw p Nout Naux : ℕ) (Q CQ C : ℝ)
    (seed : GenStage D ScalarH Dm b j₀) (n m₀ : ℕ) (tS t₀ tf : ℝ)
    (stage ext : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ)
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root))) : Prop :=
  stage n = seed ∧ hist n = tS ∧ st n = tS ∧ st m₀ ≤ tS + t₀ ∧
  (∀ j, m₀ ≤ j → j ≤ n →
    (stage j).level = j ∧ IsCascadeStage D P Mn seed (stage j) ∧
    IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat kI (hist j) tf
      (CI * D.eps j ^ min (ocDelta D.α D.q / 4) τe)
      (CI * D.eps (j - 1) ^ (D.q * min (ocDelta D.α D.q / 4) τe)) (stage j) ∧
    hist j ≤ st j ∧
    st j - tS ≤ ∑ k ∈ Finset.Ioc j n,
      (3 * ocTau D.α D.q D.Λ k + 4 * ocTauPP D.α D.q D.Λ k)) ∧
  ∀ j, m₀ < j → j ≤ n →
    IsActualSuccessor D P Mn (stage j) (ext j) ∧
    stage (j - 1) = (ext j).retained j Mn.H Mn.J ∧
    hist (j - 1) = hist j + 3 * ocTau D.α D.q D.Λ j ∧ st (j - 1) = tp j ∧
    cascadeRestart D hist st j + 4 * ocTauPP D.α D.q D.Λ j ≤ tf ∧
    PassageFrame law P Mn seedK freshK φ₀ hφ₀ Mnat kI CI τe seed (stage j) (stage (j - 1)) j η₀
      Kres Tw p Nout Naux Q CQ C (hist j) (cascadeRestart D hist st j) tf (tp j) (Preg j)

/-- The families, passage certificates and representations of the cascade for the datum `f`. -/
def CascadeOutput (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C cr c₀ : ℝ) (n m₀ : ℕ) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root)) : Prop :=
  ∃ (U : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : (j : ℕ) → ∀ v u (_ : (stage j).fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (Y0 : (j : ℕ) → ∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root))
    (aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
    (CcT : (j : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root))
    (rep : (j : ℕ) → TimeRep (CompSpace (stage j).comps)),
    Y0 n = f ∧
    (∀ j, m₀ ≤ j → j ≤ n →
      (stage j).IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ j) (streamVel (D.Φ j)) 0 (st j) tf
        (Y0 j) (fun _ _ => 0) (fun _ _ => 0) (U j) (Uw j) (Uk j) ∧
      (stage j).IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ j) (streamVel (D.Φ j)) 0
        (cascadeRestart D hist st j) tf (fun v => U j v (cascadeRestart D hist st j))
        (fun _ _ => 0) (fun _ _ => 0) (U j) (Uw j) (Uk j) ∧
      ∀ t ∈ Set.Icc (st j) tf,
        weightedNorm 1 ((stage j).mass law) ((stage j).marker law) (fun v => U j v t) ≤
          ampRef D C Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j) ∧
    (∀ j, m₀ < j → j ≤ n →
      IsRetainedTrace (stage j) (stage (j - 1)) j p (tp j)
        (Preg j (fun v => U j v (cascadeRestart D hist st j))) (Y0 (j - 1)) ∧
      PassageDatum law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
        s η₀ mu wexp Pacc Q C cr c₀
        (ampRef D C Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j)
        (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1)) (Preg j)
        (fun v => U j v (cascadeRestart D hist st j)) (U j) (U (j - 1)) ∧
      IsPassageLift (stage j) j N depth sX sZ (CcT j) ∧
      (∀ t ∈ Set.Icc (tp j) tf,
        IsSmoothRep (fun v => U j v t) (aU j t) (K + N + 2 * p + 2) ∧
        IsSmoothRep (fun v => U (j - 1) v t) (aU (j - 1) t) (K + N + 2 * p + 2)) ∧
      rep j = ((rep (j - 1)).map (readoutCLM j (D.eps (j - 1)) η₀ ((stage j).mass law)
          ((stage (j - 1)).mass law))).append
        (passageProfiles D law (stage j) (stage (j - 1)) j p N depth η₀ φ₀ (freshK (j - 1))
          (CcT j) (aU j) (aU (j - 1)))) ∧
    (∀ t ∈ Set.Icc (tS + t₀) tf, IsSmoothRep (fun v => U n v t) (aU n t) (K + N + 2 * p + 2)) ∧
    rep m₀ = ⟨fun t => compField ((stage m₀).mass law) (aU m₀ t), []⟩ ∧
    (∀ t ∈ Set.Icc (tS + t₀) tf,
      IsRepresentationAt (D.eps n) K ((rep n).atTime t) ∧
      ((rep n).atTime t).value = compField ((stage n).mass law) (aU n t)) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (tS + t₀) tf)),
      representedSize s K (D.eps n) ((rep n).atTime t) ≤
        ENNReal.ofReal (C * weightedNorm 1 ((stage n).mass law) (fun _ => 1) f)
end

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! The schedule block and the tail of the cascade
quantifier string.

* `IsCascadeSchedule`: the schedule conditions of the existential block, for the fixed
  `K, P, D₀` and seed exponents `σ_entry, λ_entry`: `Q > 0` with `Q/2 > P + qZ_K + 4`, the successor
  schedule at the usable fresh width exponent `min{σ_entry, δ + σ₀}` and the seed allowance
  `λ_entry` (`IsSuccessorSchedule`, which contains `σ₀ = a + σ` and `N_out ≥ N_aux + 4p`),
  `N_aux ≤ K_res`, `K_res + 2p ≤ N_out`, the passage orders (`IsPassageOrders`) and the widths
  (`IsCascadeWidths` at `λ_entry` and `D_*`).
* `CascadeTail`: everything after the schedule block:
  `∀ C_e ≥ 1, k_S` (seed bounds `0 < c₀ ≤ c₀max`, `0 < c_r ≤ 1`, `σ_f = σ_entry`,
  `λ_c = λ_entry`, `IsSeedAllocation`) `∃ (thr, C_H ≥ 1, Υ > 0) ∀ k_I` (`IsInvariantAdmissible`)
  `∃ (C_I^thr, C_w^thr) ∀ (C_I, C_w, j₀)` (`IsLedgerAdmissible`, `IsCarrierStart`)
  `∃ (C_cas > 0, C_Q, C_p, m₀) ∀ D` (`D.α = α`, `D.q = q`, `D.Λ = Λ`, `D.ζ = ζ`,
  `IsOCStreamSeq`) `∀ M` (`IsOCBandChain`, `D.term = M`) `∀ M_nat ≥ M ∀ law` (`IsSuccessorLaw`)
  `∀ seedK freshK` (`IsFreshKernel`) `∀ (G_n, n, s_n, t_f)` (`s_n + t₀ < t_f ≤ s_n + T₀`,
  `IsGeneratedSeed`, `m₀ < n < M`) `∃` the datum-independent frame (stages, successors, history,
  birth and preparation times, preparations) `∀ f_n`, `CascadeOutput`.

In `CascadeTail` the fresh kernels are required at the
birth levels `1 ≤ b' < M` only (composability with `fresh_axes_exist`). The lift orders
`n_pad, s_X, s_Z` remain arguments; `iteration_cascade` and `iteration_cascade_of_schedule` assert the
tail above existential floors. -/

/-- The schedule block. -/
def IsCascadeSchedule (α s q : ℝ) (K : ℕ) (Pacc lamE σE : ℝ) (D₀ : ℕ) (Q : ℝ)
    (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ) : Prop :=
  0 < Q ∧ Pacc + q * iterZ α q s K + 4 < Q / 2 ∧
    IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr
      Acl Naux Nout ∧
    Naux ≤ Kres ∧ Kres + 2 * p ≤ Nout ∧
    IsPassageOrders α q s K Pacc σ₀ L N p nk Naux ∧
    IsCascadeWidths α q lamE a σ (succDstar D₀ N p H)

/-- The tail of the cascade quantifier string, after the schedule block. -/
def CascadeTail (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀max : ℝ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (Pacc t₀ T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE Q : ℝ)
    (H J N p nk Lc Lf Lpr Naux Nout Kres npad sX sZ Kneed : ℕ) (σ₀ : ℝ) : Prop :=
  ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
    0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
    IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
  ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
    IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
  ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
    IsCarrierStart α q Λ bw CH Υ j₀ →
  ∃ (C CQ Cp : ℝ) (m₀ : ℕ), 0 < C ∧
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw),
    IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
    tS + t₀ < tf → tf - tS ≤ T₀ →
    IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
      Mnat kS seed n tS tf Ce τe r₀ D₀ →
    IsSeedPointwiseMolecular law kS seed tS tf →
    m₀ < n → n < M →
  ∃ (stage ext : ℕ → GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (hist st tp : ℕ → ℝ)
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root))),
    CascadeFrame law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK φ₀ hφ₀ Mnat kI CI τe
      (succEta0 α q s) Kres (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout
      Naux Q CQ Cp seed n m₀ tS t₀ tf stage ext hist st tp Preg ∧
    ∀ f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root),
      CascadeOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s) (ocMuS α q s)
        (ocDelta α q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ n m₀ tS t₀ tf stage hist st tp Preg f

end AVRegularity
end
end
