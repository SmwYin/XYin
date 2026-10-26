/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.GroupTheory.Exponent
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Data.Finsupp.Multiset
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Shared definitions

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87` is not an imported dependency.
Contracts are adapted to pinned Lean 4.30.0. Local prerequisites precede their consumers. See the
declaration records for exact source matches and remaining port boundaries.
-/

noncomputable section
open Filter NumberField Topology Set UniqueFactorizationMonoid
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Planning source: Density.lean:50; statement placeholder. -/
def primeIdealZetaSum {K : Type*} [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

/-- Planning source: Density.lean:64; statement placeholder. -/
def HasDirichletDensity {K : Type*} [Field K] [NumberField K]
    (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) (𝓝 δ)

/-- Planning source: NumberFieldEulerProduct.lean:45; statement placeholder. -/
abbrev NonzeroIdeal (F : Type*) [Field F] := {I : Ideal (𝓞 F) // I ≠ ⊥}

/-- Planning source: Frobenius.lean:62; statement placeholder. -/
def UnramifiedIn (𝔭 : Ideal (𝓞 K)) : Prop :=
  𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
    𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓

/-- Planning source: ZetaProduct.lean:71; statement placeholder. -/
abbrev galoisCharacter := Gal(L/K) →* ℂˣ

/-- Planning source: Density.lean:89; statement placeholder. -/
def HasLowerDirichletDensity {F : Type*} [Field F] [NumberField F]
    (S : Set (Ideal (𝓞 F))) (δ : ℝ) : Prop :=
  liminf (fun s : ℝ ↦ primeIdealZetaSum S s /
    primeIdealZetaSum (univ : Set (Ideal (𝓞 F))) s) (𝓝[>] 1) = δ

/-- Planning source: Density.lean:82; statement placeholder. -/
def HasUpperDirichletDensity {F : Type*} [Field F] [NumberField F]
    (S : Set (Ideal (𝓞 F))) (δ : ℝ) : Prop :=
  limsup (fun s : ℝ ↦ primeIdealZetaSum S s /
    primeIdealZetaSum (univ : Set (Ideal (𝓞 F))) s) (𝓝[>] 1) = δ

end Cox.Chebotarev
