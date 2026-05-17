/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import XYin.HeckeRIngs.AbstractHeckeRing.Basic
import XYin.HeckeRIngs.AbstractHeckeRing.Multiplication
import XYin.HeckeRIngs.AbstractHeckeRing.Module
import XYin.HeckeRIngs.AbstractHeckeRing.Associativity
import XYin.HeckeRIngs.AbstractHeckeRing.Ring
import XYin.HeckeRIngs.AbstractHeckeRing.Degree
import XYin.HeckeRIngs.AbstractHeckeRing.Commutativity

/-!
# Construction of Hecke rings following Shimura

This file re-exports the Hecke ring construction, split across:

* `Basic` — core definitions (`HeckePair`, `HeckeCoset`, `HeckeLeftCoset`, `decompQuot`, `𝕋`, `HeckeModule`)
* `Multiplication` — Shimura's `heckeMultiplicity`, `mulMap`, `mulSupport`, the `Mul` instance
* `Module` — `smulOrbit`, module action on left cosets, faithfulness
* `Associativity` — `IsScalarTower` (Shimura Prop 3.4)
* `Ring` — `Ring (𝕋 P ℤ)` instance and user-facing API
* `Degree` — degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ` (Shimura Prop 3.3)
-/
