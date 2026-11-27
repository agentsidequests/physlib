/-
Copyright (c) 2026 Paul Wishall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Wishall
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Darboux transformation on the Schwarzschild exterior

The first-order Darboux map sends odd-parity Regge–Wheeler solutions to even-parity
Zerilli solutions.

## i. Overview

On the exterior, in units with black-hole mass one, the derivative in tortoise radius is
the areal-radius derivative multiplied by the lapse. We use an auxiliary variable for
the tortoise derivative of the wave, so the equation is a system of two first-order
equations. The complex spectral parameter squares to minus frequency squared for a
real-frequency wave. The Darboux map uses the normalization from the Aptifold
scattering proof and requires its denominator to be nonzero.

## ii. Key results

* The partner transformation acts on any homogeneous radial system with the stated
  factorization.
* Its Schwarzschild specialization gives the Regge–Wheeler and Zerilli equations
  on the same exterior and at the same frequency, for angular multipole at least two.

## iii. Table of contents

- A. Transformation of a radial system
- B. Schwarzschild specialization

## iv. References

* K. Glampedakis, A. D. Johnson and D. Kennefick, *Darboux transformation in black hole
  perturbation theory*, Phys. Rev. D 96, 024036 (2017), equations (14)–(29).
  https://doi.org/10.1103/PhysRevD.96.024036
* Aptifold Research, *Exactly two rational parity mixtures in quadratic Schwarzschild
  scattering*, alphaXiv preprint (2026), Section 3, equation (4), for the inverse map
  and normalization used in the accompanying scattering proof.
  https://www.alphaxiv.org/abs/2611.rational-parity-mixtures-schwarzschild-scattering
-/

@[expose] public section

namespace GeneralRelativity.Schwarzschild.Darboux

noncomputable section

/-! ## A. Transformation of a radial system -/

/-- A homogeneous wave equation outside a radial cutoff. The second field is the
tortoise derivative of the first. The coefficient includes the frequency term. -/
structure RadialSolution (cutoff : ℝ) (lapse coefficient value jet : ℝ → ℂ) : Prop where
  /-- The areal derivative of the wave is its tortoise derivative divided by the lapse. -/
  valueDeriv : ∀ r, cutoff < r → HasDerivAt value (jet r / lapse r) r
  /-- The equation gives the areal derivative of the tortoise jet. -/
  jetDeriv : ∀ r, cutoff < r → HasDerivAt jet (coefficient r * value r / lapse r) r

/-- The common part of the partner coefficients, before adding or subtracting the
tortoise derivative of the superpotential. -/
def partnerCoefficient (frequency rate superpotential : ℂ) : ℂ :=
  frequency ^ 2 + superpotential ^ 2 - rate ^ 2

/-- The normalized Darboux transform of the wave value at one radius. -/
def transformedValue (frequency rate superpotential value jet : ℂ) : ℂ :=
  (superpotential * value + jet) / (rate + frequency)

/-- The tortoise derivative of the normalized Darboux-transformed wave. -/
def transformedJet (frequency rate superpotential value jet : ℂ) : ℂ :=
  (superpotential * jet + partnerCoefficient frequency rate superpotential * value) /
    (rate + frequency)

/-- The normalized Darboux transform sends the minus partner equation to the plus
partner equation. The supplied jet of the superpotential is in tortoise radius. -/
lemma transform_partner {cutoff : ℝ} {lapse weight weightJet value jet : ℝ → ℂ}
    (frequency rate : ℂ) (normalization : rate + frequency ≠ 0)
    (lapseNonzero : ∀ r, cutoff < r → lapse r ≠ 0)
    (weightDeriv : ∀ r, cutoff < r → HasDerivAt weight (weightJet r / lapse r) r)
    (minus : RadialSolution cutoff lapse
      (fun r => partnerCoefficient frequency rate (weight r) - weightJet r) value jet) :
    RadialSolution cutoff lapse
      (fun r => partnerCoefficient frequency rate (weight r) + weightJet r)
      (fun r => transformedValue frequency rate (weight r) (value r) (jet r))
      (fun r => transformedJet frequency rate (weight r) (value r) (jet r)) := by
  constructor
  · intro r hr
    have law := (((weightDeriv r hr).mul (minus.valueDeriv r hr)).add
      (minus.jetDeriv r hr)).div_const (rate + frequency)
    apply law.congr_deriv
    simp only [transformedJet]
    field_simp [lapseNonzero r hr, normalization]
    ring
  · intro r hr
    have coefficientDeriv : HasDerivAt (fun s => partnerCoefficient frequency rate (weight s))
        (2 * weight r * weightJet r / lapse r) r := by
      have law := (((weightDeriv r hr).mul (weightDeriv r hr)).const_add
        (frequency ^ 2)).sub_const (rate ^ 2)
      simp only [partnerCoefficient, pow_two, Pi.mul_apply] at law ⊢
      apply law.congr_deriv
      ring
    have law := (((weightDeriv r hr).mul (minus.jetDeriv r hr)).add
      (coefficientDeriv.mul (minus.valueDeriv r hr))).div_const (rate + frequency)
    apply law.congr_deriv
    simp only [transformedValue]
    field_simp [lapseNonzero r hr, normalization]
    ring

/-! ## B. Schwarzschild specialization -/

/-- The Schwarzschild exterior lapse in units with black-hole mass one. -/
def lapse (r : ℂ) : ℂ := 1 - 2 / r

/-- The angular parameter used in the Zerilli potential for multipole order ell. -/
def angularParameter (ell : ℕ) : ℝ := ((ell : ℝ) - 1) * ((ell : ℝ) + 2) / 2

/-- The rate associated with the algebraically special frequency. It is positive
for the physical angular parameter. -/
def specialRate (parameter : ℂ) : ℂ := parameter * (parameter + 1) / 3

/-- The Schwarzschild superpotential for the Regge–Wheeler and Zerilli pair. -/
def superpotential (parameter r : ℂ) : ℂ :=
  specialRate parameter + 3 * lapse r / (r * (parameter * r + 3))

/-- The odd-parity Regge–Wheeler potential for unit black-hole mass. -/
def reggeWheelerPotential (parameter r : ℂ) : ℂ :=
  lapse r * ((2 * parameter + 2) / r ^ 2 - 6 / r ^ 3)

/-- The even-parity Zerilli potential for unit black-hole mass. -/
def zerilliPotential (parameter r : ℂ) : ℂ :=
  2 * lapse r * (parameter ^ 2 * (parameter + 1) * r ^ 3 + 3 * parameter ^ 2 * r ^ 2 +
    9 * parameter * r + 9) / (r ^ 3 * (parameter * r + 3) ^ 2)

/-- The tortoise derivative of the Schwarzschild superpotential in rational form. -/
private def superpotentialJet (parameter r : ℂ) : ℂ :=
  let denominator := r * (parameter * r + 3)
  lapse r * (3 * ((2 / r ^ 2) * denominator -
    lapse r * (2 * parameter * r + 3)) / denominator ^ 2)

private lemma exterior_denominators {ell : ℕ} (hell : 2 ≤ ell) {r : ℝ} (hr : 2 < r) :
    (r : ℂ) ≠ 0 ∧ (angularParameter ell : ℂ) * (r : ℂ) + 3 ≠ 0 ∧ lapse (r : ℂ) ≠ 0 := by
  have rPos : 0 < r := lt_trans (by norm_num) hr
  have ellGe : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have ellGt : (1 : ℝ) < ell := lt_of_lt_of_le (by norm_num) ellGe
  have parameterPos : 0 < angularParameter ell := by
    unfold angularParameter
    exact div_pos (mul_pos (sub_pos.mpr ellGt) (by positivity)) (by norm_num)
  have denomPos : 0 < angularParameter ell * r + 3 :=
    add_pos (mul_pos parameterPos rPos) (by norm_num)
  have lapsePos : 0 < 1 - 2 / r :=
    sub_pos.mpr ((div_lt_iff₀ rPos).mpr (by simpa using hr))
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast rPos.ne'
  · exact_mod_cast denomPos.ne'
  · unfold lapse
    exact_mod_cast lapsePos.ne'

private lemma superpotential_derivative (parameter r : ℂ) (hr : r ≠ 0)
    (hden : parameter * r + 3 ≠ 0) :
    HasDerivAt (superpotential parameter)
      (3 * ((2 / r ^ 2) * (r * (parameter * r + 3)) -
        lapse r * (2 * parameter * r + 3)) / (r * (parameter * r + 3)) ^ 2) r := by
  have lapseDeriv : HasDerivAt lapse (2 / r ^ 2) r := by
    have law := (hasDerivAt_const r (1 : ℂ)).sub
      ((hasDerivAt_const r (2 : ℂ)).div (hasDerivAt_id r) hr)
    apply law.congr_deriv
    simp [neg_div]
  have denominatorDeriv : HasDerivAt (fun s : ℂ => s * (parameter * s + 3))
      (2 * parameter * r + 3) r := by
    have law := (hasDerivAt_id r).mul (((hasDerivAt_id r).const_mul parameter).add_const 3)
    apply law.congr_deriv
    change 1 * (parameter * r + 3) + r * (parameter * 1) = 2 * parameter * r + 3
    ring
  have law := ((lapseDeriv.const_mul 3).div denominatorDeriv (mul_ne_zero hr hden)).const_add
    (specialRate parameter)
  apply law.congr_deriv
  ring

private lemma potential_factorization (parameter r : ℂ) (hr : r ≠ 0)
    (hden : parameter * r + 3 ≠ 0) :
    reggeWheelerPotential parameter r =
      superpotential parameter r ^ 2 - superpotentialJet parameter r - specialRate parameter ^ 2 ∧
    zerilliPotential parameter r =
      superpotential parameter r ^ 2 + superpotentialJet parameter r -
        specialRate parameter ^ 2 := by
  dsimp only [superpotential, specialRate, reggeWheelerPotential, zerilliPotential,
    superpotentialJet, lapse]
  generalize heq : parameter * r + 3 = denominator at hden ⊢
  constructor <;> field_simp [hr, hden] <;> rw [← heq] <;> ring

/-- On the Schwarzschild exterior at unit mass, the normalized Darboux map sends a
Regge–Wheeler solution to a Zerilli solution at the same frequency and multipole. -/
lemma reggeWheeler_to_zerilli (ell : ℕ) (hell : 2 ≤ ell) (frequency : ℂ)
    (normalization : specialRate (angularParameter ell : ℂ) + frequency ≠ 0)
    {value jet : ℝ → ℂ}
    (odd : RadialSolution 2 (fun r => lapse (r : ℂ))
      (fun r => frequency ^ 2 + reggeWheelerPotential (angularParameter ell : ℂ) (r : ℂ))
      value jet) :
    RadialSolution 2 (fun r => lapse (r : ℂ))
      (fun r => frequency ^ 2 + zerilliPotential (angularParameter ell : ℂ) (r : ℂ))
      (fun r => transformedValue frequency (specialRate (angularParameter ell : ℂ))
        (superpotential (angularParameter ell : ℂ) (r : ℂ)) (value r) (jet r))
      (fun r => transformedJet frequency (specialRate (angularParameter ell : ℂ))
        (superpotential (angularParameter ell : ℂ) (r : ℂ)) (value r) (jet r)) := by
  let parameter : ℂ := angularParameter ell
  let weight : ℝ → ℂ := fun r => superpotential parameter (r : ℂ)
  let weightJet : ℝ → ℂ := fun r => superpotentialJet parameter (r : ℂ)
  have factors (r : ℝ) (hr : 2 < r) :
      partnerCoefficient frequency (specialRate parameter) (weight r) - weightJet r =
        frequency ^ 2 + reggeWheelerPotential parameter (r : ℂ) ∧
      partnerCoefficient frequency (specialRate parameter) (weight r) + weightJet r =
        frequency ^ 2 + zerilliPotential parameter (r : ℂ) := by
    obtain ⟨hr0, hden, _⟩ := exterior_denominators hell hr
    obtain ⟨oddFactor, evenFactor⟩ := potential_factorization parameter (r : ℂ) hr0 hden
    constructor
    · rw [oddFactor]
      dsimp [partnerCoefficient, weight, weightJet]
      ring
    · rw [evenFactor]
      dsimp [partnerCoefficient, weight, weightJet]
      ring
  have minus : RadialSolution 2 (fun r => lapse (r : ℂ))
      (fun r => partnerCoefficient frequency (specialRate parameter) (weight r) - weightJet r)
      value jet := by
    refine ⟨odd.valueDeriv, ?_⟩
    intro r hr
    simpa only [(factors r hr).1] using odd.jetDeriv r hr
  have weightDeriv : ∀ r : ℝ, 2 < r →
      HasDerivAt weight (weightJet r / lapse (r : ℂ)) r := by
    intro r hr
    obtain ⟨hr0, hden, hf⟩ := exterior_denominators hell hr
    have law := (superpotential_derivative parameter (r : ℂ) hr0 hden).comp_ofReal
    apply law.congr_deriv
    simp only [weightJet, superpotentialJet, mul_div_cancel_left₀ _ hf]
  have plus := transform_partner frequency (specialRate parameter) normalization
    (fun _ hr => (exterior_denominators hell hr).2.2) weightDeriv minus
  exact ⟨plus.valueDeriv, fun r hr => by simpa only [(factors r hr).2] using plus.jetDeriv r hr⟩

end

end GeneralRelativity.Schwarzschild.Darboux
